(ns authz.attrs
  "Attribute-level allow rules for occasionally-connected systems.

  Each type definition may declare an `:attrs` allow-list mapping Datomic
  attributes to the permissions that gate them:

    :attrs  {:assignment/notes  {:read :view :write :react}
             :assignment/member {:read :view}}          ; readable, never writable
    :create '(-> :assignment/organisation :edit)        ; who may create one
    :delete :edit                                       ; perm gating :db/retractEntity

  Everything is deny-by-default: an attribute not declared in any `:attrs`
  section can neither be synced down to a client nor written by one. That
  makes role/relationship attributes (org admins, managerships) server-managed
  unless you explicitly open them up.

  Two directions:

    readable-datoms   sync DOWN — filter datoms (e.g. from the tx-report
                      queue) to what a subject may see before pushing them
                      to a client.
    check-tx          sync UP — authorization-check a transaction submitted
                      by a client before transacting it. `authorize-tx!` is
                      the throwing guard variant.

  ## How check-tx judges a transaction

  The transaction is applied *speculatively* with d/with and the ACTUAL
  resulting datoms are checked — not the tx forms. That means Datomic
  handles map expansion, nested maps, reverse attrs, cardinality, lookup
  refs and (crucially) upserts: a tempid that resolves to an existing entity
  via a unique-identity attribute is checked as a WRITE to that entity, not
  as a creation. No-op re-assertions produce no datoms and cost nothing, so
  offline clients may re-send whole entity maps.

  Authority is always anchored in the pre-transaction db: writes to existing
  entities and chain targets that already exist are judged against db-before,
  so a transaction cannot grant itself permissions and use them in the same
  breath. Every genuinely new entity must pass its own type's `:create` rule
  (or the tx is denied), which is why a create-chain may target another
  entity created in the same transaction, judged on the speculative snapshot.

  Arbitrary transaction functions are refused BEFORE the speculative apply,
  so unvetted code never executes; :db/cas is the sanctioned exception."
  (:require [authz.core :as core]
            [authz.schema :as schema]
            [datomic.api :as d]))

;; ---------------------------------------------------------------------------
;; Introspection

(defn attr-spec
  "{:type <entity-type> :read <perm> :write <perm> ...} for a declared
  attribute, or nil when the attribute is not in any :attrs section."
  [schema attr]
  (when-let [t (get-in schema [:attr->type attr])]
    (assoc (get-in schema [:types t :attrs attr]) :type t)))

(defn readable-attrs [schema type] (get-in schema [:types type :readable]))
(defn writable-attrs [schema type] (get-in schema [:types type :writable]))
(defn creatable-attrs [schema type] (get-in schema [:types type :settable-at-create]))

(defn can-read-attr?
  "May `subject-eid` read `attr` off `object-eid`?"
  [schema db subject-eid attr object-eid]
  (boolean
   (when-let [{:keys [type read]} (attr-spec schema attr)]
     (when read
       (core/can? schema db (core/subject-type schema type read)
                  subject-eid read type object-eid)))))

(defn can-write-attr?
  "May `subject-eid` write `attr` on the existing entity `object-eid`?"
  [schema db subject-eid attr object-eid]
  (boolean
   (when-let [{:keys [type write]} (attr-spec schema attr)]
     (when write
       (core/can? schema db (core/subject-type schema type write)
                  subject-eid write type object-eid)))))

;; ---------------------------------------------------------------------------
;; Sync down: datom filtering

(defn- datom-eav
  "Accepts datomic.Datom objects, maps with :e/:a/:v, or [e a v] vectors.
  Numeric attribute ids are resolved to idents."
  [db d]
  (let [[e a v] (if (sequential? d)
                  [(nth d 0) (nth d 1) (nth d 2)]
                  [(:e d) (:a d) (:v d)])]
    [e (if (keyword? a) a (d/ident db a)) v]))

(defn readable-datoms
  "Filters `datoms` down to those `subject-eid` may read, deny-by-default.
  Returns {:allowed [datom ...] :denied [{:datom d :reason kw} ...]} preserving
  input order within each group. Batched: one authorization query per
  (entity-type, read-permission) pair, however many datoms come in."
  [schema db subject-eid datoms]
  (let [classified
        (mapv (fn [d]
                (let [[e a _] (datom-eav db d)
                      spec (attr-spec schema a)]
                  (cond
                    (nil? spec) {:datom d :reason :authz/undeclared-attr}
                    (nil? (:read spec)) {:datom d :reason :authz/attr-not-readable}
                    :else {:datom d :check [(:type spec) (:read spec)] :e e})))
              datoms)
        allowed-eids
        (into {}
              (map (fn [[[type perm] items]]
                     [[type perm]
                      (core/filter-authorized schema db
                                              (core/subject-type schema type perm)
                                              subject-eid perm type
                                              (into #{} (map :e) items))]))
              (group-by :check (filter :check classified)))]
    (reduce (fn [acc {:keys [datom reason check e]}]
              (cond
                reason
                (update acc :denied conj {:datom datom :reason reason})
                (contains? (get allowed-eids check) e)
                (update acc :allowed conj datom)
                :else
                (update acc :denied conj {:datom datom :reason :authz/not-authorized})))
            {:allowed [] :denied []}
            classified)))

;; ---------------------------------------------------------------------------
;; Sync up: transaction checking

(defn- entid
  "d/entid that returns nil instead of throwing on unresolvable input
  (e.g. a lookup ref whose value does not exist)."
  [db e]
  (try (d/entid db e) (catch Exception _ nil)))

(defn- existed-before?
  [db eid]
  (boolean (seq (d/datoms db :eavt eid))))

(defn- ref-attr?
  [db a]
  (= :db.type/ref (:value-type (d/attribute db a))))

(defn- deny
  [d reason message]
  (-> (select-keys d [:e :a :v :added :form])
      (assoc :reason reason :message message)))

(def ^:private supported-ops
  #{:db/add :db/retract :db/cas :db.fn/cas :db/retractEntity :db.fn/retractEntity})

(defn- pre-scan
  "Refuses tx forms this layer will not speculatively execute (arbitrary
  transaction functions) and resolves :db/retractEntity targets. Runs
  BEFORE d/with, so unvetted code never executes."
  [db tx-data]
  (reduce
   (fn [acc form]
     (cond
       (map? form)
       acc

       (and (sequential? form) (contains? supported-ops (first form)))
       (if (contains? #{:db/retractEntity :db.fn/retractEntity} (first form))
         (if-let [eid (entid db (second form))]
           (update acc :retract-targets conj {:eid eid :form form})
           (update acc :denied conj
                   (deny {:form form} :authz/unknown-entity
                         (str "entity " (pr-str (second form)) " does not exist"))))
         acc)

       :else
       (update acc :denied conj
               (deny {:form form} :authz/unsupported-op
                     "only map forms, :db/add, :db/retract, :db/cas and :db/retractEntity are allowed"))))
   {:denied [] :retract-targets []}
   tx-data))

(defn- dedupe-write-denials
  "A cardinality-one overwrite yields two datoms (assert + retract of the
  old value) — one logical write, one denial."
  [denials]
  (:out (reduce (fn [{:keys [seen] :as acc} d]
                  (let [k [(:e d) (:a d) (:reason d)]]
                    (if (contains? seen k)
                      acc
                      {:seen (conj seen k) :out (conj (:out acc) d)})))
                {:seen #{} :out []}
                denials)))

(defn- check-existing-writes
  "Denials for datoms touching pre-existing entities. Point checks are
  batched: one query per (type, write-permission) pair. Judged against
  db-before — a tx cannot grant itself write access and use it."
  [schema db subject-eid datom-maps]
  (let [classified
        (mapv (fn [{:keys [a] :as dm}]
                (let [spec (attr-spec schema a)]
                  (cond
                    (nil? spec)
                    (assoc dm :denial (deny dm :authz/undeclared-attr
                                            (str a " is not declared in any :attrs section")))
                    (nil? (:write spec))
                    (assoc dm :denial (deny dm :authz/attr-not-writable
                                            (str a " is not writable")))
                    :else
                    (assoc dm :check [(:type spec) (:write spec)]))))
              datom-maps)
        allowed-eids
        (into {}
              (map (fn [[[type perm] items]]
                     [[type perm]
                      (core/filter-authorized schema db
                                              (core/subject-type schema type perm)
                                              subject-eid perm type
                                              (into #{} (map :e) items))]))
              (group-by :check (filter :check classified)))]
    (dedupe-write-denials
     (keep (fn [{:keys [denial check e] :as dm}]
             (cond
               denial denial
               (not (contains? (get allowed-eids check) e))
               (deny dm :authz/not-authorized
                     (str "subject lacks " (second check) " on this " (first check)))))
           classified))))

(defn- eval-create
  "Evaluates a :create rule against the (speculatively resolved) datoms of
  one new entity. Returns true or a {:reason .. :message ..} denial."
  [schema db db-after subject-eid type node ent-datoms new-eids]
  (let [rel-values (fn [rel] (into [] (comp (filter #(= (:a %) rel)) (map :v)) ent-datoms))]
    (case (:op node)
      :relation
      (if (some #(= subject-eid %) (rel-values (:relation node)))
        true
        {:reason :authz/create-denied
         :message (str "create requires " (:relation node) " to be the subject")})

      :attr=
      (if (some #(= (:value node) %) (rel-values (:attr node)))
        true
        {:reason :authz/create-denied
         :message (str "create requires " (:attr node) " to be " (pr-str (:value node)))})

      :chain
      (let [rel (:relation node)
            perm (:permission node)
            target-type (get-in schema [:types type :relations rel])
            st (core/subject-type schema target-type perm)
            targets (rel-values rel)]
        (cond
          (empty? targets)
          {:reason :authz/create-denied
           :message (str "create requires " rel " to be set")}

          (some (fn [t]
                  (cond
                    (existed-before? db t)
                    (core/can? schema db st subject-eid perm target-type t)
                    ;; The target is created in this same tx. It passes its
                    ;; own create rule or the whole tx is denied, so judging
                    ;; the permission on the speculative snapshot is safe.
                    (contains? new-eids t)
                    (core/can? schema db-after st subject-eid perm target-type t)
                    :else false))
                targets)
          true

          :else
          {:reason :authz/create-denied
           :message (str "create requires " perm " on the entity at " rel)}))

      :and
      (loop [bs (:branches node)]
        (if-let [[b & more] (seq bs)]
          (let [r (eval-create schema db db-after subject-eid type b ent-datoms new-eids)]
            (if (true? r) (recur more) r))
          true))

      :or
      (loop [bs (:branches node) denial nil]
        (if-let [[b & more] (seq bs)]
          (let [r (eval-create schema db db-after subject-eid type b ent-datoms new-eids)]
            (if (true? r) true (recur more r)))
          denial)))))

(defn- check-new-entity
  "All denials for one new entity's datoms (empty seq when allowed)."
  [schema db db-after subject-eid new-eids ent-datoms]
  (let [attr->type (:attr->type schema)
        undeclared (remove #(contains? attr->type (:a %)) ent-datoms)
        declared (filter #(contains? attr->type (:a %)) ent-datoms)
        types (into #{} (map #(attr->type (:a %))) declared)]
    (concat
     (map #(deny % :authz/undeclared-attr
                 (str (:a %) " is not declared in any :attrs section"))
          undeclared)
     (cond
       (empty? declared)
       nil ; every datom already denied as undeclared

       (< 1 (count types))
       (map #(deny % :authz/ambiguous-entity-type
                   (str "new entity mixes attrs of types " types))
            declared)

       :else
       (let [type (first types)
             {:keys [create settable-at-create]} (get-in schema [:types type])]
         (if (nil? create)
           (map #(deny % :authz/no-create-rule
                       (str "type " type " has no :create rule"))
                declared)
           (let [verdict (eval-create schema db db-after subject-eid type create
                                      declared new-eids)]
             (if (true? verdict)
               (keep #(when-not (contains? settable-at-create (:a %))
                        (deny % :authz/attr-not-creatable
                              (str (:a %) " may not be set at creation")))
                     declared)
               (map #(deny % (:reason verdict) (:message verdict)) declared)))))))))

(defn- entity-type-of
  "Resolve an existing entity's type via its declared attributes."
  [schema db e]
  (let [types (into #{} (keep (:attr->type schema)) (keys (d/entity db e)))]
    (case (count types)
      1 (first types)
      0 nil
      types)))

(defn- check-retract-entity
  [schema db subject-eid {:keys [eid form]}]
  (let [type (entity-type-of schema db eid)]
    (cond
      (nil? type)
      (deny {:e eid :form form} :authz/unknown-entity-type
            "entity has no attributes declared in any :attrs section")

      (set? type)
      (deny {:e eid :form form} :authz/ambiguous-entity-type
            (str "entity mixes attrs of types " type))

      :else
      (if-let [delete-perm (get-in schema [:types type :delete])]
        (when-not (core/can? schema db
                             (core/subject-type schema type delete-perm)
                             subject-eid delete-perm type eid)
          (deny {:e eid :form form} :authz/not-authorized
                (str "subject lacks " delete-perm " on this " type)))
        (deny {:e eid :form form} :authz/no-delete-rule
              (str "type " type " has no :delete rule"))))))

(defn- check-dangling-refs
  "A ref value pointing at a new entity that has no datoms of its own (a
  tempid used only in value position) would silently create an empty
  entity."
  [db db-after new-eids tx-eid datom-maps]
  (keep (fn [{:keys [a v added] :as dm}]
          (when (and added
                     (ref-attr? db-after a)
                     (integer? v)
                     (not= v tx-eid)
                     (not (existed-before? db v))
                     (not (contains? new-eids v)))
            (deny dm :authz/dangling-tempid
                  "reference to a new entity that has no attributes of its own")))
        datom-maps))

(defn check-tx
  "Authorization-checks `tx-data` as submitted on behalf of `subject-eid`,
  against `db`, deny-by-default. The tx is applied speculatively (d/with)
  and the actual resulting datoms are judged — see the namespace docstring
  for the model. Nothing is durably transacted.

  Returns {:allowed? bool
           :denied   [{:e .. :a .. :v .. :reason kw :message str} ...]
           :ops      <count of checked datoms and entity retractions>}"
  [schema db subject-eid tx-data]
  (when-not (schema/compiled? schema)
    (throw (ex-info "authz: expected a compiled schema (see authz.schema/compile-schema)"
                    {:authz/error true :got schema})))
  (let [subject-eid (or (entid db subject-eid)
                        (throw (ex-info "authz: unknown subject"
                                        {:authz/error true :subject subject-eid})))
        {:keys [denied retract-targets]} (pre-scan db tx-data)]
    (if (seq denied)
      {:allowed? false :denied (vec denied) :ops (count tx-data)}
      (let [result (try {:ok (d/with db tx-data)}
                        (catch Exception e
                          {:err (or (.getMessage e) (str (class e)))}))]
        (if-let [err (:err result)]
          {:allowed? false
           :denied [(deny {} :authz/invalid-tx
                          (str "transaction does not apply: " err))]
           :ops (count tx-data)}
          (let [{:keys [db-after] spec-tx-data :tx-data} (:ok result)
                tx-eid (:tx (first spec-tx-data))
                retract-eids (into #{} (map :eid) retract-targets)
                dms (into []
                          (comp (remove #(contains? retract-eids (:e %)))
                                (map (fn [d] {:e (:e d)
                                              :a (d/ident db-after (:a d))
                                              :v (:v d)
                                              :added (:added d)}))
                                ;; the reified transaction's own timestamp;
                                ;; any OTHER datom on the tx entity (client-
                                ;; supplied tx metadata) is still checked
                                (remove #(and (= tx-eid (:e %))
                                              (= :db/txInstant (:a %)))))
                          spec-tx-data)
                grouped (group-by #(existed-before? db (:e %)) dms)
                existing (get grouped true [])
                new-by-e (group-by :e (get grouped false []))
                new-eids (set (keys new-by-e))
                denied (-> []
                           (into (check-existing-writes schema db subject-eid existing))
                           (into (mapcat #(check-new-entity schema db db-after subject-eid
                                                            new-eids %)
                                         (vals new-by-e)))
                           (into (keep #(check-retract-entity schema db subject-eid %)
                                       retract-targets))
                           (into (check-dangling-refs db db-after new-eids tx-eid dms)))]
            {:allowed? (empty? denied)
             :denied denied
             :ops (+ (count dms) (count retract-targets))}))))))

(defn authorize-tx!
  "Guard variant of `check-tx`: returns `tx-data` unchanged when fully
  allowed (so it threads straight into d/transact), otherwise throws ex-info
  carrying the full check-tx report."
  [schema db subject-eid tx-data]
  (let [report (check-tx schema db subject-eid tx-data)]
    (if (:allowed? report)
      tx-data
      (throw (ex-info (str "authz: transaction denied ("
                           (count (:denied report)) " of " (:ops report)
                           " operations)")
                      (assoc report :authz/denied true))))))
