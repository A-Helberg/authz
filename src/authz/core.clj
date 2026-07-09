(ns authz.core
  "The three consumption APIs over a compiled authz schema:

    can?              point check (write-path guards, single reads)
    list-query        :where clauses to splice into list queries
    list-query-attrs  transitive attribute watch-set for reactive invalidation

  plus `filter-authorized`, a batched point check (one query for many
  entities) used heavily by the attribute layer.

  All compilation happened in `authz.schema/compile-schema`; everything here
  is a lookup plus (for the checks) a single Datomic query against the
  caller's `db` snapshot."
  (:require [authz.schema :as schema]
            [clojure.walk :as walk]
            [datomic.api :as d]))

(defn- compiled-entry
  [schema object-type permission]
  (when-not (schema/compiled? schema)
    (throw (ex-info "authz: expected a compiled schema (see authz.schema/compile-schema)"
                    {:authz/error true :got schema})))
  (or (get-in schema [:compiled [object-type permission]])
      (throw (ex-info (str "authz: unknown permission " permission " on type " object-type)
                      {:authz/error true
                       :object-type object-type
                       :permission permission
                       :known (->> (keys (:compiled schema))
                                   (filter #(= object-type (first %)))
                                   (map second)
                                   set)}))))

(defn subject-type
  "The subject type a permission's terminals unify with (inferred at
  compile time)."
  [schema object-type permission]
  (:subject-type (compiled-entry schema object-type permission)))

(defn- check-subject-type!
  [entry subject-type]
  (when (not= subject-type (:subject-type entry))
    (throw (ex-info (str "authz: permission " (:permission entry) " on "
                         (:object-type entry) " checks subjects of type "
                         (:subject-type entry) ", not " subject-type)
                    {:authz/error true
                     :object-type (:object-type entry)
                     :permission (:permission entry)
                     :expected (:subject-type entry)
                     :got subject-type}))))

;; ---------------------------------------------------------------------------
;; list-query

(defn- clause-vars
  [clauses]
  (let [vars (volatile! #{})]
    (walk/postwalk (fn [x]
                     (when (and (symbol? x) (.startsWith (name x) "?"))
                       (vswap! vars conj x))
                     x)
                   clauses)
    @vars))

(defn- rename-vars
  [entry {:keys [object-var subject-var]}]
  (let [{stored-obj :object-var stored-subj :subject-var clauses :clauses} entry
        object-var (or object-var stored-obj)
        subject-var (or subject-var stored-subj)]
    (doseq [v [object-var subject-var]]
      (when-not (and (symbol? v) (.startsWith (name v) "?"))
        (throw (ex-info "authz: query vars must be symbols starting with ?"
                        {:authz/error true :var v}))))
    (when (= object-var subject-var)
      (throw (ex-info "authz: object and subject vars must differ"
                      {:authz/error true :var object-var})))
    (let [internal (disj (clause-vars clauses) stored-obj stored-subj)]
      (doseq [v [object-var subject-var]]
        (when (contains? internal v)
          (throw (ex-info "authz: var collides with an internal query variable"
                          {:authz/error true :var v :internal internal})))))
    {:object-var object-var
     :subject-var subject-var
     :clauses (if (and (= object-var stored-obj) (= subject-var stored-subj))
                clauses
                (walk/postwalk-replace {stored-obj object-var
                                        stored-subj subject-var}
                                       clauses))}))

(defn- checked-list-entry
  [schema object-type permission subject-type opts]
  (let [entry (compiled-entry schema object-type permission)]
    (check-subject-type! entry subject-type)
    (when (and (:collision? entry)
               (not (and (:object-var opts) (:subject-var opts))))
      (throw (ex-info (str "authz: " object-type " " permission " has subject type "
                           subject-type "; pass explicit :object-var and :subject-var "
                           "to disambiguate the query variables")
                      {:authz/error true
                       :object-type object-type
                       :permission permission})))
    entry))

(defn list-query
  "Returns a vector of Datalog :where clauses binding ?<object-type> and
  ?<subject-type> (e.g. ?assignment and ?user). Concat these with your own
  clauses so list endpoints only return rows the subject may see.

  When object type and subject type coincide the default variable names
  would collapse the check, so you must pass explicit :object-var and
  :subject-var in `opts`. Opts may also rename the vars in any query.

  Permissions that involve recursion cannot be expressed as bare clauses —
  they need Datomic rules alongside. This fn fails loudly for those; use
  `list-query*`, which works for every permission."
  ([schema object-type permission subject-type]
   (list-query schema object-type permission subject-type nil))
  ([schema object-type permission subject-type opts]
   (let [entry (checked-list-entry schema object-type permission subject-type opts)]
     (when (seq (:rules entry))
       (throw (ex-info (str "authz: " object-type " " permission " involves a recursive "
                            "permission and needs Datomic rules — use list-query*, put % "
                            "in your :in, and pass its :rules as that input")
                       {:authz/error true
                        :object-type object-type
                        :permission permission})))
     (:clauses (rename-vars entry opts)))))

(defn list-query*
  "Like `list-query`, but returns {:where [...] :rules [...]} and works for
  every permission, recursive or not (:rules is empty when no recursion is
  involved). When :rules is non-empty, include % in your query's :in and
  pass the rules as that input:

    (d/q {:find '[?folder] :in '[$ % ?user]
          :where (into (:where lq) my-clauses)}
         db (:rules lq) user-eid)"
  ([schema object-type permission subject-type]
   (list-query* schema object-type permission subject-type nil))
  ([schema object-type permission subject-type opts]
   (let [entry (checked-list-entry schema object-type permission subject-type opts)]
     {:where (:clauses (rename-vars entry opts))
      :rules (:rules entry)})))

(defn list-query-attrs
  "The set of Datomic attributes the compiled permission touches, transitively
  through chains and ors. Reactive layers include these in their watch-set so
  permission changes live-update subscribed clients."
  [schema object-type permission]
  (:attrs (compiled-entry schema object-type permission)))

;; ---------------------------------------------------------------------------
;; Point checks
;;
;; With both endpoints bound, direct index traversal beats a Datalog query
;; by an order of magnitude (~40x on terminal hits, ~10x on deep chains):
;; it skips per-query setup and short-circuits *inside* chains and ors,
;; where a single or-join query must evaluate every branch. Same immutable
;; db snapshot, same semantics — the generative differential suite holds
;; this walker and the clause compiler (used by list-query and
;; filter-authorized) to identical answers.

(defn- datoms*
  "d/datoms that treats an attribute unknown to the db schema as having no
  datoms, matching query behavior on partially-migrated databases."
  [db index e a]
  (try (d/datoms db index e a) (catch Exception _ nil)))

(defn- walk-check
  "Direct index-walk evaluation of a check node. `seen` is the path-scoped
  set of [type perm eid] states already being explored: recursive schemas
  plus cyclic data (folder A parent of B parent of A) would otherwise loop.
  Cutting a revisit to false is sound for the least fixed point — any
  grant that revisits its own derivation state has a shorter loop-free
  derivation (and recursion through negation is rejected at compile time)."
  [schema db type node subject-eid eid seen]
  (case (:op node)
    :relation
    (let [rel (:relation node)]
      (if (schema/reverse-relation? rel)
        (boolean (some #(= subject-eid (:e %))
                       (datoms* db :vaet eid (schema/underlying-attr rel))))
        (boolean (some #(= subject-eid (:v %)) (datoms* db :eavt eid rel)))))

    :attr=
    (boolean (some #(= (:value node) (:v %)) (datoms* db :eavt eid (:attr node))))

    :chain
    (let [rel (:relation node)
          target (get-in schema [:types type :relations rel])
          tperm (:permission node)
          tnode (get-in schema [:types target :permissions tperm])
          recursive? (contains? (:recursive schema) [target tperm])
          step (fn [teid]
                 (if recursive?
                   (let [k [target tperm teid]]
                     (when-not (contains? seen k)
                       (walk-check schema db target tnode subject-eid teid (conj seen k))))
                   (walk-check schema db target tnode subject-eid teid seen)))]
      (boolean
       (if (schema/reverse-relation? rel)
         (some #(step (:e %)) (datoms* db :vaet eid (schema/underlying-attr rel)))
         (some #(step (:v %)) (datoms* db :eavt eid rel)))))

    :not
    (not (walk-check schema db type (:branch node) subject-eid eid seen))

    :and
    (every? #(walk-check schema db type % subject-eid eid seen) (:branches node))

    :or
    (boolean (some #(walk-check schema db type % subject-eid eid seen) (:branches node)))))

(defn can?
  "Point check: may `subject-eid` exercise `permission` over `object-eid`?
  Evaluated by direct index traversal against `db`, cheapest branch first,
  short-circuiting on the first grant — most real checks hit a direct
  terminal (e.g. \"is the assignee\") without ever walking the hierarchy.
  Subject and object accept any entity identifier (eid, lookup ref, ident);
  an identifier that resolves to nothing yields false."
  [schema db subject-type subject-eid permission object-type object-eid]
  (let [entry (compiled-entry schema object-type permission)]
    (check-subject-type! entry subject-type)
    (let [subject-eid (d/entid db subject-eid)
          object-eid (d/entid db object-eid)]
      (boolean
       (and subject-eid object-eid
            (some #(walk-check schema db object-type (:node %) subject-eid object-eid #{})
                  (:branches entry)))))))

(defn explain
  "Like `can?` but reports which branch granted:
  {:granted? true :via <check-form>} on the first (cheapest) granting
  branch, or {:granted? false :tried [<check-form> ...]} listing every
  branch that was evaluated and refused."
  [schema db subject-type subject-eid permission object-type object-eid]
  (let [entry (compiled-entry schema object-type permission)
        _ (check-subject-type! entry subject-type)
        subject-eid (d/entid db subject-eid)
        object-eid (d/entid db object-eid)]
    (reduce (fn [acc {:keys [node source]}]
              (if (and subject-eid object-eid
                       (walk-check schema db object-type node subject-eid object-eid #{}))
                (reduced {:granted? true :via source})
                (update acc :tried conj source)))
            {:granted? false :tried []}
            (:branches entry))))

(defn filter-authorized
  "Batched `can?`: returns the subset of `object-eids` (as a set) over which
  `subject-eid` holds `permission`. One query regardless of collection size.
  Recursive permissions are handled transparently (their rules travel with
  the query)."
  [schema db subject-type subject-eid permission object-type object-eids]
  (let [{:keys [object-var subject-var clauses rules] :as entry}
        (compiled-entry schema object-type permission)]
    (check-subject-type! entry subject-type)
    (if (empty? object-eids)
      #{}
      (into #{}
            (map first)
            (if (seq rules)
              (d/q {:find [object-var]
                    :in ['$ '% subject-var [object-var '...]]
                    :where clauses}
                   db rules subject-eid (vec object-eids))
              (d/q {:find [object-var]
                    :in ['$ subject-var [object-var '...]]
                    :where clauses}
                   db subject-eid (vec object-eids)))))))
