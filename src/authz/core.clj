(ns authz.core
  "The consumption APIs over a compiled authz schema — three composable
  primitives, each a different artifact so the consumer always owns the
  query:

    can?              predicate — point check (write-path guards, single
                      reads, filtering a walk of your own index)
    list-query        clauses — :where clauses to splice into list queries
    grants            source — lazy, deduplicated enumeration of the
                      objects a subject holds a permission over

  plus helpers built on them: `explain` (the why), `filter-authorized`
  (batched point check — one query for many entities, used heavily by the
  attribute layer), `grants-page` (cursor pagination over `grants`) and
  `list-query-attrs` (transitive attribute watch-set for reactive
  invalidation).

  All compilation happened in `authz.schema/compile-schema`; everything here
  is a lookup plus index traversal or a single Datomic query against the
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
         db (:rules lq) user-eid)

  Pass {:all-rules? true} in `opts` to compile EVERY permission to a
  named Datomic rule instead of inlining non-recursive subtrees: :where
  becomes a single rule invocation and :rules carries a definition per
  reachable permission. Same answers (the generative differential suite
  holds both to the oracles); the trade-off is query-engine plan shape —
  named reusable subtrees versus one large or-join. Benchmark on your
  workload before preferring it; see ROADMAP for measurements."
  ([schema object-type permission subject-type]
   (list-query* schema object-type permission subject-type nil))
  ([schema object-type permission subject-type opts]
   (let [entry (checked-list-entry schema object-type permission subject-type opts)]
     (if (:all-rules? opts)
       {:where (:clauses (rename-vars (assoc entry :clauses (:clauses-rules entry)) opts))
        :rules (:rules-all entry)}
       {:where (:clauses (rename-vars entry opts))
        :rules (:rules entry)}))))

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

;; ---------------------------------------------------------------------------
;; grants: the enumeration ("source") primitive
;;
;; can? answers one (subject, object) pair; list-query lets the DB filter a
;; query — but Datalog materializes its full result set, so neither can hand
;; a UI page 3 of a 500k-row authorized set. `grants` enumerates instead:
;; the permission graph is traversed outward from the subject over the same
;; indexes the point-check walker uses, lazily, so nothing is built ahead of
;; consumption.
;;
;; Mechanism: `gen-graph` statically extracts the permission's *generating
;; dependency closure* — which terminals seed candidate objects for which
;; [type perm] key, and which chains derive one key's candidates from
;; another's (a candidate account derives the products related to it, and
;; so on up to the queried type). `gen-stream` then runs a deterministic
;; depth-first traversal over that graph with request-local dedupe.
;; Recursive permissions need no special handling — their cycle is just an
;; edge back into the same key, cut by the dedupe — so recursive closures
;; enumerate without being materialized. Candidates are exact when the
;; closure is built only from relations, chains and ors; when any
;; (and ...), (not ...) or (attr= ...) participates, generation
;; over-approximates from each conjunction's first generative conjunct and
;; every emitted candidate is verified by the point-check walker.

(defn- rel-sources
  "The entities on the from-side of relation `rel` whose target is `to-eid`
  — the inverse of the walker's traversal direction. Lazy, in index order
  (:vaet for forward relations, :eavt for reverse ones), so iteration order
  is deterministic for a given db basis."
  [db rel to-eid]
  (if (schema/reverse-relation? rel)
    (map :v (datoms* db :eavt to-eid (schema/underlying-attr rel)))
    (map :e (datoms* db :vaet to-eid rel))))

(defn- generative?
  "Can this node produce candidate objects? Mirrors the compile-time
  groundedness rules: conditions and exclusions never generate."
  [node]
  (case (:op node)
    (:relation :chain) true
    (:attr= :not) false
    :and (boolean (some generative? (:branches node)))
    :or (every? generative? (:branches node))))

(defn- gen-positions
  "The :relation and :chain nodes of a check tree that generate candidates.
  Nothing under (not ...) generates; (and ...) generates from its first
  generative conjunct only — a complete superset, since a conjunction's
  result is a subset of any single conjunct's (the remaining conjuncts are
  enforced by per-candidate verification). Compile-time groundedness
  guarantees the generative conjunct exists."
  [node]
  (case (:op node)
    (:relation :chain) [node]
    (:attr= :not) []
    :or (mapcat gen-positions (:branches node))
    :and (gen-positions (first (filter generative? (:branches node))))))

(defn- node-ops
  "All ops appearing anywhere in a check tree."
  [node]
  (into #{}
        (map :op)
        (tree-seq #(contains? #{:or :and :not} (:op %))
                  #(or (:branches %) [(:branch %)])
                  node)))

(defn- gen-graph
  "Static analysis of the generating dependency closure for `root`
  ([object-type permission]):

    :seeds     [{:key [t p] :relation rel} ...] in deterministic discovery
               order — each terminal seeds candidates for its key directly
               from the subject
    :consumers {[t p] -> [{:key [t' p'] :relation rel} ...]} — chains: a
               candidate for [t p] derives candidates for [t' p'], one
               relation hop away
    :verify?   true when any (and ...), (not ...) or (attr= ...) appears in
               the closure — generation then over-approximates and emitted
               candidates must pass the point-check walker"
  [schema root]
  (loop [todo (conj clojure.lang.PersistentQueue/EMPTY root)
         visited #{}
         seeds []
         consumers {}
         verify? false]
    (if-let [[t p :as k] (peek todo)]
      (if (contains? visited k)
        (recur (pop todo) visited seeds consumers verify?)
        (let [node (get-in schema [:types t :permissions p])
              positions (gen-positions node)
              chains (filterv #(= :chain (:op %)) positions)
              chain-keys (mapv (fn [ch]
                                 [(get-in schema [:types t :relations (:relation ch)])
                                  (:permission ch)])
                               chains)]
          (recur (into (pop todo) chain-keys)
                 (conj visited k)
                 (into seeds
                       (keep #(when (= :relation (:op %))
                                {:key k :relation (:relation %)}))
                       positions)
                 (reduce (fn [m [ch ck]]
                           (let [entry {:key k :relation (:relation ch)}]
                             (if (some #{entry} (get m ck))
                               m
                               (update m ck (fnil conj []) entry))))
                         consumers
                         (map vector chains chain-keys))
                 (or verify?
                     (boolean (some #{:and :not :attr=} (node-ops node)))))))
      {:seeds seeds :consumers consumers :verify? verify?})))

(defn- gen-stream
  "Deterministic depth-first traversal of the generating dependency graph,
  outward from the subject, with request-local dedupe per [type perm] key.
  Lazily yields candidate eids of `root` in discovery order. The dedupe
  sets grow with states visited — that is the price of correct enumeration
  over parallel paths and cycles — but the result set itself is never built
  ahead of consumption."
  [db {:keys [seeds consumers]} root subject-eid]
  (letfn [(derived [k eid]
            (map (fn [{ck :key rel :relation}]
                   {:key ck :xs (rel-sources db rel eid)})
                 (get consumers k)))
          (step [stack seen]
            (lazy-seq
             (when-let [{:keys [key xs]} (first stack)]
               (let [tail (rest stack)]
                 (if-let [xs (seq xs)]
                   (let [eid (first xs)
                         cur {:key key :xs (rest xs)}]
                     (if (contains? (get seen key) eid)
                       (step (cons cur tail) seen)
                       (let [seen (update seen key (fnil conj #{}) eid)
                             ;; derived streams go on top (depth-first), in
                             ;; node order, then the rest of this stream
                             stack (into (cons cur tail) (reverse (derived key eid)))]
                         (if (= key root)
                           (cons eid (step stack seen))
                           (step stack seen)))))
                   (step tail seen))))))]
    (step (map (fn [{:keys [key relation]}]
                 {:key key :xs (rel-sources db relation subject-eid)})
               seeds)
          {})))

(defn grants
  "The enumeration primitive: a lazy, deduplicated stream of the object
  eids over which `subject-eid` holds `permission` — the same shape as
  `d/datoms`, for when the permission graph is the cheapest index you have
  (brutal selectivity over huge sets). Produced by direct index traversal
  outward from the subject; no Datalog query runs and nothing is
  materialized ahead of consumption — recursive permissions enumerate
  without materializing their closure.

  Order is deterministic for a given (schema, db basis, subject,
  permission, object type) — stable enough to resume against the same
  basis (see `grants-page`) — but it is a traversal order, NOT a domain
  sort order. When your sort order matters and selectivity is reasonable,
  drive from your own index and filter with `can?` instead.

  Composes like any seq: (take n ...) for a page, (filter pred ...) for
  your own predicates, or feed batches into your own query through an :in
  collection binding. Permissions involving (and ...), (not ...) or
  (attr= ...) verify each candidate by the point-check walker before
  emitting it. A subject identifier that resolves to nothing yields an
  empty seq."
  [schema db subject-type subject-eid permission object-type]
  (let [entry (compiled-entry schema object-type permission)]
    (check-subject-type! entry subject-type)
    (let [subject-eid (d/entid db subject-eid)
          root [object-type permission]
          {:keys [verify?] :as graph} (gen-graph schema root)]
      (if-not subject-eid
        ()
        (cond->> (gen-stream db graph root subject-eid)
          verify? (filter (fn [eid]
                            (some #(walk-check schema db object-type (:node %)
                                               subject-eid eid #{})
                                  (:branches entry)))))))))

(defn grants-page
  "One page of `grants` plus a plain-data cursor for the next:

    {:data [eid ...]
     :cursor {:authz/cursor true :basis-t t :subject <eid>
              :permission <perm> :object-type <type> :eid <last>} | nil}

  Pass the returned cursor back as :after for the next page; a nil cursor
  means the enumeration is complete. Cursors are only meaningful against
  the same db basis (traversal order is deterministic per basis, not
  across bases): page against a stable value — hold the db, or use
  (d/as-of db (:basis-t cursor)) — and this fn fails loudly on any
  mismatch of basis, subject, permission or object type rather than
  returning a silently wrong page. The cursor is transparent data and
  contains eids; wrap or sign it at your trust boundary if it leaves your
  system.

  Resuming replays the traversal prefix, so cost grows with paging depth.
  For \"previous page\", keep your per-page cursor history, as with any
  cursor API."
  ([schema db subject-type subject-eid permission object-type]
   (grants-page schema db subject-type subject-eid permission object-type nil))
  ([schema db subject-type subject-eid permission object-type
    {:keys [limit after] :or {limit 100}}]
   (when-not (and (integer? limit) (pos? limit))
     (throw (ex-info "authz: :limit must be a positive integer"
                     {:authz/error true :limit limit})))
   (let [subject-eid* (d/entid db subject-eid)
         basis (or (d/as-of-t db) (d/basis-t db))]
     (when after
       (let [expected {:basis-t basis :subject subject-eid*
                       :permission permission :object-type object-type}]
         (when-not (and (:authz/cursor after)
                        (= expected (select-keys after (keys expected))))
           (throw (ex-info (str "authz: cursor does not match this query — cursors are only "
                                "valid for the same subject, permission, object type and db "
                                "basis; page against (d/as-of db (:basis-t cursor)) or start "
                                "from the first page")
                           {:authz/error true :expected expected :cursor after})))))
     (let [s (grants schema db subject-type subject-eid permission object-type)
           s (if after
               (rest (drop-while #(not= (:eid after) %) s))
               s)
           window (into [] (take (inc limit)) s)
           more? (> (count window) limit)
           data (if more? (subvec window 0 limit) window)]
       {:data data
        :cursor (when more?
                  {:authz/cursor true
                   :basis-t basis
                   :subject subject-eid*
                   :permission permission
                   :object-type object-type
                   :eid (peek data)})}))))
