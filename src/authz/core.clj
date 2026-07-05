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

(defn list-query
  "Returns a vector of Datalog :where clauses binding ?<object-type> and
  ?<subject-type> (e.g. ?assignment and ?user). Concat these with your own
  clauses so list endpoints only return rows the subject may see.

  When object type and subject type coincide the default variable names
  would collapse the check, so you must pass explicit :object-var and
  :subject-var in `opts`. Opts may also rename the vars in any query."
  ([schema object-type permission subject-type]
   (list-query schema object-type permission subject-type nil))
  ([schema object-type permission subject-type opts]
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
     (:clauses (rename-vars entry opts)))))

(defn list-query-attrs
  "The set of Datomic attributes the compiled permission touches, transitively
  through chains and ors. Reactive layers include these in their watch-set so
  permission changes live-update subscribed clients."
  [schema object-type permission]
  (:attrs (compiled-entry schema object-type permission)))

;; ---------------------------------------------------------------------------
;; Point checks

(defn- branch-hit?
  [db entry clauses subject-eid object-eid]
  (some? (d/q {:find [(:object-var entry) '.]
               :in ['$ (:subject-var entry) (:object-var entry)]
               :where clauses}
              db subject-eid object-eid)))

(defn can?
  "Point check: may `subject-eid` exercise `permission` over `object-eid`?
  Top-level or-branches are evaluated as separate queries, cheapest first,
  returning on the first grant — most real checks hit a direct terminal
  (e.g. \"is the assignee\") without ever walking the hierarchy branches."
  [schema db subject-type subject-eid permission object-type object-eid]
  (let [entry (compiled-entry schema object-type permission)]
    (check-subject-type! entry subject-type)
    (boolean (some #(branch-hit? db entry (:clauses %) subject-eid object-eid)
                   (:branches entry)))))

(defn explain
  "Like `can?` but reports which branch granted:
  {:granted? true :via <check-form>} on the first (cheapest) granting
  branch, or {:granted? false :tried [<check-form> ...]} listing every
  branch that was evaluated and refused."
  [schema db subject-type subject-eid permission object-type object-eid]
  (let [entry (compiled-entry schema object-type permission)]
    (check-subject-type! entry subject-type)
    (reduce (fn [acc {:keys [clauses source]}]
              (if (branch-hit? db entry clauses subject-eid object-eid)
                (reduced {:granted? true :via source})
                (update acc :tried conj source)))
            {:granted? false :tried []}
            (:branches entry))))

(defn filter-authorized
  "Batched `can?`: returns the subset of `object-eids` (as a set) over which
  `subject-eid` holds `permission`. One query regardless of collection size."
  [schema db subject-type subject-eid permission object-type object-eids]
  (let [{:keys [object-var subject-var clauses] :as entry}
        (compiled-entry schema object-type permission)]
    (check-subject-type! entry subject-type)
    (if (empty? object-eids)
      #{}
      (into #{}
            (map first)
            (d/q {:find [object-var]
                  :in ['$ subject-var [object-var '...]]
                  :where clauses}
                 db subject-eid (vec object-eids))))))
