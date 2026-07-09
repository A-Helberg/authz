(ns authz.reference
  "A naive graph-walking interpreter of the check language, used as the
  differential-testing oracle. Note: authz.core/can? now also walks indexes
  (independent code, same strategy), so the load-bearing cross-strategy
  comparison is reference-vs-list-query / reference-vs-filter-authorized,
  which exercise the Datalog clause compiler and, for recursive
  permissions, the generated Datomic rules."
  (:require [authz.schema :as schema]
            [datomic.api :as d]))

(defn- rel-targets
  [db rel eid]
  (if (schema/reverse-relation? rel)
    (map :e (d/datoms db :vaet eid (schema/underlying-attr rel)))
    (map :v (d/datoms db :eavt eid rel))))

(defn check
  "Truth-value of `perm` for `subject-eid` over `eid` of `type`, computed by
  directly interpreting the normalized check tree against the indexes.
  `seen` cuts revisits of the same (type, perm, entity) state on a
  derivation path, so recursive schemas terminate on cyclic data."
  [compiled db type perm subject-eid eid]
  (letfn [(ev [type node eid seen]
            (case (:op node)
              :relation
              (boolean (some #(= subject-eid %) (rel-targets db (:relation node) eid)))

              :chain
              (let [target (get-in compiled [:types type :relations (:relation node)])
                    tperm (:permission node)
                    tnode (get-in compiled [:types target :permissions tperm])]
                (boolean (some (fn [teid]
                                 (let [k [target tperm teid]]
                                   (when-not (contains? seen k)
                                     (ev target tnode teid (conj seen k)))))
                               (rel-targets db (:relation node) eid))))

              :attr=
              (boolean (some #(= (:value node) (:v %))
                             (d/datoms db :eavt eid (:attr node))))

              :not
              (not (ev type (:branch node) eid seen))

              :and
              (every? #(ev type % eid seen) (:branches node))

              :or
              (boolean (some #(ev type % eid seen) (:branches node)))))]
    (ev type (get-in compiled [:types type :permissions perm]) eid #{})))
