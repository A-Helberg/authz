(ns authz.reference
  "A naive graph-walking interpreter of the check language, used as the
  differential-testing oracle: it shares no code with the Datalog compiler
  (entity-API index walks instead of queries), so agreement between the two
  is strong evidence both are right."
  (:require [authz.schema :as schema]
            [datomic.api :as d]))

(defn- rel-targets
  [db rel eid]
  (if (schema/reverse-relation? rel)
    (map :e (d/datoms db :vaet eid (schema/underlying-attr rel)))
    (map :v (d/datoms db :eavt eid rel))))

(defn check
  "Truth-value of `perm` for `subject-eid` over `eid` of `type`, computed by
  directly interpreting the normalized check tree against the indexes."
  [compiled db type perm subject-eid eid]
  (letfn [(ev [type node eid]
            (case (:op node)
              :relation
              (boolean (some #(= subject-eid %) (rel-targets db (:relation node) eid)))

              :chain
              (let [target (get-in compiled [:types type :relations (:relation node)])
                    tnode (get-in compiled [:types target :permissions (:permission node)])]
                (boolean (some #(ev target tnode %)
                               (rel-targets db (:relation node) eid))))

              :attr=
              (boolean (some #(= (:value node) (:v %))
                             (d/datoms db :eavt eid (:attr node))))

              :not
              (not (ev type (:branch node) eid))

              :and
              (every? #(ev type % eid) (:branches node))

              :or
              (boolean (some #(ev type % eid) (:branches node)))))]
    (ev type (get-in compiled [:types type :permissions perm]) eid)))
