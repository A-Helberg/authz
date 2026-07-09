(ns tutorial.creation
  "Create and delete rules — new entities from offline clients."
  (:require [authz.attrs :as attrs]
            [tutorial.world :refer [schema db registry
                                    ada uma mia acme launch-plan]]))

;; A :create rule is the same check language, evaluated against the NEW
;; entity's own datoms: a terminal means "that relation's value must be
;; you"; a chain means "you need <perm> on the entity it points at".
;; :delete names the permission gating :db/retractEntity.

(defn verdict [subject tx]
  (let [r (attrs/check-tx schema db subject tx)]
    (if (:allowed? r) :allowed (-> r :denied first :reason))))

{:doc-create-rule (get-in registry [:doc :create])

 ;; (and :doc/owner (-> :doc/organisation :view)) — your own docs, in
 ;; orgs you can at least view:
 :mia-creates-her-doc
 (verdict mia [{:doc/title "Mia's notes" :doc/owner mia
                :doc/organisation acme :doc/status :draft}])
 :mia-creates-as-uma
 (verdict mia [{:doc/title "Sock puppet" :doc/owner uma
                :doc/organisation acme}])

 ;; chain create: folders need :manage on the parent — which may itself
 ;; be created in the SAME transaction (judged on the speculative db,
 ;; with authority still anchored outside the tx)
 :ada-creates-folder-and-subfolder
 (verdict ada [{:db/id "new" :folder/name "Plans" :folder/organisation acme}
               {:folder/name "Q3" :folder/parent "new"}])
 :mia-tries-the-same
 (verdict mia [{:db/id "new" :folder/name "M" :folder/organisation acme}
               {:folder/name "M2" :folder/parent "new"}])

 ;; :delete — only the doc's :edit holders may retract it
 :uma-deletes-her-doc (verdict uma [[:db/retractEntity launch-plan]])
 :mia-deletes-umas-doc (verdict mia [[:db/retractEntity launch-plan]])}
