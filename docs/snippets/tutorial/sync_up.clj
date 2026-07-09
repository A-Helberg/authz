(ns tutorial.sync-up
  "check-tx — authorization-checking transactions from offline clients."
  (:require [authz.attrs :as attrs]
            [tutorial.world :refer [schema db uma vic asg-uma acme]]))

;; check-tx applies the client's transaction SPECULATIVELY (d/with) and
;; judges the actual resulting datoms against the pre-tx db — so a tx can
;; never grant itself permissions and use them in the same breath, and
;; upserts are caught as writes, not creations.

(defn denials [report]
  (mapv #(select-keys % [:a :reason]) (:denied report)))

{;; the assignee may write notes (:write :react — assignee only)
 :uma-writes-notes
 (:allowed? (attrs/check-tx schema db uma
                            [[:db/add asg-uma :assignment/notes "done!"]]))

 ;; her peer may not
 :vic-writes-notes
 (denials (attrs/check-tx schema db vic
                          [[:db/add asg-uma :assignment/notes "hax"]]))

 ;; the upsert attack: a "new" entity map whose unique id resolves onto
 ;; uma's existing assignment — checked as a WRITE, and denied
 :vic-upserts
 (denials (attrs/check-tx schema db vic
                          [{:assignment/id "asg-uma"
                            :assignment/member vic
                            :assignment/notes "mine now"}]))

 ;; an offline client re-sending the full entity map unchanged is a
 ;; no-op: zero datoms result, zero checks run, allowed
 :uma-resends-unchanged
 (attrs/check-tx schema db uma
                 [{:assignment/id "asg-uma"
                   :assignment/member uma
                   :assignment/organisation acme
                   :assignment/notes "started"}])}
