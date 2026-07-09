(ns tutorial.chains
  "Chains — and why the first hop NEVER unifies with the subject."
  (:require [authz.core :as authz]
            [tutorial.world :refer [schema db registry who
                                    asg-uma uma vic mark]]))

;; (-> <relation> <permission>) follows the relation, then requires the
;; permission on the target. :assignment/:view combines both forms over
;; the SAME relation:
;;
;;   :assignment/member          — "you ARE the assignee"        (terminal)
;;   (-> :assignment/member      — "you may VIEW the assignee"   (chain)
;;       :view)
;;
;; The chain's first hop binds a fresh variable. If it unified with the
;; subject, "may view the assignee" would silently collapse into "is the
;; assignee" — the classic ReBAC implementation bug.

{:the-rule (get-in registry [:assignment :permissions :view])

 ;; mark manages uma's site, so mark may :view uma the user…
 :mark-may-view-uma   (authz/can? schema db :user mark :view :user uma)
 ;; …and that is exactly what lets him see her assignment:
 :mark-sees-assignment (authz/can? schema db :user mark :view :assignment asg-uma)

 ;; vic shares uma's site but manages nothing — a peer, not a viewer
 :vic-may-view-uma    (authz/can? schema db :user vic :view :user uma)

 :everyone-who-sees-it (who :view :assignment asg-uma)}
