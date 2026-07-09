(ns tutorial.terminals
  "The first form of the check language: a terminal keyword."
  (:require [tutorial.world :refer [registry who asg-uma]]))

;; :assignment's :react permission is a single keyword — a relation name.
;; A terminal means: the SUBJECT IS the entity reached by this relation.
;; So only the assignment's member may react to it. Not their manager,
;; not even the org admin — nothing else grants :react.

{:the-rule      (get-in registry [:assignment :permissions :react])
 :who-can-react (who :react :assignment asg-uma)}
