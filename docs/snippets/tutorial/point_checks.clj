(ns tutorial.point-checks
  "can?, filter-authorized and the sound cache — guarding the write path."
  (:require [authz.cache :as cache]
            [authz.core :as authz]
            [datomic.api :as d]
            [tutorial.world :refer [schema db ada yara acme
                                    site-one launch-plan]]))

;; can? is the point check every API handler guards with. It's evaluated
;; by direct index traversal, cheapest branch first — a terminal hit like
;; "is the assignee" answers in about a microsecond.

(def point
  {:ada-edits-acme?  (authz/can? schema db :user ada :edit :organisation acme)
   :yara-edits-acme? (authz/can? schema db :user yara :edit :organisation acme)})

;; filter-authorized batches: one query for any number of entities.
;; Ada admins Acme, so of the two sites she may view only her own.
(def site-zed (d/entid db [:site/name "Site Zed"]))
(def batch
  (authz/filter-authorized schema db :user ada :view :site [site-one site-zed]))

;; And because db values are immutable, caching by basis-t is SOUND —
;; a cached answer can never go stale, no TTLs, no invalidation protocol.
(def c (cache/make-cache))
(dotimes [_ 3] (cache/can? c schema db :user ada :view :doc launch-plan))

{:point point
 :batch batch
 :batch-allowed-count (count batch)
 :cache (cache/stats c)}
