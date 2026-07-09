(ns tutorial.watch-set
  "list-query-attrs — reactive invalidation without a sync pipeline."
  (:require [authz.core :as authz]
            [clojure.set :as set]
            [datomic.api :as d]
            [tutorial.world :refer [schema db who asg-uma vic]]))

;; A reactive layer re-runs a pushed query when a transaction touches any
;; attribute it depends on. list-query-attrs is the authz half of that
;; watch-set: every attribute the permission reads, transitively through
;; chains — so permission CHANGES live-update subscribed clients too.

(def watch (authz/list-query-attrs schema :assignment :view))

;; Promote vic to manager of Site One (speculatively) and prove the
;; contract: the tx touches the watch-set, and the outcome flips.
(def promotion
  (d/with db [{:manager/user vic :manager/site (d/entid db [:site/name "Site One"])}]))

(def touched
  (into #{} (map #(d/ident (:db-after promotion) (:a %))) (:tx-data promotion)))

{:watch-set watch
 :tx-touches (set/intersection touched watch)
 :who-sees-the-assignment
 {:before (who :view :assignment asg-uma)
  :after  (who (:db-after promotion) :view :assignment asg-uma)}}
