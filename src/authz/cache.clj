(ns authz.cache
  "Sound point-check caching.

  Zanzibar caches check results behind TTLs and accepts bounded staleness.
  We can do better: a Datomic db value is immutable, so a result keyed by
  [basis-t subject permission object-type object] can never go stale — a
  later db has a later basis-t and simply misses. No TTLs, no invalidation
  protocol.

    (def c (cache/make-cache))
    (cache/can? c schema db :user user-eid :edit :organisation org-eid)

  The cache is bounded: when full it flushes wholesale, which suits the
  access pattern (hot bursts of identical guards within a request/tx window
  share a basis-t; entries for old basis-ts age out at the next flush)."
  (:refer-clojure :exclude [can?])
  (:require [authz.core :as core]
            [datomic.api :as d]))

(defn make-cache
  ([] (make-cache {}))
  ([{:keys [max-entries] :or {max-entries 10000}}]
   (atom {:max-entries max-entries
          :entries {}
          :hits 0
          :misses 0})))

(defn stats
  [cache]
  (let [{:keys [entries hits misses]} @cache]
    {:entries (count entries) :hits hits :misses misses}))

(defn can?
  "Exactly authz.core/can?, memoized per db basis-t."
  [cache schema db subject-type subject-eid permission object-type object-eid]
  (let [k [(d/basis-t db) subject-eid permission object-type object-eid]
        cached (get-in @cache [:entries k] ::miss)]
    (if (not= ::miss cached)
      (do (swap! cache update :hits inc)
          cached)
      (let [v (core/can? schema db subject-type subject-eid
                         permission object-type object-eid)]
        (swap! cache (fn [{:keys [entries max-entries] :as c}]
                       (-> c
                           (update :misses inc)
                           (assoc :entries (if (>= (count entries) max-entries)
                                             {k v}
                                             (assoc entries k v))))))
        v))))
