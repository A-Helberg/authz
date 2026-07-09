(ns tutorial.sync-down
  "readable-datoms — filtering what syncs down to an offline client."
  (:require [authz.attrs :as attrs]
            [datomic.api :as d]
            [tutorial.world :refer [schema db uma vic mark yara
                                    asg-uma launch-plan]]))

;; The attrs layer is deny-by-default: an attribute not declared in any
;; :attrs section never syncs. Tail the tx-report queue (or walk an
;; entity's datoms, as here), filter per client, push what remains.

(def batch
  (into (vec (d/datoms db :eavt asg-uma))
        (d/datoms db :eavt launch-plan)))

(defn synced-attrs [subject-eid]
  (->> (attrs/readable-datoms schema db subject-eid batch)
       :allowed
       (map #(d/ident db (:a %)))
       (into (sorted-set))))

{:datoms-in-batch (count batch)
 ;; uma owns both — everything declared syncs to her, including
 ;; :doc/banned, whose :read is gated by :edit (owner/admin only)
 :to-uma  (synced-attrs uma)
 ;; vic may view the doc but not who is banned from it
 :to-vic  (synced-attrs vic)
 ;; mark sees the assignment (he manages uma) but not the doc
 :to-mark (synced-attrs mark)
 ;; the other organisation receives nothing at all
 :to-yara (synced-attrs yara)}
