(ns authz.worldgen
  "Deterministic (seeded) random world generator over the fixture's Datomic
  schema and authz registry. Used by the generative differential tests
  (small worlds, many seeds) and the benchmarks (one large world)."
  (:import (java.util Random)))

(defn world-tx
  "Returns {:tx <tx-data> :users [emails] :orgs [names] :sites [names]
  :submissions [ids] :assignments [ids] :docs [titles]} for a random world:
  a full org/geo hierarchy per org, random site memberships, managers at
  random scope levels, and content with random ownership."
  [{:keys [seed users orgs sites managers submissions assignments docs]
    :or {seed 42 users 12 orgs 2 sites 6 managers 5
         submissions 10 assignments 4 docs 6}}]
  (let [rnd (Random. (long seed))
        pick (fn [xs] (nth (vec xs) (.nextInt rnd (count xs))))
        subset (fn [xs p] (filterv (fn [_] (< (.nextDouble rnd) p)) xs))
        maybe-many (fn [m k vs] (cond-> m (seq vs) (assoc k vs)))
        user-ids (mapv #(str "u" %) (range users))
        org-ids (mapv #(str "org" %) (range orgs))
        ;; tempid pairs carry their parent so no string parsing is needed
        state-ids (vec (for [o (range orgs) s (range 2)]
                         [(str "st" o "-" s) (str "corg" o)]))
        region-ids (vec (for [o (range orgs) s (range 2) r (range 2)]
                          [(str "r" o "-" s "-" r) (str "st" o "-" s)]))
        site-ids (mapv #(str "site" %) (range sites))]
    {:users (mapv #(str % "@gen") user-ids)
     :orgs (mapv #(str "g" %) org-ids)
     :sites (mapv #(str "g" %) site-ids)
     :submissions (mapv #(str "gsub" %) (range submissions))
     :assignments (mapv #(str "gasg" %) (range assignments))
     :docs (mapv #(str "gdoc" %) (range docs))
     :tx
     (-> []
         (into (map (fn [u] {:db/id u :user/name u :user/email (str u "@gen")}))
               user-ids)
         (conj {:db/id "sys" :system/superadmins [(pick user-ids)]})
         (into (map (fn [o]
                      (-> {:db/id o :organisation/name (str "g" o)
                           :organisation/system "sys"
                           :organisation/admins [(pick user-ids)]}
                          (maybe-many :organisation/senior-leadership (subset user-ids 0.1))
                          (maybe-many :organisation/members (subset user-ids 0.25)))))
               org-ids)
         (into (map (fn [o] {:db/id (str "c" o) :country/name (str "gc" o)
                             :country/organisation o}))
               org-ids)
         (into (map (fn [[st c]] {:db/id st :state/name (str "g" st)
                                  :state/country c}))
               state-ids)
         (into (map (fn [[r st]] {:db/id r :region/name (str "g" r) :region/state st}))
               region-ids)
         (into (map (fn [s]
                      (-> {:db/id s :site/name (str "g" s)
                           :site/region (first (pick region-ids))}
                          (maybe-many :site/members (subset user-ids 0.25)))))
               site-ids)
         (into (map (fn [_]
                      (let [scope (pick [:site :region :state :country])]
                        {:manager/user (pick user-ids)
                         (keyword "manager" (name scope))
                         (case scope
                           :site (pick site-ids)
                           :region (first (pick region-ids))
                           :state (first (pick state-ids))
                           :country (str "c" (pick org-ids)))})))
               (range managers))
         (into (map (fn [i] {:submission/id (str "gsub" i)
                             :submission/submitted-by (pick user-ids)
                             :submission/organisation (pick org-ids)
                             :submission/content (str "content" i)}))
               (range submissions))
         (into (map (fn [i] {:assignment/id (str "gasg" i)
                             :assignment/member (pick user-ids)
                             :assignment/organisation (pick org-ids)
                             :assignment/notes (str "notes" i)}))
               (range assignments))
         (into (map (fn [i]
                      (-> {:doc/title (str "gdoc" i)
                           :doc/organisation (pick org-ids)
                           :doc/owner (pick user-ids)
                           :doc/status (pick [:published :draft])}
                          (maybe-many :doc/viewers (subset user-ids 0.25))
                          (maybe-many :doc/banned (subset user-ids 0.1)))))
               (range docs)))}))
