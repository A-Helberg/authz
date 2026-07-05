(ns authz.bench
  "Criterium benchmarks over a large generated world.

    mise run bench            (clojure -X:bench)

  Scenarios are plain data ({:label .. :thunk .. :check ..}) so the test
  suite can execute each one once and assert its sanity check — the harness
  itself is covered by CI (authz.bench-test) and cannot silently rot.

  Scenarios are chosen to expose the costs that matter:
  - can? on a cheap terminal branch (short-circuit's best case)
  - can? through the deep hierarchy chain (an org admin viewing a site)
  - can? denied (worst case: every branch evaluated)
  - cached can? (basis-t keyed hit)
  - filter-authorized over every site (one query, N entities)
  - list-query spliced into a full site listing
  - readable-datoms over a large sync batch
  - check-tx for a small offline write (includes the speculative d/with)"
  (:require [authz.attrs :as attrs]
            [authz.cache :as cache]
            [authz.core :as authz]
            [authz.fixture :as fx]
            [authz.worldgen :as gen]
            [criterium.core :as crit]
            [datomic.api :as d]))

(def default-world-opts
  {:seed 42 :users 2000 :orgs 3 :sites 200 :managers 150
   :submissions 3000 :assignments 500 :docs 500})

(defn build-world
  ([] (build-world default-world-opts))
  ([opts]
   (let [world (gen/world-tx opts)
         conn (fx/empty-conn)]
     @(d/transact conn (:tx world))
     (let [db (d/db conn)]
       {:db db
        :world world
        :sites (mapv #(d/entid db [:site/name %]) (:sites world))
        :users (mapv #(d/entid db [:user/email %]) (:users world))}))))

(defn scenarios
  "Benchmark scenarios over a built world. Each is {:label <string>
  :thunk <no-arg fn> :check <pred over the thunk's result>}."
  [{:keys [db world sites users]}]
  (let [some-site (first (filter #(seq (d/datoms db :eavt % :site/members)) sites))
        member (:v (first (d/datoms db :eavt some-site :site/members)))
        admin (:v (first (d/datoms db :eavt
                                   (d/entid db [:organisation/name (first (:orgs world))])
                                   :organisation/admins)))
        admin-site (first (filter #(authz/can? fx/compiled db :user admin :view :site %)
                                  sites))
        outsider (first (remove #(authz/can? fx/compiled db :user % :view :site some-site)
                                users))
        c (doto (cache/make-cache)
            ;; warm, so the cached scenario measures hits
            (cache/can? fx/compiled db :user admin :view :site admin-site))
        sync-batch (into [] (comp (mapcat #(d/datoms db :eavt %)) (take 1000))
                         (mapv #(d/entid db [:submission/id %]) (:submissions world)))
        asg (d/entid db [:assignment/id (first (:assignments world))])
        asg-member (:v (first (d/datoms db :eavt asg :assignment/member)))
        write-tx [[:db/add asg :assignment/notes "bench write"]]]
    [{:label "can? — cheap terminal hit (site member views own site)"
      :thunk #(authz/can? fx/compiled db :user member :view :site some-site)
      :check true?}
     {:label "can? — deep hierarchy grant (org admin views a site)"
      :thunk #(authz/can? fx/compiled db :user admin :view :site admin-site)
      :check true?}
     {:label "can? — denied (every branch evaluated)"
      :thunk #(authz/can? fx/compiled db :user outsider :view :site some-site)
      :check false?}
     {:label "cached can? — basis-t keyed hit"
      :thunk #(cache/can? c fx/compiled db :user admin :view :site admin-site)
      :check true?}
     {:label (str "filter-authorized — " (count sites) " sites, one query")
      :thunk #(authz/filter-authorized fx/compiled db :user admin :view :site sites)
      :check #(and (set? %) (contains? % admin-site))}
     {:label "list-query — full authorized site listing (org admin)"
      :thunk #(d/q {:find '[?site] :in '[$ ?user]
                    :where (authz/list-query fx/compiled :site :view :user)}
                   db admin)
      :check #(contains? (into #{} (map first) %) admin-site)}
     {:label (str "readable-datoms — " (count sync-batch) " datom sync batch")
      :thunk #(attrs/readable-datoms fx/compiled db admin sync-batch)
      :check #(and (seq (:allowed %))
                   (= (count sync-batch) (+ (count (:allowed %)) (count (:denied %)))))}
     {:label "check-tx — small offline write (incl. speculative d/with)"
      :thunk #(attrs/check-tx fx/compiled db asg-member write-tx)
      :check :allowed?}]))

(defn run [_]
  (println "Building world:" default-world-opts)
  (let [{:keys [users sites world] :as ctx} (build-world)]
    (println "world:" (count users) "users," (count sites) "sites,"
             (count (:submissions world)) "submissions")
    (doseq [{:keys [label thunk check]} (scenarios ctx)]
      (println)
      (println "###" label)
      (assert (check (thunk)) (str "scenario sanity check failed: " label))
      (crit/quick-bench (thunk)))))
