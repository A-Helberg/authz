(ns authz.generative-test
  "Differential testing: for seeded random worlds, the compiled Datalog
  (can?, filter-authorized, list-query) must agree with a naive
  graph-walking reference interpreter on every (subject, permission,
  object) triple."
  (:require [authz.core :as authz]
            [authz.fixture :as fx]
            [authz.reference :as ref]
            [authz.worldgen :as gen]
            [clojure.set :as set]
            [clojure.test :refer [deftest is]]
            [datomic.api :as d]))

(def ^:private perms-under-test
  [[:site :view] [:site :view-members]
   [:organisation :view] [:organisation :edit]
   [:submission :view] [:submission :edit]
   [:assignment :view] [:assignment :react]
   [:doc :view] [:doc :edit]
   [:folder :view] [:folder :manage]
   [:user :view]])

(defn- list-eids
  [db type perm subject-eid]
  (let [collision? (= type :user)
        opts (when collision? {:object-var '?target :subject-var '?subject})
        obj-var (if collision? '?target (symbol (str "?" (name type))))
        subj-var (if collision? '?subject '?user)
        {:keys [where rules]} (authz/list-query* fx/compiled type perm :user opts)]
    (into #{}
          (map first)
          (if (seq rules)
            (d/q {:find [obj-var] :in ['$ '% subj-var] :where where}
                 db rules subject-eid)
            (d/q {:find [obj-var] :in ['$ subj-var] :where where}
                 db subject-eid)))))

(defn- world-entities
  [db world]
  {:site (mapv #(d/entid db [:site/name %]) (:sites world))
   :organisation (mapv #(d/entid db [:organisation/name %]) (:orgs world))
   :submission (mapv #(d/entid db [:submission/id %]) (:submissions world))
   :assignment (mapv #(d/entid db [:assignment/id %]) (:assignments world))
   :doc (mapv #(d/entid db [:doc/title %]) (:docs world))
   :folder (into (mapv #(d/entid db [:folder/name %]) (:folders world))
                 [(d/entid db [:folder/name "gcyc-a"])
                  (d/entid db [:folder/name "gcyc-b"])])
   :user (mapv #(d/entid db [:user/email %]) (:users world))})

(deftest compiled-datalog-agrees-with-reference-interpreter
  (doseq [seed [1 7 42 1337]]
    (let [world (gen/world-tx {:seed seed})
          conn (fx/empty-conn)
          _ @(d/transact conn (:tx world))
          ;; a hostile parent cycle, grounded on one side: walker, rules and
          ;; reference must all terminate and agree on it
          _ @(d/transact conn [{:db/id "cyc-a" :folder/name "gcyc-a"
                                :folder/parent "cyc-b"}
                               {:db/id "cyc-b" :folder/name "gcyc-b"
                                :folder/parent "cyc-a"
                                :folder/organisation
                                [:organisation/name (first (:orgs world))]}])
          db (d/db conn)
          entities (world-entities db world)
          user-eids (:user entities)]
      (doseq [[type perm] perms-under-test
              subject user-eids]
        (let [eids (entities type)
              via-ref (into #{} (filter #(ref/check fx/compiled db type perm subject %)) eids)
              via-can (into #{} (filter #(authz/can? fx/compiled db :user subject perm type %)) eids)
              via-batch (authz/filter-authorized fx/compiled db :user subject perm type eids)
              via-list (set/intersection (list-eids db type perm subject) (set eids))]
          (is (= via-ref via-can)
              (str "seed " seed " " [type perm] " subject " subject ": reference vs can?"))
          (is (= via-ref via-batch)
              (str "seed " seed " " [type perm] " subject " subject ": reference vs filter-authorized"))
          (is (= via-ref via-list)
              (str "seed " seed " " [type perm] " subject " subject ": reference vs list-query")))))))
