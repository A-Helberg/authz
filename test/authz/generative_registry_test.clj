(ns authz.generative-registry-test
  "Differential testing over random REGISTRIES, not just random worlds:
  for seeded random permission schemas plus random worlds over them,
  every consumption strategy (can?, filter-authorized, list-query,
  grants) must agree with both oracles (the top-down reference
  interpreter and the bottom-up fixpoint spec) on every (subject,
  permission, object) triple. Also asserts the generator's validity
  invariants: every generated registry compiles, and every permission
  checks :user subjects."
  (:require [authz.core :as authz]
            [authz.fixpoint-oracle :as oracle]
            [authz.reference :as ref]
            [authz.registrygen :as rgen]
            [authz.schema :as schema]
            [clojure.set :as set]
            [clojure.test :refer [deftest is]]
            [datomic.api :as d]))

(defn- fresh-conn [datomic-schema]
  (let [uri (str "datomic:mem://" (d/squuid))]
    (d/create-database uri)
    (let [conn (d/connect uri)]
      @(d/transact conn datomic-schema)
      conn)))

(defn- list-eids
  [compiled db type perm subject-eid & [all-rules?]]
  (let [collision? (= type :user)
        opts (cond-> (when collision? {:object-var '?target :subject-var '?subject})
               all-rules? (assoc :all-rules? true))
        obj-var (if collision? '?target (symbol (str "?" (name type))))
        subj-var (if collision? '?subject '?user)
        {:keys [where rules]} (authz/list-query* compiled type perm :user opts)]
    (into #{}
          (map first)
          (if (seq rules)
            (d/q {:find [obj-var] :in ['$ '% subj-var] :where where}
                 db rules subject-eid)
            (d/q {:find [obj-var] :in ['$ subj-var] :where where}
                 db subject-eid)))))

(deftest random-registries-agree-across-all-strategies
  (doseq [seed [1 2 3 5 7 11 13 42 99 1337]]
    (let [{:keys [registry datomic-schema tx type-ids user-ids]}
          (rgen/gen-bundle {:seed seed})
          ;; generator validity: every generated registry must compile
          compiled (schema/compile-schema registry)
          conn (fresh-conn datomic-schema)
          _ @(d/transact conn tx)
          db (d/db conn)
          eid (fn [T id]
                (d/entid db [(if (= T :user) :user/kid (keyword (name T) "id")) id]))
          entities (into {:user (mapv #(eid :user %) user-ids)}
                         (map (fn [[T ids]] [T (mapv #(eid T %) ids)]))
                         type-ids)
          perm-keys (keys (:compiled compiled))
          spec-facts (oracle/facts compiled db)]
      (doseq [[type perm] perm-keys]
        (is (= :user (authz/subject-type compiled type perm))
            (str "seed " seed " " [type perm] ": generator subject-type invariant"))
        (doseq [subject (:user entities)]
          (let [eids (entities type)
                via-spec (oracle/objects spec-facts type perm subject)
                via-ref (into #{} (filter #(ref/check compiled db type perm subject %)) eids)
                via-can (into #{} (filter #(authz/can? compiled db :user subject perm type %)) eids)
                via-batch (authz/filter-authorized compiled db :user subject perm type eids)
                via-list-full (list-eids compiled db type perm subject)
                via-list-rules (list-eids compiled db type perm subject true)
                via-grants (set (authz/grants compiled db :user subject perm type))]
            (is (= via-ref via-can)
                (str "seed " seed " " [type perm] " subject " subject ": reference vs can?"))
            (is (= via-ref via-batch)
                (str "seed " seed " " [type perm] " subject " subject ": reference vs filter-authorized"))
            (is (= via-ref (set/intersection via-list-full (set eids)))
                (str "seed " seed " " [type perm] " subject " subject ": reference vs list-query"))
            (is (= via-list-full via-grants)
                (str "seed " seed " " [type perm] " subject " subject ": grants vs list-query (full sets)"))
            (is (= via-spec via-list-full)
                (str "seed " seed " " [type perm] " subject " subject ": fixpoint spec vs list-query (full sets)"))
            (is (= via-list-full via-list-rules)
                (str "seed " seed " " [type perm] " subject " subject ": all-rules vs inline (full sets)"))))
        (doseq [object (entities type)]
          (is (= (oracle/subjects spec-facts type perm object)
                 (set (authz/subjects compiled db :user perm type object)))
              (str "seed " seed " " [type perm] " object " object
                   ": subjects vs fixpoint spec")))))))
