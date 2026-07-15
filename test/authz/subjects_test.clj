(ns authz.subjects-test
  "Behavioural semantics of the reverse enumeration primitive
  (subjects / subjects-page): agreement with the point-check walker,
  determinism and dedupe, recursion on cyclic data, verification of
  and/not/attr= permissions, and the pagination contract in both
  orders."
  (:require [authz.core :as authz]
            [authz.fixture :as fx]
            [clojure.test :refer [deftest is testing use-fixtures]]
            [datomic.api :as d]))

(def ^:dynamic *db* nil)

(use-fixtures :once
  (fn [f] (binding [*db* (d/db (fx/fresh-conn))] (f))))

(def ^:private perms-under-test
  [[:site :view] [:site :view-members]
   [:organisation :view] [:organisation :edit]
   [:resource :view] [:resource :edit]
   [:assignment :view] [:assignment :react]
   [:submission :view] [:submission :edit]
   [:doc :view] [:doc :edit]
   [:folder :view] [:folder :manage]
   [:user :view]])

(defn- fixture-entities
  [db]
  {:site         (mapv #(fx/site db %) ["Site1" "Site2" "Site3" "SiteB"])
   :organisation [(fx/org db "Acme") (fx/org db "Beta")]
   :resource     [(fx/resource db "Acme Handbook") (fx/resource db "Beta Handbook")]
   :assignment   [(fx/assignment db "asg-uma")]
   :submission   (mapv #(fx/submission db %) ["sub-uma" "sub-wes" "sub-yara"])
   :doc          (mapv #(fx/doc db %) ["Doc Pub" "Doc Draft"])
   :folder       (mapv #(fx/folder db %) ["Root" "Sub1" "Sub2"])
   :user         (mapv #(fx/user db %) (keys fx/users))})

(deftest subjects-agrees-with-can?-everywhere
  (let [db *db*
        user-eids (mapv #(fx/user db %) (keys fx/users))
        entities (fixture-entities db)]
    (doseq [[type perm] perms-under-test
            object (entities type)]
      (let [via-can (into #{}
                          (filter #(authz/can? fx/compiled db :user % perm type object))
                          user-eids)
            via-subjects (set (authz/subjects fx/compiled db :user perm type object))]
        (is (= via-can via-subjects)
            (str [type perm] " object " object " can? vs subjects"))))))

(deftest subjects-is-deterministic-and-deduplicated
  (let [db *db*]
    (doseq [[type perm obj] [[:site :view (fx/site db "Site1")]
                             [:folder :view (fx/folder db "Sub2")]
                             [:doc :view (fx/doc db "Doc Pub")]
                             [:user :view (fx/user db :uma)]]]
      (let [s1 (vec (authz/subjects fx/compiled db :user perm type obj))
            s2 (vec (authz/subjects fx/compiled db :user perm type obj))]
        (is (= s1 s2) (str [type perm] " two runs, same order"))
        (is (= (count s1) (count (distinct s1))) (str [type perm] " no duplicates"))))))

(deftest recursive-subjects-terminate-on-cyclic-data
  (let [conn (fx/fresh-conn)
        db (:db-after
            @(d/transact conn [{:db/id "ca" :folder/name "SCycA" :folder/parent "cb"}
                               {:db/id "cb" :folder/name "SCycB" :folder/parent "ca"}]))
        cyc-a (fx/folder db "SCycA")]
    (testing "an ungrounded parent cycle yields no subjects — and returns"
      (is (= #{} (set (authz/subjects fx/compiled db :user :view :folder cyc-a)))))
    (testing "grounding the cycle yields the org's viewers for both members"
      (let [db (:db-after @(d/transact conn [[:db/add (fx/folder db "SCycB")
                                              :folder/organisation (fx/org db "Acme")]]))]
        (is (= #{(fx/user db :alice) (fx/user db :sena) (fx/user db :mia) (fx/user db :sam)}
               (set (authz/subjects fx/compiled db :user :view :folder cyc-a))))))))

(deftest impure-permissions-verify-subject-candidates
  (let [db *db*]
    (testing "banned viewer never appears among a doc's subjects"
      (is (= #{(fx/user db :uma) (fx/user db :vic) (fx/user db :alice) (fx/user db :sam)}
             (set (authz/subjects fx/compiled db :user :view :doc (fx/doc db "Doc Pub"))))
          "wes is a viewer but banned"))
    (testing "the draft's viewer grant is gated on the status condition"
      (is (= #{(fx/user db :uma) (fx/user db :alice) (fx/user db :sam)}
             (set (authz/subjects fx/compiled db :user :view :doc (fx/doc db "Doc Draft"))))))))

(deftest subject-pages-concatenate-in-both-orders
  (let [db *db*]
    (doseq [[type perm obj] [[:site :view (fx/site db "Site1")]
                             [:folder :view (fx/folder db "Sub2")]
                             [:doc :view (fx/doc db "Doc Pub")]]
            opts [{} {:order :eid}]
            :when (not (and (= type :folder) (= opts {:order :eid})))]
      (let [full (set (authz/subjects fx/compiled db :user perm type obj))
            pages (loop [pages [] after nil]
                    (let [{:keys [data cursor]}
                          (authz/subjects-page fx/compiled db :user perm type obj
                                               (assoc opts :limit 2 :after after))]
                      (if cursor
                        (recur (conj pages data) cursor)
                        (conj pages data))))
            eids (into [] cat pages)]
        (is (= full (set eids)) (str [type perm opts] " pages cover the set"))
        (is (= (count eids) (count (distinct eids))) (str [type perm opts] " no dupes"))
        (when (= opts {:order :eid})
          (is (= eids (vec (sort eids))) (str [type perm] " :eid pages ascend")))))))

(deftest subject-cursors-fail-loudly-when-misused
  (let [db *db*
        site1 (fx/site db "Site1")
        {:keys [cursor]} (authz/subjects-page fx/compiled db :user :view :site site1
                                              {:limit 1})]
    (is (map? cursor))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"cursor does not match"
                          (authz/subjects-page fx/compiled db :user :view-members :site site1
                                               {:limit 1 :after cursor}))
        "a different permission is rejected")
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"cursor does not match"
                          (authz/subjects-page fx/compiled db :user :view :site
                                               (fx/site db "Site2") {:limit 1 :after cursor}))
        "a different object is rejected")
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"acyclic"
                          (authz/subjects-page fx/compiled db :user :view :folder
                                               (fx/folder db "Sub2") {:limit 1 :order :eid}))
        ":order :eid fails loudly on recursive closures")
    (is (= () (authz/subjects fx/compiled db :user :view :site [:site/name "Ghost"]))
        "an unresolvable object enumerates nothing")))
