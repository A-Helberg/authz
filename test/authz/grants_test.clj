(ns authz.grants-test
  "Behavioural semantics of the enumeration primitive (grants /
  grants-page) against the domain fixture: agreement with the point-check
  walker, deterministic deduplicated order, recursive enumeration on
  cyclic data, verification of and/not/attr= permissions, and the
  pagination contract (pages concatenate to the full stream, cursors fail
  loudly when misused)."
  (:require [authz.core :as authz]
            [authz.fixture :as fx]
            [clojure.test :refer [deftest is testing use-fixtures]]
            [datomic.api :as d]))

(def ^:dynamic *db* nil)

(use-fixtures :once
  (fn [f] (binding [*db* (d/db (fx/fresh-conn))] (f))))

(def ^:private perms-under-test
  [[:site :view] [:site :view-members]
   [:organisation :view] [:organisation :edit] [:organisation :admin-view]
   [:resource :view] [:resource :edit]
   [:assignment :view] [:assignment :react] [:assignment :edit]
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

;; ---------------------------------------------------------------------------
;; Agreement with the walker — grants must emit exactly the granted set

(deftest grants-agrees-with-can?-everywhere
  (let [db *db*
        entities (fixture-entities db)]
    (doseq [[type perm] perms-under-test
            user-key (keys fx/users)]
      (let [u (fx/user db user-key)
            via-can (into #{}
                          (filter #(authz/can? fx/compiled db :user u perm type %))
                          (entities type))
            via-grants (set (authz/grants fx/compiled db :user u perm type))]
        (is (= via-can via-grants)
            (str [type perm user-key] " can? vs grants"))))))

(deftest enumeration-is-deterministic-and-deduplicated
  (let [db *db*]
    (doseq [[type perm] [[:site :view] [:folder :view] [:doc :view] [:user :view]]
            user-key [:sam :alice :stan :vic]]
      (let [u (fx/user db user-key)
            s1 (vec (authz/grants fx/compiled db :user u perm type))
            s2 (vec (authz/grants fx/compiled db :user u perm type))]
        (is (= s1 s2) (str [type perm user-key] " two runs, same order"))
        (is (= (count s1) (count (distinct s1)))
            (str [type perm user-key] " no duplicates"))))))

;; ---------------------------------------------------------------------------
;; Recursive permissions enumerate lazily, terminating on cyclic data

(deftest recursive-permissions-enumerate-without-materializing
  (let [conn (fx/fresh-conn)
        db (d/db conn)
        alice (fx/user db :alice)
        bob (fx/user db :bob)
        tree #{(fx/folder db "Root") (fx/folder db "Sub1") (fx/folder db "Sub2")}]
    (testing "the whole tree flows from the root's organisation"
      (is (= tree (set (authz/grants fx/compiled db :user alice :view :folder))))
      (is (= #{} (set (authz/grants fx/compiled db :user bob :view :folder)))
          "the other org's admin enumerates nothing"))
    (testing "a parent cycle terminates; grounding one member reaches both"
      (let [db (:db-after
                @(d/transact conn [{:db/id "ca" :folder/name "CycA" :folder/parent "cb"}
                                   {:db/id "cb" :folder/name "CycB" :folder/parent "ca"
                                    :folder/organisation (fx/org db "Acme")}]))
            cyc #{(fx/folder db "CycA") (fx/folder db "CycB")}]
        (is (= (into tree cyc)
               (set (authz/grants fx/compiled db :user alice :view :folder))))
        (is (= #{} (set (authz/grants fx/compiled db :user bob :view :folder)))
            "an ungranted subject terminates on the cycle too")))))

;; ---------------------------------------------------------------------------
;; and / not / attr= — over-approximating candidates must be verified out

(deftest impure-permissions-verify-candidates
  (let [db *db*]
    (testing "wes is a viewer of Doc Pub but banned — never emitted"
      (is (= #{} (set (authz/grants fx/compiled db :user (fx/user db :wes) :view :doc)))))
    (testing "vic sees the published doc but not the draft"
      (is (= #{(fx/doc db "Doc Pub")}
             (set (authz/grants fx/compiled db :user (fx/user db :vic) :view :doc)))))
    (testing "the owner and the org editor see both"
      (doseq [k [:uma :alice]]
        (is (= #{(fx/doc db "Doc Pub") (fx/doc db "Doc Draft")}
               (set (authz/grants fx/compiled db :user (fx/user db k) :view :doc))))))))

;; ---------------------------------------------------------------------------
;; Pagination contract

(deftest pages-concatenate-to-the-full-enumeration
  (let [db *db*]
    (doseq [[type perm user-key] [[:site :view :sam]
                                  [:user :view :alice]
                                  [:folder :view :mia]
                                  [:doc :view :uma]]]
      (let [u (fx/user db user-key)
            full (vec (authz/grants fx/compiled db :user u perm type))]
        (doseq [limit [1 2 3 100]]
          (let [pages (loop [pages [] after nil]
                        (let [{:keys [data cursor]}
                              (authz/grants-page fx/compiled db :user u perm type
                                                 {:limit limit :after after})]
                          (if cursor
                            (recur (conj pages data) cursor)
                            (conj pages data))))]
            (is (= full (into [] cat pages))
                (str [type perm user-key] " limit " limit))
            (is (every? #(<= (count %) limit) pages))))))))

(deftest page-shape-and-completion
  (let [db *db*
        sam (fx/user db :sam)
        full (vec (authz/grants fx/compiled db :user sam :view :site))
        {:keys [data cursor]} (authz/grants-page fx/compiled db :user sam :view :site
                                                 {:limit 2})]
    (is (= (take 2 full) data))
    (is (= (first (drop 1 data)) (:eid cursor)) "cursor points at the last row served")
    (testing "a limit covering everything returns no cursor"
      (let [{:keys [data cursor]} (authz/grants-page fx/compiled db :user sam :view :site
                                                     {:limit (count full)})]
        (is (= full data))
        (is (nil? cursor))))
    (testing "an unknown subject yields an empty page, not an error"
      (is (= {:data [] :cursor nil}
             (authz/grants-page fx/compiled db :user [:user/email "ghost@x"]
                                :view :site {:limit 5}))))))

(deftest cursors-fail-loudly-when-misused
  (let [conn (fx/fresh-conn)
        db (d/db conn)
        sam (fx/user db :sam)
        alice (fx/user db :alice)
        {:keys [cursor]} (authz/grants-page fx/compiled db :user sam :view :site
                                            {:limit 1})]
    (is (map? cursor))
    (testing "a different basis is rejected, and as-of the cursor basis works"
      (let [db2 (:db-after @(d/transact conn [{:site/name "SiteNew"
                                               :site/region [:region/name "Region1"]}]))]
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"cursor does not match"
                              (authz/grants-page fx/compiled db2 :user sam :view :site
                                                 {:limit 1 :after cursor})))
        (let [stable (d/as-of db2 (:basis-t cursor))
              page2 (authz/grants-page fx/compiled stable :user sam :view :site
                                       {:limit 1 :after cursor})]
          (is (= (take 1 (rest (authz/grants fx/compiled db :user sam :view :site)))
                 (:data page2))
              "paging continues against the pinned basis, unaffected by the new site"))))
    (testing "a different permission, type or subject is rejected"
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"cursor does not match"
                            (authz/grants-page fx/compiled db :user sam :view-members :site
                                               {:limit 1 :after cursor})))
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"cursor does not match"
                            (authz/grants-page fx/compiled db :user alice :view :site
                                               {:limit 1 :after cursor}))))))

;; ---------------------------------------------------------------------------
;; Fail-loud hygiene, same contract as the other consumption APIs

(deftest grants-validates-like-the-other-apis
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"subjects of type"
                        (authz/grants fx/compiled *db* :site 1 :view :site)))
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"unknown permission"
                        (authz/grants fx/compiled *db* :user 1 :nope :site)))
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"positive integer"
                        (authz/grants-page fx/compiled *db* :user 1 :view :site
                                           {:limit 0})))
  (is (= () (authz/grants fx/compiled *db* :user [:user/email "ghost@x"] :view :site))
      "an unresolvable subject enumerates nothing"))

(deftest eid-order-pages-are-ascending-and-seekable
  (let [db *db*]
    (testing ":order :eid pages enumerate ascending and equal the default's set"
      (doseq [[type perm user-key] [[:site :view :sam] [:doc :view :uma]
                                    [:user :view :alice] [:submission :view :alice]]]
        (let [u (fx/user db user-key)
              default-set (set (authz/grants fx/compiled db :user u perm type))
              pages (loop [pages [] after nil]
                      (let [{:keys [data cursor]}
                            (authz/grants-page fx/compiled db :user u perm type
                                               {:limit 2 :order :eid :after after})]
                        (if cursor
                          (recur (conj pages data) cursor)
                          (conj pages data))))
              eids (into [] cat pages)]
          (is (= eids (vec (sort eids)))
              (str [type perm user-key] " ascending eid order"))
          (is (= default-set (set eids))
              (str [type perm user-key] " same answer set as traversal order")))))
    (testing "seek resume equals dropping over the full eid-ordered stream"
      (doseq [[type perm user-key] [[:site :view :sam] [:doc :view :uma]]]
        (let [u (fx/user db user-key)
              full (vec (sort (authz/grants fx/compiled db :user u perm type)))]
          (doseq [limit [1 2]]
            (let [{:keys [cursor]} (authz/grants-page fx/compiled db :user u perm type
                                                      {:limit limit :order :eid})]
              (when cursor
                (is (= :seek (:mode cursor)) ":eid cursors carry :seek mode")
                (is (= (vec (take limit (drop limit full)))
                       (:data (authz/grants-page fx/compiled db :user u perm type
                                                 {:limit limit :order :eid
                                                  :after cursor})))
                    (str [type perm user-key] " limit " limit))))))))
    (testing "the default stays traversal order with replay cursors"
      (let [{:keys [cursor]} (authz/grants-page fx/compiled db :user (fx/user db :sam)
                                                :view :site {:limit 1})]
        (is (= :replay (:mode cursor)))))
    (testing "cursors from one order cannot resume the other"
      (let [{:keys [cursor]} (authz/grants-page fx/compiled db :user (fx/user db :sam)
                                                :view :site {:limit 1 :order :eid})]
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"cursor does not match"
                              (authz/grants-page fx/compiled db :user (fx/user db :sam)
                                                 :view :site {:limit 1 :after cursor})))))
    (testing ":order :eid fails loudly on recursive closures"
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"acyclic"
                            (authz/grants-page fx/compiled db :user (fx/user db :mia)
                                               :view :folder {:limit 1 :order :eid}))))))
