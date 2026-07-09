(ns authz.core-test
  "Behavioural semantics against a real in-memory Datomic db, using the
  domain fixture from the overview doc."
  (:require [authz.core :as authz]
            [authz.fixture :as fx]
            [clojure.set :as set]
            [clojure.test :refer [deftest is testing use-fixtures]]
            [datomic.api :as d]))

(def ^:dynamic *db* nil)

(use-fixtures :once
  (fn [f] (binding [*db* (d/db (fx/fresh-conn))] (f))))

(defn- who-can?
  "The set of fixture users (by key) holding `perm` over `eid`."
  [db type perm eid]
  (into #{}
        (filter #(authz/can? fx/compiled db :user (fx/user db %) perm type eid))
        (keys fx/users)))

(defn- list-eids
  "Runs list-query* for one subject and returns the matching object eids."
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
                 *db* rules subject-eid)
            (d/q {:find [obj-var] :in ['$ subj-var] :where where}
                 *db* subject-eid)))))

;; ---------------------------------------------------------------------------
;; Scoped visibility through the hierarchy

(deftest site-visibility-scopes-by-manager-level
  (let [db *db*]
    (testing "Site1 (region1, state1): members, site/state/country managers, org admin, superadmin"
      (is (= #{:uma :vic :mark :stan :carl :alice :sam}
             (who-can? db :site :view (fx/site db "Site1")))))
    (testing "Site2 (region2, state1): Rita's region manager scope reaches it, Mark's site scope does not"
      (is (= #{:wes :rita :stan :carl :alice :sam}
             (who-can? db :site :view (fx/site db "Site2")))))
    (testing "Site3 (region3, state2): only the country manager's scope reaches it"
      (is (= #{:xia :carl :alice :sam}
             (who-can? db :site :view (fx/site db "Site3")))))
    (testing "SiteB in the other organisation"
      (is (= #{:yara :bob :sam}
             (who-can? db :site :view (fx/site db "SiteB")))))))

(deftest org-view-excludes-managers-by-design
  ;; The deliberate asymmetry: managers do NOT get org :view through a
  ;; manager->organisation shortcut — it would break hierarchical scoping.
  (let [db *db*]
    (is (= #{:alice :sena :mia :sam}
           (who-can? db :organisation :view (fx/org db "Acme"))))
    (is (= #{:alice :sam}
           (who-can? db :organisation :edit (fx/org db "Acme"))))
    (is (= #{:bob :sam}
           (who-can? db :organisation :view (fx/org db "Beta"))))))

;; ---------------------------------------------------------------------------
;; Terminal vs chain: the submitter/viewer distinction

(deftest terminal-and-chain-do-not-collapse
  (let [db *db*
        sub (fx/submission db "sub-uma")]
    (testing "the submitter sees their own work (terminal)"
      (is (authz/can? fx/compiled db :user (fx/user db :uma) :view :submission sub)))
    (testing "managers of the submitter see it (chain through a fresh var)"
      (is (= #{:uma :mark :stan :carl :alice :sam}
             (who-can? db :submission :view sub))
          "if the chain's first hop unified with the subject, only Uma would appear"))
    (testing "a fellow site member is neither"
      (is (not (authz/can? fx/compiled db :user (fx/user db :vic) :view :submission sub))))))

(deftest person-derived-visibility
  (let [db *db*]
    (testing "a manager sees their people's work, and only their people's"
      (let [rita (fx/user db :rita)]
        (is (authz/can? fx/compiled db :user rita :view :submission (fx/submission db "sub-wes")))
        (is (not (authz/can? fx/compiled db :user rita :view :submission (fx/submission db "sub-uma"))))))
    (testing "who may view a user"
      (is (= #{:mark :stan :carl :alice :sam}
             (who-can? db :user :view (fx/user db :uma)))
          "note: not Uma herself, and not fellow member Vic")
      (is (= #{:alice :sam}
             (who-can? db :user :view (fx/user db :mia)))
          "an org member with no site is visible only via org admin-view"))))

(deftest assignment-permissions
  (let [db *db*
        asg (fx/assignment db "asg-uma")]
    (is (= #{:uma :mark :stan :carl :alice :sam} (who-can? db :assignment :view asg)))
    (is (= #{:uma} (who-can? db :assignment :react asg)))
    (is (= #{:alice :sam} (who-can? db :assignment :edit asg)))))

;; ---------------------------------------------------------------------------
;; and / not / attr= semantics

(deftest doc-visibility-combines-viewers-status-and-bans
  (let [db *db*]
    (testing "published doc: owner, unbanned viewers, org editors"
      (is (= #{:uma :vic :alice :sam}
             (who-can? db :doc :view (fx/doc db "Doc Pub")))
          "wes is a viewer but banned; managers get nothing"))
    (testing "draft doc: the viewer grant is gated on (attr= :doc/status :published)"
      (is (= #{:uma :alice :sam}
             (who-can? db :doc :view (fx/doc db "Doc Draft")))))
    (testing "edit ignores viewer machinery entirely"
      (is (= #{:uma :alice :sam}
             (who-can? db :doc :edit (fx/doc db "Doc Pub")))))))

(deftest publishing-flips-visibility-live
  (let [conn (fx/fresh-conn)
        db (d/db conn)
        draft (fx/doc db "Doc Draft")
        vic (fx/user db :vic)]
    (is (not (authz/can? fx/compiled db :user vic :view :doc draft)))
    (let [{:keys [db-after tx-data]} @(d/transact conn [[:db/add draft :doc/status :published]])]
      (is (authz/can? fx/compiled db-after :user vic :view :doc draft))
      (is (contains? (into #{} (map #(d/ident db-after (:a %))) tx-data) :doc/status)
          "and the flip touches the watch-set, so reactive layers re-run"))))

;; ---------------------------------------------------------------------------
;; Recursive permissions: folder trees

(deftest folders-inherit-through-arbitrary-nesting
  (let [db *db*
        sub2 (fx/folder db "Sub2")]
    (testing "grants flow from the root's organisation down the whole tree"
      (is (= #{:alice :sena :mia :sam} (who-can? db :folder :view sub2))
          "Sub2 has no organisation of its own — everything comes via Sub1 -> Root")
      (is (= #{:alice :sam} (who-can? db :folder :manage sub2))))
    (testing "explain walks the recursion"
      (is (= {:granted? true :via '(-> :folder/parent :view)}
             (authz/explain fx/compiled db :user (fx/user db :alice) :view :folder sub2))))
    (testing "list-query refuses; list-query* carries the rules"
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"list-query\*"
                            (authz/list-query fx/compiled :folder :view :user)))
      (let [{:keys [where rules]} (authz/list-query* fx/compiled :folder :view :user)]
        (is (seq rules))
        (is (= #{(fx/folder db "Root") (fx/folder db "Sub1") sub2}
               (into #{} (map first)
                     (d/q {:find '[?folder] :in '[$ % ?user] :where where}
                          db rules (fx/user db :mia))))
            "an org member lists the entire tree in one query")
        (is (= #{}
               (into #{} (map first)
                     (d/q {:find '[?folder] :in '[$ % ?user] :where where}
                          db rules (fx/user db :bob))))
            "the other org's admin lists nothing")))))

(deftest cyclic-folder-data-terminates
  (let [conn (fx/fresh-conn)
        db (:db-after @(d/transact conn [{:db/id "ca" :folder/name "CycA" :folder/parent "cb"}
                                         {:db/id "cb" :folder/name "CycB" :folder/parent "ca"}]))
        alice (fx/user db :alice)
        cyc-a (fx/folder db "CycA")
        cyc-b (fx/folder db "CycB")]
    (testing "a parent cycle with no grounding grants nothing — and returns"
      (is (false? (authz/can? fx/compiled db :user alice :view :folder cyc-a)))
      (is (false? (authz/can? fx/compiled db :user alice :view :folder cyc-b))))
    (testing "grounding one member of the cycle grants both, everywhere"
      (let [db (:db-after @(d/transact conn [[:db/add cyc-b :folder/organisation (fx/org db "Acme")]]))]
        (is (authz/can? fx/compiled db :user alice :view :folder cyc-a))
        (is (authz/can? fx/compiled db :user alice :view :folder cyc-b))
        (is (= #{cyc-a cyc-b}
               (authz/filter-authorized fx/compiled db :user alice :view :folder
                                        [cyc-a cyc-b]))
            "the Datalog rules agree with the walker on cyclic data")))))

;; ---------------------------------------------------------------------------
;; explain

(deftest explain-reports-the-granting-branch
  (let [db *db*
        pub (fx/doc db "Doc Pub")]
    (is (= {:granted? true :via :doc/owner}
           (authz/explain fx/compiled db :user (fx/user db :uma) :view :doc pub)))
    (is (= {:granted? true :via '(and :doc/viewers
                                      (attr= :doc/status :published)
                                      (not :doc/banned))}
           (authz/explain fx/compiled db :user (fx/user db :vic) :view :doc pub)))
    (is (= {:granted? true :via '(-> :doc/organisation :edit)}
           (authz/explain fx/compiled db :user (fx/user db :alice) :view :doc pub)))
    (let [{:keys [granted? tried]} (authz/explain fx/compiled db :user (fx/user db :wes)
                                                  :view :doc pub)]
      (is (false? granted?))
      (is (= 3 (count tried)) "every branch was evaluated and refused"))))

;; ---------------------------------------------------------------------------
;; can? / filter-authorized / list-query agree everywhere

(deftest point-batch-and-list-checks-agree
  (let [db *db*
        entities {:site         (mapv #(fx/site db %) ["Site1" "Site2" "Site3" "SiteB"])
                  :organisation [(fx/org db "Acme") (fx/org db "Beta")]
                  :resource     [(fx/resource db "Acme Handbook") (fx/resource db "Beta Handbook")]
                  :assignment   [(fx/assignment db "asg-uma")]
                  :submission   (mapv #(fx/submission db %) ["sub-uma" "sub-wes" "sub-yara"])
                  :doc          (mapv #(fx/doc db %) ["Doc Pub" "Doc Draft"])
                  :folder       (mapv #(fx/folder db %) ["Root" "Sub1" "Sub2"])
                  :user         (mapv #(fx/user db %) (keys fx/users))}
        perms [[:site :view] [:site :view-members]
               [:organisation :view] [:organisation :edit] [:organisation :admin-view]
               [:resource :view] [:resource :edit]
               [:assignment :view] [:assignment :react] [:assignment :edit]
               [:submission :view] [:submission :edit]
               [:doc :view] [:doc :edit]
               [:folder :view] [:folder :manage]
               [:user :view]]]
    (doseq [[type perm] perms
            user-key (keys fx/users)]
      (let [u (fx/user db user-key)
            eids (entities type)
            via-can (into #{} (filter #(authz/can? fx/compiled db :user u perm type %)) eids)
            via-filter (authz/filter-authorized fx/compiled db :user u perm type eids)
            via-list (set/intersection (list-eids db type perm u) (set eids))]
        (is (= via-can via-filter) (str [type perm user-key] " can? vs filter-authorized"))
        (is (= via-can via-list) (str [type perm user-key] " can? vs list-query"))))))

;; ---------------------------------------------------------------------------
;; list-query composition and variable contract

(deftest list-query-composes-with-application-filters
  (let [db *db*
        sites-in (fn [user-key region-name]
                   (into #{}
                         (map first)
                         (d/q {:find '[?site]
                               :in '[$ ?user ?region]
                               :where (into (authz/list-query fx/compiled :site :view :user)
                                            '[[?site :site/region ?region]])}
                              db (fx/user db user-key) (fx/region db region-name))))]
    (is (= #{(fx/site db "Site1")} (sites-in :stan "Region1")))
    (is (= #{(fx/site db "Site2")} (sites-in :stan "Region2")))
    (is (= #{} (sites-in :rita "Region1")) "Rita manages Region2 only")
    (is (= #{(fx/site db "Site1")} (sites-in :mark "Region1")))))

(deftest list-query-var-renaming
  (let [db *db*
        clauses (authz/list-query fx/compiled :site :view :user
                                  {:subject-var '?viewer :object-var '?s})]
    (is (= #{(fx/site db "Site1")}
           (into #{}
                 (map first)
                 (d/q {:find '[?s] :in '[$ ?viewer]
                       :where (into clauses '[[?s :site/name "Site1"]])}
                      db (fx/user db :mark)))))))

(deftest same-type-queries-require-explicit-vars
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"disambiguate"
                        (authz/list-query fx/compiled :user :view :user)))
  (is (seq (authz/list-query fx/compiled :user :view :user
                             {:object-var '?target :subject-var '?viewer}))))

(deftest wrong-subject-type-fails-loud
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"subjects of type"
                        (authz/list-query fx/compiled :site :view :manager)))
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"subjects of type"
                        (authz/can? fx/compiled *db* :site 1 :view :site 2))))

(deftest unknown-permission-and-uncompiled-schema-fail-loud
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"unknown permission"
                        (authz/list-query fx/compiled :site :nope :user)))
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"compiled schema"
                        (authz/can? fx/registry *db* :user 1 :view :site 2))))

;; ---------------------------------------------------------------------------
;; Reactive invalidation

(deftest watch-set-covers-permission-changes
  (let [conn (fx/fresh-conn)
        db (d/db conn)
        watch (authz/list-query-attrs fx/compiled :site :view)
        mark (fx/user db :mark)
        site3 (fx/site db "Site3")]
    (is (= #{:site/members :manager/site :manager/user
             :site/region :manager/region :region/state
             :manager/state :state/country :manager/country
             :country/organisation :organisation/admins
             :organisation/system :system/superadmins}
           watch))
    (is (not (authz/can? fx/compiled db :user mark :view :site site3)))
    (let [{:keys [db-after tx-data]} @(d/transact conn [{:manager/user mark
                                                         :manager/site site3}])
          touched (into #{} (map #(d/ident db-after (:a %))) tx-data)]
      (is (seq (set/intersection touched watch))
          "the granting tx touches watched attrs, so a reactive layer re-runs")
      (is (authz/can? fx/compiled db-after :user mark :view :site site3)))))
