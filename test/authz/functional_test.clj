(ns authz.functional-test
  "Black-box functional suite: everything here goes through the public API
  only — a registry and world go in, behavior comes out (booleans, row sets,
  reports, thrown errors). No assertions on compiled internals.

  Uses its own self-contained domain (orgs, teams, tasks, reports) so it
  doubles as a consumer's-eye example of the library:

    org    — admins and members
    team   — belongs to an org; a lead and members
    task   — belongs to a team; an assignee
    report — an author, reviewers who may only see it while :submitted and
             not blocked, and org admins who always may"
  (:require [authz.attrs :as attrs]
            [authz.cache :as cache]
            [authz.core :as authz]
            [authz.schema :as schema]
            [clojure.set :as set]
            [clojure.test :refer [deftest is testing use-fixtures]]
            [datomic.api :as d]))

;; ---------------------------------------------------------------------------
;; The domain: inputs only — a Datomic schema, an authz registry, a world

(def datomic-schema
  (concat
   (for [[ident many?] [[:org/admins true] [:org/members true]
                        [:team/org false] [:team/lead false] [:team/members true]
                        [:task/team false] [:task/assignee false]
                        [:report/author false] [:report/org false]
                        [:report/reviewers true] [:report/blocked true]]]
     {:db/ident ident
      :db/valueType :db.type/ref
      :db/cardinality (if many? :db.cardinality/many :db.cardinality/one)})
   (for [ident [:user/handle :org/name :team/name :task/id :report/id]]
     {:db/ident ident
      :db/valueType :db.type/string
      :db/cardinality :db.cardinality/one
      :db/unique :db.unique/identity})
   [{:db/ident :task/title :db/valueType :db.type/string :db/cardinality :db.cardinality/one}
    {:db/ident :report/title :db/valueType :db.type/string :db/cardinality :db.cardinality/one}
    {:db/ident :task/status :db/valueType :db.type/keyword :db/cardinality :db.cardinality/one}
    {:db/ident :report/state :db/valueType :db.type/keyword :db/cardinality :db.cardinality/one}]))

(def registry
  {:user
   {:relations   {:team/_members :team}
    ;; a user is visible to whoever has lead-view over a team they belong to
    :permissions {:view '(-> :team/_members :lead-view)}}

   :org
   {:relations   {:org/admins :user
                  :org/members :user}
    :permissions {:admin :org/admins
                  :view  '(or :org/admins :org/members)}
    :attrs       {:org/name {:read :view :write :admin}}}

   :team
   {:relations   {:team/org :org
                  :team/lead :user
                  :team/members :user}
    :permissions {:lead-view '(or :team/lead (-> :team/org :admin))
                  :view      '(or :team/members :team/lead (-> :team/org :admin))
                  :edit      '(or :team/lead (-> :team/org :admin))}
    :create      '(-> :team/org :admin)
    :delete      :edit
    :attrs       {:team/name    {:read :view :write :edit}
                  :team/org     {:read :view}
                  :team/lead    {:read :view :create? true}
                  :team/members {:read :view}}}

   :task
   {:relations   {:task/team :team
                  :task/assignee :user}
    :permissions {:view '(or :task/assignee (-> :task/team :view))
                  :edit '(or :task/assignee (-> :task/team :edit))}
    :create      '(-> :task/team :edit)
    :delete      :edit
    :attrs       {:task/id       {:read :view :create? true}
                  :task/title    {:read :view :write :edit}
                  :task/status   {:read :view :write :edit}
                  :task/team     {:read :view}
                  :task/assignee {:read :view :create? true}}}

   :report
   {:relations   {:report/author :user
                  :report/org :org
                  :report/reviewers :user
                  :report/blocked :user}
    :permissions {:view '(or :report/author
                             (and :report/reviewers
                                  (attr= :report/state :submitted)
                                  (not :report/blocked))
                             (-> :report/org :admin))
                  :edit :report/author}
    :create      '(and :report/author (-> :report/org :view))
    :delete      :edit
    :attrs       {:report/id        {:read :view :create? true}
                  :report/title     {:read :view :write :edit}
                  :report/state     {:read :view :write :edit}
                  :report/author    {:read :view}
                  :report/org       {:read :view}
                  :report/reviewers {:read :view :write :edit :create? true}
                  :report/blocked   {:read :edit :write :edit :create? true}}}})

(def compiled (schema/compile-schema registry))

(def all-users ["ada" "zoe" "yan" "mel" "tom" "lea" "lou" "nia"])

(def world-tx
  (into
   (mapv (fn [h] {:db/id h :user/handle h}) all-users)
   [{:db/id "acme" :org/name "acme"
     :org/admins ["ada"] :org/members ["mel" "tom" "lea" "lou"]}
    {:db/id "zeta" :org/name "zeta"
     :org/admins ["zoe"] :org/members ["yan"]}
    {:db/id "alpha" :team/name "alpha" :team/org "acme"
     :team/lead "lea" :team/members ["mel" "tom"]}
    {:db/id "beta" :team/name "beta" :team/org "acme"
     :team/lead "lou" :team/members ["tom"]}
    {:db/id "zteam" :team/name "zteam" :team/org "zeta"
     :team/lead "yan" :team/members ["yan"]}
    {:task/id "t1" :task/team "alpha" :task/assignee "mel"
     :task/title "Fix login" :task/status :todo}
    {:task/id "t2" :task/team "beta" :task/assignee "tom"
     :task/title "Ship exports" :task/status :doing}
    {:report/id "r-draft" :report/author "mel" :report/org "acme"
     :report/reviewers ["tom" "lea"] :report/state :draft
     :report/title "Q3 draft"}
    {:report/id "r-live" :report/author "mel" :report/org "acme"
     :report/reviewers ["tom" "lea"] :report/blocked ["tom"]
     :report/state :submitted :report/title "Q3 wrap-up"}]))

(defn- world-conn []
  (let [uri (str "datomic:mem://" (d/squuid))]
    (d/create-database uri)
    (let [conn (d/connect uri)]
      @(d/transact conn (vec datomic-schema))
      @(d/transact conn world-tx)
      conn)))

(def ^:dynamic *db* nil)

(use-fixtures :once
  (fn [f] (binding [*db* (d/db (world-conn))] (f))))

;; lookups
(defn- u [db h] (d/entid db [:user/handle h]))
(defn- team [db n] (d/entid db [:team/name n]))
(defn- org [db n] (d/entid db [:org/name n]))
(defn- task [db i] (d/entid db [:task/id i]))
(defn- report [db i] (d/entid db [:report/id i]))

(defn- who
  "Handles of every user holding `perm` over `eid`."
  [db type perm eid]
  (into #{} (filter #(authz/can? compiled db :user (u db %) perm type eid)) all-users))

;; ---------------------------------------------------------------------------
;; Compilation is the only setup

(deftest schema-compiles-to-an-immutable-value
  (is (schema/compiled? compiled))
  (is (= compiled (schema/compile-schema registry))
      "same registry in, same value out"))

;; ---------------------------------------------------------------------------
;; Point-check behavior across the whole language

(deftest team-visibility
  (let [db *db*]
    (is (= #{"mel" "tom" "lea" "ada"} (who db :team :view (team db "alpha")))
        "members + lead + org admin; the other team's lead sees nothing")
    (is (= #{"tom" "lou" "ada"} (who db :team :view (team db "beta"))))
    (is (= #{"lea" "ada"} (who db :team :edit (team db "alpha"))))
    (is (= #{"yan" "zoe"} (who db :team :view (team db "zteam")))
        "orgs are fully isolated")))

(deftest task-visibility-follows-assignee-and-team
  (let [db *db*]
    (is (= #{"mel" "tom" "lea" "ada"} (who db :task :view (task db "t1"))))
    (is (= #{"mel" "lea" "ada"} (who db :task :edit (task db "t1")))
        "a fellow team member may view but not edit")
    (is (= #{"tom" "lou" "ada"} (who db :task :view (task db "t2"))))))

(deftest report-visibility-combines-reviewers-state-and-blocks
  (let [db *db*]
    (is (= #{"mel" "ada"} (who db :report :view (report db "r-draft")))
        "reviewers see nothing while the report is a draft")
    (is (= #{"mel" "lea" "ada"} (who db :report :view (report db "r-live")))
        "once submitted, unblocked reviewers see it; tom is blocked")
    (is (= #{"mel"} (who db :report :edit (report db "r-live")))
        "only the author edits — not even the org admin")))

(deftest person-visibility-through-reverse-relations
  (let [db *db*]
    (is (= #{"lea" "ada"} (who db :user :view (u db "mel")))
        "mel is visible to their team lead and org admin — not to peers, not to self")
    (is (= #{"lea" "lou" "ada"} (who db :user :view (u db "tom")))
        "tom is in two teams, so both leads see him")
    (is (= #{"yan" "zoe"} (who db :user :view (u db "yan")))
        "yan leads their own team, so yan genuinely sees themself")
    (is (= #{} (who db :user :view (u db "nia")))
        "a user in no team is visible to nobody")))

;; ---------------------------------------------------------------------------
;; List endpoints: the database filters rows, the caller adds app clauses

(deftest list-endpoints-return-only-authorized-rows
  (let [db *db*
        task-ids-for (fn [handle]
                       (into #{} (map first)
                             (d/q {:find '[?id] :in '[$ ?user]
                                   :where (into (authz/list-query compiled :task :view :user)
                                                '[[?task :task/id ?id]])}
                                  db (u db handle))))]
    (is (= #{"t1" "t2"} (task-ids-for "tom")))
    (is (= #{"t1"} (task-ids-for "mel")))
    (is (= #{"t2"} (task-ids-for "lou")))
    (is (= #{"t1" "t2"} (task-ids-for "ada")))
    (is (= #{} (task-ids-for "nia")))
    (is (= #{} (task-ids-for "zoe")) "the other org's admin gets zero rows")))

(deftest list-query-composes-with-application-filters
  (let [db *db*
        todo-tasks (fn [handle]
                     (into #{} (map first)
                           (d/q {:find '[?id] :in '[$ ?user]
                                 :where (into (authz/list-query compiled :task :view :user)
                                              '[[?task :task/status :todo]
                                                [?task :task/id ?id]])}
                                db (u db handle))))]
    (is (= #{"t1"} (todo-tasks "ada")))
    (is (= #{} (todo-tasks "lou")) "lou's only visible task is not :todo")))

(deftest listing-users-a-user-may-view
  ;; object type = subject type: the caller must name the query vars
  (let [db *db*
        visible-to (fn [handle]
                     (into #{} (map first)
                           (d/q {:find '[?handle] :in '[$ ?viewer]
                                 :where (into (authz/list-query
                                               compiled :user :view :user
                                               {:object-var '?target :subject-var '?viewer})
                                              '[[?target :user/handle ?handle]])}
                                db (u db handle))))]
    (is (= #{"mel" "tom"} (visible-to "lea")))
    (is (= #{"mel" "tom"} (visible-to "ada")))
    (is (= #{"yan"} (visible-to "zoe")))
    (is (= #{} (visible-to "mel")))))

;; ---------------------------------------------------------------------------
;; explain: the "why" is part of the contract

(deftest explain-reports-the-granting-rule-as-written
  (let [db *db*
        t1 (task db "t1")
        live (report db "r-live")]
    (is (= {:granted? true :via :task/assignee}
           (authz/explain compiled db :user (u db "mel") :view :task t1)))
    (is (= {:granted? true :via '(-> :task/team :view)}
           (authz/explain compiled db :user (u db "lea") :view :task t1)))
    (is (= {:granted? true :via '(and :report/reviewers
                                      (attr= :report/state :submitted)
                                      (not :report/blocked))}
           (authz/explain compiled db :user (u db "lea") :view :report live)))
    (is (= {:granted? true :via '(-> :report/org :admin)}
           (authz/explain compiled db :user (u db "ada") :view :report live)))
    (let [{:keys [granted? tried]} (authz/explain compiled db :user (u db "tom")
                                                  :view :report live)]
      (is (false? granted?))
      (is (= 3 (count tried)) "every rule was tried and refused"))))

;; ---------------------------------------------------------------------------
;; All read APIs agree, for every subject and object

(def ^:private sweep-perms
  [[:team :view] [:team :edit]
   [:task :view] [:task :edit]
   [:report :view] [:report :edit]
   [:org :view] [:org :admin]
   [:user :view]])

(defn- entities-by-type [db]
  {:team (mapv #(team db %) ["alpha" "beta" "zteam"])
   :task (mapv #(task db %) ["t1" "t2"])
   :report (mapv #(report db %) ["r-draft" "r-live"])
   :org (mapv #(org db %) ["acme" "zeta"])
   :user (mapv #(u db %) all-users)})

(defn- list-eids [db type perm subject-eid]
  (let [collision? (= type :user)
        opts (when collision? {:object-var '?target :subject-var '?subject})
        obj-var (if collision? '?target (symbol (str "?" (name type))))
        subj-var (if collision? '?subject '?user)]
    (into #{} (map first)
          (d/q {:find [obj-var] :in ['$ subj-var]
                :where (authz/list-query compiled type perm :user opts)}
               db subject-eid))))

(deftest point-batch-and-list-checks-agree-everywhere
  (let [db *db*
        ents (entities-by-type db)]
    (doseq [[type perm] sweep-perms
            handle all-users]
      (let [s (u db handle)
            eids (ents type)
            via-can (into #{} (filter #(authz/can? compiled db :user s perm type %)) eids)
            via-batch (authz/filter-authorized compiled db :user s perm type eids)
            via-list (set/intersection (list-eids db type perm s) (set eids))]
        (is (= via-can via-batch) (str [type perm handle] " can? vs filter-authorized"))
        (is (= via-can via-list) (str [type perm handle] " can? vs list-query"))))))

;; ---------------------------------------------------------------------------
;; The reactive contract: any visibility change must touch the watch-set

(defn- outcome-map [db]
  (let [ents (entities-by-type db)]
    (into {}
          (for [[type perm] sweep-perms
                s (:user ents)
                o (ents type)]
            [[type perm s o] (authz/can? compiled db :user s perm type o)]))))

(deftest any-visibility-change-touches-the-watch-set
  (let [conn (world-conn)
        mutations
        [["a new team member gains team visibility"
          (fn [db] [[:db/add (team db "alpha") :team/members (u db "yan")]])]
         ["a lead handover moves person-visibility"
          (fn [db] [[:db/retract (team db "alpha") :team/lead (u db "lea")]
                    [:db/add (team db "alpha") :team/lead (u db "tom")]])]
         ["submitting a report opens it to reviewers"
          (fn [db] [[:db/add (report db "r-draft") :report/state :submitted]])]
         ["blocking a reviewer closes it again"
          (fn [db] [[:db/add (report db "r-live") :report/blocked (u db "lea")]])]
         ["a new org admin gains everything"
          (fn [db] [[:db/add (org db "acme") :org/admins (u db "nia")]])]]]
    (doseq [[label mutate] mutations]
      (let [db-before (d/db conn)
            {:keys [db-after tx-data]} @(d/transact conn (mutate db-before))
            touched (into #{} (map #(d/ident db-after (:a %))) tx-data)
            before (outcome-map db-before)
            after (outcome-map db-after)
            changed (into #{}
                          (comp (filter (fn [[k v]] (not= v (get before k))))
                                (map (fn [[[type perm _ _] _]] [type perm])))
                          after)]
        (testing label
          (is (seq changed) "the mutation changed at least one outcome")
          (doseq [[type perm] changed]
            (is (seq (set/intersection touched (authz/list-query-attrs compiled type perm)))
                (str "outcomes for " [type perm] " changed, but the tx touched "
                     "none of its watch-set — a reactive layer would go stale"))))))))

;; ---------------------------------------------------------------------------
;; The offline client lifecycle, end to end

(deftest offline-client-round-trip
  (let [conn (world-conn)
        db (d/db conn)
        mel (u db "mel") tom (u db "tom") lea (u db "lea") yan (u db "yan")
        live (report db "r-live") draft (report db "r-draft")
        acme (org db "acme")
        batch (into [] (mapcat #(d/datoms db :eavt %))
                    [acme (org db "zeta") (team db "alpha")
                     (task db "t1") draft live])
        allowed-attrs (fn [res e]
                        (into #{}
                              (comp (filter #(= e (:e %)))
                                    (map #(d/ident db (:a %))))
                              (:allowed res)))]

    (testing "sync down is filtered per client, deny-by-default"
      (let [for-tom (attrs/readable-datoms compiled db tom batch)]
        (is (contains? (allowed-attrs for-tom (task db "t1")) :task/title))
        (is (contains? (allowed-attrs for-tom acme) :org/name))
        (is (empty? (allowed-attrs for-tom draft))
            "draft reports don't sync to reviewers")
        (is (empty? (allowed-attrs for-tom live))
            "tom is blocked on the live report")
        (is (empty? (allowed-attrs for-tom (org db "zeta")))
            "the other org never syncs"))
      (let [for-lea (attrs/readable-datoms compiled db lea batch)]
        (is (contains? (allowed-attrs for-lea live) :report/title))
        (is (not (contains? (allowed-attrs for-lea live) :report/blocked))
            "reviewers cannot see who is blocked"))
      (is (contains? (allowed-attrs (attrs/readable-datoms compiled db mel batch) live)
                     :report/blocked)
          "the author syncs even the blocked list (read gated by :edit)"))

    (testing "the author's offline edit syncs up and transacts"
      (let [tx [[:db/add live :report/title "Q3 wrap-up (final)"]]
            {:keys [db-after]} @(d/transact conn (attrs/authorize-tx! compiled db mel tx))]
        (is (= "Q3 wrap-up (final)" (:report/title (d/entity db-after live))))))

    (testing "re-sending the full entity map after reconnect is a free no-op"
      (let [db (d/db conn)
            result (attrs/check-tx compiled db mel
                                   [{:report/id "r-live"
                                     :report/author mel
                                     :report/org acme
                                     :report/title "Q3 wrap-up (final)"
                                     :report/state :submitted}])]
        (is (:allowed? result))
        (is (zero? (:ops result)))))

    (testing "tampering is denied with a reviewable report"
      (let [db (d/db conn)]
        (is (not (:allowed? (attrs/check-tx compiled db tom
                                            [[:db/add live :report/title "hax"]]))))
        (let [upsert (attrs/check-tx compiled db tom
                                     [{:report/id "r-live" :report/author tom}])]
          (is (not (:allowed? upsert))
              "an upsert onto someone else's report is a write, not a create")
          (is (every? :reason (:denied upsert)))
          (is (every? :message (:denied upsert))))))

    (testing "creation follows the :create rules"
      (let [db (d/db conn)]
        (is (not (:allowed? (attrs/check-tx compiled db yan
                                            [{:report/id "r-yan" :report/author yan
                                              :report/org acme :report/state :draft}])))
            "authoring requires :view on the org")
        (is (not (:allowed? (attrs/check-tx compiled db mel
                                            [{:task/id "t-mel" :task/team (team db "alpha")
                                              :task/assignee mel :task/title "self-serve"}])))
            "task creation is lead/admin-gated, being the assignee is not enough")
        (is (:allowed? (attrs/check-tx compiled db lea
                                       [{:task/id "t-new" :task/team (team db "alpha")
                                         :task/assignee mel :task/title "New task"
                                         :task/status :todo}])))
        @(d/transact conn (attrs/authorize-tx! compiled db mel
                                               [{:report/id "r-new" :report/author mel
                                                 :report/org acme :report/title "New"
                                                 :report/state :draft}]))))

    (testing "deletion follows the :delete rule"
      (let [db (d/db conn)
            r-new (report db "r-new")]
        (is (not (:allowed? (attrs/check-tx compiled db tom [[:db/retractEntity r-new]]))))
        (let [{:keys [db-after]}
              @(d/transact conn (attrs/authorize-tx! compiled db mel
                                                     [[:db/retractEntity r-new]]))]
          (is (nil? (d/entid db-after [:report/id "r-new"]))))))))

;; ---------------------------------------------------------------------------
;; Cache: always current, never stale

(deftest cache-serves-current-db-values
  (let [conn (world-conn)
        db (d/db conn)
        c (cache/make-cache)
        tom (u db "tom")
        draft (report db "r-draft")]
    (is (false? (cache/can? c compiled db :user tom :view :report draft)))
    (let [db2 (:db-after @(d/transact conn [[:db/add draft :report/state :submitted]]))]
      (is (true? (cache/can? c compiled db2 :user tom :view :report draft))
          "a new db value misses the cache and recomputes — no staleness")
      (is (false? (cache/can? c compiled db :user tom :view :report draft))
          "the old snapshot's answer is still correct for that snapshot")
      (is (true? (cache/can? c compiled db2 :user tom :view :report draft)))
      (is (pos? (:hits (cache/stats c)))))))

;; ---------------------------------------------------------------------------
;; Recursive permissions: the public contract

(deftest recursive-permissions-contract
  (let [reg {:user {}
             :node {:relations   {:node/owner :user
                                  :node/parent :node}
                    :permissions {:view '(or :node/owner (-> :node/parent :view))}}}
        rschema (schema/compile-schema reg)
        uri (str "datomic:mem://" (d/squuid))
        _ (d/create-database uri)
        conn (d/connect uri)
        _ @(d/transact conn [{:db/ident :node/owner :db/valueType :db.type/ref
                              :db/cardinality :db.cardinality/one}
                             {:db/ident :node/parent :db/valueType :db.type/ref
                              :db/cardinality :db.cardinality/one}
                             {:db/ident :node/name :db/valueType :db.type/string
                              :db/cardinality :db.cardinality/one
                              :db/unique :db.unique/identity}
                             {:db/ident :person/handle :db/valueType :db.type/string
                              :db/cardinality :db.cardinality/one
                              :db/unique :db.unique/identity}])
        _ @(d/transact conn [{:db/id "owner" :person/handle "owner"}
                             {:db/id "other" :person/handle "other"}
                             {:db/id "n0" :node/name "n0" :node/owner "owner"}
                             {:db/id "n1" :node/name "n1" :node/parent "n0"}
                             {:db/id "n2" :node/name "n2" :node/parent "n1"}
                             {:db/id "n3" :node/name "n3" :node/parent "n2"}])
        db (d/db conn)
        node (fn [n] (d/entid db [:node/name n]))
        owner (d/entid db [:person/handle "owner"])
        other (d/entid db [:person/handle "other"])]
    (testing "ownership inherits down arbitrary nesting"
      (is (authz/can? rschema db :user owner :view :node (node "n3")))
      (is (not (authz/can? rschema db :user other :view :node (node "n3")))))
    (testing "list-query fails loudly; list-query* is the sanctioned path"
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"list-query\*"
                            (authz/list-query rschema :node :view :user)))
      (let [{:keys [where rules]} (authz/list-query* rschema :node :view :user)]
        (is (seq rules))
        (is (= #{(node "n0") (node "n1") (node "n2") (node "n3")}
               (into #{} (map first)
                     (d/q {:find '[?node] :in '[$ % ?user] :where where}
                          db rules owner))))))
    (testing "list-query* also serves non-recursive permissions, with empty rules"
      (let [{:keys [where rules]} (authz/list-query* compiled :task :view :user)]
        (is (empty? rules))
        (is (vector? where))))
    (testing "cyclic data terminates and answers correctly"
      (let [db (:db-after @(d/transact conn [{:db/id "c1" :node/name "c1" :node/parent "c2"}
                                             {:db/id "c2" :node/name "c2" :node/parent "c1"}]))
            c1 (d/entid db [:node/name "c1"])]
        (is (false? (authz/can? rschema db :user owner :view :node c1))
            "an ungrounded cycle grants nothing — and returns")
        (let [db (:db-after @(d/transact conn [[:db/add (d/entid db [:node/name "c2"])
                                                :node/owner owner]]))]
          (is (true? (authz/can? rschema db :user owner :view :node
                                 (d/entid db [:node/name "c1"])))
              "grounding one member of the cycle grants through it"))))))

;; ---------------------------------------------------------------------------
;; Errors are loud and carry data

(deftest error-contract
  (let [db *db*]
    (testing "unknown permission"
      (let [e (try (authz/can? compiled db :user (u db "mel") :frobnicate :task (task db "t1"))
                   nil
                   (catch clojure.lang.ExceptionInfo e e))]
        (is (some? e))
        (is (contains? (:known (ex-data e)) :view)
            "the error names the permissions that do exist")))
    (testing "wrong subject type"
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"subjects of type"
                            (authz/list-query compiled :task :view :team))))
    (testing "raw registry instead of compiled schema"
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"compiled schema"
                            (authz/can? registry db :user 1 :view :task 2))))
    (testing "same-type query without explicit vars"
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"disambiguate"
                            (authz/list-query compiled :user :view :user))))
    (testing "unknown subject in tx checking"
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"unknown subject"
                            (attrs/check-tx compiled db [:user/handle "ghost"] []))))))
