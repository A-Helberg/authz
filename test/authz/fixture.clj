(ns authz.fixture
  "Shared test world: the domain shape from the overview doc — a hierarchy
  system -> organisation -> country/state/region -> site -> users, managers
  as first-class scope entities, and content (resources, assignments,
  submissions) hanging off the organisation."
  (:require [authz.schema :as schema]
            [datomic.api :as d]))

;; ---------------------------------------------------------------------------
;; Datomic schema

(def datomic-schema
  (concat
   (for [[ident cardinality] [[:system/superadmins :many]
                              [:organisation/system :one]
                              [:organisation/admins :many]
                              [:organisation/senior-leadership :many]
                              [:organisation/members :many]
                              [:country/organisation :one]
                              [:state/country :one]
                              [:region/state :one]
                              [:site/region :one]
                              [:site/members :many]
                              [:manager/user :one]
                              [:manager/site :one]
                              [:manager/region :one]
                              [:manager/state :one]
                              [:manager/country :one]
                              [:resource/organisation :one]
                              [:assignment/member :one]
                              [:assignment/organisation :one]
                              [:submission/submitted-by :one]
                              [:submission/organisation :one]
                              [:folder/organisation :one]
                              [:folder/parent :one]
                              [:doc/organisation :one]
                              [:doc/owner :one]
                              [:doc/viewers :many]
                              [:doc/banned :many]]]
     {:db/ident ident
      :db/valueType :db.type/ref
      :db/cardinality (if (= :many cardinality) :db.cardinality/many :db.cardinality/one)})
   (for [ident [:organisation/name :country/name :state/name :region/name
                :site/name :resource/title :assignment/id :submission/id
                :folder/name :doc/title]]
     {:db/ident ident
      :db/valueType :db.type/string
      :db/cardinality :db.cardinality/one
      :db/unique :db.unique/identity})
   [{:db/ident :user/email
     :db/valueType :db.type/string
     :db/cardinality :db.cardinality/one
     :db/unique :db.unique/identity}
    {:db/ident :user/name
     :db/valueType :db.type/string
     :db/cardinality :db.cardinality/one}
    {:db/ident :assignment/notes
     :db/valueType :db.type/string
     :db/cardinality :db.cardinality/one}
    {:db/ident :submission/content
     :db/valueType :db.type/string
     :db/cardinality :db.cardinality/one}
    {:db/ident :doc/status
     :db/valueType :db.type/keyword
     :db/cardinality :db.cardinality/one}]))

;; ---------------------------------------------------------------------------
;; Authz registry

(def registry
  {:system
   {:relations   {:system/superadmins :user}
    :permissions {:superadmin :system/superadmins}}

   :user
   {:relations   {:site/_members :site
                  :organisation/_members :organisation}
    :permissions {:view '(or (-> :site/_members :view-members)
                             (-> :organisation/_members :admin-view))}}

   :manager
   {:relations   {:manager/user :user}
    :permissions {:is-user :manager/user}}

   :organisation
   ;; NOTE: deliberately NO manager->organisation shortcut on :view /
   ;; :admin-view — managers are scoped to their site/region/state/country
   ;; and adding the shortcut would break hierarchical scoping.
   {:relations   {:organisation/system :system
                  :organisation/admins :user
                  :organisation/senior-leadership :user
                  :organisation/members :user}
    :permissions {:view       '(or :organisation/admins
                                   :organisation/senior-leadership
                                   :organisation/members
                                   (-> :organisation/system :superadmin))
                  :admin-view '(or :organisation/admins
                                   (-> :organisation/system :superadmin))
                  :edit       '(or :organisation/admins
                                   (-> :organisation/system :superadmin))}
    ;; :attrs but no :create — clients may edit the name but never create orgs
    :attrs       {:organisation/name {:read :view :write :edit}}}

   :country
   {:relations   {:country/organisation :organisation
                  :manager/_country :manager}
    :permissions {:manage-members '(or (-> :manager/_country :is-user)
                                       (-> :country/organisation :admin-view))}}

   :state
   {:relations   {:state/country :country
                  :manager/_state :manager}
    :permissions {:manage-members '(or (-> :manager/_state :is-user)
                                       (-> :state/country :manage-members))}}

   :region
   {:relations   {:region/state :state
                  :manager/_region :manager}
    :permissions {:manage-members '(or (-> :manager/_region :is-user)
                                       (-> :region/state :manage-members))}}

   :site
   {:relations   {:site/region :region
                  :site/members :user
                  :manager/_site :manager}
    :permissions {:view         '(or :site/members
                                     (-> :manager/_site :is-user)
                                     (-> :site/region :manage-members))
                  :view-members '(or (-> :manager/_site :is-user)
                                     (-> :site/region :manage-members))}}

   :resource
   {:relations   {:resource/organisation :organisation}
    :permissions {:view '(-> :resource/organisation :view)
                  :edit '(-> :resource/organisation :edit)}
    :create      '(-> :resource/organisation :edit)
    :delete      :edit
    :attrs       {:resource/title        {:read :view :write :edit}
                  :resource/organisation {:read :view}}}

   :assignment
   {:relations   {:assignment/member :user
                  :assignment/organisation :organisation}
    ;; Terminal AND chain over the same relation: the assignee can view,
    ;; and so can anyone who may view the assignee as a user.
    :permissions {:view  '(or :assignment/member
                              (-> :assignment/member :view))
                  :react :assignment/member
                  :edit  '(-> :assignment/organisation :edit)}
    :create      '(-> :assignment/organisation :edit)
    :delete      :edit
    :attrs       {:assignment/id           {:read :view :create? true}
                  :assignment/notes        {:read :view :write :react}
                  :assignment/member       {:read :view :create? true}
                  :assignment/organisation {:read :view}}}

   :submission
   {:relations   {:submission/submitted-by :user
                  :submission/organisation :organisation}
    :permissions {:view '(or :submission/submitted-by
                             (-> :submission/submitted-by :view))
                  :edit :submission/submitted-by}
    ;; Terminal create rule: you may create a submission you submit yourself.
    :create      :submission/submitted-by
    :delete      :edit
    :attrs       {:submission/id           {:read :view :create? true}
                  :submission/content      {:read :view :write :edit}
                  :submission/submitted-by {:read :view}
                  :submission/organisation {:read :view :create? true}}}

   :folder
   ;; Exercises create-chains that may target an entity created in the SAME
   ;; transaction (create a folder and its subfolder together).
   {:relations   {:folder/organisation :organisation
                  :folder/parent :folder}
    :permissions {:view   '(-> :folder/organisation :view)
                  :manage '(-> :folder/organisation :edit)}
    :create      '(or (-> :folder/organisation :edit)
                      (-> :folder/parent :manage))
    :delete      :manage
    :attrs       {:folder/name         {:read :view :write :manage}
                  :folder/organisation {:read :view}
                  :folder/parent       {:read :view}}}

   :doc
   ;; Exercises and / not / attr=: viewers see a doc only while it is
   ;; published and they are not banned from it.
   {:relations   {:doc/organisation :organisation
                  :doc/owner :user
                  :doc/viewers :user
                  :doc/banned :user}
    :permissions {:view '(or :doc/owner
                             (and :doc/viewers
                                  (attr= :doc/status :published)
                                  (not :doc/banned))
                             (-> :doc/organisation :edit))
                  :edit '(or :doc/owner
                             (-> :doc/organisation :edit))}
    ;; and in a create rule: own docs, in orgs you can at least view
    :create      '(and :doc/owner (-> :doc/organisation :view))
    :delete      :edit
    :attrs       {:doc/title        {:read :view :write :edit}
                  :doc/status       {:read :view :write :edit}
                  :doc/owner        {:read :view}
                  :doc/organisation {:read :view}
                  :doc/viewers      {:read :view :write :edit :create? true}
                  :doc/banned       {:read :edit :write :edit :create? true}}}})

(def compiled (schema/compile-schema registry))

;; ---------------------------------------------------------------------------
;; World

(def world-tx
  [;; users
   {:db/id "sam" :user/name "Sam" :user/email "sam@x"}     ; superadmin
   {:db/id "alice" :user/name "Alice" :user/email "alice@x"} ; acme org admin
   {:db/id "sena" :user/name "Sena" :user/email "sena@x"}  ; acme senior leadership
   {:db/id "mia" :user/name "Mia" :user/email "mia@x"}     ; acme org member (no site)
   {:db/id "uma" :user/name "Uma" :user/email "uma@x"}     ; site1 member
   {:db/id "vic" :user/name "Vic" :user/email "vic@x"}     ; site1 member
   {:db/id "wes" :user/name "Wes" :user/email "wes@x"}     ; site2 member
   {:db/id "xia" :user/name "Xia" :user/email "xia@x"}     ; site3 member
   {:db/id "mark" :user/name "Mark" :user/email "mark@x"}  ; manages site1
   {:db/id "rita" :user/name "Rita" :user/email "rita@x"}  ; manages region2
   {:db/id "stan" :user/name "Stan" :user/email "stan@x"}  ; manages state1
   {:db/id "carl" :user/name "Carl" :user/email "carl@x"}  ; manages country1
   {:db/id "bob" :user/name "Bob" :user/email "bob@x"}     ; beta org admin
   {:db/id "yara" :user/name "Yara" :user/email "yara@x"}  ; beta site member
   ;; system
   {:db/id "sys" :system/superadmins ["sam"]}
   ;; acme hierarchy: country1 -> state1 -> region1 (site1), region2 (site2)
   ;;                          -> state2 -> region3 (site3)
   {:db/id "acme" :organisation/name "Acme" :organisation/system "sys"
    :organisation/admins ["alice"] :organisation/senior-leadership ["sena"]
    :organisation/members ["mia"]}
   {:db/id "country1" :country/name "Country1" :country/organisation "acme"}
   {:db/id "state1" :state/name "State1" :state/country "country1"}
   {:db/id "state2" :state/name "State2" :state/country "country1"}
   {:db/id "region1" :region/name "Region1" :region/state "state1"}
   {:db/id "region2" :region/name "Region2" :region/state "state1"}
   {:db/id "region3" :region/name "Region3" :region/state "state2"}
   {:db/id "site1" :site/name "Site1" :site/region "region1" :site/members ["uma" "vic"]}
   {:db/id "site2" :site/name "Site2" :site/region "region2" :site/members ["wes"]}
   {:db/id "site3" :site/name "Site3" :site/region "region3" :site/members ["xia"]}
   {:manager/user "mark" :manager/site "site1"}
   {:manager/user "rita" :manager/region "region2"}
   {:manager/user "stan" :manager/state "state1"}
   {:manager/user "carl" :manager/country "country1"}
   ;; beta org, isolated from acme
   {:db/id "beta" :organisation/name "Beta" :organisation/system "sys"
    :organisation/admins ["bob"]}
   {:db/id "country-b" :country/name "CountryB" :country/organisation "beta"}
   {:db/id "state-b" :state/name "StateB" :state/country "country-b"}
   {:db/id "region-b" :region/name "RegionB" :region/state "state-b"}
   {:db/id "site-b" :site/name "SiteB" :site/region "region-b" :site/members ["yara"]}
   ;; content
   {:resource/title "Acme Handbook" :resource/organisation "acme"}
   {:resource/title "Beta Handbook" :resource/organisation "beta"}
   {:assignment/id "asg-uma" :assignment/member "uma"
    :assignment/organisation "acme" :assignment/notes "start"}
   {:submission/id "sub-uma" :submission/submitted-by "uma"
    :submission/organisation "acme" :submission/content "uma's work"}
   {:submission/id "sub-wes" :submission/submitted-by "wes"
    :submission/organisation "acme" :submission/content "wes's work"}
   {:submission/id "sub-yara" :submission/submitted-by "yara"
    :submission/organisation "beta" :submission/content "yara's work"}
   {:db/id "folder-root" :folder/name "Root" :folder/organisation "acme"}
   ;; doc-pub: published; vic may view as viewer, wes is banned
   {:db/id "doc-pub" :doc/title "Doc Pub" :doc/organisation "acme"
    :doc/owner "uma" :doc/viewers ["vic" "wes"] :doc/banned ["wes"]
    :doc/status :published}
   ;; doc-draft: not published; viewers see nothing yet
   {:db/id "doc-draft" :doc/title "Doc Draft" :doc/organisation "acme"
    :doc/owner "uma" :doc/viewers ["vic"] :doc/status :draft}])

(defn empty-conn
  "A fresh in-memory Datomic connection with only the schema transacted."
  []
  (let [uri (str "datomic:mem://" (d/squuid))]
    (d/create-database uri)
    (let [conn (d/connect uri)]
      @(d/transact conn (vec datomic-schema))
      conn)))

(defn fresh-conn
  "A fresh in-memory Datomic connection with schema and world transacted."
  []
  (let [conn (empty-conn)]
    @(d/transact conn world-tx)
    conn))

(def users
  {:sam "sam@x" :alice "alice@x" :sena "sena@x" :mia "mia@x" :uma "uma@x"
   :vic "vic@x" :wes "wes@x" :xia "xia@x" :mark "mark@x" :rita "rita@x"
   :stan "stan@x" :carl "carl@x" :bob "bob@x" :yara "yara@x"})

(defn user [db k] (d/entid db [:user/email (get users k)]))
(defn org [db n] (d/entid db [:organisation/name n]))
(defn site [db n] (d/entid db [:site/name n]))
(defn region [db n] (d/entid db [:region/name n]))
(defn resource [db t] (d/entid db [:resource/title t]))
(defn assignment [db i] (d/entid db [:assignment/id i]))
(defn submission [db i] (d/entid db [:submission/id i]))
(defn folder [db n] (d/entid db [:folder/name n]))
(defn doc [db t] (d/entid db [:doc/title t]))
