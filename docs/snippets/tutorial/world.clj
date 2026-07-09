(ns tutorial.world
  "The world every page of this tutorial runs against: one registry, one
  in-memory Datomic database. Every result you see on the right was
  produced by evaluating that page's code against exactly this."
  (:require [authz.core :as authz]
            [authz.schema :as authz.schema]
            [datomic.api :as d]))

;; --------------------------------------------------------------------------
;; The authz registry — the whole permission model is this one data structure

(def registry
  {:user
   {:relations   {:site/_members :site}
    ;; you may view a user if you may view-members of a site they belong to
    :permissions {:view '(-> :site/_members :view-members)}}

   :organisation
   {:relations   {:organisation/admins :user
                  :organisation/members :user}
    :permissions {:view '(or :organisation/admins :organisation/members)
                  :edit :organisation/admins}
    :attrs       {:organisation/name {:read :view :write :edit}}}

   :manager
   ;; managers are first-class entities linking a user to a scope
   {:relations   {:manager/user :user}
    :permissions {:is-user :manager/user}}

   :site
   {:relations   {:site/organisation :organisation
                  :site/members :user
                  :manager/_site :manager}   ; reverse: managers pointing here
    :permissions {:view         '(or :site/members
                                     (-> :manager/_site :is-user)
                                     (-> :site/organisation :edit))
                  :view-members '(or (-> :manager/_site :is-user)
                                     (-> :site/organisation :edit))}}

   :assignment
   {:relations   {:assignment/member :user
                  :assignment/organisation :organisation}
    ;; terminal AND chain over the same relation — the tutorial's key lesson
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

   :doc
   {:relations   {:doc/organisation :organisation
                  :doc/owner :user
                  :doc/viewers :user
                  :doc/banned :user}
    :permissions {:view '(or :doc/owner
                             (and :doc/viewers
                                  (attr= :doc/status :published)
                                  (not :doc/banned))
                             (-> :doc/organisation :edit))
                  :edit '(or :doc/owner (-> :doc/organisation :edit))}
    :create      '(and :doc/owner (-> :doc/organisation :view))
    :delete      :edit
    :attrs       {:doc/title        {:read :view :write :edit}
                  :doc/status       {:read :view :write :edit}
                  :doc/owner        {:read :view}
                  :doc/organisation {:read :view}
                  :doc/viewers      {:read :view :write :edit :create? true}
                  :doc/banned       {:read :edit :write :edit :create? true}}}

   :folder
   ;; recursive: a folder inherits from its parent, bottoming out at a root
   ;; folder attached to an organisation
   {:relations   {:folder/organisation :organisation
                  :folder/parent :folder}
    :permissions {:view   '(or (-> :folder/organisation :view)
                               (-> :folder/parent :view))
                  :manage '(or (-> :folder/organisation :edit)
                               (-> :folder/parent :manage))}
    :create      '(or (-> :folder/organisation :edit)
                      (-> :folder/parent :manage))
    :delete      :manage
    :attrs       {:folder/name         {:read :view :write :manage}
                  :folder/organisation {:read :view}
                  :folder/parent       {:read :view}}}})

;; compile ONCE — an immutable value you pass around, like a db
(def schema (authz.schema/compile-schema registry))

;; --------------------------------------------------------------------------
;; A small world: Acme (and a rival, Zeta, to prove isolation)

(def datomic-schema
  (concat
   (for [[ident many?] [[:organisation/admins true] [:organisation/members true]
                        [:site/organisation false] [:site/members true]
                        [:manager/user false] [:manager/site false]
                        [:assignment/member false] [:assignment/organisation false]
                        [:doc/organisation false] [:doc/owner false]
                        [:doc/viewers true] [:doc/banned true]
                        [:folder/organisation false] [:folder/parent false]]]
     {:db/ident ident :db/valueType :db.type/ref
      :db/cardinality (if many? :db.cardinality/many :db.cardinality/one)})
   (for [ident [:user/name :organisation/name :site/name
                :assignment/id :doc/title :folder/name]]
     {:db/ident ident :db/valueType :db.type/string
      :db/cardinality :db.cardinality/one :db/unique :db.unique/identity})
   [{:db/ident :assignment/notes :db/valueType :db.type/string
     :db/cardinality :db.cardinality/one}
    {:db/ident :doc/status :db/valueType :db.type/keyword
     :db/cardinality :db.cardinality/one}]))

(def world
  [{:db/id "ada" :user/name "ada"}    ; Acme's org admin
   {:db/id "mia" :user/name "mia"}    ; Acme org member, no site
   {:db/id "uma" :user/name "uma"}    ; Site One member
   {:db/id "vic" :user/name "vic"}    ; Site One member, uma's peer
   {:db/id "mark" :user/name "mark"}  ; manages Site One
   {:db/id "bob" :user/name "bob"}    ; Zeta's org admin
   {:db/id "yara" :user/name "yara"}  ; Zeta site member

   {:db/id "acme" :organisation/name "Acme"
    :organisation/admins ["ada"] :organisation/members ["mia"]}
   {:db/id "site1" :site/name "Site One" :site/organisation "acme"
    :site/members ["uma" "vic"]}
   {:manager/user "mark" :manager/site "site1"}

   {:db/id "zeta" :organisation/name "Zeta" :organisation/admins ["bob"]}
   {:db/id "site-z" :site/name "Site Zed" :site/organisation "zeta"
    :site/members ["yara"]}

   {:assignment/id "asg-uma" :assignment/member "uma"
    :assignment/organisation "acme" :assignment/notes "started"}

   {:doc/title "Launch plan" :doc/organisation "acme" :doc/owner "uma"
    :doc/viewers ["vic" "mia"] :doc/banned ["mia"] :doc/status :published}
   {:doc/title "Rough draft" :doc/organisation "acme" :doc/owner "uma"
    :doc/viewers ["vic"] :doc/status :draft}

   {:db/id "root" :folder/name "Root" :folder/organisation "acme"}
   {:db/id "sub" :folder/name "Reports" :folder/parent "root"}
   {:db/id "subsub" :folder/name "2026" :folder/parent "sub"}])

(defonce conn
  (let [uri (str "datomic:mem://authz-tutorial")]
    (d/create-database uri)
    (let [c (d/connect uri)]
      @(d/transact c (vec datomic-schema))
      @(d/transact c world)
      c)))

(def db (d/db conn))

;; --------------------------------------------------------------------------
;; Lookup helpers the tutorial pages use

(defn user [n] (d/entid db [:user/name n]))
(def users ["ada" "mia" "uma" "vic" "mark" "bob" "yara"])

(def ada (user "ada"))   (def mia (user "mia"))   (def uma (user "uma"))
(def vic (user "vic"))   (def mark (user "mark")) (def bob (user "bob"))
(def yara (user "yara"))

(def acme (d/entid db [:organisation/name "Acme"]))
(def zeta (d/entid db [:organisation/name "Zeta"]))
(def site-one (d/entid db [:site/name "Site One"]))
(def asg-uma (d/entid db [:assignment/id "asg-uma"]))
(def launch-plan (d/entid db [:doc/title "Launch plan"]))
(def rough-draft (d/entid db [:doc/title "Rough draft"]))
(def folder-2026 (d/entid db [:folder/name "2026"]))

(defn who
  "The names of every user holding `perm` over `eid` — the tutorial's
  favourite way to show a permission's whole truth at a glance."
  ([perm type eid] (who db perm type eid))
  ([db perm type eid]
   (into (sorted-set)
         (filter (fn [n] (authz/can? schema db :user (user n) perm type eid)))
         users)))

;; what this page evaluates to:
{:users (count users)
 :organisations 2
 :types (into (sorted-set) (keys registry))
 :recursive-permissions (:recursive schema)}
