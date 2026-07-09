(ns tutorial.list-queries
  "list-query — the database filters your list endpoints for you."
  (:require [authz.core :as authz]
            [datomic.api :as d]
            [tutorial.world :refer [schema db user]]))

;; list-query returns :where clauses binding ?<object-type> and ?user.
;; Concat them with your own filters into ONE query — rows the subject
;; may not see are never returned, on the same consistent snapshot.

(defn visible-sites [viewer-name]
  (into (sorted-set)
        (map first)
        (d/q {:find '[?name]
              :in '[$ ?user]
              :where (into (authz/list-query schema :site :view :user)
                           '[[?site :site/name ?name]])}
             db (user viewer-name))))

;; Recursive permissions need Datomic rules alongside their clauses, so
;; they use list-query* — put % in :in and pass the rules through:

(defn visible-folders [viewer-name]
  (let [{:keys [where rules]} (authz/list-query* schema :folder :view :user)]
    (into (sorted-set)
          (map first)
          (d/q {:find '[?name]
                :in '[$ % ?user]
                :where (into where '[[?folder :folder/name ?name]])}
               db rules (user viewer-name)))))

{:sites   {:uma  (visible-sites "uma")     ; her own site
           :ada  (visible-sites "ada")     ; org admin: all of Acme's
           :bob  (visible-sites "bob")     ; Zeta's admin sees only Zeta's
           :yara (visible-sites "yara")}
 :folders {:mia (visible-folders "mia")    ; the whole tree, one query
           :bob (visible-folders "bob")}}
