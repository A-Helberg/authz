(ns tutorial.disjunction
  "(or ...) — any branch grants, and explain tells you which one did."
  (:require [authz.core :as authz]
            [tutorial.world :refer [schema db registry who
                                    site-one uma mark ada yara]]))

;; :site/:view ors three ways in: be a member, manage the site, or be
;; able to edit the whole organisation. Branches stay independent — and
;; point checks try them cheapest-first, so "is a member" answers without
;; ever walking the org hierarchy.

{:the-rule (get-in registry [:site :permissions :view])

 :who-sees-site-one (who :view :site site-one)

 ;; explain reports the branch that granted (the cheapest one that hit):
 :uma  (authz/explain schema db :user uma :view :site site-one)
 :mark (authz/explain schema db :user mark :view :site site-one)
 :ada  (authz/explain schema db :user ada :view :site site-one)

 ;; on denial you get every branch that was tried and refused:
 :yara (authz/explain schema db :user yara :view :site site-one)}
