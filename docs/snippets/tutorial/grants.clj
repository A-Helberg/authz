(ns tutorial.grants
  "grants — lazily enumerate everything a subject can reach, page by page."
  (:require [authz.core :as authz]
            [datomic.api :as d]
            [tutorial.world :refer [schema db user]]))

;; can? answers one (subject, object) pair; list-query lets the database
;; filter a query — but Datalog materializes its full result set. grants
;; is the third primitive: a lazy, deduplicated stream of authorized
;; object eids, produced by walking the permission graph outward from the
;; subject over Datomic's indexes. Nothing is computed ahead of what you
;; consume — even for recursive permissions like the folder tree.

(defn- folder-name [eid] (:folder/name (d/entity db eid)))
(defn- doc-title [eid] (:doc/title (d/entity db eid)))

;; It composes like any seq — ada's whole recursive folder tree, enumerated:
(def adas-folders
  (mapv folder-name (authz/grants schema db :user (user "ada") :view :folder)))

;; Permissions with and / not / attr= verify every candidate before it is
;; emitted: vic only sees the published doc, and mia — a viewer, but
;; banned — sees nothing at all.
(def doc-views
  (into {}
        (map (fn [n] [n (mapv doc-title
                              (authz/grants schema db :user (user n) :view :doc))]))
        ["uma" "vic" "mia" "bob"]))

;; grants-page wraps the stream for UIs: one page of results plus a
;; plain-data cursor. Pass the cursor back as :after for the next page —
;; against the same db basis; a mismatched basis, subject or permission
;; fails loudly instead of returning a silently wrong page. A nil cursor
;; means the enumeration is complete.
(def pages-of-two
  (loop [pages [] after nil]
    (let [{:keys [data cursor]}
          (authz/grants-page schema db :user (user "ada") :view :folder
                             {:limit 2 :after after})]
      (if cursor
        (recur (conj pages (mapv folder-name data)) cursor)
        (conj pages (mapv folder-name data))))))

{:adas-folders adas-folders
 :doc-views    doc-views
 :pages-of-two pages-of-two}
