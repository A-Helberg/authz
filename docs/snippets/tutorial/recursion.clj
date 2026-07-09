(ns tutorial.recursion
  "Recursive permissions — folder trees that inherit from their parent."
  (:require [authz.core :as authz]
            [datomic.api :as d]
            [tutorial.world :refer [schema db registry who
                                    folder-2026 ada]]))

;; :folder/:view references ITSELF through (-> :folder/parent :view).
;; The compiler allows the cycle because it can bottom out — the other
;; or-branch grounds at an organisation. (A cycle with no way out is
;; rejected at compile time; so is recursion through (not ...).)

;; "2026" sits three levels deep: 2026 -> Reports -> Root -> Acme.
;; Nothing is granted ON the folder — everything inherits down:

(def deep-visibility
  {:the-rule (get-in registry [:folder :permissions :view])
   :who-sees-2026 (who :view :folder folder-2026)})

;; Even hostile data terminates: two folders as each other's parent.
(def cyclic
  (let [{db :db-after} (d/with db [{:db/id "a" :folder/name "A" :folder/parent "b"}
                                   {:db/id "b" :folder/name "B" :folder/parent "a"}])
        folder-a (d/entid db [:folder/name "A"])]
    {:ada-sees-the-cycle? (authz/can? schema db :user ada :view :folder folder-a)}))

(assoc deep-visibility :ungrounded-cycle cyclic)
