(ns tutorial.conditions
  "(and ...), (not ...) and (attr= ...) — conditions and exclusions."
  (:require [datomic.api :as d]
            [tutorial.world :refer [registry who db
                                    launch-plan rough-draft]]))

;; Viewers see a doc only while it is published AND they are not banned
;; from it. Conditions and exclusions grant nothing alone — the compiler
;; rejects an (or ...) branch that never references the subject — so they
;; ride along in an (and ...) with a granting check.

(def the-rule (get-in registry [:doc :permissions :view]))

;; "Launch plan" is :published; vic is a viewer, mia is a banned viewer.
;; "Rough draft" is :draft; its viewers see nothing yet.
(def before
  {:launch-plan (who :view :doc launch-plan)
   :rough-draft (who :view :doc rough-draft)})

;; Publish the draft — speculatively, with d/with. Authorization reads any
;; db value, so "what would visibility be IF..." is one expression:
(def if-published
  (:db-after (d/with db [[:db/add rough-draft :doc/status :published]])))

{:the-rule the-rule
 :before   before
 :after-publishing {:rough-draft (who if-published :view :doc rough-draft)}}
