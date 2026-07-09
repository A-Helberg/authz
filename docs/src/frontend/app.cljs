(ns frontend.app
  (:require [solidclj.docs :as docs]
            [frontend.pages :as pages]))

(defn app []
  [docs/app {:title    "authz"
             :subtitle "tutorial"
             :sections pages/sections}])
