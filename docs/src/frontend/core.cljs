(ns frontend.core
  (:require [solidclj.api :refer [render]]
            [frontend.app :as app]))

(defonce ^:private dispose* (atom nil))

(defn- mount! []
  (reset! dispose* (render [app/app] (.getElementById js/document "app"))))

(defn ^:export init []
  (mount!))

(defn ^:dev/after-load reload []
  (when-let [dispose @dispose*] (dispose))
  (mount!))
