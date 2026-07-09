(ns frontend.result
  "The right-hand panel of every example: the value the snippet actually
  returned when `mise run docs:gen` evaluated it against in-memory Datomic.
  Both the displayed source (shadow.resource/inline) and this result come
  from the same file, so they cannot drift apart."
  (:require [cljs.reader :as reader]
            [shadow.resource :as rc]))

(def ^:private results
  (reader/read-string (rc/inline "gen/results.edn")))

(defn captured?
  "Test hook: is there a captured result for this snippet path?"
  [path]
  (contains? results path))

(defn view
  "Component factory for a snippet's captured evaluation result."
  [path]
  (fn []
    [:pre {:class "m-0 text-xs leading-relaxed overflow-x-auto whitespace-pre-wrap text-gray-800"}
     (get results path (str "⚠ no captured result for " path
                            " — run `mise run docs:gen`"))]))
