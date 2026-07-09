(ns authz.docs-gen
  "The JVM half of the tutorial's no-drift guarantee.

  authz runs on the JVM against Datomic, so tutorial examples cannot
  execute in the browser the way a UI library's can. The equivalent
  property is preserved by evaluating every snippet file here — against a
  real in-memory Datomic — and capturing what it returned. The site then
  inlines the SAME file for display (shadow.resource/inline) and shows the
  captured value in the result panel: the code you read is the code that
  produced the result next to it.

  A snippet that throws fails this step, and the docs cannot build —
  broken samples cannot ship. Run via `mise run docs:gen`."
  (:require [clojure.java.io :as io]
            [clojure.pprint :as pp]))

(def snippets
  "Evaluation order == pedagogical order; world.clj first, everything else
  requires it."
  ["tutorial/world.clj"
   "tutorial/terminals.clj"
   "tutorial/chains.clj"
   "tutorial/disjunction.clj"
   "tutorial/conditions.clj"
   "tutorial/recursion.clj"
   "tutorial/point_checks.clj"
   "tutorial/list_queries.clj"
   "tutorial/watch_set.clj"
   "tutorial/sync_down.clj"
   "tutorial/sync_up.clj"
   "tutorial/creation.clj"
   "tutorial/fail_loud.clj"])

(defn run [_]
  (let [results (into {}
                      (map (fn [path]
                             (println "  eval" path)
                             (let [value (load-file (str "snippets/" path))]
                               [path (with-out-str (pp/pprint value))])))
                      snippets)]
    (io/make-parents "resources/gen/results.edn")
    (spit "resources/gen/results.edn" (pr-str results))
    (println "wrote" (count results) "snippet results to resources/gen/results.edn")))
