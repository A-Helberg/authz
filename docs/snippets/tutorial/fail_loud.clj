(ns tutorial.fail-loud
  "Schema hygiene — every mistake dies at compile time, with data."
  (:require [authz.schema :as authz.schema]))

;; compile-schema validates everything up front: you cannot deploy a
;; registry that references missing permissions, grants nobody anything,
;; or recurses without a way to bottom out.

(defn error-of [registry]
  (try
    (authz.schema/compile-schema registry)
    :compiled-fine
    (catch clojure.lang.ExceptionInfo e
      (select-keys (ex-data e) [:type :permission :targets :scc :form]))))

{:chain-to-missing-permission
 (error-of {:user {}
            :task {:relations   {:task/assignee :user}
                   :permissions {:view '(-> :task/assignee :nope)}}})

 :ungrounded-condition
 (error-of {:user {}
            :task {:relations   {:task/assignee :user}
                   :permissions {:view '(attr= :task/status :open)}}})

 :recursion-with-no-base-case
 (error-of {:user {}
            :folder {:relations   {:folder/parent :folder
                                   :folder/owner  :user}
                     :permissions {:view '(-> :folder/parent :view)}}})

 :terminals-of-two-subject-types
 (error-of {:user {} :team {}
            :task {:relations   {:task/assignee :user
                                 :task/team     :team}
                   :permissions {:view '(or :task/assignee :task/team)}}})}
