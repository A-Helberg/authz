(ns authz.schema-test
  "Schema hygiene (fail-loud) and compilation-shape tests. The compiled
  Datalog is asserted structurally here; behavioural semantics run against a
  real Datomic db in authz.core-test."
  (:require [authz.fixture :as fx]
            [authz.schema :as schema]
            [clojure.test :refer [deftest is testing]]))

(defn- schema-error
  "Compiles and returns the ex-data of the schema error, or nil if it
  compiled cleanly. Rethrows anything that is not a schema error."
  [registry]
  (try
    (schema/compile-schema registry)
    nil
    (catch clojure.lang.ExceptionInfo e
      (when-not (:authz/schema-error (ex-data e)) (throw e))
      (assoc (ex-data e) ::message (ex-message e)))))

;; ---------------------------------------------------------------------------
;; Compilation shape

(def mini
  {:user       {:relations   {:user/boss :user}
                :permissions {:view :user/boss}}
   :submission {:relations   {:submission/submitted-by :user}
                :permissions {:self   :submission/submitted-by
                              :viewer '(-> :submission/submitted-by :view)}}
   :org        {:relations   {:grant/_org :user}
                :permissions {:granted :grant/_org}}})

(def mini-compiled (schema/compile-schema mini))

(deftest terminal-compiles-to-subject-unification
  (is (= '[[?submission :submission/submitted-by ?user]]
         (:clauses (get-in mini-compiled [:compiled [:submission :self]])))))

(deftest chain-first-hop-binds-fresh-variable
  ;; "someone who may view the submitter", NOT "is the submitter": the first
  ;; hop must bind a fresh var even though the relation targets the subject's
  ;; type. Getting this wrong silently collapses the two.
  (is (= '[[?submission :submission/submitted-by ?user-1]
           [?user-1 :user/boss ?user]]
         (:clauses (get-in mini-compiled [:compiled [:submission :viewer]])))))

(deftest reverse-relation-inverts-the-pattern
  (is (= '[[?user :grant/org ?org]]
         (:clauses (get-in mini-compiled [:compiled [:org :granted]])))))

(deftest same-type-subject-gets-a-distinct-variable
  (let [{:keys [object-var subject-var collision? clauses]}
        (get-in mini-compiled [:compiled [:user :view]])]
    (is (true? collision?))
    (is (= '?user object-var))
    (is (= '?user-subject subject-var))
    (is (= '[[?user :user/boss ?user-subject]] clauses))))

(deftest or-compiles-to-or-join-over-object-and-subject
  (let [compiled (schema/compile-schema
                  {:user {}
                   :sys  {:relations   {:sys/admins :user}
                          :permissions {:super :sys/admins}}
                   :org  {:relations   {:org/admins :user
                                        :org/sys    :sys}
                          :permissions {:edit '(or :org/admins
                                                   (-> :org/sys :super))}}})]
    (is (= '[(or-join [?org ?user]
                      [?org :org/admins ?user]
                      (and [?org :org/sys ?sys-1]
                           [?sys-1 :sys/admins ?user]))]
           (:clauses (get-in compiled [:compiled [:org :edit]]))))))

(deftest single-branch-or-collapses
  (let [compiled (schema/compile-schema
                  {:user {}
                   :t    {:relations   {:t/u :user}
                          :permissions {:p '(or :t/u)}}})]
    (is (= '[[?t :t/u ?user]]
           (:clauses (get-in compiled [:compiled [:t :p]]))))))

(deftest keyword-and-vector-check-forms-are-accepted
  (let [compiled (schema/compile-schema
                  {:user {}
                   :b    {:relations   {:b/u :user}
                          :permissions {:q [:or :b/u]}}
                   :a    {:relations   {:a/b :b}
                          :permissions {:p [:-> :a/b :q]}}})]
    (is (= '[[?a :a/b ?b-1] [?b-1 :b/u ?user]]
           (:clauses (get-in compiled [:compiled [:a :p]]))))))

(deftest and-not-attr=-compile
  (let [compiled (schema/compile-schema
                  {:user {}
                   :doc  {:relations   {:doc/viewers :user
                                        :doc/banned  :user}
                          :permissions {:view '(and :doc/viewers
                                                    (attr= :doc/status :published)
                                                    (not :doc/banned))}}})]
    (is (= '[[?doc :doc/viewers ?user]
             [?doc :doc/status :published]
             (not-join [?doc ?user] [?doc :doc/banned ?user])]
           (:clauses (get-in compiled [:compiled [:doc :view]]))))))

(deftest not-join-binds-only-the-vars-the-exclusion-uses
  (let [compiled (schema/compile-schema
                  {:user {}
                   :doc  {:relations   {:doc/viewers :user}
                          :permissions {:view '(and :doc/viewers
                                                    (not (attr= :doc/status :archived)))}}})]
    (is (= '[[?doc :doc/viewers ?user]
             (not-join [?doc] [?doc :doc/status :archived])]
           (:clauses (get-in compiled [:compiled [:doc :view]]))))))

(deftest branches-are-cost-ordered-with-sources
  (let [{:keys [branches]} (get-in fx/compiled [:compiled [:site :view]])]
    (is (= 3 (count branches)))
    (is (= :site/members (:source (first branches)))
        "the direct terminal is the cheapest branch")
    (is (apply <= (map :cost branches)))
    (is (every? :clauses branches)))
  (let [{:keys [branches clauses]} (get-in fx/compiled [:compiled [:assignment :react]])]
    (is (= 1 (count branches)) "non-or permissions have a single branch")
    (is (= clauses (:clauses (first branches))))))

(deftest rejects-ungrounded-checks
  (testing "a pure condition grants nothing and is rejected"
    (is (schema-error {:user {}
                       :a    {:relations   {:a/u :user}
                              :permissions {:p '(attr= :a/status :on)}}})))
  (testing "a pure exclusion is rejected"
    (is (schema-error {:user {}
                       :a    {:relations   {:a/u :user}
                              :permissions {:p '(not :a/u)}}})))
  (testing "an or branch that never references the subject is rejected"
    (is (schema-error {:user {}
                       :a    {:relations   {:a/u :user}
                              :permissions {:p '(or :a/u (attr= :a/status :on))}}})))
  (testing "grounding through (and ...) is fine"
    (is (schema/compiled?
         (schema/compile-schema
          {:user {}
           :a    {:relations   {:a/u :user}
                  :permissions {:p '(or :a/u
                                        (and :a/u (attr= :a/status :on)))}}})))))

(deftest attribute-extraction-is-transitive-and-forward-normalized
  (is (= #{:submission/submitted-by :user/boss}
         (:attrs (get-in mini-compiled [:compiled [:submission :viewer]]))))
  (is (= #{:grant/org}
         (:attrs (get-in mini-compiled [:compiled [:org :granted]])))))

(deftest subject-type-is-inferred-from-terminals
  (is (= :user (:subject-type (get-in mini-compiled [:compiled [:submission :viewer]]))))
  (is (= :user (:subject-type (get-in fx/compiled [:compiled [:site :view]]))))
  (is (= :user (:subject-type (get-in fx/compiled [:compiled [:system :superadmin]])))))

(deftest fixture-compiles-deterministically
  (is (schema/compiled? fx/compiled))
  (is (= fx/compiled (schema/compile-schema fx/registry))
      "compilation is a pure function of the registry"))

(deftest settable-at-create-combines-writable-create-relations-and-overrides
  (let [types (:types fx/compiled)]
    (is (= #{:submission/content :submission/submitted-by
             :submission/id :submission/organisation}
           (get-in types [:submission :settable-at-create])))
    (is (= #{:resource/title :resource/organisation}
           (get-in types [:resource :settable-at-create])))
    (is (= #{:submission/content} (get-in types [:submission :writable])))
    (is (= #{:submission/id :submission/content :submission/submitted-by
             :submission/organisation}
           (get-in types [:submission :readable])))))

;; ---------------------------------------------------------------------------
;; Fail-loud hygiene

(deftest rejects-relation-to-unknown-type
  (is (= :ghost (:target (schema-error
                          {:a {:relations {:a/x :ghost} :permissions {}}})))))

(deftest rejects-terminal-with-unknown-relation
  (let [err (schema-error {:user {}
                           :a    {:relations   {:a/u :user}
                                  :permissions {:p :a/nope}}})]
    (is (= :a/nope (:relation err)))))

(deftest rejects-chain-with-unknown-relation
  (is (schema-error {:user {}
                     :a    {:relations   {:a/u :user}
                            :permissions {:p '(-> :a/nope :view)}}})))

(deftest rejects-chain-to-unknown-permission-on-target
  (let [err (schema-error {:user {:permissions {:view :user/self}}
                           :a    {:relations   {:a/u :user}
                                  :permissions {:p '(-> :a/u :nope)}}})]
    ;; note: :user :view is itself broken here, but the chain check must
    ;; fire regardless — accept either failure
    (is err))
  (let [err (schema-error {:user {:relations   {:user/boss :user}
                                  :permissions {:view :user/boss}}
                           :a    {:relations   {:a/u :user}
                                  :permissions {:p '(-> :a/u :nope)}}})]
    (is (= :nope (:permission err)))))

(deftest rejects-empty-permission-body
  (let [err (schema-error {:a {:permissions {:p nil}}})]
    (is (re-find #"quote" (::message err)))))

(deftest rejects-unsupported-check-forms
  (is (schema-error {:user {}
                     :a    {:relations   {:a/u :user}
                            :permissions {:p '(xor :a/u :a/u)}}}))
  (is (schema-error {:user {}
                     :a    {:relations   {:a/u :user}
                            :permissions {:p '(-> :a/u)}}}))
  (is (schema-error {:user {}
                     :a    {:relations   {:a/u :user}
                            :permissions {:p '(not :a/u :a/u)}}}))
  (is (schema-error {:user {}
                     :a    {:relations   {:a/u :user}
                            :permissions {:p '(attr= :a/status)}}}))
  (is (schema-error {:user {}
                     :a    {:relations   {:a/u :user}
                            :permissions {:p '(attr= :a/status [:a :b])}}})
      "attr= value must be a literal")
  (is (schema-error {:a {:permissions {:p "view"}}})))

(deftest rejects-unknown-definition-keys
  (is (schema-error {:a {:permission {:p :a/u}}})))

(deftest rejects-recursion-that-cannot-bottom-out
  (testing "a mutual cycle with no base case anywhere"
    (let [err (schema-error {:a {:relations   {:a/b :b}
                                 :permissions {:p '(-> :a/b :q)}}
                             :b {:relations   {:b/a :a}
                                 :permissions {:q '(-> :b/a :p)}}})]
      (is (set? (:scc err)))))
  (testing "self-recursion with no base case"
    (is (schema-error {:user {}
                       :f    {:relations   {:f/parent :f :f/owner :user}
                              :permissions {:p '(-> :f/parent :p)}}})))
  (testing "(and base recursive-chain) still never bottoms out"
    (is (schema-error {:user {}
                       :f    {:relations   {:f/parent :f :f/owner :user}
                              :permissions {:p '(and :f/owner (-> :f/parent :p))}}}))))

(deftest recursion-with-a-base-case-compiles-to-rules
  (let [c (schema/compile-schema
           {:user {}
            :f    {:relations   {:f/parent :f :f/owner :user}
                   :permissions {:p '(or :f/owner (-> :f/parent :p))}}})]
    (is (schema/compiled? c))
    (is (= '[(authz-f--p ?f ?user)]
           (get-in c [:compiled [:f :p] :clauses]))
        "a recursive permission's clauses are one invocation of its rule")
    (is (= '[[(authz-f--p ?f ?user) [?f :f/owner ?user]]
             [(authz-f--p ?f ?user) [?f :f/parent ?f-1] (authz-f--p ?f-1 ?user)]]
           (get-in c [:compiled [:f :p] :rules]))
        "one rule definition per or-branch; the recursive branch re-invokes")
    (is (true? (get-in c [:compiled [:f :p] :recursive?])))
    (is (= #{:f/owner :f/parent} (get-in c [:compiled [:f :p] :attrs]))
        "attribute extraction reaches through the cycle exactly once")))

(deftest mutual-recursion-sharing-a-base-case-compiles
  ;; q has no base case of its own, but bottoms out through p's — the
  ;; fixpoint validation accepts this
  (let [c (schema/compile-schema
           {:user {}
            :a    {:relations   {:a/b :b :a/owner :user}
                   :permissions {:p '(or :a/owner (-> :a/b :q))}}
            :b    {:relations   {:b/a :a}
                   :permissions {:q '(-> :b/a :p)}}})]
    (is (schema/compiled? c))
    (is (= 3 (count (get-in c [:compiled [:b :q] :rules])))
        "q's rule set carries every definition of its cycle: p's two branches + q's one")))

(deftest rejects-recursion-through-negation
  (is (schema-error {:user {}
                     :f    {:relations   {:f/parent :f :f/owner :user}
                            :permissions {:p '(or :f/owner
                                                  (and :f/owner
                                                       (not (-> :f/parent :p))))}}})))

(deftest non-recursive-perm-chaining-into-recursion-carries-the-rules
  (let [c (schema/compile-schema
           {:user {}
            :f    {:relations   {:f/parent :f :f/owner :user}
                   :permissions {:p '(or :f/owner (-> :f/parent :p))}}
            :doc  {:relations   {:doc/folder :f}
                   :permissions {:view '(-> :doc/folder :p)}}})]
    (is (false? (get-in c [:compiled [:doc :view] :recursive?])))
    (is (= '[[?doc :doc/folder ?f-1] (authz-f--p ?f-1 ?user)]
           (get-in c [:compiled [:doc :view] :clauses]))
        "the chain stops inlining at the cycle boundary and invokes the rule")
    (is (seq (get-in c [:compiled [:doc :view] :rules])))))

(deftest rejects-terminals-unifying-multiple-subject-types
  (let [err (schema-error {:user {}
                           :team {}
                           :doc  {:relations   {:doc/owner :user
                                                :doc/team  :team}
                                  :permissions {:p '(or :doc/owner :doc/team)}}})]
    (is (= #{:user :team} (:targets err)))))

(deftest rejects-attr-spec-problems
  (testing "unknown permission"
    (is (schema-error {:user {}
                       :a    {:relations   {:a/u :user}
                              :permissions {:view :a/u}
                              :attrs       {:a/name {:read :nope}}}})))
  (testing "unknown spec keys"
    (is (schema-error {:user {}
                       :a    {:relations   {:a/u :user}
                              :permissions {:view :a/u}
                              :attrs       {:a/name {:red :view}}}})))
  (testing "attr claimed by two types"
    (let [err (schema-error {:user {}
                             :a    {:relations   {:a/u :user}
                                    :permissions {:view :a/u}
                                    :attrs       {:shared/name {:read :view}}}
                             :b    {:relations   {:b/u :user}
                                    :permissions {:view :b/u}
                                    :attrs       {:shared/name {:read :view}}}})]
      (is (= :shared/name (:attr err))))))

(deftest rejects-create-rule-problems
  (testing "reverse relation in create rule"
    (is (schema-error {:user {}
                       :a    {:relations   {:x/_a :user}
                              :permissions {:view :x/_a}
                              :create      :x/_a
                              :attrs       {:x/a {:read :view}}}})))
  (testing "create relation not declared in :attrs"
    (is (schema-error {:user {}
                       :a    {:relations   {:a/owner :user}
                              :permissions {:view :a/owner}
                              :create      :a/owner}})))
  (testing "(not ...) is not supported in create rules"
    (is (schema-error {:user {}
                       :a    {:relations   {:a/owner :user}
                              :permissions {:view :a/owner}
                              :create      '(and :a/owner (not :a/owner))
                              :attrs       {:a/owner {:read :view}}}}))))

(deftest attr=-attributes-join-the-watch-set
  ;; a status flip must invalidate reactive subscriptions
  (is (contains? (:attrs (get-in fx/compiled [:compiled [:doc :view]]))
                 :doc/status))
  (is (contains? (:attrs (get-in fx/compiled [:compiled [:doc :view]]))
                 :doc/banned)))

(deftest rejects-unknown-delete-permission
  (let [err (schema-error {:user {}
                           :a    {:relations   {:a/u :user}
                                  :permissions {:view :a/u}
                                  :delete      :nope}})]
    (is (= :nope (:delete err)))))
