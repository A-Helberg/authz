(ns authz.schema
  "Validation and compilation of an authz registry into an immutable,
  pre-compiled schema value.

  A registry is a plain map of entity type -> definition:

    {:organisation
     {:relations   {:organisation/admins   :user
                    :manager/_organisation :manager}
      :permissions {:view '(or :organisation/admins
                               (-> :organisation/system :superadmin))
                    :edit :organisation/admins}
      :attrs       {:organisation/name {:read :view :write :edit}}
      :create      '(-> :organisation/system :superadmin)
      :delete      :edit}}

  The permission check language:

    :some/relation          terminal — the subject IS the entity reached by
                            this relation (subject and relation target unify)
    (-> <rel> <perm>)       chain — follow the relation, then require <perm>
                            on the target. The first hop binds a FRESH
                            variable and never unifies with the subject.
    (or <check> ...)        disjunction — any branch grants.
    (and <check> ...)       conjunction — all must hold.
    (not <check>)           exclusion — the subject must NOT satisfy the
                            check (compiles to not-join).
    (attr= <attr> <value>)  condition — the object has <attr> = literal
                            <value> (e.g. status = published). Grants
                            nothing by itself; combine under (and ...).

  Groundedness: every permission, every (or ...) branch, and every create
  rule must reference the subject through at least one terminal or chain
  not under a (not ...). This is what keeps or-join/not-join variable
  binding well-formed, and what stops a pure condition or pure exclusion
  from accidentally granting everyone.

  ## Recursion

  Permissions may reference themselves (directly or mutually) through
  chains — e.g. a folder is visible if its parent folder is:

    :folder {:relations   {:folder/parent :folder
                           :folder/organisation :organisation}
             :permissions {:view '(or (-> :folder/organisation :view)
                                      (-> :folder/parent :view))}}

  Recursive permissions compile to named Datomic rules instead of inline
  clauses, so their list queries need the rule set passed as the % input —
  use authz.core/list-query* for those (authz.core/list-query fails loudly).
  Two things are validated at compile time:

  - every recursive permission must be able to bottom out — some evaluation
    path must leave its cycle (computed as a fixpoint over the strongly
    connected component, so mutual recursion with one shared base case is
    fine, but a permission that can only ever re-enter its cycle is not);
  - recursion through (not ...) is rejected (non-stratified Datalog).

  Relations name Datomic attributes; a leading underscore on the attribute
  name (:manager/_organisation) traverses the attribute in reverse.

  `compile-schema` fail-louds on every schema hygiene problem (unknown
  references, malformed bodies, degenerate recursion, ambiguous subject
  types, ungrounded checks, attributes claimed by two types) and returns an
  immutable value with every permission pre-compiled — Datalog clauses,
  named rules where recursion demands them, cost-ordered branches for
  short-circuiting point checks, and the transitive attribute set."
  (:require [clojure.string :as str]
            [clojure.walk :as walk]))

;; ---------------------------------------------------------------------------
;; Errors

(defn- fail
  [msg data]
  (throw (ex-info (str "authz schema error: " msg)
                  (assoc data :authz/schema-error true))))

;; ---------------------------------------------------------------------------
;; Relations

(defn reverse-relation?
  "True when the relation traverses its Datomic attribute in reverse
  (underscore convention, e.g. :manager/_organisation)."
  [rel]
  (str/starts-with? (name rel) "_"))

(defn underlying-attr
  "The forward Datomic attribute a relation traverses (strips the underscore)."
  [rel]
  (if (reverse-relation? rel)
    (keyword (namespace rel) (subs (name rel) 1))
    rel))

(defn rel-clause
  "Datalog data pattern traversing relation `rel` from `from-var` to `to-var`."
  [rel from-var to-var]
  (if (reverse-relation? rel)
    [to-var (underlying-attr rel) from-var]
    [from-var rel to-var]))

;; ---------------------------------------------------------------------------
;; Check-expression normalization

(def ^:private chain-ops #{'-> :->})
(def ^:private or-ops #{'or :or})
(def ^:private and-ops #{'and :and})
(def ^:private not-ops #{'not :not})
(def ^:private attr=-ops #{'attr= :attr=})

(defn- normalize-check
  "Parses a check expression into {:op :relation|:chain|:or|:and|:not|:attr=}
  nodes, keeping the source form for explain output. Single-branch (or x)
  and (and x) collapse to x."
  [form ctx]
  (cond
    (keyword? form)
    {:op :relation :relation form :source form}

    (and (sequential? form) (contains? chain-ops (first form)))
    (let [[_ rel perm] form]
      (when-not (and (= 3 (count form)) (keyword? rel) (keyword? perm))
        (fail "chain must be (-> <relation> <permission>)" (assoc ctx :form form)))
      {:op :chain :relation rel :permission perm :source form})

    (and (sequential? form) (contains? attr=-ops (first form)))
    (let [[_ attr value] form]
      (when-not (and (= 3 (count form)) (keyword? attr) (namespace attr))
        (fail "condition must be (attr= <namespaced-attr> <value>)"
              (assoc ctx :form form)))
      (when (or (nil? value) (coll? value))
        (fail "attr= value must be a literal" (assoc ctx :form form)))
      {:op :attr= :attr attr :value value :source form})

    (and (sequential? form) (contains? not-ops (first form)))
    (do (when-not (= 2 (count form))
          (fail "exclusion must be (not <check>)" (assoc ctx :form form)))
        {:op :not :branch (normalize-check (second form) ctx) :source form})

    (and (sequential? form) (contains? or-ops (first form)))
    (let [branches (rest form)]
      (when (empty? branches)
        (fail "(or ...) needs at least one branch" (assoc ctx :form form)))
      (if (= 1 (count branches))
        (normalize-check (first branches) ctx)
        {:op :or :branches (mapv #(normalize-check % ctx) branches) :source form}))

    (and (sequential? form) (contains? and-ops (first form)))
    (let [branches (rest form)]
      (when (empty? branches)
        (fail "(and ...) needs at least one branch" (assoc ctx :form form)))
      (if (= 1 (count branches))
        (normalize-check (first branches) ctx)
        {:op :and :branches (mapv #(normalize-check % ctx) branches) :source form}))

    (nil? form)
    (fail "empty permission body (did you forget to quote it?)" ctx)

    :else
    (fail "unsupported check form; expected a relation keyword, (-> rel perm), (or ...), (and ...), (not ...) or (attr= attr value)"
          (assoc ctx :form form))))

;; ---------------------------------------------------------------------------
;; Structural validation

(def ^:private def-keys #{:relations :permissions :attrs :create :delete})
(def ^:private attr-spec-keys #{:read :write :create?})

(defn- validate-structure!
  [registry]
  (when-not (map? registry)
    (fail "registry must be a map of type -> definition" {:registry registry}))
  (doseq [[type definition] registry]
    (let [ctx {:type type}]
      (when-not (keyword? type)
        (fail "entity type must be a keyword" ctx))
      (when-not (map? definition)
        (fail "definition must be a map" ctx))
      (when-let [unknown (seq (remove def-keys (keys definition)))]
        (fail "unknown definition keys" (assoc ctx :keys (vec unknown) :allowed def-keys)))
      (doseq [[rel target] (:relations definition)]
        (when-not (and (keyword? rel) (namespace rel))
          (fail "relation must be a namespaced keyword" (assoc ctx :relation rel)))
        (when-not (contains? registry target)
          (fail "relation targets unknown type" (assoc ctx :relation rel :target target))))
      (doseq [[perm _] (:permissions definition)]
        (when-not (keyword? perm)
          (fail "permission name must be a keyword" (assoc ctx :permission perm)))))))

;; ---------------------------------------------------------------------------
;; Reference checks

(defn- check-refs!
  "Every relation a node mentions must exist on its type; every chained
  permission must exist on the relation's target type."
  [defs type node ctx]
  (case (:op node)
    :relation
    (when-not (contains? (get-in defs [type :relations]) (:relation node))
      (fail "terminal references unknown relation"
            (assoc ctx :relation (:relation node)
                   :known (set (keys (get-in defs [type :relations]))))))

    :chain
    (let [rel (:relation node)
          target (get-in defs [type :relations rel])]
      (when-not target
        (fail "chain references unknown relation"
              (assoc ctx :relation rel
                     :known (set (keys (get-in defs [type :relations]))))))
      (when-not (contains? (get-in defs [target :permissions]) (:permission node))
        (fail "chain references unknown permission on target type"
              (assoc ctx :relation rel :target-type target
                     :permission (:permission node)
                     :known (set (keys (get-in defs [target :permissions])))))))

    :attr=
    nil ; conditions reference plain Datomic attrs, not registry relations

    :not
    (check-refs! defs type (:branch node) ctx)

    (:or :and)
    (run! #(check-refs! defs type % ctx) (:branches node))))

;; ---------------------------------------------------------------------------
;; Groundedness

(defn- grounded?
  "A node is grounded when it reaches the subject through a terminal or
  chain not under (not ...). Fails loudly on ungrounded (or ...) branches,
  which would compile to or-join branches that don't bind the subject."
  [node ctx]
  (case (:op node)
    (:relation :chain) true
    :attr= false
    :not (do (grounded? (:branch node) ctx) false)
    :and (let [gs (mapv #(grounded? % ctx) (:branches node))]
           (boolean (some true? gs)))
    :or (do (doseq [b (:branches node)]
              (when-not (grounded? b ctx)
                (fail "every (or ...) branch must reference the subject via a relation or chain (wrap conditions/exclusions in (and ...) with a granting check)"
                      (assoc ctx :branch (:source b)))))
            true)))

(defn- validate-grounded!
  [node ctx]
  (when-not (grounded? node ctx)
    (fail "check must reference the subject via a relation or chain — a pure condition or exclusion would grant nothing (or everything)"
          (assoc ctx :form (:source node)))))

;; ---------------------------------------------------------------------------
;; The permission graph: SCCs and recursion validation

(defn- chain-edges
  "The [type perm] nodes a check body references through chains."
  [defs type node]
  (case (:op node)
    (:relation :attr=) #{}
    :chain #{[(get-in defs [type :relations (:relation node)]) (:permission node)]}
    :not (chain-edges defs type (:branch node))
    (:or :and) (transduce (map #(chain-edges defs type %)) into #{} (:branches node))))

(defn- strongly-connected-components
  "Tarjan over the permission graph. `nodes` must be in a deterministic
  order (compilation is a pure function of the registry)."
  [nodes edges]
  (let [state (atom {:index 0 :indices {} :low {} :stack [] :on #{} :sccs []})]
    (letfn [(strong! [v]
              (swap! state (fn [s] (-> s
                                       (assoc-in [:indices v] (:index s))
                                       (assoc-in [:low v] (:index s))
                                       (update :index inc)
                                       (update :stack conj v)
                                       (update :on conj v))))
              (doseq [w (sort-by str (get edges v))]
                (cond
                  (not (contains? (:indices @state) w))
                  (do (strong! w)
                      (swap! state update-in [:low v] min (get-in @state [:low w])))
                  (contains? (:on @state) w)
                  (swap! state update-in [:low v] min (get-in @state [:indices w]))))
              (when (= (get-in @state [:low v]) (get-in @state [:indices v]))
                (swap! state
                       (fn [s]
                         (loop [stack (:stack s) on (:on s) scc #{}]
                           (let [w (peek stack)
                                 stack (pop stack)
                                 on (disj on w)
                                 scc (conj scc w)]
                             (if (= w v)
                               (-> s (assoc :stack stack :on on)
                                   (update :sccs conj scc))
                               (recur stack on scc))))))))]
      (doseq [v nodes]
        (when-not (contains? (:indices @state) v)
          (strong! v)))
      (:sccs @state))))

(defn- check-stratified!
  "Recursion through negation is non-stratified Datalog: a chain under
  (not ...) may not target a permission in the same cycle."
  [defs node->scc [type perm :as k] node under-not?]
  (case (:op node)
    (:relation :attr=) nil
    :chain
    (let [target [(get-in defs [type :relations (:relation node)]) (:permission node)]]
      (when (and under-not? (= (node->scc k) (node->scc target)))
        (fail "recursion through (not ...) is not stratified"
              {:type type :permission perm :target target})))
    :not (check-stratified! defs node->scc k (:branch node) true)
    (:or :and) (run! #(check-stratified! defs node->scc k % under-not?) (:branches node))))

(defn- check-base-cases!
  "Every permission in a cyclic SCC must be able to bottom out: some
  evaluation path must leave the cycle. Computed as a least fixpoint over
  the SCC, so mutual recursion sharing one base case is fine, but a
  permission whose every path re-enters the cycle is rejected."
  [defs scc]
  (letfn [(terminates? [ok type node]
            (case (:op node)
              (:relation :attr= :not) true
              :chain (let [tk [(get-in defs [type :relations (:relation node)])
                               (:permission node)]]
                       (if (contains? scc tk) (contains? ok tk) true))
              :or (boolean (some #(terminates? ok type %) (:branches node)))
              :and (every? #(terminates? ok type %) (:branches node))))]
    (let [fixpoint (loop [ok #{}]
                     (let [ok' (into ok
                                     (filter (fn [[t p]]
                                               (terminates? ok t (get-in defs [t :permissions p]))))
                                     scc)]
                       (if (= ok ok') ok (recur ok'))))]
      (doseq [[t p] scc]
        (when-not (contains? fixpoint [t p])
          (fail "recursive permission can never bottom out — every evaluation path re-enters its own cycle; add a non-recursive (or ...) branch"
                {:type t :permission p :scc scc}))))))

(defn- reachable-nodes
  [edges start]
  (loop [seen #{start} frontier [start]]
    (if-let [[n & more] (seq frontier)]
      (let [new (remove seen (get edges n))]
        (recur (into seen new) (into (vec more) new)))
      seen)))

;; ---------------------------------------------------------------------------
;; Subject-type inference and attribute extraction (cycle-safe)

(defn- terminal-targets
  "The set of types that terminals of this check unify the subject with
  (including terminals under (not ...) — exclusion constrains the same
  subject). `visited` cuts cycles."
  [defs type node visited]
  (case (:op node)
    :relation #{(get-in defs [type :relations (:relation node)])}
    :attr= #{}
    :chain (let [target (get-in defs [type :relations (:relation node)])
                 k [target (:permission node)]]
             (if (contains? visited k)
               #{}
               (terminal-targets defs target
                                 (get-in defs [target :permissions (:permission node)])
                                 (conj visited k))))
    :not (terminal-targets defs type (:branch node) visited)
    (:or :and) (transduce (map #(terminal-targets defs type % visited))
                          into #{} (:branches node))))

(defn- node-attrs
  "The set of Datomic attributes a check touches, transitively through
  chains, ors, ands, nots and conditions — cycle-safe. Reverse relations
  are normalized to their forward attribute (that is what appears in
  datoms)."
  [defs type node visited]
  (case (:op node)
    :relation #{(underlying-attr (:relation node))}
    :attr= #{(:attr node)}
    :chain (let [rel (:relation node)
                 target (get-in defs [type :relations rel])
                 k [target (:permission node)]]
             (if (contains? visited k)
               #{(underlying-attr rel)}
               (into #{(underlying-attr rel)}
                     (node-attrs defs target
                                 (get-in defs [target :permissions (:permission node)])
                                 (conj visited k)))))
    :not (node-attrs defs type (:branch node) visited)
    (:or :and) (transduce (map #(node-attrs defs type % visited))
                          into #{} (:branches node))))

;; ---------------------------------------------------------------------------
;; Compilation to Datalog

(defn- vars-in
  [clauses]
  (let [acc (volatile! #{})]
    (walk/postwalk (fn [x]
                     (when (and (symbol? x) (str/starts-with? (name x) "?"))
                       (vswap! acc conj x))
                     x)
                   clauses)
    @acc))

(defn rule-sym
  "The deterministic Datomic rule name for a recursive [type perm]."
  [[type perm]]
  (symbol (str "authz-"
               (str/replace (subs (str type) 1) "/" "-")
               "--"
               (str/replace (subs (str perm) 1) "/" "-"))))

(defn- compile-node
  "Compiles a check node into a vector of Datalog :where clauses. Chains
  into permissions that live in a cycle emit a rule invocation instead of
  inlining (they cannot be unrolled). `counter` numbers fresh intermediate
  variables so compilation is deterministic."
  [defs rule-perms type node obj-var subj-var counter]
  (case (:op node)
    :relation
    [(rel-clause (:relation node) obj-var subj-var)]

    :attr=
    [[obj-var (:attr node) (:value node)]]

    :chain
    (let [rel (:relation node)
          target (get-in defs [type :relations rel])
          tk [target (:permission node)]
          ;; Fresh variable: the first hop of a chain must NOT unify with the
          ;; subject, even when the relation targets the subject's type.
          mid (symbol (str "?" (name target) "-" (swap! counter inc)))]
      (if (contains? rule-perms tk)
        [(rel-clause rel obj-var mid)
         (list (rule-sym tk) mid subj-var)]
        (into [(rel-clause rel obj-var mid)]
              (compile-node defs rule-perms target
                            (get-in defs [target :permissions (:permission node)])
                            mid subj-var counter))))

    :not
    (let [clauses (compile-node defs rule-perms type (:branch node) obj-var subj-var counter)
          ;; not-join only over the outer vars the exclusion actually uses —
          ;; e.g. (not (attr= ...)) never mentions the subject
          used (filterv (vars-in clauses) [obj-var subj-var])]
      [(list* 'not-join used clauses)])

    :and
    (into [] (mapcat #(compile-node defs rule-perms type % obj-var subj-var counter))
          (:branches node))

    :or
    [(list* 'or-join [obj-var subj-var]
            (map (fn [branch]
                   (let [clauses (compile-node defs rule-perms type branch obj-var subj-var counter)]
                     (if (= 1 (count clauses))
                       (first clauses)
                       (list* 'and clauses))))
                 (:branches node)))]))

(defn- pattern-count
  "Number of data patterns in compiled clauses — the static cost estimate
  used to order or-branches for short-circuiting point checks."
  [clauses]
  (let [n (volatile! 0)]
    (walk/postwalk (fn [x]
                     (when (and (vector? x) (= 3 (count x)) (keyword? (second x)))
                       (vswap! n inc))
                     x)
                   clauses)
    @n))

(defn- perm-vars
  [type subject-type]
  (let [collision? (= subject-type type)]
    {:collision? collision?
     :object-var (symbol (str "?" (name type)))
     :subject-var (if collision?
                    (symbol (str "?" (name subject-type) "-subject"))
                    (symbol (str "?" (name subject-type))))}))

(defn- compile-rule-defs
  "One Datomic rule definition per top-level or-branch of a recursive
  permission (multiple definitions with the same head = disjunction)."
  [defs rule-perms subject-types [type perm :as k]]
  (let [node (get-in defs [type :permissions perm])
        {:keys [object-var subject-var]} (perm-vars type (get subject-types k))
        head (list (rule-sym k) object-var subject-var)]
    (mapv (fn [b]
            (into [head]
                  (compile-node defs rule-perms type b object-var subject-var (atom 0))))
          (if (= :or (:op node)) (:branches node) [node]))))

;; ---------------------------------------------------------------------------
;; :create rules

(defn- validate-create!
  "Create rules are evaluated against the *transaction-local* datoms of a new
  entity, so their first hops must be forward relations (a reverse relation
  would live on some other entity) and exclusion is not supported."
  [defs type node ctx]
  (case (:op node)
    (:relation :chain)
    (when (reverse-relation? (:relation node))
      (fail "create rules may only use forward relations"
            (assoc ctx :relation (:relation node))))
    :attr=
    nil
    :not
    (fail "create rules do not support (not ...)" (assoc ctx :form (:source node)))
    (:or :and)
    (run! #(validate-create! defs type % ctx) (:branches node))))

(defn- create-rule-relations
  "Attributes the create rule reads off the new entity's tx-local datoms."
  [node]
  (case (:op node)
    (:relation :chain) #{(:relation node)}
    :attr= #{(:attr node)}
    :not #{}
    (:or :and) (transduce (map create-rule-relations) into #{} (:branches node))))

;; ---------------------------------------------------------------------------
;; :attrs sections

(defn- validate-attrs!
  [defs type attrs ctx]
  (doseq [[attr spec] attrs]
    (let [ctx (assoc ctx :attr attr)]
      (when-not (and (keyword? attr) (namespace attr))
        (fail "declared attr must be a namespaced keyword" ctx))
      (when (reverse-relation? attr)
        (fail "declared attr must be a forward Datomic attribute" ctx))
      (when-not (map? spec)
        (fail "attr spec must be a map like {:read <perm> :write <perm>}" ctx))
      (when-let [unknown (seq (remove attr-spec-keys (keys spec)))]
        (fail "unknown attr spec keys" (assoc ctx :keys (vec unknown) :allowed attr-spec-keys)))
      (doseq [k [:read :write]]
        (when-let [perm (get spec k)]
          (when-not (contains? (get-in defs [type :permissions]) perm)
            (fail "attr spec references unknown permission"
                  (assoc ctx :spec-key k :permission perm
                         :known (set (keys (get-in defs [type :permissions])))))))))))

;; ---------------------------------------------------------------------------
;; compile-schema

(defn compiled?
  [x]
  (boolean (and (map? x) (:authz/schema? x))))

(defn compile-schema
  "Validates `registry` and compiles it into an immutable schema value.
  Every permission is pre-compiled once, here — nothing is re-walked or
  rebuilt at query time. Throws ex-info (:authz/schema-error true) on any
  hygiene problem."
  [registry]
  (validate-structure! registry)
  (let [defs (reduce-kv
              (fn [defs type definition]
                (assoc defs type
                       (-> definition
                           (update :relations #(or % {}))
                           (update :permissions
                                   (fn [perms]
                                     (reduce-kv
                                      (fn [m p body]
                                        (assoc m p (normalize-check body {:type type :permission p})))
                                      {} (or perms {}))))
                           (cond-> (contains? definition :create)
                             (update :create #(normalize-check % {:type type :create true}))))))
              {} registry)]
    ;; Reference, groundedness and shape checks for permissions and creates.
    (doseq [[type d] defs]
      (doseq [[perm node] (:permissions d)]
        (check-refs! defs type node {:type type :permission perm})
        (validate-grounded! node {:type type :permission perm}))
      (when-let [create (:create d)]
        (check-refs! defs type create {:type type :create true})
        (validate-create! defs type create {:type type :create true})
        (validate-grounded! create {:type type :create true})))
    ;; The permission graph: recursion is allowed, but must be stratified
    ;; and able to bottom out.
    (let [nodes (vec (sort-by str (for [[t d] defs, p (keys (:permissions d))] [t p])))
          edges (into {} (map (fn [[t p :as k]]
                                [k (chain-edges defs t (get-in defs [t :permissions p]))]))
                      nodes)
          sccs (strongly-connected-components nodes edges)
          node->scc (into {} (for [scc sccs, n scc] [n scc]))
          cyclic-sccs (filterv (fn [scc]
                                 (or (> (count scc) 1)
                                     (contains? (get edges (first scc)) (first scc))))
                               sccs)
          recursive (into #{} cat cyclic-sccs)]
      (doseq [[t p :as k] nodes]
        (check-stratified! defs node->scc k (get-in defs [t :permissions p]) false))
      (run! #(check-base-cases! defs %) cyclic-sccs)
      ;; Attr sections, create-settable attrs, delete rules, attr->type map.
      (doseq [[type d] defs]
        (validate-attrs! defs type (:attrs d) {:type type})
        (when-let [create (:create d)]
          (doseq [rel (create-rule-relations create)]
            (when-not (contains? (:attrs d) rel)
              (fail "create rule relation must be declared in :attrs"
                    {:type type :relation rel}))))
        (when-let [delete (:delete d)]
          (when-not (contains? (:permissions d) delete)
            (fail ":delete must name a permission on the same type"
                  {:type type :delete delete
                   :known (set (keys (:permissions d)))}))))
      (let [attr->type (reduce (fn [m [type attr]]
                                 (if-let [other (get m attr)]
                                   (fail "attr declared by more than one type"
                                         {:attr attr :types [other type]})
                                   (assoc m attr type)))
                               {}
                               (for [[type d] defs, attr (keys (:attrs d))] [type attr]))
            types (reduce-kv
                   (fn [types type d]
                     (let [attrs (:attrs d)
                           create-rels (some-> (:create d) create-rule-relations)
                           settable (into #{}
                                          (keep (fn [[attr spec]]
                                                  (when (if (contains? spec :create?)
                                                          (:create? spec)
                                                          (or (:write spec)
                                                              (contains? create-rels attr)))
                                                    attr)))
                                          attrs)]
                       (assoc types type
                              (assoc d
                                     :readable (into #{} (keep (fn [[a s]] (when (:read s) a))) attrs)
                                     :writable (into #{} (keep (fn [[a s]] (when (:write s) a))) attrs)
                                     :settable-at-create settable))))
                   {} defs)
            subject-types (into {}
                                (map (fn [[t p :as k]]
                                       (let [targets (terminal-targets
                                                      defs t (get-in defs [t :permissions p]) #{})]
                                         (when (not= 1 (count targets))
                                           (fail "permission terminals unify the subject with more than one type"
                                                 {:type t :permission p :targets targets}))
                                         [k (first targets)])))
                                nodes)
            rule-defs (into {}
                            (map (fn [k] [k (compile-rule-defs defs recursive subject-types k)]))
                            (sort-by str recursive))
            compiled (reduce
                      (fn [compiled [type perm :as k]]
                        (let [node (get-in defs [type :permissions perm])
                              subject-type (get subject-types k)
                              {:keys [collision? object-var subject-var]} (perm-vars type subject-type)
                              recursive? (contains? recursive k)
                              clauses (if recursive?
                                        ;; a recursive permission IS its rule
                                        [(list (rule-sym k) object-var subject-var)]
                                        (compile-node defs recursive type node
                                                      object-var subject-var (atom 0)))
                              rules (->> (reachable-nodes edges k)
                                         (filter recursive)
                                         (sort-by str)
                                         (mapcat rule-defs)
                                         vec)
                              ;; Top-level or branches compile separately, cost-
                              ;; ordered, so point checks can short-circuit on
                              ;; the cheap branch (usually a direct terminal).
                              branches (->> (if (= :or (:op node)) (:branches node) [node])
                                            (mapv (fn [b]
                                                    (let [cs (compile-node defs recursive type b
                                                                           object-var subject-var (atom 0))]
                                                      {:clauses cs
                                                       :cost (pattern-count cs)
                                                       :source (:source b)
                                                       ;; point checks evaluate the normalized
                                                       ;; node by direct index walk
                                                       :node b})))
                                            (sort-by :cost)
                                            vec)]
                          (assoc compiled k
                                 {:object-type type
                                  :permission perm
                                  :subject-type subject-type
                                  :object-var object-var
                                  :subject-var subject-var
                                  :collision? collision?
                                  :recursive? recursive?
                                  :clauses clauses
                                  :rules rules
                                  :branches branches
                                  :attrs (node-attrs defs type node #{})})))
                      {}
                      nodes)]
        {:authz/schema? true
         :types types
         :attr->type attr->type
         :recursive recursive
         :compiled compiled}))))
