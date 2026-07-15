(ns authz.fixpoint-oracle
  "The executable spec: a bottom-up stratified least-fixpoint evaluator
  implementing SEMANTICS.md §3 as literally as possible.

  This is the second, strategy-independent oracle. authz.reference walks
  the graph top-down with visited sets — the same *strategy* as
  authz.core's walker, so a subtle flaw in the visited-set reasoning
  could hide in both. This namespace instead materializes I_N: extract
  every relation extension into plain sets, compute a stratification,
  then iterate each stratum's operator to its least fixed point. Slow by
  design, naive by design — its job is to be obviously the same thing as
  the spec, not to be fast.

  Only the check-language *syntax* (the normalized node trees in the
  compiled schema) is shared with the implementation; evaluation shares
  nothing."
  (:require [authz.schema :as schema]
            [datomic.api :as d]))

;; ---------------------------------------------------------------------------
;; SEMANTICS §1: relation extensions and attr facts, extracted eagerly

(defn- extension
  "⟦rel⟧_D as an index {from -> #{to}}. Forward: (x, a, y) ∈ D with y an
  eid. Reverse (_a): (y, a, x) ∈ D. Values that are not eids contribute
  nothing (relations traverse refs)."
  [db rel]
  (let [attr (schema/underlying-attr rel)
        datoms (try (d/datoms db :aevt attr) (catch Exception _ nil))
        reverse? (schema/reverse-relation? rel)]
    (reduce (fn [m datom]
              (if (number? (:v datom))
                (let [[from to] (if reverse?
                                  [(:v datom) (:e datom)]
                                  [(:e datom) (:v datom)])]
                  (update m from (fnil conj #{}) to))
                m))
            {}
            datoms)))

(defn- attr-facts
  "{[e v] ...} for attribute a — the AttrEq leaf's denotation."
  [db a]
  (into #{}
        (map (fn [datom] [(:e datom) (:v datom)]))
        (try (d/datoms db :aevt a) (catch Exception _ nil))))

(defn- node-leaves
  "All relation names and attr= attributes a node tree touches."
  [node]
  (case (:op node)
    :relation {:rels #{(:relation node)}}
    :chain {:rels #{(:relation node)}}
    :attr= {:attrs #{(:attr node)}}
    :not (node-leaves (:branch node))
    (:or :and) (apply merge-with into (map node-leaves (:branches node)))))

;; ---------------------------------------------------------------------------
;; SEMANTICS §2: polarity-labelled dependencies and stratification

(defn- deps
  "{[target-key negative?] ...} for a node interpreted at `type`."
  [types type node under-not?]
  (case (:op node)
    (:relation :attr=) #{}
    :chain #{[[(get-in types [type :relations (:relation node)])
               (:permission node)]
              under-not?]}
    :not (deps types type (:branch node) true)
    (:or :and) (into #{} (mapcat #(deps types type % under-not?)) (:branches node))))

(defn- stratify
  "σ : Keys → ℕ with σ(k) ≥ σ(k') on positive edges and σ(k) > σ(k') on
  negative ones, by naive iteration to fixpoint. Throws when no such σ
  exists (a negative cycle) — compile-schema rejects those, so reaching
  the throw here means the validators and the spec disagree."
  [ks deps-of]
  (loop [sigma (zipmap ks (repeat 0)) i 0]
    (let [sigma' (reduce (fn [s k]
                           (reduce (fn [s [k' neg?]]
                                     (update s k max (cond-> (get s k') neg? inc)))
                                   s (deps-of k)))
                         sigma ks)]
      (cond (= sigma sigma') sigma
            (> i (count ks)) (throw (ex-info "fixpoint-oracle: not stratified" {:keys ks}))
            :else (recur sigma' (inc i))))))

;; ---------------------------------------------------------------------------
;; SEMANTICS §3: satisfaction and the iterated least fixpoint

(defn- sat?
  "I, T, s, o ⊨ node — the satisfaction table, verbatim."
  [{:keys [types exts attrs]} I type node s o]
  (case (:op node)
    :relation (contains? (get-in exts [(:relation node) o]) s)
    :chain (let [target (get-in types [type :relations (:relation node)])
                 q (:permission node)]
             (boolean (some #(contains? (get I [target q]) [s %])
                            (get-in exts [(:relation node) o]))))
    :attr= (contains? (get attrs (:attr node)) [o (:value node)])
    :not (not (sat? {:types types :exts exts :attrs attrs} I type (:branch node) s o))
    :and (every? #(sat? {:types types :exts exts :attrs attrs} I type % s o)
                 (:branches node))
    :or (boolean (some #(sat? {:types types :exts exts :attrs attrs} I type % s o)
                       (:branches node)))))

(defn facts
  "I_N for the whole registry: {[type perm] #{[subject object] ...}}.
  Strata are evaluated in order; within a stratum the operator F_n is
  iterated to its least fixed point from below. The candidate pair space
  is domain × domain, where the domain is every eid occurring in any
  relation extension — sufficient for safe (grounded) registries, whose
  answer sets are domain-independent (SEMANTICS §2)."
  [compiled db]
  (let [types (:types compiled)
        ks (vec (sort-by str (for [[t d] types, p (keys (:permissions d))] [t p])))
        node-of (fn [[t p]] (get-in types [t :permissions p]))
        leaves (apply merge-with into (map (comp node-leaves node-of) ks))
        ctx {:types types
             :exts (into {} (map (fn [r] [r (extension db r)])) (:rels leaves))
             :attrs (into {} (map (fn [a] [a (attr-facts db a)])) (:attrs leaves))}
        domain (into #{}
                     (mapcat (fn [[_ index]]
                               (into (set (keys index)) cat (vals index))))
                     (:exts ctx))
        deps-of (into {} (map (fn [[t p :as k]] [k (deps types t (node-of k) false)])) ks)
        sigma (stratify ks deps-of)
        strata (->> ks (group-by sigma) (sort-by key) (map val))]
    (reduce
     (fn [I stratum]
       (loop [I I]
         (let [I' (reduce
                   (fn [I [t _ :as k]]
                     (let [node (node-of k)]
                       (update I k into
                               (for [s domain, o domain
                                     :when (and (not (contains? (get I k) [s o]))
                                                (sat? ctx I t node s o))]
                                 [s o]))))
                   I stratum)]
           (if (= I I') I (recur I')))))
     (zipmap ks (repeat #{}))
     strata)))

(defn objects
  "{o | grants(type, perm, subject, o)} read off a `facts` result."
  [I type perm subject]
  (into #{}
        (keep (fn [[s o]] (when (= s subject) o)))
        (get I [type perm])))

(defn subjects
  "{s | grants(type, perm, s, object)} read off a `facts` result."
  [I type perm object]
  (into #{}
        (keep (fn [[s o]] (when (= o object) s)))
        (get I [type perm])))
