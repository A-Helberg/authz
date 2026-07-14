(ns authz.registrygen
  "Random REGISTRY generation: random permission schemas -- not just
  random worlds -- plus a matching Datomic schema and a random world
  over the generated types. Schema-space is where compilation bugs live
  (or-join shape, collision variables, recursion, negation placement,
  and/not/attr= mixing), so the differential suite runs over these too.

  One builder, two front doors. `build-bundle` turns a plain-data
  RECIPE of choices into a valid bundle, totally: indices clamp by mod,
  dropped links fall back to terminals, recursive and mutual branches
  only attach beside at least one base branch. Any recipe -- including
  every shrunk mutation test.check produces -- builds a compilable
  registry, so a compile-schema failure is a real finding in this
  builder or in the validators. `gen-bundle` synthesizes a recipe
  deterministically from a seed (fixed-seed regression coverage);
  authz.registry-prop-test generates recipes via test.check (shrinking).

  Validity by construction, without narrowing the interesting space:
  terminals always target :user (one subject type per permission);
  chains reference already-generated permissions of strictly earlier
  types (acyclic levels), the permission itself through a same-type
  :parent relation (self-recursion), or its same-type twin (:p1/:p2
  mutual recursion) -- always beside a non-recursive base branch;
  negation wraps terminals, conditions, or chains to earlier types
  only. Cross-type mutual pairs (pm/pmb over fresh relations both ways)
  are added in a second pass, after every negation target has been
  chosen, so negation through a cycle is impossible by construction."
  (:import (java.util Random)))

;; ---------------------------------------------------------------------------
;; the builder: recipe -> valid bundle, total for any recipe shape

(defn- build-branch
  [i link pool recipe]
  (let [owner (keyword (str "t" i) "owner")
        flag (keyword (str "t" i) "flag")
        chain-of (fn [c]
                   (let [[lattr ltype] link
                         perms (pool ltype)]
                     (list '-> lattr (nth perms (mod c (count perms))))))
        core (let [c (:core recipe)]
               (if (and (vector? c) link) (chain-of (second c)) owner))
        extras (map (fn [e]
                      (cond
                        (= e :flag=) (list 'attr= flag :on)
                        (= e :not-owner) (list 'not owner)
                        (vector? e) (if link
                                      (list 'not (chain-of (second e)))
                                      (list 'attr= flag :on))))
                    (:extras recipe))]
    (if (seq extras)
      (apply list 'and core extras)
      core)))

(defn build-bundle
  "recipe -> {:registry :datomic-schema :tx :type-ids :user-ids}, valid
  for any recipe shape. Recipe keys: :types (vector of
  {:link nat? :parent? bool :mutual? bool :p0 branch
   :p1 {:branches [branch..] :recursive? bool}?} where branch =
  {:core :owner | [:chain nat] :extras [..]}), :cross-pairs (vector of
  {:hi nat :lo nat :extra-base? bool}), :users-n, :entities-n, :tape
  (vector of nats driving world link choices)."
  [{:keys [types cross-pairs users-n entities-n tape]}]
  (let [types (if (seq types) (vec types) [{:p0 {:core :owner :extras []}}])
        n (count types)
        users-n (max 1 (or users-n 1))
        entities-n (max 1 (or entities-n 1))
        tape (if (seq tape) (vec tape) [0])
        tp (fn [i] (nth tape (mod i (count tape))))
        state
        (reduce
         (fn [{:keys [pool defs]} i]
           (let [tr (nth types i)
                 T (keyword (str "t" i))
                 owner (keyword (str "t" i) "owner")
                 link (when (and (pos? i) (:link tr))
                        [(keyword (str "t" i) "link")
                         (keyword (str "t" (mod (:link tr) i)))])
                 parent (when (:parent? tr) (keyword (str "t" i) "parent"))
                 rels (cond-> {owner :user}
                        link (assoc (first link) (second link))
                        parent (assoc parent T))
                 p0 (build-branch i link pool (:p0 tr))
                 mutual? (boolean (and parent (:mutual? tr) (:p1 tr)))
                 p1 (when-let [pr (:p1 tr)]
                      (let [base (mapv #(build-branch i link pool %) (:branches pr))
                            ;; recursion and mutuality only ever attach
                            ;; beside a base branch, whatever the recipe
                            base (if (seq base)
                                   base
                                   [(build-branch i link pool {:core :owner :extras []})])
                            bs (cond-> base
                                 (and parent (:recursive? pr)) (conj (list '-> parent :p1))
                                 mutual? (conj (list '-> parent :p2)))]
                        (if (= 1 (count bs)) (first bs) (apply list 'or bs))))
                 p2 (when (and mutual? p1) (list '-> parent :p1))
                 perms (cond-> {:p0 p0}
                         p1 (assoc :p1 p1)
                         p2 (assoc :p2 p2))]
             {:pool (assoc pool T (vec (keys perms)))
              :defs (assoc defs T {:relations rels :permissions perms})}))
         {:pool {} :defs {}}
         (range n))
        ;; cross-type mutual pairs, added AFTER every negation target was
        ;; chosen: pm on the earlier type and pmb on the later one
        ;; reference each other over fresh relations both ways, with the
        ;; base branch on pmb (mutual recursion sharing one base case)
        defs (reduce
              (fn [defs [q pr]]
                (if (< n 2)
                  defs
                  (let [k (inc (mod (:hi pr 0) (dec n)))
                        j (mod (:lo pr 0) k)
                        tj (keyword (str "t" j))
                        tk (keyword (str "t" k))
                        xattr (keyword (str "t" j) (str "x" q))
                        battr (keyword (str "t" k) (str "b" q))
                        pm (keyword (str "pm" q))
                        pmb (keyword (str "pmb" q))
                        ownerj (keyword (str "t" j) "owner")
                        ownerk (keyword (str "t" k) "owner")]
                    (-> defs
                        (update-in [tj :relations] assoc xattr tk)
                        (update-in [tk :relations] assoc battr tj)
                        (update-in [tj :permissions] assoc pm
                                   (if (:extra-base? pr)
                                     (list 'or ownerj (list '-> xattr pmb))
                                     (list '-> xattr pmb)))
                        (update-in [tk :permissions] assoc pmb
                                   (list 'or ownerk (list '-> battr pm)))))))
              (:defs state)
              (map-indexed vector cross-pairs))
        registry (assoc defs
                        :user {:relations {:t0/_owner :t0}
                               :permissions {:pu (list '-> :t0/_owner
                                                       (first ((:pool state) :t0)))}})
        ref-attrs (distinct (for [[_ d] defs, [rel _] (:relations d)] rel))
        datomic-schema
        (vec (concat
              [{:db/ident :user/kid :db/valueType :db.type/string
                :db/cardinality :db.cardinality/one :db/unique :db.unique/identity}]
              (for [i (range n)]
                {:db/ident (keyword (str "t" i) "id") :db/valueType :db.type/string
                 :db/cardinality :db.cardinality/one :db/unique :db.unique/identity})
              (for [i (range n)]
                {:db/ident (keyword (str "t" i) "flag") :db/valueType :db.type/keyword
                 :db/cardinality :db.cardinality/one})
              (for [a ref-attrs]
                {:db/ident a :db/valueType :db.type/ref
                 :db/cardinality (if (= "owner" (name a))
                                   :db.cardinality/many :db.cardinality/one)})))
        user-ids (mapv #(str "u" %) (range users-n))
        type-ids (into {} (for [i (range n)]
                            [(keyword (str "t" i)) (mapv #(str "t" i "-" %) (range entities-n))]))
        tx (-> []
               (into (map (fn [u] {:db/id u :user/kid u})) user-ids)
               (into (mapcat
                      (fn [i]
                        (let [T (keyword (str "t" i))
                              d (get defs T)]
                          (map-indexed
                           (fn [j eid]
                             (reduce
                              (fn [m [k [rel target]]]
                                (let [z (+ (* 31 i) (* 7 j) k)]
                                  (cond
                                    (= target :user)
                                    (if (even? (tp z))
                                      (assoc m rel
                                             (vec (distinct
                                                   [(nth user-ids (mod (tp (inc z)) users-n))
                                                    (nth user-ids (mod (tp (+ z 2)) users-n))])))
                                      m)
                                    :else
                                    (if (pos? (mod (tp z) 3))
                                      (assoc m rel (nth (type-ids target)
                                                        (mod (tp (inc z)) entities-n)))
                                      m))))
                              {:db/id eid
                               (keyword (str "t" i) "id") eid
                               (keyword (str "t" i) "flag") (if (even? (tp (+ (* 31 i) j)))
                                                              :on :off)}
                              (map-indexed vector (:relations d))))
                           (type-ids T)))))
                     (range n)))]
    {:registry registry
     :datomic-schema datomic-schema
     :tx tx
     :type-ids type-ids
     :user-ids user-ids}))

;; ---------------------------------------------------------------------------
;; the seeded front door: synthesize a recipe deterministically

(defn gen-bundle
  "Deterministic bundle from a seed: synthesizes a recipe with
  java.util.Random and delegates to build-bundle."
  [{:keys [seed types-n entities-n users-n]
    :or {seed 42 types-n 4 entities-n 3 users-n 4}}]
  (let [rnd (Random. (long seed))
        prob (fn [p] (< (.nextDouble rnd) p))
        nat (fn [] (.nextInt rnd 97))
        extra (fn [] (case (.nextInt rnd 3)
                       0 :flag=
                       1 :not-owner
                       2 [:not-chain (nat)]))
        branch (fn []
                 {:core (if (prob 0.5) [:chain (nat)] :owner)
                  :extras (vec (mapv (fn [_] (extra))
                                     (range (.nextInt rnd 3))))})
        types (mapv (fn [i]
                      {:link (when (and (pos? i) (prob 0.7)) (nat))
                       :parent? (prob 0.6)
                       :mutual? (prob 0.4)
                       :p0 (branch)
                       :p1 (when (prob 0.7)
                             {:branches (mapv (fn [_] (branch))
                                              (range (inc (.nextInt rnd 2))))
                              :recursive? (prob 0.8)})})
                    (range types-n))
        cross-pairs (cond-> []
                      (prob 0.6) (conj {:hi (nat) :lo (nat) :extra-base? (prob 0.5)})
                      (prob 0.25) (conj {:hi (nat) :lo (nat) :extra-base? (prob 0.5)}))
        tape (mapv (fn [_] (nat)) (range 48))]
    (build-bundle {:types types
                   :cross-pairs cross-pairs
                   :users-n users-n
                   :entities-n entities-n
                   :tape tape})))
