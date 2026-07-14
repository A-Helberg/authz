(ns authz.registrygen
  "Deterministic (seeded) random REGISTRY generator: random permission
  schemas -- not just random worlds -- plus a matching Datomic schema and
  a random world over the generated types. Schema-space is where
  compilation bugs live (or-join shape, collision variables, recursion,
  negation placement, and/not/attr= mixing), so the differential suite
  runs over these too.

  Validity by construction, without narrowing the interesting space:
  terminals always target :user (one subject type per permission);
  chains reference already-generated permissions of strictly earlier
  types (acyclic levels) or the permission itself through a same-type
  :parent relation (recursion, always appended to at least one
  non-recursive base branch); negation wraps terminals, conditions, or
  chains to earlier types only -- never a same-cycle chain -- so every
  generated registry is grounded and stratified. A registry that fails
  compile-schema is therefore a real finding, in this generator or in
  the validators."
  (:import (java.util Random)))

(defn gen-bundle
  "Returns {:registry .. :datomic-schema .. :tx .. :type-ids .. :user-ids ..}
  for a random registry and a random world over it."
  [{:keys [seed types-n entities-n users-n]
    :or {seed 42 types-n 4 entities-n 3 users-n 4}}]
  (let [rnd (Random. (long seed))
        pick (fn [xs] (nth (vec xs) (.nextInt rnd (count xs))))
        prob (fn [p] (< (.nextDouble rnd) p))
        tkw (fn [i] (keyword (str "t" i)))
        tattr (fn [i nm] (keyword (str "t" i) nm))

        ;; ------------------------------------------------------------------
        ;; registry, built in type order so chains can only look backwards
        state
        (reduce
         (fn [{:keys [pool defs]} i]
           (let [T (tkw i)
                 owner (tattr i "owner")
                 link (when (and (pos? i) (prob 0.7))
                        (let [j (.nextInt rnd i)]
                          [(tattr i "link") (tkw j)]))
                 parent (when (prob 0.6) (tattr i "parent"))
                 flag (tattr i "flag")
                 rels (cond-> {owner :user}
                        link (assoc (first link) (second link))
                        parent (assoc parent T))
                 extra (fn []
                         (case (.nextInt rnd 3)
                           0 (list 'attr= flag :on)
                           1 (list 'not owner)
                           2 (if link
                               (list 'not (list '-> (first link)
                                                (pick (pool (second link)))))
                               (list 'attr= flag :on))))
                 gen-core (fn []
                            (if (and link (prob 0.5))
                              (list '-> (first link) (pick (pool (second link))))
                              owner))
                 branch (fn []
                          (let [core (gen-core)]
                            (case (.nextInt rnd 3)
                              0 core
                              1 (list 'and core (extra))
                              2 (list 'and core (extra) (extra)))))
                 p0 (branch)
                 perms (cond-> {:p0 p0}
                         (prob 0.7)
                         (assoc :p1
                                (let [n (inc (.nextInt rnd 2))
                                      base (into [] (map (fn [_] (branch))) (range n))
                                      branches (if (and parent (prob 0.8))
                                                 (conj base (list '-> parent :p1))
                                                 base)]
                                  (if (= 1 (count branches))
                                    (first branches)
                                    (apply list 'or branches)))))]
             {:pool (assoc pool T (vec (keys perms)))
              :defs (assoc defs T {:relations rels :permissions perms})}))
         {:pool {} :defs {}}
         (range types-n))

        ;; :user itself gets a reverse-relation chain permission, exercising
        ;; same-type subject/object collision in list queries
        registry (assoc (:defs state)
                        :user {:relations {:t0/_owner :t0}
                               :permissions {:pu (list '-> :t0/_owner
                                                       (pick ((:pool state) :t0)))}})

        ;; ------------------------------------------------------------------
        ;; Datomic schema for the generated attributes
        ref-attrs (distinct
                   (for [[_ d] (:defs state)
                         [rel _] (:relations d)]
                     rel))
        datomic-schema
        (concat
         [{:db/ident :user/kid :db/valueType :db.type/string
           :db/cardinality :db.cardinality/one :db/unique :db.unique/identity}]
         (for [i (range types-n)]
           {:db/ident (tattr i "id") :db/valueType :db.type/string
            :db/cardinality :db.cardinality/one :db/unique :db.unique/identity})
         (for [i (range types-n)]
           {:db/ident (tattr i "flag") :db/valueType :db.type/keyword
            :db/cardinality :db.cardinality/one})
         (for [a ref-attrs]
           {:db/ident a :db/valueType :db.type/ref
            :db/cardinality (if (= "owner" (name a))
                              :db.cardinality/many :db.cardinality/one)}))

        ;; ------------------------------------------------------------------
        ;; a random world: owners are random user subsets, links random
        ;; earlier-type targets, parents random same-type entities (self
        ;; links and cycles included -- recursion must terminate on them)
        user-ids (mapv #(str "u" %) (range users-n))
        type-ids (into {} (for [i (range types-n)]
                            [(tkw i) (mapv #(str "t" i "-" %) (range entities-n))]))
        tx (-> []
               (into (map (fn [u] {:db/id u :user/kid u})) user-ids)
               (into (mapcat
                      (fn [i]
                        (let [T (tkw i)
                              d (get (:defs state) T)]
                          (mapv
                           (fn [eid]
                             (reduce
                              (fn [m [rel target]]
                                (cond
                                  (= target :user)
                                  (if (prob 0.8)
                                    (assoc m rel
                                           (vec (distinct
                                                 (mapv (fn [_] (pick user-ids))
                                                       (range (inc (.nextInt rnd 2)))))))
                                    m)
                                  :else
                                  (if (prob 0.6)
                                    (assoc m rel (pick (type-ids target)))
                                    m)))
                              {:db/id eid
                               (tattr i "id") eid
                               (tattr i "flag") (pick [:on :off])}
                              (:relations d)))
                           (type-ids T)))))
                     (range types-n)))]
    {:registry registry
     :datomic-schema (vec datomic-schema)
     :tx tx
     :type-ids type-ids
     :user-ids user-ids}))
