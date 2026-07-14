(ns authz.registry-prop-test
  "Property-based differential testing WITH SHRINKING: test.check
  generators produce a plain-data RECIPE of choices, and `build-bundle`
  -- a total, tolerant builder -- turns any recipe (including every
  shrunk mutation of it) into a valid registry + Datomic schema + world:
  indices clamp by mod, dropped links fall back to terminals, recursive
  branches only attach beside a base branch. Shrinking therefore
  minimizes genuinely (fewer types, fewer branches, fewer entities,
  simpler tapes) while every intermediate stays compilable, so a
  compile-schema exception inside the property is itself a shrinkable
  finding.

  When this spec fails, test.check reports the SHRUNK recipe. Reproduce
  with:

    (authz.registry-prop-test/build-bundle shrunk-recipe)

  and feed the bundle to the deterministic comparison in
  authz.generative-registry-test to pinpoint the disagreeing strategy.

  The seeded generator (authz.registrygen) stays as fixed-seed
  regression coverage; this namespace explores fresh schemas on every
  run."
  (:require [authz.core :as authz]
            [authz.fixpoint-oracle :as oracle]
            [authz.reference :as ref]
            [authz.schema :as schema]
            [clojure.set :as set]
            [clojure.test.check.clojure-test :refer [defspec]]
            [clojure.test.check.generators :as gen]
            [clojure.test.check.properties :as prop]
            [datomic.api :as d]))

;; ---------------------------------------------------------------------------
;; Recipes: pure choice data, every mutation of which builds validly

(def ^:private extra-gen
  (gen/one-of [(gen/return :flag=)
               (gen/return :not-owner)
               (gen/tuple (gen/return :not-chain) gen/nat)]))

(def ^:private branch-gen
  (gen/hash-map :core (gen/one-of [(gen/return :owner)
                                   (gen/tuple (gen/return :chain) gen/nat)])
                :extras (gen/vector extra-gen 0 2)))

(def ^:private type-gen
  (gen/hash-map :link (gen/frequency [[1 (gen/return nil)] [2 gen/nat]])
                :parent? gen/boolean
                :p0 branch-gen
                :p1 (gen/frequency
                     [[1 (gen/return nil)]
                      [2 (gen/hash-map :branches (gen/vector branch-gen 1 2)
                                       :recursive? gen/boolean)]])))

(def recipe-gen
  (gen/hash-map :types (gen/vector type-gen 1 4)
                :users-n (gen/choose 1 4)
                :entities-n (gen/choose 1 3)
                :tape (gen/vector gen/nat 1 48)))

;; ---------------------------------------------------------------------------
;; The builder: recipe -> valid bundle, total by construction

(defn- build-branch
  [i link pool recipe]
  (let [owner (keyword (str "t" i) "owner")
        flag (keyword (str "t" i) "flag")
        chain-of (fn [n]
                   (let [[lattr ltype] link
                         perms (pool ltype)]
                     (list '-> lattr (nth perms (mod n (count perms))))))
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
  for any recipe shape."
  [{:keys [types users-n entities-n tape]}]
  (let [n (count types)
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
                 p1 (when-let [pr (:p1 tr)]
                      (let [bs (mapv #(build-branch i link pool %) (:branches pr))
                            bs (if (and parent (:recursive? pr))
                                 (conj bs (list '-> parent :p1))
                                 bs)]
                        (when (seq bs)
                          (if (= 1 (count bs)) (first bs) (apply list 'or bs)))))
                 perms (cond-> {:p0 p0} p1 (assoc :p1 p1))]
             {:pool (assoc pool T (vec (keys perms)))
              :defs (assoc defs T {:relations rels :permissions perms})}))
         {:pool {} :defs {}}
         (range n))
        registry (assoc (:defs state)
                        :user {:relations {:t0/_owner :t0}
                               :permissions {:pu (list '-> :t0/_owner
                                                       (first ((:pool state) :t0)))}})
        ref-attrs (distinct (for [[_ d] (:defs state), [rel _] (:relations d)] rel))
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
                              d (get (:defs state) T)]
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
;; The property: all strategies agree with both oracles on every triple

(defn- list-eids
  [compiled db type perm subject-eid]
  (let [collision? (= type :user)
        opts (when collision? {:object-var '?target :subject-var '?subject})
        obj-var (if collision? '?target (symbol (str "?" (name type))))
        subj-var (if collision? '?subject '?user)
        {:keys [where rules]} (authz/list-query* compiled type perm :user opts)]
    (into #{}
          (map first)
          (if (seq rules)
            (d/q {:find [obj-var] :in ['$ '% subj-var] :where where}
                 db rules subject-eid)
            (d/q {:find [obj-var] :in ['$ subj-var] :where where}
                 db subject-eid)))))

(defn- bundle-agrees?
  "True when every strategy agrees with both oracles on every triple of
  the bundle's world."
  [{:keys [registry datomic-schema tx type-ids user-ids]}]
  (let [compiled (schema/compile-schema registry)
        uri (str "datomic:mem://" (d/squuid))]
    (try
      (d/create-database uri)
      (let [conn (d/connect uri)
            _ @(d/transact conn datomic-schema)
            _ @(d/transact conn tx)
            db (d/db conn)
            eid (fn [T id]
                  (d/entid db [(if (= T :user) :user/kid (keyword (name T) "id")) id]))
            entities (into {:user (mapv #(eid :user %) user-ids)}
                           (map (fn [[T ids]] [T (mapv #(eid T %) ids)]))
                           type-ids)
            spec-facts (oracle/facts compiled db)]
        (every?
         identity
         (for [[type perm] (keys (:compiled compiled))
               subject (:user entities)]
           (let [eids (entities type)
                 via-spec (oracle/objects spec-facts type perm subject)
                 via-ref (into #{} (filter #(ref/check compiled db type perm subject %)) eids)
                 via-can (into #{} (filter #(authz/can? compiled db :user subject perm type %)) eids)
                 via-batch (authz/filter-authorized compiled db :user subject perm type eids)
                 via-list-full (list-eids compiled db type perm subject)
                 via-grants (set (authz/grants compiled db :user subject perm type))]
             (and (= via-ref via-can)
                  (= via-ref via-batch)
                  (= via-ref (set/intersection via-list-full (set eids)))
                  (= via-list-full via-grants)
                  (= via-spec via-list-full))))))
      (finally
        (d/delete-database uri)))))

(defspec shrinking-random-registries-agree 40
  (prop/for-all [recipe recipe-gen]
                (bundle-agrees? (build-bundle recipe))))
