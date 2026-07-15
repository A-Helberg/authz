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

    (authz.registrygen/build-bundle shrunk-recipe)

  and feed the bundle to the deterministic comparison in
  authz.generative-registry-test to pinpoint the disagreeing strategy.

  The seeded generator (authz.registrygen) stays as fixed-seed
  regression coverage; this namespace explores fresh schemas on every
  run."
  (:require [authz.core :as authz]
            [authz.fixpoint-oracle :as oracle]
            [authz.reference :as ref]
            [authz.registrygen :as rgen]
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
                :mutual? gen/boolean
                :p0 branch-gen
                :p1 (gen/frequency
                     [[1 (gen/return nil)]
                      [2 (gen/hash-map :branches (gen/vector branch-gen 1 2)
                                       :recursive? gen/boolean)]])))

(def recipe-gen
  (gen/hash-map :types (gen/vector type-gen 1 4)
                :cross-pairs (gen/vector (gen/hash-map :hi gen/nat
                                                       :lo gen/nat
                                                       :extra-base? gen/boolean)
                                         0 2)
                :users-n (gen/choose 1 4)
                :entities-n (gen/choose 1 3)
                :tape (gen/vector gen/nat 1 48)))

;; ---------------------------------------------------------------------------
;; The builder lives in authz.registrygen (shared with the seeded
;; generator); reproduce a shrunk recipe with (rgen/build-bundle recipe)

;; ---------------------------------------------------------------------------
;; The property: all strategies agree with both oracles on every triple

(defn- list-eids
  [compiled db type perm subject-eid & [all-rules?]]
  (let [collision? (= type :user)
        opts (cond-> (when collision? {:object-var '?target :subject-var '?subject})
               all-rules? (assoc :all-rules? true))
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
                 via-list-rules (list-eids compiled db type perm subject true)
                 via-grants (set (authz/grants compiled db :user subject perm type))]
             (and (= via-ref via-can)
                  (= via-ref via-batch)
                  (= via-ref (set/intersection via-list-full (set eids)))
                  (= via-list-full via-grants)
                  (= via-spec via-list-full)
                  (= via-list-full via-list-rules)
                  (every? (fn [object]
                            (= (oracle/subjects spec-facts type perm object)
                               (set (authz/subjects compiled db :user perm type object))))
                          eids))))))
      (finally
        (d/delete-database uri)))))

(defspec shrinking-random-registries-agree 40
  (prop/for-all [recipe recipe-gen]
                (bundle-agrees? (rgen/build-bundle recipe))))
