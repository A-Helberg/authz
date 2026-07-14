(ns authz.kernel-test
  "Cross-check against the VERIFIED kernel: the Scala module exported
  from verification/checked/Authz_Export.thy, whose evaluator carries
  the machine-checked theorem kernel_correct (its Some answer IS the
  spec's grants). The shim marshals the compiled registry, a
  stratification, and the relevant datoms into the kernel's model types
  (naturals via interning; the semantics only compares them) and
  compares the kernel's verdict with authz/can? triple by triple.

  The kernel is a reference checker, not a performance artifact -- it
  recomputes its fixpoint tower per query -- so this suite runs it on a
  small world that still exercises every construct: terminals, chains,
  recursion, and/not/attr=, and same-type subjects. It also checks the
  fail-loud contract: an unstratified sigma is rejected with None."
  (:require [authz.core :as authz]
            [authz.fixture :as fx]
            [authz.fixpoint-oracle]
            [authz.schema :as schema]
            [clojure.test :refer [deftest is testing]]
            [datomic.api :as d]))

;; ---------------------------------------------------------------------------
;; Scala interop

(def ^:private module
  (-> (Class/forName "AuthzKernel$") (.getField "MODULE$") (.get nil)))

(defn- sbigint [n] (scala.math.BigInt/apply (long n)))
(defn- snat [n] (AuthzKernel$Nat. (sbigint n)))
(defn- stuple [a b] (scala.Tuple2. a b))

(defn- slist
  "A scala.collection.immutable.List from a Clojure seq."
  [xs]
  (reduce (fn [acc x] (.$colon$colon acc x))
          scala.collection.immutable.Nil$/MODULE$
          (reverse xs)))

;; ---------------------------------------------------------------------------
;; Marshalling: registry + db -> kernel model (naturals via interning)

(defn- interner []
  (let [state (atom {})]
    (fn [x]
      (or (get @state x)
          (let [n (count @state)]
            (swap! state assoc x n)
            n)))))

(defn- marshal
  "Marshals the compiled schema and the registry-relevant datoms of `db`
  into kernel_check's inputs. Returns {:kr :kp :ks :ds :ty :perm :attrs}."
  [compiled db]
  (let [ty (interner) perm (interner) attr (interner) lit (interner)
        types (:types compiled)
        rel->k (fn [rel]
                 (if (schema/reverse-relation? rel)
                   (AuthzKernel$Rev. (snat (attr (schema/underlying-attr rel))))
                   (AuthzKernel$Fwd. (snat (attr rel)))))
        ref-attrs (into #{}
                        (mapcat (fn [[_ d]] (map schema/underlying-attr
                                                 (keys (:relations d)))))
                        types)
        val->vl (fn [a v]
                  (if (contains? ref-attrs a)
                    (AuthzKernel$Ent. (snat v))
                    (AuthzKernel$Lit. (snat (lit v)))))
        node->check (fn node->check [node]
                      (case (:op node)
                        :relation (AuthzKernel$Terminal. (rel->k (:relation node)))
                        :chain (AuthzKernel$Chain. (rel->k (:relation node))
                                                   (snat (perm (:permission node))))
                        :attr= (AuthzKernel$AttrEq. (snat (attr (:attr node)))
                                                    (val->vl (:attr node) (:value node)))
                        :not (AuthzKernel$CNot. (node->check (:branch node)))
                        :and (reduce (fn [acc c] (AuthzKernel$CAnd. c acc))
                                     (node->check (last (:branches node)))
                                     (map node->check (reverse (butlast (:branches node)))))
                        :or (reduce (fn [acc c] (AuthzKernel$COr. c acc))
                                    (node->check (last (:branches node)))
                                    (map node->check (reverse (butlast (:branches node)))))))
        kr (for [[T d] types
                 [rel target] (:relations d)]
             (stuple (stuple (snat (ty T)) (rel->k rel)) (snat (ty target))))
        kp (for [[T d] types
                 [p node] (:permissions d)]
             (stuple (stuple (snat (ty T)) (snat (perm p))) (node->check node)))
        ;; stratification: reuse the executable spec's stratifier
        ks-keys (vec (sort-by str (for [[t d] types, p (keys (:permissions d))] [t p])))
        deps-of (into {}
                      (map (fn [[t p :as k]]
                             [k (#'authz.fixpoint-oracle/deps
                                 types t (get-in types [t :permissions p]) false)]))
                      ks-keys)
        sigma (#'authz.fixpoint-oracle/stratify ks-keys deps-of)
        ks (for [[k n] sigma]
             (stuple (stuple (snat (ty (first k))) (snat (perm (second k)))) (snat n)))
        ;; every attribute any permission touches, transitively — the
        ;; compiler already computed these watch-sets
        all-attrs (into ref-attrs
                        (mapcat :attrs)
                        (vals (:compiled compiled)))
        ds (for [a all-attrs
                 datom (d/datoms db :aevt a)]
             (stuple (snat (:e datom))
                     (stuple (snat (attr a)) (val->vl a (:v datom)))))]
    {:kr (slist kr) :kp (slist kp) :ks (slist ks) :ds (slist ds)
     :ty ty :perm perm}))

(defn- kernel-can?
  "The verified kernel's verdict: true/false, or ::none if it rejected
  the inputs."
  [{:keys [kr kp ks ds ty perm]} subject-eid p T object-eid]
  (let [res (.kernel_check module kr kp ks ds
                           (snat subject-eid) (snat (ty T)) (snat (perm p))
                           (snat object-eid))]
    (if (.isDefined res) (.get res) ::none)))

;; ---------------------------------------------------------------------------
;; A small world over the fixture registry: every construct, few eids

(def ^:private mini-world
  [{:db/id "ada" :user/name "Ada" :user/email "k-ada@x"}
   {:db/id "uma" :user/name "Uma" :user/email "k-uma@x"}
   {:db/id "sys" :system/superadmins ["ada"]}
   {:db/id "acme" :organisation/name "K-Acme" :organisation/system "sys"
    :organisation/admins ["ada"] :organisation/members ["uma"]}
   {:db/id "root" :folder/name "K-Root" :folder/organisation "acme"}
   {:db/id "sub" :folder/name "K-Sub" :folder/parent "root"}
   {:db/id "doc-pub" :doc/title "K-Pub" :doc/organisation "acme"
    :doc/owner "uma" :doc/viewers ["ada"] :doc/status :published}
   {:db/id "doc-drf" :doc/title "K-Drf" :doc/organisation "acme"
    :doc/owner "uma" :doc/viewers ["ada"] :doc/banned ["ada"]
    :doc/status :draft}])

(deftest verified-kernel-agrees-with-can?
  (let [conn (fx/empty-conn)
        db (:db-after @(d/transact conn mini-world))
        m (marshal fx/compiled db)
        user #(d/entid db [:user/email %])
        ada (user "k-ada@x") uma (user "k-uma@x")
        org (d/entid db [:organisation/name "K-Acme"])
        root (d/entid db [:folder/name "K-Root"])
        sub (d/entid db [:folder/name "K-Sub"])
        dpub (d/entid db [:doc/title "K-Pub"])
        ddrf (d/entid db [:doc/title "K-Drf"])
        triples (for [s [ada uma]
                      [p T o] [[:view :organisation org] [:edit :organisation org]
                               [:view :folder root] [:view :folder sub]
                               [:manage :folder sub]
                               [:view :doc dpub] [:view :doc ddrf]
                               [:edit :doc dpub]
                               [:view :user ada] [:view :user uma]]]
                  [s p T o])]
    (doseq [[s p T o] triples]
      (let [expected (authz/can? fx/compiled db :user s p T o)
            actual (kernel-can? m s p T o)]
        (is (= expected actual)
            (str "kernel vs can? on " [p T] " subject " s " object " o))))))

(deftest kernel-rejects-unstratified-sigma
  (let [conn (fx/empty-conn)
        db (:db-after @(d/transact conn mini-world))
        m (marshal fx/compiled db)
        ;; break the stratification: :resource/:view chains into
        ;; :organisation/:view, so forcing sigma(org view) above
        ;; sigma(resource view) violates the sigma we hand over
        ty (:ty m) perm (:perm m)
        bad-ks (slist [(stuple (stuple (snat (ty :organisation))
                                       (snat (perm :view)))
                               (snat 99))])
        res (.kernel_check module (:kr m) (:kp m) bad-ks (:ds m)
                           (snat 1) (snat (ty :resource)) (snat (perm :view))
                           (snat 2))]
    (is (not (.isDefined res))
        "an unstratified sigma must be rejected with None, never answered")))
