(ns authz.attrs-test
  "The attribute-level allow layer: sync-down datom filtering and sync-up
  transaction checking for occasionally-connected clients."
  (:require [authz.attrs :as attrs]
            [authz.fixture :as fx]
            [authz.schema :as schema]
            [clojure.test :refer [deftest is testing use-fixtures]]
            [datomic.api :as d]))

(def ^:dynamic *db* nil)

(use-fixtures :once
  (fn [f] (binding [*db* (d/db (fx/fresh-conn))] (f))))

(defn- denials
  "reason -> set of denied attrs, for compact assertions."
  [report]
  (reduce (fn [m {:keys [reason a]}] (update m reason (fnil conj #{}) a))
          {}
          (:denied report)))

;; ---------------------------------------------------------------------------
;; Introspection + point checks

(deftest attr-introspection
  (is (= #{:submission/id :submission/content :submission/submitted-by
           :submission/organisation}
         (attrs/readable-attrs fx/compiled :submission)))
  (is (= #{:submission/content} (attrs/writable-attrs fx/compiled :submission)))
  (is (= #{:submission/id :submission/content :submission/submitted-by
           :submission/organisation}
         (attrs/creatable-attrs fx/compiled :submission)))
  (is (= :assignment (:type (attrs/attr-spec fx/compiled :assignment/notes))))
  (is (nil? (attrs/attr-spec fx/compiled :user/email))
      "attrs outside every :attrs section are invisible to the layer"))

(deftest attr-point-checks
  (let [db *db*
        asg (fx/assignment db "asg-uma")]
    (testing "read follows the :read permission"
      (is (attrs/can-read-attr? fx/compiled db (fx/user db :uma) :assignment/notes asg))
      (is (attrs/can-read-attr? fx/compiled db (fx/user db :mark) :assignment/notes asg))
      (is (not (attrs/can-read-attr? fx/compiled db (fx/user db :vic) :assignment/notes asg))))
    (testing "write follows the :write permission (narrower than read here)"
      (is (attrs/can-write-attr? fx/compiled db (fx/user db :uma) :assignment/notes asg))
      (is (not (attrs/can-write-attr? fx/compiled db (fx/user db :mark) :assignment/notes asg)))
      (is (not (attrs/can-write-attr? fx/compiled db (fx/user db :uma) :assignment/member asg))
          "declared read-only attr is never writable"))
    (testing "undeclared attrs are deny-by-default"
      (is (not (attrs/can-read-attr? fx/compiled db (fx/user db :sam) :user/email (fx/user db :uma)))))))

;; ---------------------------------------------------------------------------
;; Sync down: readable-datoms

(deftest readable-datoms-filters-deny-by-default
  (let [db *db*
        asg (fx/assignment db "asg-uma")
        uma (fx/user db :uma)
        mark (fx/user db :mark)
        input [[asg :assignment/notes "start"]
               [asg :assignment/member uma]
               [uma :user/email "uma@x"]
               [(fx/submission db "sub-yara") :submission/content "yara's work"]]
        {:keys [allowed denied]} (attrs/readable-datoms fx/compiled db mark input)]
    (is (= [(input 0) (input 1)] allowed)
        "Mark manages Uma's site, so her assignment datoms sync down to him")
    (is (= [{:datom (input 2) :reason :authz/undeclared-attr}
            {:datom (input 3) :reason :authz/not-authorized}]
           denied)
        "an undeclared attr and another org's submission stay behind")))

(deftest readable-datoms-accepts-raw-datomic-datoms
  ;; The tx-report-queue / d/datoms shape: Datom objects with numeric attr ids.
  (let [db *db*
        asg (fx/assignment db "asg-uma")
        raw (vec (d/datoms db :eavt asg))
        {:keys [allowed denied]} (attrs/readable-datoms fx/compiled db (fx/user db :uma) raw)]
    (is (= 4 (count allowed)) "id, member, organisation, notes")
    (is (empty? denied)))
  (let [db *db*
        raw (vec (d/datoms db :eavt (fx/assignment db "asg-uma")))]
    (is (empty? (:allowed (attrs/readable-datoms fx/compiled db (fx/user db :yara) raw)))
        "a user from the other organisation receives nothing")))

(deftest org-asymmetry-holds-for-datoms-too
  (let [db *db*
        datom [(fx/org db "Acme") :organisation/name "Acme"]]
    (is (= [datom] (:allowed (attrs/readable-datoms fx/compiled db (fx/user db :mia) [datom]))))
    (is (= :authz/not-authorized
           (-> (attrs/readable-datoms fx/compiled db (fx/user db :mark) [datom])
               :denied first :reason))
        "managers don't get org datoms — same asymmetry as org :view")))

;; ---------------------------------------------------------------------------
;; Sync up: writes to existing entities

(deftest write-checks-on-existing-entities
  (let [db *db*
        asg (fx/assignment db "asg-uma")
        check (fn [user-key tx] (attrs/check-tx fx/compiled db (fx/user db user-key) tx))]
    (testing "the assignee may write notes (list, map and cas forms)"
      (is (:allowed? (check :uma [[:db/add asg :assignment/notes "done"]])))
      (is (:allowed? (check :uma [{:db/id asg :assignment/notes "done"}])))
      (is (:allowed? (check :uma [[:db/cas asg :assignment/notes "start" "done"]])))
      (is (:allowed? (check :uma [[:db/retract asg :assignment/notes "start"]])))
      (is (:allowed? (check :uma [[:db/retract asg :assignment/notes]]))
          "2-arity retract"))
    (testing "a viewer may not write"
      (is (= {:authz/not-authorized #{:assignment/notes}}
             (denials (check :mark [[:db/add asg :assignment/notes "hi"]])))))
    (testing "a stranger may not write"
      (is (not (:allowed? (check :vic [[:db/add asg :assignment/notes "hi"]])))))
    (testing "declared read-only attrs reject writes for everyone"
      (is (= {:authz/attr-not-writable #{:assignment/member}}
             (denials (check :alice [[:db/add asg :assignment/member (fx/user db :vic)]])))))
    (testing "undeclared attrs reject writes for everyone"
      (is (= {:authz/undeclared-attr #{:user/email}}
             (denials (check :sam [[:db/add (fx/user db :uma) :user/email "new@x"]])))))
    (testing "lookup refs work for entity and subject"
      (is (:allowed? (attrs/check-tx fx/compiled db [:user/email "uma@x"]
                                     [[:db/add [:assignment/id "asg-uma"]
                                       :assignment/notes "via lookup"]])))
      (is (= #{:authz/invalid-tx}
             (set (keys (denials (check :uma [[:db/add [:assignment/id "nope"]
                                               :assignment/notes "x"]])))))
          "an unresolvable lookup ref cannot even apply speculatively"))
    (testing "a tx that Datomic itself would reject is denied, not passed through"
      (is (= #{:authz/invalid-tx}
             (set (keys (denials (check :uma [[:db/add asg :assignment/notes 123]])))))
          "wrong value type")
      (is (= #{:authz/invalid-tx}
             (set (keys (denials (check :uma [[:db/cas asg :assignment/notes
                                               "wrong-old" "new"]])))))
          "cas mismatch"))))

(deftest upserts-are-checked-as-writes-not-creations
  ;; The attack: a unique-identity attr in a "new" entity map makes Datomic
  ;; upsert onto the existing entity. The create rule alone would pass
  ;; (vic names himself as submitter), but the resulting datoms hit sub-uma.
  (let [db *db*
        uma (fx/user db :uma)
        acme (fx/org db "Acme")]
    (testing "hostile upsert is denied through write checks"
      (let [report (attrs/check-tx fx/compiled db (fx/user db :vic)
                                   [{:submission/id "sub-uma"
                                     :submission/submitted-by (fx/user db :vic)
                                     :submission/content "hax"}])]
        (is (not (:allowed? report)))
        (is (contains? (denials report) :authz/not-authorized))))
    (testing "the owner re-sending their full entity map is a no-op and allowed"
      (is (:allowed? (attrs/check-tx fx/compiled db uma
                                     [{:submission/id "sub-uma"
                                       :submission/submitted-by uma
                                       :submission/organisation acme
                                       :submission/content "uma's work"}]))))
    (testing "the owner re-sending with changed content is one checked write"
      (let [report (attrs/check-tx fx/compiled db uma
                                   [{:submission/id "sub-uma"
                                     :submission/submitted-by uma
                                     :submission/organisation acme
                                     :submission/content "revised offline"}])]
        (is (:allowed? report))
        (is (= 2 (:ops report)) "assert + retract of the old value")))))

;; ---------------------------------------------------------------------------
;; Sync up: creation

(deftest terminal-create-rule-binds-to-the-subject
  (let [db *db*
        uma (fx/user db :uma)
        acme (fx/org db "Acme")
        new-sub (fn [submitter] {:db/id "new-sub"
                                 :submission/id "sub-new"
                                 :submission/submitted-by submitter
                                 :submission/organisation acme
                                 :submission/content "offline work"})]
    (is (:allowed? (attrs/check-tx fx/compiled db uma [(new-sub uma)]))
        "you may create a submission you submit yourself")
    (is (= :authz/create-denied
           (-> (attrs/check-tx fx/compiled db (fx/user db :mark) [(new-sub uma)])
               :denied first :reason))
        "even Uma's manager may not submit as Uma")
    (is (not (:allowed? (attrs/check-tx fx/compiled db uma
                                        [(new-sub (fx/user db :vic))])))
        "nor may Uma submit as someone else")))

(deftest chain-create-rule-requires-permission-on-the-target
  (let [db *db*
        new-res (fn [org] {:resource/title "New Doc" :resource/organisation org})]
    (testing "org admins create resources in their org"
      (is (:allowed? (attrs/check-tx fx/compiled db (fx/user db :alice)
                                     [(new-res (fx/org db "Acme"))])))
      (is (:allowed? (attrs/check-tx fx/compiled db (fx/user db :bob)
                                     [(new-res (fx/org db "Beta"))]))))
    (testing "members and other-org admins do not"
      (is (not (:allowed? (attrs/check-tx fx/compiled db (fx/user db :mia)
                                          [(new-res (fx/org db "Acme"))]))))
      (is (not (:allowed? (attrs/check-tx fx/compiled db (fx/user db :alice)
                                          [(new-res (fx/org db "Beta"))])))))
    (testing "the chain relation must be present"
      (is (= :authz/create-denied
             (-> (attrs/check-tx fx/compiled db (fx/user db :alice)
                                 [{:resource/title "Orphan"}])
                 :denied first :reason)))
      (is (contains? (denials (attrs/check-tx fx/compiled db (fx/user db :alice)
                                              [{:resource/title "X"
                                                :resource/organisation "tmp-org"}]))
                     :authz/invalid-tx)
          "a tempid used only in value position is refused by Datomic itself"))))

(deftest create-chains-may-target-entities-created-in-the-same-tx
  (let [db *db*
        alice (fx/user db :alice)
        acme (fx/org db "Acme")]
    (testing "folder and subfolder in one tx, explicit tempids"
      (is (:allowed? (attrs/check-tx fx/compiled db alice
                                     [{:db/id "A" :folder/name "A" :folder/organisation acme}
                                      {:db/id "B" :folder/name "B" :folder/parent "A"}]))))
    (testing "nested entity maps work the same way"
      (is (:allowed? (attrs/check-tx fx/compiled db alice
                                     [{:folder/name "Outer"
                                       :folder/parent {:folder/name "Inner"
                                                       :folder/organisation acme}}]))))
    (testing "authority still comes from outside the tx"
      (let [mia (fx/user db :mia)]
        (is (not (:allowed? (attrs/check-tx fx/compiled db mia
                                            [{:db/id "A" :folder/name "MA"
                                              :folder/organisation acme}
                                             {:db/id "B" :folder/name "MB"
                                              :folder/parent "A"}])))
            "the root folder fails mia's create rule, so the subfolder's
             speculative grant never becomes authority")
        (is (not (:allowed? (attrs/check-tx fx/compiled db mia
                                            [{:folder/name "M"
                                              :folder/parent (fx/folder db "Root")}])))
            "and chaining to an existing folder is judged on db-before")))
    (testing "and-create-rule: own docs in orgs you can view"
      (let [mia (fx/user db :mia)]
        (is (:allowed? (attrs/check-tx fx/compiled db mia
                                       [{:doc/title "Mia's doc" :doc/owner mia
                                         :doc/organisation acme :doc/status :draft}])))
        (is (not (:allowed? (attrs/check-tx fx/compiled db mia
                                            [{:doc/title "Sock" :doc/owner alice
                                              :doc/organisation acme}])))
            "both and-branches must hold: mia is not the owner here")
        (is (not (:allowed? (attrs/check-tx fx/compiled db (fx/user db :uma)
                                            [{:doc/title "U" :doc/owner (fx/user db :uma)
                                              :doc/organisation (fx/org db "Beta")}])))
            "owner alone is not enough without :view on the org")))))

(deftest creation-attr-rules
  (let [db *db*
        alice (fx/user db :alice)
        acme (fx/org db "Acme")
        uma (fx/user db :uma)]
    (testing "create-settable covers writable + rule relations + :create? overrides"
      (is (:allowed? (attrs/check-tx fx/compiled db alice
                                     [{:assignment/id "asg-2"
                                       :assignment/member uma
                                       :assignment/organisation acme
                                       :assignment/notes "fresh"}]))))
    (testing "create-only attrs are frozen after creation"
      (is (= {:authz/attr-not-writable #{:submission/submitted-by}}
             (denials (attrs/check-tx fx/compiled db uma
                                      [[:db/add (fx/submission db "sub-uma")
                                        :submission/submitted-by (fx/user db :vic)]])))))
    (testing "types without a :create rule reject new entities"
      (is (= {:authz/no-create-rule #{:organisation/name}}
             (denials (attrs/check-tx fx/compiled db (fx/user db :sam)
                                      [{:organisation/name "Rogue Org"}])))))
    (testing "a new entity mixing attrs of two types is rejected"
      (is (contains? (denials (attrs/check-tx fx/compiled db alice
                                              [{:resource/title "T"
                                                :submission/content "C"}]))
                     :authz/ambiguous-entity-type)))
    (testing "undeclared attrs on new entities are rejected"
      (is (contains? (denials (attrs/check-tx fx/compiled db alice
                                              [{:resource/title "T"
                                                :resource/organisation acme
                                                :user/email "sneak@x"}]))
                     :authz/undeclared-attr)))
    (testing "dangling tempids in value position are rejected"
      (is (contains? (denials (attrs/check-tx fx/compiled db alice
                                              [{:assignment/id "asg-3"
                                                :assignment/member "ghost-user"
                                                :assignment/organisation acme}]))
                     :authz/invalid-tx)
          "Datomic refuses a tempid that never appears in entity position"))))

;; ---------------------------------------------------------------------------
;; Sync up: entity retraction and unsupported forms

(deftest retract-entity-follows-the-delete-rule
  (let [db *db*
        sub (fx/submission db "sub-uma")
        check (fn [user-key tx] (attrs/check-tx fx/compiled db (fx/user db user-key) tx))]
    (is (:allowed? (check :uma [[:db/retractEntity sub]])))
    (is (not (:allowed? (check :vic [[:db/retractEntity sub]]))))
    (is (not (:allowed? (check :alice [[:db/retractEntity sub]])))
        "submission :delete is :edit = submitted-by; even the org admin may not")
    (let [report (check :sam [[:db/retractEntity (fx/user db :uma)]])]
      (is (contains? (denials report) :authz/unknown-entity-type)
          "entities with no declared attrs cannot be retracted through this layer")
      (is (not (:allowed? report))))))

(deftest unsupported-and-malformed-forms-are-denied-not-ignored
  (let [db *db*
        check (fn [tx] (attrs/check-tx fx/compiled db (fx/user db :alice) tx))]
    (is (contains? (denials (check [[:my.custom/tx-fn 1 2]])) :authz/unsupported-op)
        "arbitrary tx functions are refused before speculative execution")
    (is (contains? (denials (check ["not a tx form"])) :authz/unsupported-op))
    (is (not (:allowed? (check [{:db/id "datomic.tx" :resource/title "smuggled"}])))
        "client-supplied tx metadata is not silently waved through")
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"unknown subject"
                          (attrs/check-tx fx/compiled db [:user/email "ghost@x"] [])))))

;; ---------------------------------------------------------------------------
;; End to end: the offline round-trip

(deftest authorize-tx!-guards-the-write-path
  (let [conn (fx/fresh-conn)
        db (d/db conn)
        uma (fx/user db :uma)
        tx [{:submission/id "sub-offline"
             :submission/submitted-by uma
             :submission/organisation (fx/org db "Acme")
             :submission/content "written on the plane"}]]
    (testing "allowed tx passes through unchanged and transacts"
      (is (identical? tx (attrs/authorize-tx! fx/compiled db uma tx)))
      (let [{:keys [db-after]} @(d/transact conn (attrs/authorize-tx! fx/compiled db uma tx))
            sub (d/entid db-after [:submission/id "sub-offline"])]
        (is (some? sub))
        (testing "and the new datoms sync down to the right people only"
          (let [raw (vec (d/datoms db-after :eavt sub))]
            (is (= 4 (count (:allowed (attrs/readable-datoms fx/compiled db-after
                                                             (fx/user db-after :mark) raw)))))
            (is (empty? (:allowed (attrs/readable-datoms fx/compiled db-after
                                                         (fx/user db-after :vic) raw))))))))
    (testing "denied tx throws with the full report"
      (let [bad [[:db/add (fx/assignment db "asg-uma") :assignment/notes "hax"]]
            e (try (attrs/authorize-tx! fx/compiled db (fx/user db :vic) bad)
                   nil
                   (catch clojure.lang.ExceptionInfo e e))]
        (is (some? e))
        (is (:authz/denied (ex-data e)))
        (is (= 1 (count (:denied (ex-data e)))))))))

;; ---------------------------------------------------------------------------
;; :db/retractEntity component cascades: the parent's :delete covers the
;; retraction datoms of its :db/isComponent closure — and nothing else

(def ^:private cascade-schema-extras
  [{:db/ident :order/id :db/valueType :db.type/string
    :db/cardinality :db.cardinality/one :db/unique :db.unique/identity}
   {:db/ident :order/owner :db/valueType :db.type/ref
    :db/cardinality :db.cardinality/one}
   {:db/ident :order/lines :db/valueType :db.type/ref
    :db/cardinality :db.cardinality/many :db/isComponent true}
   {:db/ident :line/sku :db/valueType :db.type/string
    :db/cardinality :db.cardinality/one}
   {:db/ident :line/note :db/valueType :db.type/ref
    :db/cardinality :db.cardinality/one :db/isComponent true}
   {:db/ident :note/text :db/valueType :db.type/string
    :db/cardinality :db.cardinality/one}])

(def ^:private cascade-registry
  ;; line attrs are READ-ONLY and :line has no :delete rule; :note is not
  ;; even in the registry — deleting an order must still cascade cleanly
  (schema/compile-schema
   {:user {}
    :order {:relations {:order/owner :user}
            :permissions {:own :order/owner}
            :delete :own
            :attrs {:order/id {:read :own}
                    :order/owner {:read :own}
                    :order/lines {:read :own}}}
    :line {:relations {:order/_lines :order}
           :permissions {:view '(-> :order/_lines :own)}
           :attrs {:line/sku {:read :view}
                   :line/note {:read :view}}}}))

(defn- cascade-world []
  (let [conn (fx/empty-conn)]
    @(d/transact conn cascade-schema-extras)
    @(d/transact conn
       [{:db/id "ada" :user/name "CAda" :user/email "c-ada@x"}
        {:db/id "eve" :user/name "CEve" :user/email "c-eve@x"}
        {:db/id "o1" :order/id "o1" :order/owner "ada"
         :order/lines [{:line/sku "sku-1"
                        :line/note {:note/text "note-1"}}
                       {:line/sku "sku-2"}]}
        {:db/id "o2" :order/id "o2" :order/owner "eve"
         :order/lines [{:line/sku "sku-3"}]}])
    (d/db conn)))

(deftest retract-entity-cascades-under-the-parents-delete
  (let [db (cascade-world)
        ada (d/entid db [:user/email "c-ada@x"])
        eve (d/entid db [:user/email "c-eve@x"])
        o1 (d/entid db [:order/id "o1"])
        o2 (d/entid db [:order/id "o2"])
        l3 (:db/id (first (:order/lines (d/entity db o2))))]
    (testing "the owner's :delete covers the whole component closure,
              two levels deep, with read-only line attrs and :note not
              even in the registry"
      (is (:allowed? (attrs/check-tx cascade-registry db ada
                                     [[:db/retractEntity o1]]))))
    (testing "the :delete rule still gates the parent itself"
      (let [report (attrs/check-tx cascade-registry db eve
                                   [[:db/retractEntity o1]])]
        (is (not (:allowed? report)))
        (is (= #{:authz/not-authorized} (into #{} (map :reason) (:denied report))))))
    (testing "reachability guard: a bundled retraction of an UNRELATED
              entity's attr gets no inherited authority"
      (is (not (:allowed? (attrs/check-tx cascade-registry db ada
                                          [[:db/retractEntity o1]
                                           [:db/retract l3 :line/sku "sku-3"]])))))
    (testing "additions bundled onto a deleted entity are ordinary writes,
              not covered by :delete"
      (is (not (:allowed? (attrs/check-tx cascade-registry db ada
                                          [[:db/retractEntity o1]
                                           [:db/add o1 :order/id "hax"]])))))))
