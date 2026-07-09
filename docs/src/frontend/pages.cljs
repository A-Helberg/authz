(ns frontend.pages
  "The tutorial's content. Each page shows a snippet file inlined at
  compile time (shadow.resource/inline) next to the value that exact file
  returned when evaluated on the JVM against in-memory Datomic
  (frontend.result) — the code you read is the code that produced the
  result, and a snippet that throws fails the docs build."
  (:require [shadow.resource :as rc]
            [frontend.result :as result]))

(def sections
  [{:title "Getting started"
    :pages
    [{:id    :welcome
      :title "What is authz?"
      :prose
      [:<>
       [:p "authz is relationship-based access control (ReBAC) for Datomic, in "
        "the spirit of Google Zanzibar — with one key twist: permissions are "
        [:strong "never checked by walking a graph at runtime"] ". They compile "
        "into Datalog " [:code ":where"] " clauses that get spliced into your "
        "ordinary application queries, so authorization is evaluated by the "
        "database itself, in the same query that fetches the data, against the "
        "same consistent snapshot."]
       [:p "On top of that sits an attribute-level allow layer for occasionally "
        "connected systems: filter datoms before syncing them down to offline "
        "clients, and authorization-check the transactions those clients send "
        "back up."]
       [:p "Every page of this tutorial is a real Clojure file, shown on the "
        "left exactly as it is on disk. The panel on the right is the value "
        "that file returned when it was evaluated against a real in-memory "
        "Datomic database. They are the same file — the docs cannot lie about "
        "what the library does, and an example that stops working stops the "
        "docs from building."]]}

     {:id    :world
      :title "The world"
      :prose
      [:<>
       [:p "One registry, one database, used by every page that follows. The "
        "registry is a plain map: each entity type declares its "
        [:strong "relations"] " (Datomic attributes connecting it to other "
        "types — a leading underscore traverses in reverse) and its "
        [:strong "permissions"] " (check expressions in a five-form language "
        "you'll meet one form at a time)."]
       [:p [:code "compile-schema"] " validates everything and returns an "
        "immutable value — compile once at startup, pass it around like a "
        [:code "db"] ". There is no global registry, no sync pipeline, no "
        "materialized permission tuples."]
       [:p "The cast: Acme has an org admin (ada), an org member (mia), a site "
        "with two members (uma, vic), and mark — who manages that site through "
        "a first-class manager entity. Zeta is a rival organisation that "
        "should never see any of it."]]
      :examples
      [{:source    (rc/inline "tutorial/world.clj")
        :component (result/view "tutorial/world.clj")}]}]}

   {:title "The check language"
    :pages
    [{:id    :terminals
      :title "Terminals"
      :prose
      [:<>
       [:p "A terminal is a relation keyword standing alone. It means the "
        "subject " [:em "is"] " the entity reached by that relation — subject "
        "and relation target unify."]
       [:p "Deny-by-default follows from the shape of the language: a "
        "permission grants exactly what its expression says, and nothing "
        "grants " [:code ":react"] " to anyone but the assignee."]]
      :examples
      [{:source    (rc/inline "tutorial/terminals.clj")
        :component (result/view "tutorial/terminals.clj")}]}

     {:id    :chains
      :title "Chains"
      :prose
      [:<>
       [:p "A chain " [:code "(-> <relation> <permission>)"] " follows the "
        "relation, then requires the permission on the target. This is how "
        "permissions cascade: grants compose across types, forming a graph."]
       [:p "The subtlety this page exists for: the chain's first hop binds a "
        [:strong "fresh variable"] ", never the subject — even when the "
        "relation targets the subject's own type. \"May view the assignee\" "
        "and \"is the assignee\" are different rules, and this is the line "
        "that keeps them different. It's what makes \"a manager sees their "
        "people's work, and only their people's work\" a one-line rule."]]
      :examples
      [{:source    (rc/inline "tutorial/chains.clj")
        :component (result/view "tutorial/chains.clj")}]}

     {:id    :disjunction
      :title "Disjunction & explain"
      :prose
      [:<>
       [:p [:code "(or ...)"] " — any branch grants. Branches compile "
        "independently (to " [:code "or-join"] " in list queries), and point "
        "checks evaluate them cheapest-first with short-circuiting."]
       [:p [:code "explain"] " is " [:code "can?"] " with its reasoning showing: "
        "the granting branch as written in your registry, or every branch "
        "tried on denial. Build your \"why can this user see this?\" support "
        "tooling on it."]]
      :examples
      [{:source    (rc/inline "tutorial/disjunction.clj")
        :component (result/view "tutorial/disjunction.clj")}]}

     {:id    :conditions
      :title "Conditions & exclusions"
      :prose
      [:<>
       [:p [:code "(attr= <attr> <value>)"] " conditions on the object's own "
        "state; " [:code "(not <check>)"] " excludes; " [:code "(and ...)"]
        " combines. Neither a condition nor an exclusion grants anything by "
        "itself — the compiler rejects a branch that never references the "
        "subject, so \"everyone except banned users\" cannot be written by "
        "accident."]
       [:p "Because checks read plain db values, \"what would visibility be "
        "if…\" is just " [:code "d/with"] " — no test doubles, no mocking."]]
      :examples
      [{:source    (rc/inline "tutorial/conditions.clj")
        :component (result/view "tutorial/conditions.clj")}]}

     {:id    :recursion
      :title "Recursion"
      :prose
      [:<>
       [:p "Permissions may reference themselves through chains — folder "
        "trees inherit from their parent, to any depth. Recursive permissions "
        "compile to named Datomic rules instead of inline clauses."]
       [:p "Two compile-time guarantees keep it safe: every recursive "
        "permission must be able to bottom out (some path must leave the "
        "cycle), and recursion through " [:code "(not ...)"] " is rejected as "
        "non-stratified. And at runtime, checks terminate even on cyclic "
        [:em "data"] " that hostile clients might create."]]
      :examples
      [{:source    (rc/inline "tutorial/recursion.clj")
        :component (result/view "tutorial/recursion.clj")}]}]}

   {:title "Consuming the schema"
    :pages
    [{:id    :point-checks
      :title "Point checks"
      :prose
      [:<>
       [:p "The write-path guard: " [:code "can?"] " before you transact. "
        "It evaluates by direct index traversal — cost-ordered branches, "
        "short-circuiting — so a terminal hit answers in about a microsecond "
        "and even deep hierarchy walks stay in the tens of microseconds."]
       [:p [:code "filter-authorized"] " batches any number of entities into "
        "one query, and " [:code "authz.cache"] " memoizes point checks keyed "
        "by " [:code "basis-t"] " — sound with no TTLs, because a Datomic db "
        "value can never change under a cached answer."]]
      :examples
      [{:source    (rc/inline "tutorial/point_checks.clj")
        :component (result/view "tutorial/point_checks.clj")}]}

     {:id    :list-queries
      :title "List queries"
      :prose
      [:<>
       [:p "The dominant pattern: splice " [:code "list-query"] "'s clauses "
        "into your own query so list endpoints only ever return rows the "
        "subject may see. Filtering happens inside the database, composed "
        "with your application filters, on one consistent snapshot — never "
        "post-hoc in application code."]
       [:p "The variable contract: clauses bind " [:code "?<object-type>"]
        " and " [:code "?user"] ", and your query's " [:code ":in"] " is "
        [:code "[$ ?user ...]"] ". Recursive permissions carry Datomic rules "
        "with them — " [:code "list-query*"] " returns "
        [:code "{:where ... :rules ...}"] " and you pass the rules as the "
        [:code "%"] " input."]]
      :examples
      [{:source    (rc/inline "tutorial/list_queries.clj")
        :component (result/view "tutorial/list_queries.clj")}]}

     {:id    :watch-set
      :title "The watch-set"
      :prose
      [:<>
       [:p "Reactive layers re-run server-pushed queries when a transaction "
        "touches an attribute they depend on. " [:code "list-query-attrs"]
        " contributes the authorization half of that watch-set: every "
        "attribute the permission reads, transitively through chains and "
        "conditions."]
       [:p "The contract this buys: any transaction that changes anyone's "
        "access necessarily touches the watch-set, so permission changes "
        "live-update subscribed clients — promote someone to manager and "
        "their new world streams in. (It over-approximates: a touched "
        "attribute may cause a re-run that finds nothing changed. Safe, "
        "occasionally wasteful.)"]]
      :examples
      [{:source    (rc/inline "tutorial/watch_set.clj")
        :component (result/view "tutorial/watch_set.clj")}]}]}

   {:title "Occasionally connected"
    :pages
    [{:id    :sync-down
      :title "Syncing down"
      :prose
      [:<>
       [:p "Each type may declare an " [:code ":attrs"] " allow-list gating "
        "its attributes with the type's own permissions. Everything is "
        "deny-by-default: an undeclared attribute never syncs and can never "
        "be written — which keeps role and relationship attributes "
        "server-managed unless you explicitly open them up."]
       [:p [:code "readable-datoms"] " filters a batch of datoms (from the "
        "tx-report queue, or an initial sync walk) down to what one subject "
        "may see. Checks are batched per (type, permission) pair, so a "
        "thousand-datom batch costs a handful of queries."]]
      :examples
      [{:source    (rc/inline "tutorial/sync_down.clj")
        :component (result/view "tutorial/sync_down.clj")}]}

     {:id    :sync-up
      :title "Syncing up"
      :prose
      [:<>
       [:p "When an offline client reconnects and sends a transaction, "
        [:code "check-tx"] " applies it " [:em "speculatively"] " with "
        [:code "d/with"] " and judges the actual resulting datoms — so "
        "Datomic handles map expansion, cardinality, lookup refs and "
        "upserts, and a tx can never grant itself permissions and use them "
        "in the same breath (authority is anchored in the pre-tx snapshot)."]
       [:p "Judging resulting datoms has two lovely consequences: the upsert "
        "attack below is caught as a write to the existing entity, and a "
        "client re-sending an unchanged entity map produces zero datoms — "
        "free resyncs. " [:code "authorize-tx!"] " is the throwing guard that "
        "threads straight into " [:code "d/transact"] "."]]
      :examples
      [{:source    (rc/inline "tutorial/sync_up.clj")
        :component (result/view "tutorial/sync_up.clj")}]}

     {:id    :creation
      :title "Creating & deleting"
      :prose
      [:<>
       [:p "New entities are governed by the type's " [:code ":create"]
        " rule — the same check language, read against the new entity's own "
        "tx-local datoms. A terminal means \"that relation's value must be "
        "you\" (create your own submissions); a chain means \"you need this "
        "permission on the entity it points at\" (create resources in orgs "
        "you edit). Chains may even target an entity created in the same "
        "transaction."]
       [:p "Attributes settable at creation default to the writable set plus "
        "the create rule's own relations (overridable per-attr with "
        [:code ":create?"] ") — so an owner ref can be set at birth and "
        "frozen afterwards with zero extra configuration. "
        [:code ":delete"] " names the permission gating "
        [:code ":db/retractEntity"] "."]]
      :examples
      [{:source    (rc/inline "tutorial/creation.clj")
        :component (result/view "tutorial/creation.clj")}]}]}

   {:title "Hygiene"
    :pages
    [{:id    :fail-loud
      :title "Failing loudly"
      :prose
      [:<>
       [:p "Authorization bugs should not be discovered in production — or "
        "worse, not discovered. " [:code "compile-schema"] " rejects every "
        "malformed registry at compile time with data-carrying errors: "
        "unknown references, checks that could never grant (or would grant "
        "everyone), recursion that can't bottom out, terminals that confuse "
        "subject types."]
       [:p "The same posture runs through the whole API: querying with the "
        "wrong subject type throws instead of returning false, "
        [:code "list-query"] " on a recursive permission points you at "
        [:code "list-query*"] ", and " [:code "check-tx"] " denies anything "
        "it doesn't positively understand."]]
      :examples
      [{:source    (rc/inline "tutorial/fail_loud.clj")
        :component (result/view "tutorial/fail_loud.clj")}]}]}])
