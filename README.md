# authz

Relationship-based access control (ReBAC) for Datomic, in the spirit of
Google Zanzibar / SpiceDB / OpenFGA, with one key twist: **permissions are
never materialized or checked by walking a graph at runtime — they compile
into Datalog `:where` clauses** that get spliced into ordinary application
queries. Authorization is evaluated by the database itself, in the same
query that fetches the data, against the same consistent snapshot.

On top of the query layer, an **attribute-level allow layer** makes the same
schema usable in occasionally-connected systems: filter datoms before
syncing them down to offline clients, and authorization-check transactions
those clients send back up.

See `authz-overview.md` for the conceptual background this reproduces.

## Setup

Tooling is managed with [mise](https://mise.jdx.dev):

```sh
mise install     # java (temurin-21) + clojure + bun/node (docs site)
mise run test    # full test suite (in-memory Datomic, incl. generative tests)
mise run bench   # criterium benchmarks over a large generated world
mise run repl
```

See `ROADMAP.md` for what's done and what's next.

## Tutorial

`docs/` is a guided tutorial site (built on
[solidclj-docs](https://github.com/A-Helberg/solidclj)): every page shows a
real snippet file next to the value it returned when evaluated against an
in-memory Datomic — the displayed code and its result come from the same
file, so the tutorial cannot drift from the library. A snippet that throws
fails the docs build.

```sh
mise run docs        # everything: gen + css, then dev server on http://localhost:2080
mise run docs:build  # full release build
mise run docs:test   # render-smoke-test every page under happy-dom
```

(`docs:gen`, `docs:css` and `docs:watch` also exist as individual steps.)

## Defining a schema

A registry is a plain map of entity type → definition. Compile it **once**
(at startup, or at the top level) into an immutable schema value; every
permission is pre-compiled to Datalog there and nothing is re-walked at
query time.

```clojure
(require '[authz.schema :as schema])

(def registry
  {:user
   {:relations   {:site/_members :site}
    :permissions {:view '(-> :site/_members :view-members)}}

   :site
   {:relations   {:site/region   :region
                  :site/members  :user
                  :manager/_site :manager}
    :permissions {:view         '(or :site/members
                                     (-> :manager/_site :is-user)
                                     (-> :site/region :manage-members))
                  :view-members '(or (-> :manager/_site :is-user)
                                     (-> :site/region :manage-members))}}
   ...})

(def authz (schema/compile-schema registry))
```

### Relations

`<datomic-attribute> -> <target-type>`. A leading underscore on the
attribute name (`:manager/_site`) traverses the attribute in reverse
(from a site to the managers pointing at it) — no bidirectional schema
needed.

### Permissions

The check language:

| form | meaning |
|---|---|
| `:assignment/member` | terminal — the subject **is** the entity reached by this relation |
| `(-> <rel> <perm>)` | chain — follow the relation, then require `<perm>` on the target |
| `(or <check> ...)` | disjunction — any branch grants |
| `(and <check> ...)` | conjunction — all must hold |
| `(not <check>)` | exclusion — the subject must **not** satisfy the check |
| `(attr= <attr> <value>)` | condition — the object has `<attr>` = literal value |

Conditions and exclusions grant nothing by themselves — combine them under
`(and ...)` with a granting check:

```clojure
:view '(or :doc/owner
           (and :doc/viewers
                (attr= :doc/status :published)
                (not :doc/banned))
           (-> :doc/organisation :edit))
```

### Recursion

Permissions may reference themselves through chains — the classic folder
tree:

```clojure
:folder
{:relations   {:folder/parent :folder
               :folder/organisation :organisation}
 :permissions {:view '(or (-> :folder/organisation :view)
                          (-> :folder/parent :view))}}
```

Recursive permissions compile to named Datomic rules. Point checks
(`can?`, `explain`) work unchanged and terminate even on cyclic *data*
(A parent of B parent of A). For list queries, use `list-query*`, which
returns `{:where [...] :rules [...]}` — put `%` in your `:in` and pass the
rules:

```clojure
(let [{:keys [where rules]} (authz/list-query* schema :folder :view :user)]
  (d/q {:find '[?folder] :in '[$ % ?user]
        :where (into where my-clauses)}
       db rules user-eid))
```

`list-query` fails loudly for recursive permissions (and `list-query*`
works for every permission, with empty `:rules` when no recursion is
involved). Two things are enforced at compile time: every recursive
permission must be able to bottom out — some path must leave its cycle
(mutual recursion sharing one base case is fine) — and recursion through
`(not ...)` is rejected as non-stratified.

Semantics that are load-bearing and covered by tests:

- **Terminal = subject unification; chain first hop = fresh variable.**
  `'(-> :submission/submitted-by :view)` means "someone who may view the
  submitter", *not* "is the submitter" — even though the relation targets
  the subject's own type.
- **`or` compiles to `or-join`**, `not` to `not-join`, with the object and
  subject vars as join keys, so branches stay independent.
- **Groundedness**: every permission and every `or` branch must reference
  the subject through a terminal or chain not under `(not ...)` — a pure
  condition or exclusion is rejected at compile time.

### Fail-loud hygiene

`compile-schema` throws (ex-data has `:authz/schema-error`) on: unknown
relations/permissions/types, malformed or empty (unquoted) check bodies,
recursion that can never bottom out, recursion through negation,
ungrounded checks, terminals that unify the subject with more than one
type, attributes claimed by two types, and invalid `:attrs` / `:create` /
`:delete` declarations.

## The three primitives

authz never owns your query — it hands you one of three composable
artifacts, and you choose the driver:

```clojure
(require '[authz.core :as authz])

;; 1. Predicate — point check: write-path guards, single reads, or
;;    filtering a lazy walk of your own index when YOUR sort order matters
(authz/can? schema db :user user-eid :edit :organisation org-eid)

;; 2. Clauses — splice into your own query so the DB filters for you
(d/q {:find '[?assignment]
      :in   '[$ ?user]
      :where (into (authz/list-query schema :assignment :view :user)
                   '[[?assignment :assignment/organisation ?org] ...])}
     db user-eid)

;; 3. Source — lazy, deduplicated enumeration of authorized objects, the
;;    same shape as d/datoms, for when the permission graph is the
;;    cheapest index you have (huge sets, brutal selectivity). Composes
;;    like any seq; nothing is materialized ahead of consumption, even
;;    for recursive permissions.
(take 20 (authz/grants schema db :user user-eid :view :assignment))
```

There is also a watch-set for reactive invalidation — re-run pushed
queries when a tx touches any of these attrs, so permission changes
live-update:

```clojure
(authz/list-query-attrs schema :assignment :view)
;;=> #{:assignment/member :site/members :manager/site ...}
```

`list-query` binds `?<object-type>` and `?<subject-type>` (e.g.
`?assignment`, `?user`); query `:in` is uniformly `[$ ?user ?<object> ...]`.
Pass `{:object-var .. :subject-var ..}` to rename — required when object
and subject types coincide (e.g. listing users a user may view), where the
default names would collide.

`can?` is evaluated by direct index traversal (both endpoints are bound, so
this beats a Datalog query ~10–40x): cost-ordered branches, short-circuiting
on the first grant — "is the assignee" answers in ~1 µs without ever walking
the hierarchy. List queries keep the compiled Datalog; the generative
differential suite holds both strategies to identical answers. `explain`
uses the same machinery to answer *why*:

```clojure
(authz/explain schema db :user vic-eid :view :doc doc-eid)
;;=> {:granted? true :via (and :doc/viewers (attr= :doc/status :published) (not :doc/banned))}
;;   or {:granted? false :tried [<every branch evaluated>]}
```

`grants` enumerates by direct index traversal outward from the subject —
no Datalog query runs, so unlike `list-query` the full result set is never
materialized: "page 3 of the 500k things this user may view" costs what it
takes to walk there, not to compute all 500k. Its order is deterministic
for a given db basis (that's what makes cursors work), but it is a
traversal order, not a domain sort order — when you need *your* order,
drive from your own index and filter with `can?`. For UI ergonomics,
`grants-page` wraps it in a page envelope with a plain-data cursor:

```clojure
(authz/grants-page schema db :user user-eid :view :assignment {:limit 20})
;;=> {:data [eid ...]
;;    :cursor {:authz/cursor true :basis-t 1234 :eid 17592186045424 ...}}

;; next page — against the same basis (hold the db value, or as-of the
;; cursor's basis-t); mismatched basis/subject/permission fails loudly
(authz/grants-page schema (d/as-of db (:basis-t cursor))
                   :user user-eid :view :assignment
                   {:limit 20 :after cursor})
;; a nil :cursor means the enumeration is complete
```

The cursor is transparent data and contains eids — wrap or sign it at
your trust boundary if it leaves your system. Counting a full authorized
set is just `(count (grants ...))`.

There is also `filter-authorized`, a batched `can?` (one query for any
number of entities) — the attribute layer is built on it — and
`authz.cache`, a *sound* point-check cache: results are keyed by
`[basis-t subject perm type object]`, and since db values are immutable a
cached result can never go stale. No TTLs, no invalidation protocol.

```clojure
(def c (cache/make-cache))
(cache/can? c schema db :user user-eid :edit :organisation org-eid)
```

## Attribute-level allow (offline / occasionally-connected)

Each type may declare which attributes clients can read and write, gated by
the type's own permissions — plus rules for creating and deleting whole
entities:

```clojure
:assignment
{:relations   {...}
 :permissions {:view '(or :assignment/member (-> :assignment/member :view))
               :react :assignment/member
               :edit '(-> :assignment/organisation :edit)}
 :create      '(-> :assignment/organisation :edit) ; who may create one
 :delete      :edit                                ; perm gating :db/retractEntity
 :attrs       {:assignment/id     {:read :view :create? true}
               :assignment/notes  {:read :view :write :react}
               :assignment/member {:read :view :create? true}}}
```

Everything is **deny-by-default**: an attribute not declared in any `:attrs`
section can neither be synced down nor written by a client. Relationship
and role attributes (admins, managerships) therefore stay server-managed
unless you explicitly open them up.

### Sync down — filtering datoms

```clojure
(require '[authz.attrs :as attrs])

;; e.g. tail the tx-report-queue and fan datoms out per connected client:
(attrs/readable-datoms schema db user-eid datoms)
;;=> {:allowed [...] :denied [{:datom .. :reason :authz/not-authorized} ...]}
```

Accepts raw `datomic.Datom`s (numeric attr ids), maps, or `[e a v]` vectors.
Checks are batched: one query per (type, read-permission) pair regardless of
how many datoms come in.

### Sync up — checking client transactions

```clojure
(attrs/check-tx schema db user-eid tx-data)
;;=> {:allowed? false :denied [{:e .. :a .. :v .. :reason .. :message ..}] :ops 7}

;; or as a guard that threads straight into transact:
@(d/transact conn (attrs/authorize-tx! schema db user-eid tx-data))
```

The transaction is applied **speculatively with `d/with`** and the *actual
resulting datoms* are checked, not the tx forms. Datomic therefore handles
map expansion, nested maps, reverse attributes, cardinality, lookup refs
and — crucially — **upserts**: a tempid that resolves to an existing entity
through a unique-identity attribute is checked as a *write* to that entity,
never as a creation. No-op re-assertions produce no datoms, so offline
clients can re-send whole entity maps for free. Arbitrary transaction
functions are refused *before* the speculative apply (`:db/cas` is the
sanctioned exception); a tx Datomic itself would reject is denied as
`:authz/invalid-tx`.

**Authority is anchored in db-before**: writes to existing entities and
create-chains to existing entities are judged against the pre-transaction
snapshot, so a tx cannot grant itself permissions and use them in the same
breath.

**New entities** are governed by the type's `:create` rule — the same check
language, evaluated against the new entity's own datoms:

- terminal `:submission/submitted-by` — that relation's value must be the
  subject ("you may create a submission you submit yourself")
- chain `(-> :resource/organisation :edit)` — the subject needs `:edit` on
  the entity the relation points at. The target may itself be created in
  the same transaction (create a folder *and* its subfolder together): it
  must pass its own `:create` rule, and the permission is then judged on
  the speculative snapshot.
- `(and ...)`, `(or ...)` and `(attr= ...)` compose as usual; `(not ...)`
  is not supported in create rules.

Attributes settable at creation = writable attrs ∪ the create rule's own
relations, plus/minus explicit `{:create? true/false}` overrides. So
`:submission/submitted-by` above is settable when creating but frozen
afterwards, without extra configuration.

`:delete` names a permission on the same type that gates
`:db/retractEntity`; the entity's type is inferred from its declared
attributes.

Point checks are batched per (type, permission) pair, and
`can-read-attr?` / `can-write-attr?` exist for one-off checks.

## Design notes

- The compiled schema is a first-class immutable value — no global registry
  atom. Compile once, pass it around, swap it atomically on deploy.
- Compilation is deterministic: same registry, same value (intermediate
  query vars are counter-named, e.g. `?site-1`), which also means Datomic's
  by-value query cache hits on every call.
- `list-query-attrs` over-approximates (any touched attr invalidates),
  which is safe for reactive layers but may cause spurious re-runs.
  `attr=` conditions join the watch-set, so a status flip re-runs
  subscriptions.
- Subject types are inferred from terminals at compile time and checked
  loudly at call time, so `(can? .. :site ..)` with the wrong subject type
  throws instead of silently returning false.
- The semantics is a specification, not folklore: [SEMANTICS.md](SEMANTICS.md)
  defines the check language as stratified least-fixed-point (Datalog)
  semantics, and every evaluation strategy in the library is *held to*
  it. The bottom-up fixpoint evaluator in
  `test/authz/fixpoint_oracle.clj` implements that document directly and
  serves as the executable spec; the Isabelle/HOL formalization under
  [`verification/`](verification/) mechanizes it. Precisely stated:
  **every theorem in the spec's proof-obligation list is machine-checked,
  in one sorry-free session** — the semantics' well-definedness,
  finiteness from groundedness, the characterization theorem,
  stratification-independence, walker correctness in full (soundness
  and completeness of the visited-set walker that powers
  `can?`/`explain`), and enumeration exactness in full (generation
  completeness, exactness of the pure-closure fast path, and the
  verified-filter capstone for `grants`). The Datalog-compilation path
  rests on the differential suite permanently (its consumer is
  Datomic's query engine), and the models' fidelity to the Clojure —
  the ~10-line index adapter and emission order — is what the
  differential suite pins in CI. See `verification/README.md` for the
  exact claims boundary.
- Correctness is defended four ways: an exhaustive fixture with
  hand-computed grant sets; a black-box functional suite
  (`functional_test.clj`) that exercises only the public API against its own
  self-contained domain — registry and world in, behavior out;
  generative differential tests — seeded random worlds where every
  strategy (compiled Datalog, the point-check walker, and the `grants`
  enumeration) must agree with two independent oracles (the top-down
  reference interpreter and the bottom-up fixpoint spec) on every
  (subject, permission, object) triple; and the machine-checked
  semantics above (`mise run verify`). CI runs all
  of it on GitHub
  Actions (`.github/workflows/ci.yml`), including a smoke test of the
  benchmark harness (each scenario executed once, no criterium timing).

## Layout

```
SEMANTICS.md            the specification: stratified LFP semantics of the check language
verification/           Isabelle/HOL mechanization (mise run verify); see its README
src/authz/schema.clj    registry validation + compilation to Datalog
src/authz/core.clj      can? / explain / filter-authorized / list-query(-attrs) / grants(-page)
src/authz/attrs.clj     attribute allow layer: readable-datoms / check-tx
src/authz/cache.clj     basis-t keyed (sound) point-check cache
test/authz/fixture.clj  shared domain world (hierarchy, managers, content)
test/authz/*_test.clj   hygiene, compilation shape, semantics, offline flows
test/authz/functional_test.clj  black-box suite over the public API only
test/authz/fixpoint_oracle.clj  the executable spec (bottom-up stratified LFP)
test/authz/reference.clj + worldgen.clj + generative_test.clj  differential harness
test/authz/bench_test.clj  benchmark-harness smoke test (runs in CI)
bench/authz/bench.clj   criterium benchmarks (mise run bench)
```
