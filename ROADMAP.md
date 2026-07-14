# Roadmap

Improvement ideas for the authz library, most stolen from or inspired by
Google Zanzibar (and its descendants SpiceDB / OpenFGA), adapted to this
library's compile-to-query architecture.

A guiding observation: Zanzibar's zookie protocol exists to keep checks
consistent with the content they protect. Because we splice authorization
into the same Datomic query on the same immutable `db` value, the online
path gets that consistency for free. The offline path re-opens the problem
— several items below are about closing it there.

## Done

- **Compile once, immutable schema value** — no per-call recompilation, no
  global registry atom. (`authz.schema/compile-schema`)
- **Batched checks** — `filter-authorized` (one query for N entities); the
  attribute layer groups by (type, permission) pair. (`authz.core`,
  `authz.attrs`)
- **Deterministic compilation → Datomic query-cache hits** — identical
  clause values on every call, counter-named intermediates.
- **Deny-by-default attribute layer** for occasionally-connected clients:
  `readable-datoms` (sync down), `check-tx`/`authorize-tx!` (sync up),
  `:create`/`:delete` rules.
- **Intersection & exclusion** (Zanzibar userset rewrites): `(and ...)` and
  `(not ...)` (compiles to `not-join`), with groundedness validation so
  every `or` branch still binds subject and object.
- **Caveats / attribute conditions** (SpiceDB caveats): `(attr= <attr>
  <value>)`, e.g. status = published, evaluated in-query and included in
  the reactive watch-set.
- **Short-circuiting point checks** (Zanzibar cheap-branch-first): `can?`
  and `explain` evaluate cost-ordered branches by **direct index traversal**
  rather than d/q — short-circuiting between *and inside* branches. Measured
  ~40x on terminal hits, ~10x on deep chains/denials vs the query path.
  List queries keep the compiled `or-join`; the generative differential
  suite holds walker and clause compiler to identical answers.
- **Explain API** (Zanzibar Expand, the "why" half): `explain` reports
  which branch granted, or every branch tried on denial.
- **Sound check caching** (Zanzibar's TTL caches, made exact): results
  keyed by `[basis-t subject perm type object]` can never go stale because
  db values are immutable. (`authz.cache`)
- **Speculative `d/with` transaction checking** (contextual tuples,
  Datomic-native): `check-tx` applies the client tx speculatively and
  checks the *actual* resulting datoms. Fixes the upsert bypass (a
  unique-identity tempid resolving to an existing entity is now checked as
  a write, not a create); supports create-chains targeting entities created
  in the same tx; makes no-op resends of full entity maps free. Authority
  is always anchored in db-before.
- **Benchmarks** (`mise run bench`) and **generative differential tests**
  (random worlds checked against a naive graph-walking reference
  implementation).

- **Recursive permissions via Datalog rules** (Zanzibar's nested-groups /
  Leopard motivation, solved natively): permissions may reference
  themselves through chains (folder inherits `:view` from parent folder).
  Cyclic SCCs compile to named Datomic rules; `list-query*` returns
  `{:where :rules}` (`list-query` fails loudly for recursive perms);
  the point-check walker and the reference interpreter terminate on cyclic
  *data* via path-scoped visited sets. Validated at compile time: every
  recursive permission must be able to bottom out (fixpoint over the SCC),
  and recursion through `(not ...)` is rejected as non-stratified.

- **Cursor-paginated enumeration — the third primitive** (Zanzibar/SpiceDB
  lookup-resources, as a composable seq): `list-query` splices into
  Datalog, which eagerly materializes its full result set — it cannot
  serve page 3 of a 500k-row authorized set without computing all 500k.
  `grants` enumerates instead: a lazy, deduplicated stream of authorized
  object eids in the same shape as `d/datoms`, completing the primitive
  set — **clauses** (`list-query`), **predicate** (`can?`, still the
  right driver when the consumer's own sort order matters), **source**
  (`grants`, for when the permission graph is the cheapest index
  available). Mechanism: a deterministic depth-first traversal of the
  permission's generating dependency closure, outward from the subject
  over the walker's indexes, with request-local dedupe; recursive
  closures enumerate without being materialized, and `and`/`not`/`attr=`
  permissions verify each candidate through the point-check walker.
  `grants-page` adds the page envelope: plain-data cursors (basis +
  position, transparent by design — wrap at your trust boundary),
  validated fail-loud against basis/subject/permission/type; resume
  replays the traversal prefix. Counting is `(count (grants ...))`. The
  generative differential suite holds `grants` to reproducing the full
  `list-query` result set on every random world.

- **The semantics as a specification, with two oracles and a
  mechanization** (Cedar-style verification-guided development):
  SEMANTICS.md defines the check language as stratified
  least-fixed-point semantics — every implicit decision (terminal
  unification, fresh chain variables, sticky negative polarity, safety
  as range-restriction, types as schema-level) written down. Two
  independent oracles hold every strategy to it: the existing top-down
  reference interpreter and a new bottom-up fixpoint evaluator
  (`fixpoint_oracle.clj`) that implements the spec literally — different
  strategy, shared blind spots eliminated. The Isabelle/HOL sessions
  under `verification/` mechanize the semantics; machine-checked so far:
  satisfaction invariance and monotonicity, per-stratum operator
  monotonicity (so the least fixed points exist), strata growth and
  stability, and a grounding sanity theorem. `mise run verify`
  re-checks the proofs.

- **The verified kernel, exported to Scala and cross-checked from
  Clojure** — the full Cedar-style pipeline, closed: an executable
  bottom-up evaluator (early-exit fixpoint iteration proven equal to the
  lfp via chain stabilization in a finite fact space; executable
  stratified/safe checkers proven equivalent to the spec predicates, so
  bad input gets None, never a wrong answer) with `kernel_correct`
  machine-checked, `export_code`d as a Scala module, compiled to
  `verification/export/authz-kernel.jar` (`mise run kernel:build`), and
  cross-checked against `can?` from `test/authz/kernel_test.clj` in the
  regular suite. All proof obligations from SEMANTICS.md are
  **discharged and machine-checked** in the single sorry-free session:
  well-definedness, finiteness-from-safety, the characterization
  theorem, the Kleene/rank tower, Obligation W, Obligation E, and
  stratification-independence.

- **Random registries in the generative suite.** Seeded random
  permission schemas (registrygen.clj: valid by construction without
  narrowing the space — cross-type chains, self-recursion with base
  cases, negated terminals/conditions/chains, and/attr= mixing,
  same-type collision via a reverse-relation user permission) plus
  random worlds over them; every strategy must agree with both oracles
  on every triple (generative_registry_test.clj). Plus test.check
  shrinking (registry_prop_test.clj): generators emit a plain-data
  recipe and a total builder turns any recipe -- including every shrunk
  mutation -- into a valid bundle, so failures minimize genuinely
  (verified: a planted failure shrank to two types, one user, one
  entity, one negated chain). One builder serves both front doors (the
  seeded generator synthesizes recipes), and generates all three
  recursion shapes: self (:p1 via parent), same-type mutual (:p1/:p2
  twins), and cross-type mutual (pm/pmb pairs over fresh relations both
  ways, added after all negation targets are chosen so negation through
  a cycle is impossible by construction).

- **Named rules for non-recursive permissions** — measured, shipped as
  an option, inline kept as the default. `list-query*` with
  `{:all-rules? true}` compiles every permission to a named Datomic rule
  (one invocation as :where, a definition per reachable permission as
  :rules); held to both oracles as a sixth strategy in every
  differential suite. Benchmark on the 2000-user world: the cheap site
  listing gets ~35% slower under rules (0.60ms -> 0.81ms, indirection
  overhead dominates small queries) while the heavy submission listing
  gets ~20% faster (54.0ms -> 43.5ms, the shared user-:view subtree is
  evaluated once as a set instead of re-expanded per or-branch). Verdict:
  workload-dependent -- default stays inline, use the option where large
  queries share subtrees, re-measure on your data (`mise run bench` has
  side-by-side scenarios).

## Next
- **Sync tokens for the offline path (zookies).** Stamp every sync-down
  batch with `d/basis-t`; clients echo the last basis-t they saw. Lets the
  server detect revocations between sync points ("re-filter everything
  since t") instead of trusting the client's stale view. Design a
  revocation-diff API: given (subject, db-from, db-to), which previously
  synced datoms are no longer readable?
- **Schema version tokens.** Offline clients cache the attr allow-list; a
  version stamp (hash of the compiled schema) lets them detect that their
  cached notion of "what I may edit" is outdated.
- **Finer-grained reactive invalidation.** `list-query-attrs`
  over-approximates: any touched watched attr re-runs the subscription.
  Given a tx datom `[e a v]`, a small connectivity probe could decide
  whether `e` is actually linked to the subscription's subject/object
  before re-running.
- **Statistics-based branch cost model.** Branch ordering currently uses a
  static pattern count. Sampling actual branch selectivity per deployment
  (or reading Datomic index stats) would order better; Zanzibar hedges
  requests — the analogue here is evaluating the two cheapest branches in
  parallel and cancelling.
- **Leopard-style transitive-closure materialization (opt-in,
  benchmark-gated).** For very deep hierarchies, maintain a flattened
  ancestor ref attr via a tx-listener pipeline. Violates the "no
  materialization" core semantic, so: last resort, behind real benchmark
  numbers, clearly opt-in.
- **`subjects-query` / expand API.** "Who has access to X?" — the reverse
  direction of `list-query` (bind the object, list subjects), plus a tree
  expansion for admin UIs. `explain` already covers the per-subject "why".
- **Seek-based cursor resume for `grants`.** Resuming an enumeration
  replays the traversal prefix (deterministic order makes this correct
  and simple), so page N costs O(pages 1..N). If paging depth ever shows
  up in benchmarks, investigate cursors that snapshot enough traversal
  state to seek — per-stream index positions rather than a last-emitted
  eid. More state in the cursor, more invariants to hold; benchmark
  first.
- **Parameterized caveats.** `attr=` covers literal conditions; SpiceDB
  caveats take request-time context (e.g. `ip-range`, `time-of-day`).
  Would need an args-passing convention through `can?`/`list-query`.
- **`:db/retractEntity` component cascades.** Retraction datoms of
  component entities are currently checked as ordinary writes on those
  entities; a `:delete`-rule-aware cascade policy would be friendlier.
