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

## Next

- **Discharge the last proof obligation**: stratification-independence
  (`verification/obligations/`, stated with a proof plan) — a
  robustness statement about the spec itself; every
  implementation-facing theorem is machine-checked. **Done, in the
  checked session**: finiteness-from-safety (`grants_finite`), the
  characterization theorem (`grants_iff_sat`), the Kleene/rank tower
  (`Authz_Kleene`), Obligation W in full — `walker_sound` +
  `walker_complete` (`Authz_Walker`; en route the naive fuel-free
  soundness statement was found to be false — fuel death under
  negation) — and Obligation E in full (`Authz_Enum`): generation
  completeness, exactness of the pure-closure fast path (retiring the
  code-comment argument in `authz.core`), and the verified-filter
  capstones. Then: an executable refinement of the spec exported to
  Scala for a runtime-checkable kernel (the bounded-iteration
  evaluator + proof it equals the lfp).
- **Random registries in the generative suite.** Worlds are generated;
  the registry is still the fixed fixture. Schema-space is where
  compilation bugs live (collision vars, SCC shapes, mutual recursion,
  not-under-and). Generate small random valid registries + worlds,
  ideally via test.check for shrinking.

- **Named rules for non-recursive permissions too.** Recursion forced the
  rule machinery into existence; emitting rules for *all* permissions
  (behind `list-query*`) would give Datomic named, reusable subtrees
  instead of giant inlined `or-join`s. Benchmark before switching.
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
