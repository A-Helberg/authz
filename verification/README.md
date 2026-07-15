# Machine-checked semantics

This directory mechanizes [SEMANTICS.md](../SEMANTICS.md) in
Isabelle/HOL. It exists so that the README's correctness claims can be
precise, and so that changes to the semantics are expensive on purpose.

## Claims discipline

One session, **`Authz`** (`checked/`), containing **no `sorry`** — every
theorem is machine-checked end to end, and only theorems in this
session may be described as "proven" anywhere in this repository. Every
proof obligation from SEMANTICS.md §5 that is dischargeable against the
model is discharged. (During development, stated-but-open theorems
lived in a separate `quick_and_dirty` session, `Authz_Obligations`, and
moved here only when their last `sorry` was gone; that session is
retired — recreate it if new obligations arise.)

## What is proven

- **The model** (`Authz_Syntax`): the check language, relation
  extensions, polarity-labelled dependencies, stratification, safety
  (groundedness), and the active domain.
- **Well-definedness** (`Authz_Semantics`): satisfaction invariance and
  monotonicity, per-stratum operator monotonicity (Knaster–Tarski gives
  the least fixed points), strata growth, stratum bounds, and key
  stability.
- **Safety implies finiteness** (`grants_finite`): for a grounded
  registry over a finite database every answer set is finite — the
  proven semantic content of the groundedness validator.
- **The characterization theorem** (`grants_iff_sat`): a permission
  holds exactly when its body is satisfied over the interpretation of
  all grants — the semantics satisfies its own equations.
- **Kleene iterates and derivation rank** (`Authz_Kleene`):
  satisfaction is finitary, each stratum is the union of its finite
  iterates, and every granted fact has a minimal derivation height with
  strictly descending same-stratum children.
- **Obligation W** (`Authz_Walker`): `walker_sound` and
  `walker_complete` — the visited-set walker computes `grants`
  (underwrites `can?`, `explain`, the reference interpreter, and the
  verification mode of `grants`). One well-founded induction on
  (fuel, check size) carries both directions simultaneously; the
  `vcond` invariant shows blocking a state a minimal derivation needs
  is *impossible*. Discovered en route: fuel-free soundness is false
  (fuel death inside a negation flips False to True), and the two
  directions are mutually recursive through negation.
- **Obligation E** (`Authz_Enum`): the gen-graph/gen-stream enumeration
  is exact. `cand_complete` (generation misses nothing),
  `cand_sound_pure` (the pure-closure fast path is exactly the grants —
  the implementation's unverified path, proven), and the
  `enum_spec` capstones (candidates filtered by the proven walker equal
  the answer set, distinct and finite). Emission order is abstracted;
  order-level behaviour stays with the differential suite.
- **Stratification-independence** (`Authz_Sigma`): `sigma_independent` —
  any two stratifications yield the same `grants`; the semantics is a
  property of the registry, not of the stratum assignment the compiler
  happens to compute.
- **The reverse enumeration is exact** (`Authz_Subjects`): `scand`
  models the (key, object)-state traversal of `authz.core/subjects`;
  `scand_complete` (no subject is missed — the same iterate induction
  as Obligation E, riding `sat_gen_pos` with the roles swapped),
  `scand_sound_pure` (pure closures exact, reusing
  `gterm_sat_pure`/`gchain_sat_pure` verbatim), and the
  `subjects_pure_exact` / `subjects_verified_exact` capstones. The
  proof built sorry-free on the first attempt — the machinery really is
  symmetric.
- **The verified kernel** (`Authz_Kernel` + `Authz_Export`): an
  executable bottom-up evaluator over concrete lists — a machine-checked
  twin of the Clojure fixpoint oracle — with `kernel_correct`: whenever
  it answers `Some b`, `b` *is* the spec's `grants`, and
  `kernel_defined`: it answers exactly when its inputs pass the
  executable `stratified`/`safe` checkers (proven equivalent to the spec
  predicates), returning `None` otherwise. Supporting results: subject
  confinement (safety confines subjects to the active domain, bounding
  the search space), `kstep = stepF` under confinement, and
  `fixloop`/`chain_stabilize` (early-exit iteration inside a finite fact
  space reaches the least fixed point and equals the worst-case funpow
  the proofs reason about). `Authz_Export` emits it as a Scala module
  (`mise run kernel:build` → `export/authz-kernel.jar`);
  `test/authz/kernel_test.clj` marshals real registries and Datomic
  datoms into the model and cross-checks the kernel against `can?` —
  a verified referee on the JVM. It recomputes its fixpoint tower per
  query, so treat it as a reference checker for scoped worlds and
  spot-checks, not a production evaluator.

## Building

```sh
mise run verify          # isabelle build -D verification
```

Requires [Isabelle2025-2](https://isabelle.in.tum.de) on the PATH or at
`/Applications/Isabelle2025-2.app`. The first build compiles the HOL
heap image (minutes); later builds are incremental (seconds).

## Correspondence to the implementation

| Isabelle                    | SEMANTICS.md | Clojure                                   |
|-----------------------------|--------------|-------------------------------------------|
| `ext`                       | §1           | `rel-sources` / `rel-targets` adapters    |
| `check`, `deps`, `stratified`, `safe` | §2 | `authz.schema` normalization + validators |
| `sat`, `stepF`, `strata`, `grants` | §3    | `authz.fixpoint-oracle` (executable spec) |
| `walk`, `walker_sound/complete` | §5 W     | `walk-check` in `authz.core`              |
| `cand`, `gterms`/`gchains`, `enum_spec` | §4 E1–E3, §5 E | `gen-graph`/`gen-stream`/`grants` in `authz.core` |

What no proof can reach — the ~10-line index adapter's fidelity to
`d/datoms`, the stream's emission order, and the Datalog-compilation
path (whose consumer is Datomic's query engine) — is pinned by the
differential test suite in CI: every strategy against two independent
oracles on generated worlds.

Deliberate model simplifications, all noted in the theories: `And`/`Or`
are binary (the n-ary forms fold to them), eids and attributes are
naturals (the semantics only compares them), the negative-dependency
marking is sticky under double negation (matching the conservative
`check-stratified!`), and the walker model is fuel-indexed (the Clojure
walker's termination is intrinsic; at sufficient fuel they agree).
