# Machine-checked semantics

This directory mechanizes [SEMANTICS.md](../SEMANTICS.md) in
Isabelle/HOL. It exists so that the README's correctness claims can be
precise, and so that changes to the semantics are expensive on purpose.

## Claims discipline

Two sessions, one hard rule:

- **`Authz`** (`checked/`) — contains **no `sorry`**. Everything here is
  machine-checked end to end. Only theorems in this session may be
  described as "proven" anywhere in this repository.
- **`Authz_Obligations`** (`obligations/`) — theorem *statements* for
  the open obligations of SEMANTICS.md §5, built with `quick_and_dirty`.
  Each carries its proof plan as a comment. Work happens here; a theorem
  moves to `checked/` only when its last `sorry` is gone.

## What is currently proven (session `Authz`)

- The check language, relation extensions, polarity-labelled
  dependencies, stratification, and safety (`Authz_Syntax`).
- The satisfaction relation and the stratified least-fixed-point
  semantics are **well-defined** (`Authz_Semantics`):
  `sat_invariant` (satisfaction depends only on mentioned keys),
  `sat_mono` (monotone when negated keys are frozen),
  `stepF_mono` (each stratum's operator is monotone, so the least fixed
  points exist by Knaster–Tarski),
  `strata_mono_level` / `strata_stratum_bound` / `key_stability`
  (strata grow, add only their own stratum's facts, and a key's facts
  are complete at its own stratum),
  `terminal_grants` (sanity: a bare-terminal permission denotes exactly
  its relation extension).
- **Safety implies finiteness** (`grants_finite`, formerly Obligation
  E's precondition): for a safe (grounded) registry over a finite
  database, every answer set is finite — it lives inside the active
  domain (`generative_sat_adom` + `strata_origin` + `adom_finite`).
  This is the proven semantic content of the groundedness validator.
- **The characterization theorem** (`grants_iff_sat`,
  `Authz_Semantics`): a permission holds exactly when its body is
  satisfied over the interpretation of all grants — the semantics
  satisfies its own equations.
- **Kleene iterates and derivation rank** (`Authz_Kleene`):
  satisfaction is finitary (`sat_chain`), each stratum is the union of
  its finite iterates (`strata_iter`), and `drank`/`drank_step` give
  every granted fact a minimal derivation height with strictly
  descending same-stratum children.
- **Obligation W, in full** (`Authz_Walker`): `walker_sound` and
  `walker_complete` — the visited-set walker computes `grants`. This
  underwrites `can?`, `explain`, the reference interpreter, and the
  verification mode of the `grants` enumeration. Proven by a single
  well-founded induction on (fuel, check size) carrying soundness and
  completeness simultaneously; the stratum structure enters only
  through side conditions (`deps_le`, `vhigh`, `vcond` — the last shows
  blocking a state a minimal derivation needs is *impossible*, not
  merely harmless). Two corrections to the naive statements were
  discovered en route: soundness also needs sufficient fuel (fuel death
  inside a negation flips False to True), and the two directions are
  mutually recursive through negation, so neither can be proven alone.

## What is stated but open (session `Authz_Obligations`)

- **E** `enum_spec` — the enumeration contract for `grants` (its
  finiteness precondition and its walker component are both
  discharged; what remains is modelling the gen-graph traversal).
- `sigma_independent` — the semantics does not depend on the choice of
  stratification.

Until these are discharged, the corresponding implementation claims
rest on the differential test suite: the bottom-up fixpoint oracle
(`test/authz/fixpoint_oracle.clj`) implements SEMANTICS.md §3 directly
and every strategy is tested against it on generated worlds in CI.

## Building

```sh
mise run verify          # isabelle build -D verification (both sessions)
```

Requires [Isabelle2025-2](https://isabelle.in.tum.de) on the PATH or at
`/Applications/Isabelle2025-2.app`. The first build compiles the HOL
heap image (minutes); later builds are incremental.

## Correspondence to the implementation

| Isabelle                    | SEMANTICS.md | Clojure                                   |
|-----------------------------|--------------|-------------------------------------------|
| `ext`                       | §1           | `rel-sources` / `rel-targets` adapters    |
| `check`, `deps`, `stratified`, `safe` | §2 | `authz.schema` normalization + validators |
| `sat`, `stepF`, `strata`, `grants` | §3    | `authz.fixpoint-oracle` (executable spec) |
| `walk` (obligations)        | §5 W         | `walk-check` in `authz.core`              |
| `enum_spec` (obligations)   | §4 E1–E3     | `grants` in `authz.core`                  |

Deliberate model simplifications, all noted in the theories: `And`/`Or`
are binary (the n-ary forms fold to them; both are associative), eids
and attributes are naturals (the semantics only compares them), and the
negative-dependency marking is sticky under double negation (matching
the implementation's conservative `check-stratified!`).
