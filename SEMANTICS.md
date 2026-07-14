# The formal semantics of authz

This document is the specification. Every evaluation strategy in the
library — the point-check walker, the compiled Datalog clauses, the
Datomic rules for recursive permissions, and the `grants` enumeration —
is *held to* the definitions below; none of them *is* the definition.
The bottom-up fixpoint oracle in `test/authz/fixpoint_oracle.clj`
implements this document as literally as possible and serves as the
executable spec in the differential test suite. The Isabelle/HOL
formalization under `verification/` mechanizes it.

Scope: the core check language and its consumption APIs. The
attribute-level allow layer (`authz.attrs`) is a protocol over these
semantics plus Datomic's transaction semantics; it needs its own
specification and is out of scope here.

Notation: we write finite maps as `f : A ⇀ B`, set comprehension as
`{x | P}`, and `⊨` for satisfaction.

## 1. The data model

**Values and datoms.** Fix countable sets `Eid` (entity ids) and `Lit`
(literals: strings, keywords, numbers, …), disjoint. A *value* is an
element of `Val = Eid ⊎ Lit`. A *datom* is a triple `(e, a, v)` with
`e ∈ Eid`, `a ∈ Attr`, `v ∈ Val`.

**Database.** A database value `D` is a **finite** set of datoms. This
models a Datomic db value at one basis: immutable, and set-semantics
(Datomic stores each `(e, a, v)` at most once). Cardinality-many
attributes appear as several datoms sharing `(e, a)`; cardinality-one is
the functional special case — the semantics never distinguishes them.

An attribute unknown to `D`'s schema simply has no datoms. There is no
error case at the semantic level; the implementation's tolerance of
partially-migrated databases (`datoms*` in `authz.core`) is the
operational reflection of this.

**Relations.** A *relation name* is either a forward attribute `a` or a
reverse attribute `_a` (underscore convention). Its *extension* in `D`
is a binary relation on `Eid`:

    ⟦a⟧_D  = {(x, y) | (x, a, y) ∈ D, y ∈ Eid}      forward
    ⟦_a⟧_D = {(x, y) | (y, a, x) ∈ D}                reverse

In both cases `x` is the entity *on the declaring type's side* and `y`
is the target. A forward datom whose value is a literal contributes
nothing to a relation extension (relations traverse refs).

**Types are schema-level, not data-level.** Nothing in `D` says an eid
"is a" `:folder`. The registry's types classify *positions in checks*,
not entities. Consequently `grants` below is defined for every
`(subject-eid, object-eid)` pair; whether an eid is a sensible member of
a type is the application's concern. (This matches every strategy in the
implementation: all of them answer by following attributes, none
consults a type tag.)

## 2. The registry and the check language

**Registry.** A registry `Γ` assigns to each type `T ∈ Type` a
definition:

    relations_T   : Rel ⇀ Type        (relation name → target type)
    permissions_T : Perm ⇀ Check      (permission name → check body)

Write `Keys(Γ) = {(T, p) | p ∈ dom(permissions_T)}` for the set of
*permission keys*.

**Checks** (already normalized — `(or x)` and `(and x)` collapse to
`x`, sources are retained only for `explain`):

    c ::= Terminal r            r ∈ dom(relations_T)
        | Chain r q             r ∈ dom(relations_T), q ∈ dom(permissions_{relations_T(r)})
        | AttrEq a l            a ∈ Attr, l ∈ Val (a literal in practice)
        | Not c
        | And c₁ … cₙ           n ≥ 2
        | Or  c₁ … cₙ           n ≥ 2

A check body is always interpreted *at* a type `T`; its terminals and
chains resolve against `relations_T`. The only cross-references between
bodies are `Chain r q` nodes, which delegate to the named permission `q`
of the target type — sub-checks are never inlined anonymous bodies. The
implementation's reference validation (`check-refs!` in `authz.schema`)
enforces exactly the side conditions written in the grammar.

**Safety (groundedness).** Define `generative(c)`:

    generative(Terminal r) = generative(Chain r q) = true
    generative(AttrEq a l) = generative(Not c)     = false
    generative(And c₁…cₙ)  = ∃i. generative(cᵢ)
    generative(Or c₁…cₙ)   = ∀i. generative(cᵢ)

A registry is *safe* when every permission body and every `:create` rule
is generative, and — the stronger, branch-local condition actually
enforced — every branch of every `Or` is generative. This is the classic
Datalog range-restriction: it makes every answer set below *finite* and
*domain-independent* (computable from the active domain of `D`, never
from the ambient universe `Eid`). A pure `AttrEq` branch would grant a
permission to *every* subject in the universe; a pure `Not` branch,
worse. `validate-grounded!` rejects both at compile time.

**The dependency graph.** For `k = (T, p) ∈ Keys(Γ)` with body `c`,
collect references with their polarity (whether they occur under an odd
number of `Not`s):

    deps(k) = {((T', q), pol) | Chain r q occurs in c at polarity pol,
                                 T' = relations_T(r)}

**Stratification.** `Γ` is *stratified* when there is a function
`σ : Keys(Γ) → ℕ` with, for every `k` and `(k', pol) ∈ deps(k)`:

    pol positive:  σ(k) ≥ σ(k')
    pol negative:  σ(k) > σ(k')

Equivalently: no cycle in the dependency graph passes through a negative
edge. This is exactly what `check-stratified!` enforces (a chain under
`(not …)` may not target a key in its own strongly connected component).
Everything below assumes `Γ` safe and stratified; the compile-time
validators are *sufficient* for these assumptions (obligation V below).

**Base cases are hygiene, not soundness.** The "every recursive
permission must be able to bottom out" check (`check-base-cases!`)
rejects keys whose every derivation path re-enters their own cycle. The
semantics is perfectly well-defined without it — the least fixed point
of such a permission is simply empty, i.e. it denies everyone, forever.
It is rejected because it is certainly a schema-authoring mistake, not
because it would be unsound.

## 3. The semantics

**Interpretations.** An *interpretation* is a set
`I ⊆ Keys(Γ) × Eid × Eid`; read `(k, s, o) ∈ I` as "subject `s` holds
permission `k` over object `o`".

**Satisfaction.** Given an interpretation `I` (supplying the meaning of
chained permissions), a type `T`, subject `s` and object `o`:

    I, T, s, o ⊨ Terminal r    iff  (o, s) ∈ ⟦r⟧_D
    I, T, s, o ⊨ Chain r q     iff  ∃m. (o, m) ∈ ⟦r⟧_D  ∧  ((relations_T(r), q), s, m) ∈ I
    I, T, s, o ⊨ AttrEq a l    iff  (o, a, l) ∈ D
    I, T, s, o ⊨ Not c         iff  not (I, T, s, o ⊨ c)
    I, T, s, o ⊨ And c₁…cₙ     iff  ∀i. I, T, s, o ⊨ cᵢ
    I, T, s, o ⊨ Or c₁…cₙ      iff  ∃i. I, T, s, o ⊨ cᵢ

Two load-bearing readings, both deliberate and both already documented
as such in the implementation:

- **Terminal = unification.** `Terminal r` holds when the subject *is*
  a value of the relation — `(o, s) ∈ ⟦r⟧_D`, the subject occurring in
  the extension itself.
- **Chain = fresh existential.** `Chain r q` introduces a *new* bound
  variable `m`. Even when `relations_T(r)` is the subject's own type,
  `m` is never unified with `s`: "may view the assignee" and "is the
  assignee" are different checks. Cardinality-many relations make the
  existential range over every value.

**The stratified least fixed point.** Fix a stratification `σ` with
strata `0 … N`. Define interpretations `I₀ ⊆ I₁ ⊆ … ⊆ I_N` by
recursion on the stratum. Given `I_{n-1}` (take `I_{-1} = ∅`), define
the operator

    F_n(J) = I_{n-1} ∪ { (k, s, o) | k = (T, p), σ(k) = n,
                                     (I_{n-1} ∪ J), T, s, o ⊨ permissions_T(p) }

`F_n` is **monotone** in `J`: by stratification, every `Chain` that
occurs under a `Not` targets a key of stratum `< n`, whose facts are
frozen in `I_{n-1}`; every same-stratum `Chain` occurs positively, and
`⊨` is monotone in `I` at positive positions (structural induction).
By Knaster–Tarski `F_n` has a least fixed point; set `I_n = lfp(F_n)`.

**Definition (grants).** For `k = (T, p) ∈ Keys(Γ)`:

    grants_Γ,D(T, p, s, o)   iff   ((T, p), s, o) ∈ I_N

Standard results carry over: the definition is independent of the choice
of `σ` (any two stratifications yield the same `I_N`), and `I_N` is
finite whenever `Γ` is safe.

**Consequences worth naming** (each corresponds to behavior the test
suite pins):

1. *Deny by default.* `I₋₁ = ∅`: nothing is granted except by finite
   derivation from datoms. A recursive permission over cyclic data with
   no grounding derivation (folder A parent of B parent of A, no
   organisation anywhere) grants nothing — a cycle is not a proof.
2. *Recursion = transitive closure.* A folder tree of any depth is
   covered by finitely many applications of `F_n`.
3. *Negation is evaluated against completed lower strata*, so `(and x
   (not y))` can never oscillate; there is exactly one answer set.
4. *No unknown-attribute errors.* A check over an attribute absent from
   `D` is simply false at its leaf.

## 4. What each API means

Let `Γ` be safe and stratified, `D` a db value, and write `grants` for
`grants_Γ,D`.

**`can?`** `(can? schema db S s p T o) = true` iff `grants(T, p, s', o')`
where `s', o'` are the eids `s, o` resolve to via `d/entid`; if either
resolves to nothing, the answer is `false`. The subject-type argument
`S` is an API-level contract check (it must equal the compile-time
inferred subject type of `(T, p)`) and does not participate in the
semantics.

**`explain`** returns, on success, a *witness*: the source form of one
`Or`-branch `cᵢ` of the body with `I_N, T, s, o ⊨ cᵢ`. Which branch is
reported (the cheapest by the static cost order) is an implementation
choice, not part of the semantics; that *some* reported branch satisfies
`⊨` is.

**`filter-authorized`** `(filter-authorized schema db S s p T os) =
{o ∈ os | grants(T, p, s, o)}`.

**`list-query` / `list-query*`** produce Datalog such that for every
query `Q` extending the returned clauses, the rows returned are exactly
the rows of `Q`'s unrestricted meaning for which the bound
`(subject, object)` pair satisfies `grants`. (This is the one obligation
whose discharge necessarily *trusts Datomic's query engine*; it is held
to the spec by differential testing only. See §6.)

**`grants` (the enumeration)** — specified as three properties of the
returned sequence `E = grants(schema, db, S, s, p, T)`:

    E1 (exactness):    set(E) = {o | grants(T, p, s, o)}
    E2 (no duplicates): E is duplicate-free
    E3 (determinism):  E is a pure function of (Γ, basis of D, s, p, T)

Laziness, cursors and `grants-page` are contracts *about* `E`: a cursor
denotes a position in `E`, and page `k` is the corresponding window.
E1–E3 make that meaningful; the pagination layer adds no semantic
content. Note E1's finiteness leans on safety (§2) — this is why
groundedness is a hard error and not a lint.

**`authz.cache`** is sound by construction: `D` is immutable per basis
and `grants` is a pure function of it, so a cache keyed by
`[basis subject perm type object]` cannot go stale. No proof obligation
beyond E3-style purity.

**`list-query-attrs`** returns `A(T, p)` with the *frame property*: if a
transaction from `D` to `D'` touches no attribute in `A(T, p)`, then
`grants_Γ,D(T, p, ·, ·) = grants_Γ,D'(T, p, ·, ·)`. (Over-approximation
is allowed and expected: touching a watched attribute does not imply any
answer changed.)

## 5. Proof obligations

The named theorems the implementation is held to, in the order they
should be discharged. W and E are mechanized (or in progress) in
`verification/`; all are exercised by the differential suite against the
executable spec regardless.

- **V (validators sufficient).** If `compile-schema` accepts `Γ`, then
  `Γ` is well-formed (grammar side conditions), safe, and stratified —
  i.e. the assumptions of §3 hold. *(This turns the compile-time
  validators from lint into load-bearing precondition-establishers.)*
- **W (walker correct) — DISCHARGED** (`verification/checked/Authz_Walker.thy`):
  for accepted `Γ`, `walk-check(T, body, s, o, ∅) = grants(T, p, s, o)`.
  Mechanization notes: soundness and completeness are mutually
  recursive through negation and are proven simultaneously by one
  well-founded induction on (fuel, check size); the completeness
  invariant shows a visited state a minimal derivation needs can never
  be blocked; and in the fuel-indexed model *soundness also requires
  sufficient fuel* — fuel death inside a negation flips `false` to
  `true` (the Clojure walker is fuel-free with intrinsic termination,
  so the caveat is a model artifact, but it is why the naive fuel-free
  soundness statement is unprovable). *(This theorem underwrites
  `can?`, `explain`, the reference interpreter, and the verification
  mode of `grants`.)*
- **E (enumeration exact) — DISCHARGED** (`verification/checked/Authz_Enum.thy`):
  for accepted `Γ`, E1–E2; E3 holds trivially of the functional model,
  and the implementation's emission *order* remains covered by the
  differential suite. The candidate machinery is modelled as an
  inductive relation (seeds closed under consumer-chain edges);
  `cand_complete` proves generation misses nothing, `cand_sound_pure`
  proves the pure-closure fast path exact (the argument that previously
  lived in a code comment in `authz.core`), and `enum_verified_exact`
  composes candidate completeness with theorem W for impure closures.
- **Q (compiled Datalog).** `list-query`'s clauses and the recursive
  rules mean `grants` *under Datomic's Datalog semantics*. Not
  mechanizable without formalizing Datomic; discharged forever by
  differential testing against the executable spec (§6).
- **F (frame property).** `list-query-attrs` satisfies §4's frame
  property. Provable structurally (every relation and attribute `⊨`
  consults is in the watch-set); currently held empirically by
  metamorphic tests.

## 6. The trusted base

After all obligations are discharged, believing an authz answer means
trusting: (1) this document's faithfulness to your intent; (2) the
Isabelle kernel and its Scala code generator, for the mechanized
theorems; (3) the ~10-line index adapter (`rel-sources`/`datoms*`)
faithfully presenting `⟦·⟧_D` from `d/datoms`; (4) Datomic's index
reads — and, *only for the `list-query` path*, Datomic's full query
engine; (5) the JVM. The differential suite (walker vs Datalog vs
enumeration vs the fixpoint oracle, on generated worlds) runs in CI as
the standing cross-check on (3) and (4) — the parts no proof can reach.
