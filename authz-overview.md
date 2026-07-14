# Authz system — conceptual overview (handoff doc)

This describes the authorization system in this codebase at the level of *what it is and how it's used*, so another implementation (an optimized library) can reproduce the semantics. Implementation details of the current version are intentionally omitted except where they define behavior.

## The model in one paragraph

It's a relationship-based access control (ReBAC) system, in the spirit of Google Zanzibar / SpiceDB / OpenFGA, but with a key twist: **permissions are never materialized or checked by walking a graph at runtime — they compile into Datomic Datalog `:where` clauses** that get spliced into ordinary application queries. Authorization is therefore evaluated by the database itself, in the same query that fetches the data, against the same consistent snapshot (`db` value).

## The schema DSL

A single registry of *definitions* (one per entity type) is declared in one file. Each definition has:

- **Relations** — `(relation <datomic-attribute> <target-type>)`. A relation names a Datomic attribute that connects this entity type to another type. Reverse relations use Datomic's underscore convention: `:manager/_organisation` means "traverse `:manager/organisation` backwards" (i.e. from an organisation to the managers pointing at it).
- **Permissions** — `(permission <name> <check-expression>)`. The check expression is a small quoted s-expression language with exactly three forms:
  1. **Terminal keyword** — `:assignment/member` means "the subject IS the entity reached by this relation" (subject and relation target unify). E.g. `(permission :react :assignment/member)` = only the assignee can react.
  2. **Thread/chain** — `(-> <relation> <permission-on-target-type>)` means "follow the relation to the related entity, then require that permission on it". This is how permissions cascade/inherit: `(permission :view '(-> :resource/organisation :view))` = you can view a resource iff you can view its organisation. Chains are two elements (one hop + one permission name); deeper nesting comes from the target permission itself chaining further. Crucially, the first hop of a chain does **not** unify with the subject even when the relation targets the subject's type — `(-> :submission/submitted-by :view)` means "someone who may view the submitter", not "the submitter".
  3. **Disjunction** — `(or <check> <check> ...)` — any branch grants. Compiles to Datalog `or-join`. There is no `and`, no negation, no attribute/condition checks (e.g. "status = published") — those are left to the API layer by design.

That's the whole language. Its power comes from composition: permission names on one type reference permission names on related types, forming a DAG of grants.

## The three consumption APIs

1. **`(can? db subject-type subject-eid permission object-type object-eid)`** — point check. Used for write-path guards ("may this user edit this org?") before transacting. Returns truthy/falsy.
2. **`(list-query object-type permission subject-type)`** — returns a vector of Datalog `:where` clauses binding `?<object-type>` and `?<subject-type>` (e.g. `?assignment`, `?user`). Callers `concat` these clauses with their own filters into one Datomic query, so **list endpoints only ever return rows the subject is authorized to see** — filtering happens inside the DB query, not post-hoc. This is the dominant usage pattern in the API layer.
3. **`(list-query-attrs object-type permission subject-type)`** — returns the set of Datomic attributes mentioned anywhere in the compiled permission (transitively through chains and ors). Used by the reactive/streaming layer ("flows"): server-pushed queries re-run when a transaction touches any watched attribute, so the authz-relevant attributes must be included in the watch-set. This makes permission changes (e.g. someone gains a manager role) live-update subscribed clients.

## The domain rules it encodes (the shape, not the full list)

- A **hierarchy**: system → organisation → country/state/region → site → users, plus content types (resources, forms, learning modules, capture forms, folders, heads-up posts, planner schedules/occurrences, assignments, submissions) that mostly hang off the organisation.
- **Roles are relationships**, not enum flags: org-admins, senior-leadership, members are ref attributes on organisation; superadmins/tr-admins on a singleton system entity; **managers are first-class entities** linking a user to a scope (site OR region OR state OR country) — scope is which ref is set.
- **Scoped visibility** falls out of chaining: a site's `:view` ors together "manager of this site", "manage-members on its state", "manage-members on its region", and "org-level view-members" — so a state manager sees all sites in the state without any site-level grants.
- **Person-derived visibility**: submissions and assignments are visible to their subject *or* anyone who may `:view` that subject as a user — this is what makes "a manager sees their people's work, and only their people's work" a one-line rule.
- Deliberate **asymmetries** are load-bearing and documented in the schema comments, e.g.: org `:view`/`:view-members` intentionally exclude the manager→organisation shortcut (would break hierarchical scoping); `:post-heads-up` sits between `:edit` and `:view` in breadth; instance-level checks that aren't static role facts (like "is this user a member of the schedule's site" before claiming a planner occurrence) are explicitly pushed to the API layer, not the authz schema.

## Usage conventions in the API layer

- Every server API function takes `db` + `user-eid` (from the authenticated request) and either guards with `can?` (writes/single reads) or splices `list-query` clauses (lists).
- Query `:in` is uniformly `[$ ?user ?<object> ...]` — the subject var name is derived from the type name, so callers must use matching var names (`?user`, `?assignment`, ...) in their own clauses.
- Flow (reactive) endpoints combine their data attrs with `list-query-attrs` for invalidation.

## Semantics an optimized library must preserve

1. Compile-to-query, not check-at-runtime: authz composes with arbitrary application filtering in a single DB query on a consistent snapshot. No sync/materialization pipeline, no denormalized permission tuples.
2. Terminal-keyword = subject unification; chain-first-hop = fresh variable even on same-type relations (the submitter/viewer distinction above). Getting this wrong silently collapses "can view the submitter" into "is the submitter".
3. Reverse relations (`_attr`) invert the query pattern rather than requiring bidirectional schema.
4. `or` branches must be independent (or-join with the subject and object vars as the join keys).
5. Attribute extraction must be transitive through the whole compiled tree, for reactive invalidation.
6. Fail-loud schema hygiene: duplicate/missing permission or relation names, and unquoted (empty) permission bodies, are asserted at definition time.

## Known weaknesses / optimization targets

- Compilation happens on every call (`list-query`/`can?` re-walk the registry and rebuild clauses each time); results are pure functions of the static schema and could be compiled once/cached.
- `or-join` fan-out: deep chains under `or` produce large clause trees; Datomic evaluates every branch. Clause ordering / branch pruning by selectivity is untuned.
- The registry is a global mutable atom (with a test-scoped override); a library should make it a first-class immutable compiled schema value.
- No `and`, no negation, no attribute conditions, no caveats/ABAC — fine so far, but the expression language has room to grow.
- `list-query-attrs` over-approximates (any touched attribute invalidates), which is safe but causes spurious re-runs.
- No cycle detection across permission references; the schema is a DAG only by discipline.
- Variable naming by type (`?user`, `?site`) is a public contract with callers and a collision hazard; gensym is only used for same-type intermediates.
