theory Authz_Obligations
  imports Authz.Authz_Semantics
begin

text \<open>
  STATED, NOT YET PROVEN. This session builds with \<open>quick_and_dirty\<close>;
  every \<open>sorry\<close> below is an open obligation from SEMANTICS.md section 5. The
  checked session (\<open>Authz\<close>) contains no sorries -- keep it that way; new
  work starts here and moves there only when its proof is complete.

  Each obligation carries its proof plan as a comment.
\<close>

section \<open>Derivation fuel\<close>

text \<open>\<open>adom\<close> lives in the checked session now (it carries
  \<open>grants_finite\<close>, discharged and moved to \<open>Authz_Semantics\<close>).\<close>

definition fuel_bound :: "reg \<Rightarrow> db \<Rightarrow> nat" where
  "fuel_bound \<Gamma> D = card (rkeys \<Gamma>) * card (adom D) + 1"

section \<open>Obligation W: the point-check walker\<close>

text \<open>A model of \<open>walk-check\<close> (authz.core): top-down evaluation with a
  path-scoped visited set, a revisit answered \<open>False\<close>. The Clojure
  tracks visited states only for recursive keys -- an optimization, since
  a non-recursive key can never be revisited; the model inserts always.
  Fuel replaces the termination argument so the function is total by
  construction; \<open>walker_correct\<close> quantifies over sufficient fuel.\<close>

fun walk :: "nat \<Rightarrow> reg \<Rightarrow> db \<Rightarrow> (key \<times> eid) set \<Rightarrow> ty \<Rightarrow> check \<Rightarrow> eid \<Rightarrow> eid \<Rightarrow> bool" where
  "walk 0 \<Gamma> D V T c s ob = False"
| "walk (Suc f) \<Gamma> D V T (Terminal r) s ob = ((ob, s) \<in> ext D r)"
| "walk (Suc f) \<Gamma> D V T (Chain r q) s ob =
     (case rels \<Gamma> T r of
        None \<Rightarrow> False
      | Some T' \<Rightarrow>
          (case perms \<Gamma> T' q of
             None \<Rightarrow> False
           | Some c' \<Rightarrow>
               (\<exists>m. (ob, m) \<in> ext D r \<and> ((T', q), m) \<notin> V \<and>
                    walk f \<Gamma> D (insert ((T', q), m) V) T' c' s m)))"
| "walk (Suc f) \<Gamma> D V T (AttrEq a v) s ob = ((ob, a, v) \<in> D)"
| "walk (Suc f) \<Gamma> D V T (CNot c) s ob = (\<not> walk (Suc f) \<Gamma> D V T c s ob)"
| "walk (Suc f) \<Gamma> D V T (CAnd c1 c2) s ob =
     (walk (Suc f) \<Gamma> D V T c1 s ob \<and> walk (Suc f) \<Gamma> D V T c2 s ob)"
| "walk (Suc f) \<Gamma> D V T (COr c1 c2) s ob =
     (walk (Suc f) \<Gamma> D V T c1 s ob \<or> walk (Suc f) \<Gamma> D V T c2 s ob)"

text \<open>Proof plan. Soundness (walk \<Longrightarrow> grants): induction on fuel; every
  positive leaf the walk uses is a datom, every chain hop wraps a
  smaller walk whose conclusion feeds \<open>stepF\<close>; negative subtrees flip to
  the completeness direction at a strictly lower stratum (well-founded
  because \<open>stratified\<close>), so the induction is really over the
  lexicographic (stratum, fuel).

  Completeness (grants \<Longrightarrow> walk, with V = {} and enough fuel): every fact
  of \<open>strata\<close> has a derivation tree of finite height (lfp = \<Union> of the
  iterates by Kleene, using monotonicity from the checked session; each
  iterate gives height); choose a minimal-height derivation and show by
  induction on height that its states are pairwise distinct along each
  path -- a repeated state would allow cutting the derivation shorter --
  hence the visited set never blocks it and \<open>fuel_bound\<close> suffices. The
  interaction with V \<noteq> {} needs the strengthened statement: walk
  computes grants restricted to derivations avoiding V, and minimal
  derivations avoid any V they started under.\<close>

theorem walker_sound:
  assumes "stratified \<Gamma> \<sigma>" and "perms \<Gamma> T p = Some c"
      and "walk f \<Gamma> D {} T c s ob"
  shows "grants \<Gamma> D \<sigma> (T, p) s ob"
  sorry

theorem walker_complete:
  assumes "stratified \<Gamma> \<sigma>" "finite D" and "perms \<Gamma> T p = Some c"
      and "grants \<Gamma> D \<sigma> (T, p) s ob" and "f \<ge> fuel_bound \<Gamma> D"
  shows "walk f \<Gamma> D {} T c s ob"
  sorry

section \<open>Obligation E: the enumeration\<close>

text \<open>What \<open>authz.core/grants\<close> must satisfy (E1-E3 of SEMANTICS section 4).
  \<open>enum_spec\<close> is the specification; the traversal itself (gen-graph /
  gen-stream) is not yet modelled here. Modelling plan: represent the
  stream as unfolding of the step function over an explicit stack+seen
  state, prove (completeness) every fact is reachable from a seed
  through consumer edges -- mirroring its finite-height derivation -- and
  (soundness for pure closures) an emitted candidate embeds a
  derivation; impure closures compose with Obligation W.\<close>

definition enum_spec :: "reg \<Rightarrow> db \<Rightarrow> (key \<Rightarrow> nat) \<Rightarrow> key \<Rightarrow> eid \<Rightarrow> eid list \<Rightarrow> bool" where
  "enum_spec \<Gamma> D \<sigma> k s xs \<longleftrightarrow>
     distinct xs \<and> set xs = {ob. grants \<Gamma> D \<sigma> k s ob}"

text \<open>E1's finiteness precondition -- \<open>grants_finite\<close> -- is DISCHARGED:
  see \<open>Authz_Semantics\<close> in the checked session (via
  \<open>generative_sat_adom\<close> and \<open>strata_origin\<close>, both of which are also
  useful stepping stones for the walker proofs below).\<close>

section \<open>Stratification-independence\<close>

text \<open>SEMANTICS section 3 asserts the standard result that \<open>grants\<close> does not
  depend on the choice of \<sigma>. Proof plan: both directions by induction
  over \<subseteq>-ordered iterates, using \<open>key_stability\<close> to align strata; or
  port the textbook proof that all stratifications of a program yield
  the perfect model.\<close>

theorem sigma_independent:
  assumes "stratified \<Gamma> \<sigma>1" "stratified \<Gamma> \<sigma>2"
  shows "grants \<Gamma> D \<sigma>1 k s ob = grants \<Gamma> D \<sigma>2 k s ob"
  sorry

end
