theory Authz_Obligations
  imports Authz.Authz_Walker
begin

text \<open>
  STATED, NOT YET PROVEN. This session builds with \<open>quick_and_dirty\<close>;
  every \<open>sorry\<close> below is an open obligation from SEMANTICS.md section 5.
  The checked session (\<open>Authz\<close>) contains no sorries -- keep it that way;
  new work starts here and moves there only when its proof is complete.

  DISCHARGED so far (see the checked session): \<open>grants_finite\<close>
  (Authz_Semantics), and Obligation W in full -- \<open>walker_sound\<close> and
  \<open>walker_complete\<close> (Authz_Walker), including the corrected statements:
  both directions require sufficient fuel, since fuel death inside a
  negation flips False to True.
\<close>

section \<open>Obligation E: the enumeration\<close>

text \<open>What \<open>authz.core/grants\<close> must satisfy (E1-E3 of SEMANTICS
  section 4). \<open>enum_spec\<close> is the specification; the traversal itself
  (gen-graph / gen-stream) is not yet modelled here. Modelling plan:
  represent the stream as unfolding of the step function over an
  explicit stack+seen state, prove (completeness) every fact is
  reachable from a seed through consumer edges -- mirroring its
  finite-height derivation via \<open>drank\<close> -- and (soundness for pure
  closures) an emitted candidate embeds a derivation; impure closures
  compose with \<open>walker_sound\<close>/\<open>walker_complete\<close>. \<open>grants_finite\<close>
  supplies the finiteness E1 presupposes.\<close>

definition enum_spec :: "reg \<Rightarrow> db \<Rightarrow> (key \<Rightarrow> nat) \<Rightarrow> key \<Rightarrow> eid \<Rightarrow> eid list \<Rightarrow> bool" where
  "enum_spec \<Gamma> D \<sigma> k s xs \<longleftrightarrow>
     distinct xs \<and> set xs = {ob. grants \<Gamma> D \<sigma> k s ob}"

section \<open>Stratification-independence\<close>

text \<open>SEMANTICS section 3 asserts the standard result that \<open>grants\<close>
  does not depend on the choice of \<sigma>. Proof plan: both directions by
  induction over \<subseteq>-ordered iterates (\<open>strata_iter\<close> from the checked
  session gives finite derivations to induct on), using
  \<open>key_stability\<close> to align strata; or port the textbook proof that all
  stratifications of a program yield the perfect model.\<close>

theorem sigma_independent:
  assumes "stratified \<Gamma> \<sigma>1" "stratified \<Gamma> \<sigma>2"
  shows "grants \<Gamma> D \<sigma>1 k s ob = grants \<Gamma> D \<sigma>2 k s ob"
  sorry

end
