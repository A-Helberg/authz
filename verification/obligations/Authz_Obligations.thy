theory Authz_Obligations
  imports Authz.Authz_Enum
begin

text \<open>
  STATED, NOT YET PROVEN. This session builds with \<open>quick_and_dirty\<close>;
  every \<open>sorry\<close> below is an open obligation from SEMANTICS.md section 5.
  The checked session (\<open>Authz\<close>) contains no sorries -- keep it that way;
  new work starts here and moves there only when its proof is complete.

  DISCHARGED (see the checked session): \<open>grants_finite\<close> and the
  characterization theorem \<open>grants_iff_sat\<close> (Authz_Semantics), the
  Kleene/rank tower (Authz_Kleene), Obligation W in full --
  \<open>walker_sound\<close> / \<open>walker_complete\<close> (Authz_Walker) -- and Obligation E
  in full -- \<open>cand_complete\<close>, \<open>cand_sound_pure\<close>, \<open>enum_verified_exact\<close>,
  \<open>enum_spec_verified\<close> / \<open>enum_spec_pure\<close> (Authz_Enum).
\<close>

section \<open>Stratification-independence\<close>

text \<open>SEMANTICS section 3 asserts the standard result that \<open>grants\<close>
  does not depend on the choice of \<sigma>. Proof plan: both directions by
  induction over \<subseteq>-ordered iterates (\<open>strata_iter\<close> from the checked
  session gives finite derivations to induct on), using
  \<open>key_stability\<close> to align strata; or port the textbook proof that all
  stratifications of a program yield the perfect model. Note this is a
  robustness statement about the spec itself, not about any evaluation
  strategy -- every implementation-facing theorem is already
  discharged relative to one fixed \<sigma>.\<close>

theorem sigma_independent:
  assumes "stratified \<Gamma> \<sigma>1" "stratified \<Gamma> \<sigma>2"
  shows "grants \<Gamma> D \<sigma>1 k s ob = grants \<Gamma> D \<sigma>2 k s ob"
  sorry

end
