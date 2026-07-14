theory Authz_Semantics
  imports Authz_Syntax
begin

text \<open>
  The stratified least-fixed-point semantics of SEMANTICS.md section 3, and the
  theorems that make it well-defined:

    * \<open>sat_invariant\<close> -- satisfaction depends only on the facts of the
      keys a check mentions;
    * \<open>sat_mono\<close>      -- satisfaction is monotone when the keys under a
      negation are frozen;
    * \<open>stepF_mono\<close>    -- hence each stratum's operator is monotone and
      Knaster-Tarski applies: the per-stratum least fixed points exist;
    * \<open>strata_mono_level\<close>, \<open>strata_stratum_bound\<close>, \<open>key_stability\<close> --
      strata only grow, only add facts of their own stratum, and a key's
      facts are complete at its own stratum;
    * \<open>terminal_grants\<close> -- sanity: the machinery grounds out, a bare
      terminal means exactly its relation extension.
\<close>

type_synonym interp = "(key \<times> eid \<times> eid) set"

fun sat :: "reg \<Rightarrow> db \<Rightarrow> interp \<Rightarrow> ty \<Rightarrow> check \<Rightarrow> eid \<Rightarrow> eid \<Rightarrow> bool" where
  "sat \<Gamma> D I T (Terminal r) s ob = ((ob, s) \<in> ext D r)"
| "sat \<Gamma> D I T (Chain r q) s ob =
     (\<exists>T' m. rels \<Gamma> T r = Some T' \<and> (ob, m) \<in> ext D r \<and> ((T', q), s, m) \<in> I)"
| "sat \<Gamma> D I T (AttrEq a v) s ob = ((ob, a, v) \<in> D)"
| "sat \<Gamma> D I T (CNot c) s ob = (\<not> sat \<Gamma> D I T c s ob)"
| "sat \<Gamma> D I T (CAnd c1 c2) s ob = (sat \<Gamma> D I T c1 s ob \<and> sat \<Gamma> D I T c2 s ob)"
| "sat \<Gamma> D I T (COr c1 c2) s ob = (sat \<Gamma> D I T c1 s ob \<or> sat \<Gamma> D I T c2 s ob)"

lemma sat_invariant:
  assumes "\<And>k s' m. k \<in> fst ` deps \<Gamma> T c \<Longrightarrow> ((k, s', m) \<in> I) = ((k, s', m) \<in> I')"
  shows "sat \<Gamma> D I T c s ob = sat \<Gamma> D I' T c s ob"
  using assms
proof (induction c arbitrary: s ob)
  case (Chain r q)
  show ?case
  proof (cases "rels \<Gamma> T r")
    case None then show ?thesis by simp
  next
    case (Some T')
    then have "(T', q) \<in> fst ` deps \<Gamma> T (Chain r q)" by force
    with Chain.prems Some show ?thesis by auto
  qed
next
  case (CNot c)
  have "sat \<Gamma> D I T c s ob = sat \<Gamma> D I' T c s ob"
    by (rule CNot.IH) (use CNot.prems in force)
  then show ?case by simp
next
  case (CAnd c1 c2)
  have "sat \<Gamma> D I T c1 s ob = sat \<Gamma> D I' T c1 s ob"
    by (rule CAnd.IH(1)) (use CAnd.prems in force)
  moreover have "sat \<Gamma> D I T c2 s ob = sat \<Gamma> D I' T c2 s ob"
    by (rule CAnd.IH(2)) (use CAnd.prems in force)
  ultimately show ?case by simp
next
  case (COr c1 c2)
  have "sat \<Gamma> D I T c1 s ob = sat \<Gamma> D I' T c1 s ob"
    by (rule COr.IH(1)) (use COr.prems in force)
  moreover have "sat \<Gamma> D I T c2 s ob = sat \<Gamma> D I' T c2 s ob"
    by (rule COr.IH(2)) (use COr.prems in force)
  ultimately show ?case by simp
qed simp_all

lemma sat_mono:
  assumes "I \<subseteq> I'"
      and frozen: "\<And>k s' m. (k, True) \<in> deps \<Gamma> T c \<Longrightarrow> ((k, s', m) \<in> I) = ((k, s', m) \<in> I')"
      and "sat \<Gamma> D I T c s ob"
  shows "sat \<Gamma> D I' T c s ob"
  using assms
proof (induction c arbitrary: s ob)
  case (Chain r q)
  then show ?case by (auto split: option.splits)
next
  case (CNot c)
  have "\<And>k s' m. k \<in> fst ` deps \<Gamma> T c \<Longrightarrow> ((k, s', m) \<in> I) = ((k, s', m) \<in> I')"
  proof -
    fix k s' m assume "k \<in> fst ` deps \<Gamma> T c"
    then obtain b where "(k, b) \<in> deps \<Gamma> T c" by auto
    then have "(k, True) \<in> deps \<Gamma> T (CNot c)" by force
    then show "((k, s', m) \<in> I) = ((k, s', m) \<in> I')" by (rule CNot.prems(2))
  qed
  then have "sat \<Gamma> D I T c s ob = sat \<Gamma> D I' T c s ob"
    by (rule sat_invariant)
  with CNot.prems(3) show ?case by simp
next
  case (CAnd c1 c2)
  have frz1: "\<And>k s' m. (k, True) \<in> deps \<Gamma> T c1 \<Longrightarrow> ((k, s', m) \<in> I) = ((k, s', m) \<in> I')"
    by (rule CAnd.prems(2)) simp
  have frz2: "\<And>k s' m. (k, True) \<in> deps \<Gamma> T c2 \<Longrightarrow> ((k, s', m) \<in> I) = ((k, s', m) \<in> I')"
    by (rule CAnd.prems(2)) simp
  from CAnd.prems(3) have "sat \<Gamma> D I T c1 s ob" "sat \<Gamma> D I T c2 s ob" by simp_all
  with CAnd.IH(1)[OF CAnd.prems(1) frz1] CAnd.IH(2)[OF CAnd.prems(1) frz2]
  show ?case by simp
next
  case (COr c1 c2)
  have frz1: "\<And>k s' m. (k, True) \<in> deps \<Gamma> T c1 \<Longrightarrow> ((k, s', m) \<in> I) = ((k, s', m) \<in> I')"
    by (rule COr.prems(2)) simp
  have frz2: "\<And>k s' m. (k, True) \<in> deps \<Gamma> T c2 \<Longrightarrow> ((k, s', m) \<in> I) = ((k, s', m) \<in> I')"
    by (rule COr.prems(2)) simp
  from COr.prems(3) have "sat \<Gamma> D I T c1 s ob \<or> sat \<Gamma> D I T c2 s ob" by simp
  with COr.IH(1)[OF COr.prems(1) frz1] COr.IH(2)[OF COr.prems(1) frz2]
  show ?case by auto
qed auto

text \<open>The per-stratum operator. Same-stratum facts are consulted only
  through \<open>restr\<close>, so lower-stratum facts come exclusively from the
  completed \<open>L\<close> -- that is what makes negation harmless and the operator
  monotone.\<close>

definition restr :: "(key \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> interp \<Rightarrow> interp" where
  "restr \<sigma> n J = {x \<in> J. \<sigma> (fst x) = n}"

definition stepF :: "reg \<Rightarrow> db \<Rightarrow> (key \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> interp \<Rightarrow> interp \<Rightarrow> interp" where
  "stepF \<Gamma> D \<sigma> n L J =
     L \<union> {((T, p), s, ob) | T p s ob.
            \<sigma> (T, p) = n \<and>
            (\<exists>c. perms \<Gamma> T p = Some c \<and> sat \<Gamma> D (L \<union> restr \<sigma> n J) T c s ob)}"

lemma restr_mono: "J \<subseteq> J' \<Longrightarrow> restr \<sigma> n J \<subseteq> restr \<sigma> n J'"
  by (auto simp: restr_def)

lemma stepF_mono:
  assumes strat: "stratified \<Gamma> \<sigma>"
  shows "mono (stepF \<Gamma> D \<sigma> n L)"
proof (rule monoI)
  fix J J' :: interp assume JJ: "J \<subseteq> J'"
  show "stepF \<Gamma> D \<sigma> n L J \<subseteq> stepF \<Gamma> D \<sigma> n L J'"
  proof
    fix x assume "x \<in> stepF \<Gamma> D \<sigma> n L J"
    then consider (lower) "x \<in> L"
      | (new) T p s ob c where "x = ((T, p), s, ob)" "\<sigma> (T, p) = n"
          "perms \<Gamma> T p = Some c" "sat \<Gamma> D (L \<union> restr \<sigma> n J) T c s ob"
      by (auto simp: stepF_def)
    then show "x \<in> stepF \<Gamma> D \<sigma> n L J'"
    proof cases
      case lower then show ?thesis by (simp add: stepF_def)
    next
      case new
      have "sat \<Gamma> D (L \<union> restr \<sigma> n J') T c s ob"
      proof (rule sat_mono)
        show "L \<union> restr \<sigma> n J \<subseteq> L \<union> restr \<sigma> n J'"
          using restr_mono[OF JJ] by blast
      next
        fix k s' m assume kneg: "(k, True) \<in> deps \<Gamma> T c"
        have "\<sigma> k < \<sigma> (T, p)"
          using strat[unfolded stratified_def, rule_format, OF new(3) kneg] by simp
        then have "\<sigma> k < n" using new(2) by simp
        then have "(k, s', m) \<notin> restr \<sigma> n J" and "(k, s', m) \<notin> restr \<sigma> n J'"
          by (auto simp: restr_def)
        then show "((k, s', m) \<in> L \<union> restr \<sigma> n J) = ((k, s', m) \<in> L \<union> restr \<sigma> n J')"
          by blast
      next
        show "sat \<Gamma> D (L \<union> restr \<sigma> n J) T c s ob" by (fact new)
      qed
      with new show ?thesis by (auto simp: stepF_def)
    qed
  qed
qed

text \<open>The iterated fixpoint and the meaning of a permission.\<close>

fun strata :: "reg \<Rightarrow> db \<Rightarrow> (key \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> interp" where
  "strata \<Gamma> D \<sigma> 0 = lfp (stepF \<Gamma> D \<sigma> 0 {})"
| "strata \<Gamma> D \<sigma> (Suc n) = lfp (stepF \<Gamma> D \<sigma> (Suc n) (strata \<Gamma> D \<sigma> n))"

definition grants :: "reg \<Rightarrow> db \<Rightarrow> (key \<Rightarrow> nat) \<Rightarrow> key \<Rightarrow> eid \<Rightarrow> eid \<Rightarrow> bool" where
  "grants \<Gamma> D \<sigma> k s ob \<longleftrightarrow> (k, s, ob) \<in> strata \<Gamma> D \<sigma> (\<sigma> k)"

lemma stepF_lower:
  assumes "stratified \<Gamma> \<sigma>"
  shows "L \<subseteq> lfp (stepF \<Gamma> D \<sigma> n L)"
proof -
  have "L \<subseteq> stepF \<Gamma> D \<sigma> n L (lfp (stepF \<Gamma> D \<sigma> n L))"
    unfolding stepF_def by blast
  also have "stepF \<Gamma> D \<sigma> n L (lfp (stepF \<Gamma> D \<sigma> n L)) = lfp (stepF \<Gamma> D \<sigma> n L)"
    by (rule lfp_unfold[OF stepF_mono[OF assms], symmetric])
  finally show ?thesis .
qed

theorem strata_mono_level:
  assumes "stratified \<Gamma> \<sigma>" "m \<le> n"
  shows "strata \<Gamma> D \<sigma> m \<subseteq> strata \<Gamma> D \<sigma> n"
  using assms(2)
proof (induction n)
  case (Suc n)
  then consider "m \<le> n" | "m = Suc n" by fastforce
  then show ?case
  proof cases
    case 1
    with Suc.IH have "strata \<Gamma> D \<sigma> m \<subseteq> strata \<Gamma> D \<sigma> n" .
    also have "\<dots> \<subseteq> strata \<Gamma> D \<sigma> (Suc n)"
      using stepF_lower[OF assms(1)] by simp
    finally show ?thesis .
  qed simp
qed simp

theorem strata_stratum_bound:
  assumes strat: "stratified \<Gamma> \<sigma>"
  shows "x \<in> strata \<Gamma> D \<sigma> n \<Longrightarrow> \<sigma> (fst x) \<le> n"
proof (induction n arbitrary: x)
  case 0
  have sub: "stepF \<Gamma> D \<sigma> 0 {} {y. \<sigma> (fst y) \<le> 0} \<subseteq> {y. \<sigma> (fst y) \<le> 0}"
    unfolding stepF_def by auto
  have "strata \<Gamma> D \<sigma> 0 \<subseteq> {y. \<sigma> (fst y) \<le> 0}"
    unfolding strata.simps by (rule lfp_lowerbound) (rule sub)
  with "0.prems" show ?case by auto
next
  case (Suc n)
  have sub: "stepF \<Gamma> D \<sigma> (Suc n) (strata \<Gamma> D \<sigma> n) {y. \<sigma> (fst y) \<le> Suc n}
               \<subseteq> {y. \<sigma> (fst y) \<le> Suc n}"
    unfolding stepF_def using Suc.IH by fastforce
  have "strata \<Gamma> D \<sigma> (Suc n) \<subseteq> {y. \<sigma> (fst y) \<le> Suc n}"
    unfolding strata.simps by (rule lfp_lowerbound) (rule sub)
  with Suc.prems show ?case by auto
qed

theorem key_stability:
  assumes strat: "stratified \<Gamma> \<sigma>" and le: "\<sigma> k \<le> n"
  shows "((k, s, ob) \<in> strata \<Gamma> D \<sigma> n) = ((k, s, ob) \<in> strata \<Gamma> D \<sigma> (\<sigma> k))"
proof
  assume "(k, s, ob) \<in> strata \<Gamma> D \<sigma> (\<sigma> k)"
  with strata_mono_level[OF strat le] show "(k, s, ob) \<in> strata \<Gamma> D \<sigma> n" by blast
next
  assume "(k, s, ob) \<in> strata \<Gamma> D \<sigma> n"
  with le show "(k, s, ob) \<in> strata \<Gamma> D \<sigma> (\<sigma> k)"
  proof (induction n)
    case (Suc n)
    show ?case
    proof (cases "\<sigma> k = Suc n")
      case True with Suc.prems show ?thesis by simp
    next
      case False
      with Suc.prems(1) have le': "\<sigma> k \<le> n" by simp
      have unfold: "strata \<Gamma> D \<sigma> (Suc n) =
              stepF \<Gamma> D \<sigma> (Suc n) (strata \<Gamma> D \<sigma> n) (strata \<Gamma> D \<sigma> (Suc n))"
        using lfp_unfold[OF stepF_mono[OF strat]] by simp
      from Suc.prems(2) have "(k, s, ob) \<in> strata \<Gamma> D \<sigma> n"
        by (subst (asm) unfold) (use False in \<open>auto simp: stepF_def\<close>)
      with Suc.IH le' show ?thesis by blast
    qed
  qed simp
qed

text \<open>Sanity: for a permission whose body is a bare terminal, \<open>grants\<close>
  is exactly the relation extension -- the fixpoint tower grounds out.\<close>

theorem terminal_grants:
  assumes strat: "stratified \<Gamma> \<sigma>"
      and body: "perms \<Gamma> T p = Some (Terminal r)"
  shows "grants \<Gamma> D \<sigma> (T, p) s ob = ((ob, s) \<in> ext D r)"
proof -
  define n where "n = \<sigma> (T, p)"
  define L where "L = (if n = 0 then {} else strata \<Gamma> D \<sigma> (n - 1))"
  have eval: "strata \<Gamma> D \<sigma> n = lfp (stepF \<Gamma> D \<sigma> n L)"
    unfolding n_def L_def by (cases "\<sigma> (T, p)") auto
  have notL: "((T, p), s, ob) \<notin> L"
  proof (cases n)
    case 0 then show ?thesis by (simp add: L_def)
  next
    case (Suc m)
    then have L_eq: "L = strata \<Gamma> D \<sigma> m" by (simp add: L_def)
    show ?thesis
    proof
      assume "((T, p), s, ob) \<in> L"
      then have "\<sigma> (fst ((T, p), s, ob)) \<le> m"
        unfolding L_eq by (rule strata_stratum_bound[OF strat])
      then have "\<sigma> (T, p) \<le> m" by simp
      with Suc n_def show False by simp
    qed
  qed
  have unfold: "lfp (stepF \<Gamma> D \<sigma> n L) = stepF \<Gamma> D \<sigma> n L (lfp (stepF \<Gamma> D \<sigma> n L))"
    by (rule lfp_unfold[OF stepF_mono[OF strat]])
  show ?thesis
  proof
    assume "grants \<Gamma> D \<sigma> (T, p) s ob"
    then have "((T, p), s, ob) \<in> lfp (stepF \<Gamma> D \<sigma> n L)"
      using eval by (simp add: grants_def n_def)
    then have "((T, p), s, ob) \<in> stepF \<Gamma> D \<sigma> n L (lfp (stepF \<Gamma> D \<sigma> n L))"
      using unfold by simp
    with notL body show "(ob, s) \<in> ext D r"
      by (auto simp: stepF_def)
  next
    assume "(ob, s) \<in> ext D r"
    with body have "((T, p), s, ob) \<in> stepF \<Gamma> D \<sigma> n L (lfp (stepF \<Gamma> D \<sigma> n L))"
      by (auto simp: stepF_def n_def)
    then have "((T, p), s, ob) \<in> lfp (stepF \<Gamma> D \<sigma> n L)"
      using unfold by simp
    then show "grants \<Gamma> D \<sigma> (T, p) s ob"
      using eval by (simp add: grants_def n_def)
  qed
qed

text \<open>Safety implies finiteness (Obligation E's precondition, discharged):
  a generative check confines its object to the active domain, every fact
  in the fixpoint tower originates from some satisfaction, hence every
  answer set of a safe registry lives inside \<open>adom D\<close> -- finite whenever
  the database is. This is the semantic content of the groundedness
  validator: without it, a pure condition or exclusion would grant over
  the ambient universe.\<close>

lemma generative_sat_adom:
  assumes "generative c" and "sat \<Gamma> D I T c s ob"
  shows "ob \<in> adom D"
  using assms
proof (induction c)
  case (Terminal r)
  then show ?case by (auto intro: ext_fst_adom)
next
  case (Chain r q)
  then show ?case by (auto intro: ext_fst_adom)
next
  case (CAnd c1 c2)
  then show ?case by auto
next
  case (COr c1 c2)
  then show ?case by auto
qed simp_all

lemma strata_origin:
  assumes strat: "stratified \<Gamma> \<sigma>"
  shows "x \<in> strata \<Gamma> D \<sigma> n \<Longrightarrow>
           \<exists>T p s ob c I. x = ((T, p), s, ob) \<and>
                          perms \<Gamma> T p = Some c \<and> sat \<Gamma> D I T c s ob"
proof (induction n)
  case 0
  have unfold: "strata \<Gamma> D \<sigma> 0 = stepF \<Gamma> D \<sigma> 0 {} (strata \<Gamma> D \<sigma> 0)"
    using lfp_unfold[OF stepF_mono[OF strat]] by simp
  from "0.prems" show ?case
    by (subst (asm) unfold) (auto simp: stepF_def)
next
  case (Suc n)
  have unfold: "strata \<Gamma> D \<sigma> (Suc n) =
          stepF \<Gamma> D \<sigma> (Suc n) (strata \<Gamma> D \<sigma> n) (strata \<Gamma> D \<sigma> (Suc n))"
    using lfp_unfold[OF stepF_mono[OF strat]] by simp
  from Suc.prems
  have "x \<in> stepF \<Gamma> D \<sigma> (Suc n) (strata \<Gamma> D \<sigma> n) (strata \<Gamma> D \<sigma> (Suc n))"
    by (subst (asm) unfold)
  then consider (lower) "x \<in> strata \<Gamma> D \<sigma> n"
    | (new) T p s ob c where "x = ((T, p), s, ob)" "perms \<Gamma> T p = Some c"
        "sat \<Gamma> D (strata \<Gamma> D \<sigma> n \<union> restr \<sigma> (Suc n) (strata \<Gamma> D \<sigma> (Suc n)))
             T c s ob"
    by (auto simp: stepF_def)
  then show ?case
  proof cases
    case lower with Suc.IH show ?thesis by blast
  next
    case new then show ?thesis by blast
  qed
qed

theorem grants_finite:
  assumes strat: "stratified \<Gamma> \<sigma>" and sf: "safe \<Gamma>" and fin: "finite D"
  shows "finite {ob. grants \<Gamma> D \<sigma> k s ob}"
proof -
  have "{ob. grants \<Gamma> D \<sigma> k s ob} \<subseteq> adom D"
  proof
    fix ob assume "ob \<in> {ob. grants \<Gamma> D \<sigma> k s ob}"
    then have "(k, s, ob) \<in> strata \<Gamma> D \<sigma> (\<sigma> k)" by (simp add: grants_def)
    then obtain T p s' ob' c I where eq: "(k, s, ob) = ((T, p), s', ob')"
        and pc: "perms \<Gamma> T p = Some c" and st: "sat \<Gamma> D I T c s' ob'"
      using strata_origin[OF strat] by blast
    from sf pc have "generative c" unfolding safe_def by blast
    from generative_sat_adom[OF this st] eq show "ob \<in> adom D" by auto
  qed
  with adom_finite[OF fin] show ?thesis
    using finite_subset by blast
qed

end
