theory Authz_Enum
  imports Authz_Walker
begin

text \<open>
  Obligation E: the \<open>grants\<close> enumeration is exact.

  The implementation (gen-graph / gen-stream in authz.core) enumerates
  candidates by seeding each key's terminals from the subject and
  closing under consumer-chain edges, with request-local dedupe; when
  the generating closure contains only relations, chains and ors
  ("pure"), candidates are emitted raw, otherwise each candidate is
  verified by the point-check walker. Mathematically the candidate set
  is a least fixed point, so it is modelled here as an inductive
  relation \<open>cand\<close> -- emission order is abstracted (E1/E2, exactness and
  distinctness, are the semantic content; the stream's order-level
  properties remain covered by the differential suite).

  \<open>gterms\<close>/\<open>gchains\<close> mirror gen-positions: nothing under a negation
  generates, a conjunction generates from its first generative conjunct
  (the n-ary AST folds to the binary one), a disjunction from both
  branches. The three results:

    \<open>cand_complete\<close>    -- generation misses nothing: every granted
                         object is a candidate (induction over strata
                         and iterates, riding sat_gen_pos);
    \<open>cand_sound_pure\<close>  -- for pure closures candidates are exactly the
                         grants: the implementation's unverified fast
                         path is exact (this retires the pure-closure
                         argument that lives in a code comment);
    \<open>enum capstones\<close>   -- candidates filtered by the proven walker
                         equal the grants set, and enum_spec holds of
                         their (finite) enumeration.
\<close>

section \<open>Generating positions\<close>

fun gterms :: "check \<Rightarrow> rel set" where
  "gterms (Terminal r) = {r}"
| "gterms (Chain r q) = {}"
| "gterms (AttrEq a v) = {}"
| "gterms (CNot c) = {}"
| "gterms (CAnd c1 c2) = (if generative c1 then gterms c1 else gterms c2)"
| "gterms (COr c1 c2) = gterms c1 \<union> gterms c2"

fun gchains :: "check \<Rightarrow> (rel \<times> perm) set" where
  "gchains (Terminal r) = {}"
| "gchains (Chain r q) = {(r, q)}"
| "gchains (AttrEq a v) = {}"
| "gchains (CNot c) = {}"
| "gchains (CAnd c1 c2) = (if generative c1 then gchains c1 else gchains c2)"
| "gchains (COr c1 c2) = gchains c1 \<union> gchains c2"

text \<open>A generative check that is satisfied yields evidence through one
  of its generating positions -- the completeness of gen-positions.\<close>

lemma sat_gen_pos:
  assumes gen: "generative c" and st: "sat \<Gamma> D I T c s ob"
  shows "(\<exists>r. r \<in> gterms c \<and> (ob, s) \<in> ext D r) \<or>
         (\<exists>r q T' m. (r, q) \<in> gchains c \<and> rels \<Gamma> T r = Some T' \<and>
                     (ob, m) \<in> ext D r \<and> ((T', q), s, m) \<in> I)"
  using gen st
proof (induction c)
  case (Terminal r) then show ?case by auto
next
  case (Chain r q) then show ?case by auto
next
  case (AttrEq a v) then show ?case by simp
next
  case (CNot c) then show ?case by simp
next
  case (CAnd c1 c2)
  show ?case
  proof (cases "generative c1")
    case True
    from CAnd.prems(2) have "sat \<Gamma> D I T c1 s ob" by simp
    from CAnd.IH(1)[OF True this] True show ?thesis by simp
  next
    case False
    with CAnd.prems(1) have "generative c2" by simp
    moreover from CAnd.prems(2) have "sat \<Gamma> D I T c2 s ob" by simp
    ultimately show ?thesis using CAnd.IH(2) False by simp
  qed
next
  case (COr c1 c2)
  from COr.prems(1) have g1: "generative c1" and g2: "generative c2" by simp_all
  from COr.prems(2) have "sat \<Gamma> D I T c1 s ob \<or> sat \<Gamma> D I T c2 s ob" by simp
  then show ?case
  proof
    assume "sat \<Gamma> D I T c1 s ob"
    from COr.IH(1)[OF g1 this] show ?thesis
    proof (elim disjE)
      assume "\<exists>r. r \<in> gterms c1 \<and> (ob, s) \<in> ext D r"
      then show ?thesis by force
    next
      assume "\<exists>r q T' m. (r, q) \<in> gchains c1 \<and> rels \<Gamma> T r = Some T' \<and>
                (ob, m) \<in> ext D r \<and> ((T', q), s, m) \<in> I"
      then show ?thesis by force
    qed
  next
    assume "sat \<Gamma> D I T c2 s ob"
    from COr.IH(2)[OF g2 this] show ?thesis
    proof (elim disjE)
      assume "\<exists>r. r \<in> gterms c2 \<and> (ob, s) \<in> ext D r"
      then show ?thesis by force
    next
      assume "\<exists>r q T' m. (r, q) \<in> gchains c2 \<and> rels \<Gamma> T r = Some T' \<and>
                (ob, m) \<in> ext D r \<and> ((T', q), s, m) \<in> I"
      then show ?thesis by force
    qed
  qed
qed

text \<open>Purity: only relations, chains and disjunctions -- the closure
  shape for which the implementation skips per-candidate verification
  (matching node-ops in authz.core: any And/Not/AttrEq forces it).\<close>

fun pure :: "check \<Rightarrow> bool" where
  "pure (Terminal r) = True"
| "pure (Chain r q) = True"
| "pure (AttrEq a v) = False"
| "pure (CNot c) = False"
| "pure (CAnd c1 c2) = False"
| "pure (COr c1 c2) = (pure c1 \<and> pure c2)"

text \<open>For pure checks the converse of \<open>sat_gen_pos\<close> holds: evidence at
  a generating position already satisfies the whole check.\<close>

lemma gterm_sat_pure:
  assumes "pure c" and "r \<in> gterms c" and "(ob, s) \<in> ext D r"
  shows "sat \<Gamma> D I T c s ob"
  using assms
proof (induction c)
  case (COr c1 c2)
  then show ?case by (cases "r \<in> gterms c1") auto
qed auto

lemma gchain_sat_pure:
  assumes "pure c" and "(r, q) \<in> gchains c" and "rels \<Gamma> T r = Some T'"
      and "(ob, m) \<in> ext D r" and "((T', q), s, m) \<in> I"
  shows "sat \<Gamma> D I T c s ob"
  using assms
proof (induction c)
  case (COr c1 c2)
  then show ?case by (cases "(r, q) \<in> gchains c1") auto
qed auto

section \<open>The candidate relation\<close>

inductive cand :: "reg \<Rightarrow> db \<Rightarrow> eid \<Rightarrow> key \<Rightarrow> eid \<Rightarrow> bool"
  for \<Gamma> :: reg and D :: db and s :: eid where
  seed: "\<lbrakk>perms \<Gamma> T p = Some c; r \<in> gterms c; (ob, s) \<in> ext D r\<rbrakk>
           \<Longrightarrow> cand \<Gamma> D s (T, p) ob"
| chain: "\<lbrakk>perms \<Gamma> T p = Some c; (r, q) \<in> gchains c; rels \<Gamma> T r = Some T';
           cand \<Gamma> D s (T', q) m; (ob, m) \<in> ext D r\<rbrakk>
           \<Longrightarrow> cand \<Gamma> D s (T, p) ob"

lemma cand_adom:
  assumes "cand \<Gamma> D s k ob"
  shows "ob \<in> adom D"
  using assms by (induction rule: cand.induct) (auto intro: ext_fst_adom)

lemma cand_finite:
  assumes "finite D"
  shows "finite {ob. cand \<Gamma> D s k ob}"
proof -
  have "{ob. cand \<Gamma> D s k ob} \<subseteq> adom D" using cand_adom by blast
  with adom_finite[OF assms] show ?thesis using finite_subset by blast
qed

section \<open>Completeness: generation misses nothing\<close>

lemma cand_complete_iter:
  assumes strat: "stratified \<Gamma> \<sigma>" and sf: "safe \<Gamma>"
  shows "((T, p), s, ob) \<in> iterF \<Gamma> D \<sigma> n m \<Longrightarrow> \<sigma> (T, p) = n
           \<Longrightarrow> cand \<Gamma> D s (T, p) ob"
proof (induction n arbitrary: T p m ob rule: less_induct)
  case (less n)
  from less.prems show ?case
  proof (induction m arbitrary: T p ob)
    case 0 then show ?case by simp
  next
    case (Suc m)
    from Suc.prems(1)
    have "((T, p), s, ob)
            \<in> stepF \<Gamma> D \<sigma> n (lowinterp \<Gamma> D \<sigma> n) (iterF \<Gamma> D \<sigma> n m)"
      by (simp add: iterF_Suc)
    moreover have "((T, p), s, ob) \<notin> lowinterp \<Gamma> D \<sigma> n"
      using lowinterp_stratum_bound[OF strat] Suc.prems(2) by fastforce
    ultimately obtain c where pc: "perms \<Gamma> T p = Some c"
        and st: "sat \<Gamma> D (lowinterp \<Gamma> D \<sigma> n \<union> restr \<sigma> n (iterF \<Gamma> D \<sigma> n m))
                   T c s ob"
      by (auto simp: stepF_def)
    have gen: "generative c" using sf pc unfolding safe_def by blast
    from sat_gen_pos[OF gen st]
    show ?case
    proof
      assume "\<exists>r. r \<in> gterms c \<and> (ob, s) \<in> ext D r"
      then obtain r where "r \<in> gterms c" "(ob, s) \<in> ext D r" by blast
      with pc show ?thesis by (blast intro: cand.seed)
    next
      assume "\<exists>r q T' m'. (r, q) \<in> gchains c \<and> rels \<Gamma> T r = Some T' \<and>
                (ob, m') \<in> ext D r \<and>
                ((T', q), s, m')
                  \<in> lowinterp \<Gamma> D \<sigma> n \<union> restr \<sigma> n (iterF \<Gamma> D \<sigma> n m)"
      then obtain r q T' m' where gc: "(r, q) \<in> gchains c"
          and rT: "rels \<Gamma> T r = Some T'"
          and em: "(ob, m') \<in> ext D r"
          and fmem: "((T', q), s, m')
                       \<in> lowinterp \<Gamma> D \<sigma> n \<union> restr \<sigma> n (iterF \<Gamma> D \<sigma> n m)"
        by blast
      have "cand \<Gamma> D s (T', q) m'"
      proof (cases "((T', q), s, m') \<in> restr \<sigma> n (iterF \<Gamma> D \<sigma> n m)")
        case True
        then have "\<sigma> (T', q) = n" and "((T', q), s, m') \<in> iterF \<Gamma> D \<sigma> n m"
          by (auto simp: restr_def)
        then show ?thesis by (rule Suc.IH[rotated])
      next
        case False
        with fmem have lmem: "((T', q), s, m') \<in> lowinterp \<Gamma> D \<sigma> n" by blast
        have sn: "\<sigma> (T', q) < n"
          using lowinterp_stratum_bound[OF strat lmem] by simp
        have "grants \<Gamma> D \<sigma> (T', q) s m'"
          using low_iff[OF strat sn] lmem by blast
        then have "((T', q), s, m') \<in> strata \<Gamma> D \<sigma> (\<sigma> (T', q))"
          by (simp add: grants_def)
        then obtain m2 where "((T', q), s, m') \<in> iterF \<Gamma> D \<sigma> (\<sigma> (T', q)) m2"
          using strata_iter[OF strat] by blast
        from less.IH[OF sn this] show ?thesis by simp
      qed
      with pc gc rT em show ?thesis by (blast intro: cand.chain)
    qed
  qed
qed

theorem cand_complete:
  assumes strat: "stratified \<Gamma> \<sigma>" and sf: "safe \<Gamma>"
      and g: "grants \<Gamma> D \<sigma> k s ob"
  shows "cand \<Gamma> D s k ob"
proof -
  obtain T p where k: "k = (T, p)" by (cases k) blast
  from g k have "((T, p), s, ob) \<in> strata \<Gamma> D \<sigma> (\<sigma> (T, p))"
    by (simp add: grants_def)
  then obtain m where "((T, p), s, ob) \<in> iterF \<Gamma> D \<sigma> (\<sigma> (T, p)) m"
    using strata_iter[OF strat] by blast
  from cand_complete_iter[OF strat sf this] k show ?thesis by simp
qed

section \<open>Soundness on pure closures\<close>

definition chain_edge :: "reg \<Rightarrow> key \<Rightarrow> key \<Rightarrow> bool" where
  "chain_edge \<Gamma> k k' \<longleftrightarrow>
     (\<exists>c r. perms \<Gamma> (fst k) (snd k) = Some c \<and> (r, snd k') \<in> gchains c \<and>
            rels \<Gamma> (fst k) r = Some (fst k'))"

definition pure_from :: "reg \<Rightarrow> key \<Rightarrow> bool" where
  "pure_from \<Gamma> k \<longleftrightarrow>
     (\<forall>k'. (chain_edge \<Gamma>)\<^sup>*\<^sup>* k k' \<longrightarrow>
        (\<forall>c. perms \<Gamma> (fst k') (snd k') = Some c \<longrightarrow> pure c))"

lemma pure_from_self:
  assumes "pure_from \<Gamma> k" and "perms \<Gamma> (fst k) (snd k) = Some c"
  shows "pure c"
  using assms unfolding pure_from_def by blast

lemma pure_from_step:
  assumes "pure_from \<Gamma> k" and "chain_edge \<Gamma> k k'"
  shows "pure_from \<Gamma> k'"
  using assms unfolding pure_from_def
  by (meson converse_rtranclp_into_rtranclp)

theorem cand_sound_pure:
  assumes strat: "stratified \<Gamma> \<sigma>"
      and c: "cand \<Gamma> D s k ob" and pf: "pure_from \<Gamma> k"
  shows "grants \<Gamma> D \<sigma> k s ob"
  using c pf
proof (induction rule: cand.induct)
  case (seed T p c r ob)
  have pc: "pure c" using pure_from_self[OF seed.prems] seed.hyps(1) by simp
  have "sat \<Gamma> D (ginterp \<Gamma> D \<sigma>) T c s ob"
    using gterm_sat_pure[OF pc seed.hyps(2) seed.hyps(3)] .
  then show ?case using grants_iff_sat[OF strat seed.hyps(1)] by simp
next
  case (chain T p c r q T' m ob)
  have edge: "chain_edge \<Gamma> (T, p) (T', q)"
    unfolding chain_edge_def using chain.hyps(1,2,3) by force
  have "grants \<Gamma> D \<sigma> (T', q) s m"
    using chain.IH pure_from_step[OF chain.prems edge] by simp
  then have gm: "((T', q), s, m) \<in> ginterp \<Gamma> D \<sigma>" by (simp add: ginterp_iff)
  have pc: "pure c" using pure_from_self[OF chain.prems] chain.hyps(1) by simp
  have "sat \<Gamma> D (ginterp \<Gamma> D \<sigma>) T c s ob"
    using gchain_sat_pure[OF pc chain.hyps(2,3) chain.hyps(5) gm] .
  then show ?case using grants_iff_sat[OF strat chain.hyps(1)] by simp
qed

section \<open>Obligation E, discharged\<close>

text \<open>The pure fast path is exact: for a pure generating closure the
  raw candidate set IS the answer set.\<close>

theorem enum_pure_exact:
  assumes strat: "stratified \<Gamma> \<sigma>" and sf: "safe \<Gamma>" and pf: "pure_from \<Gamma> k"
  shows "{ob. cand \<Gamma> D s k ob} = {ob. grants \<Gamma> D \<sigma> k s ob}"
  using cand_complete[OF strat sf] cand_sound_pure[OF strat _ pf] by blast

text \<open>The verified path is exact for every closure: candidates filtered
  by the (proven) walker are the answer set.\<close>

theorem enum_verified_exact:
  assumes strat: "stratified \<Gamma> \<sigma>" and sf: "safe \<Gamma>"
      and finD: "finite D" and finK: "finite (rkeys \<Gamma>)"
      and pc: "perms \<Gamma> T p = Some c"
      and fuel: "wbound \<Gamma> D {} c \<le> f"
  shows "{ob. cand \<Gamma> D s (T, p) ob \<and> walk f \<Gamma> D {} T c s ob}
           = {ob. grants \<Gamma> D \<sigma> (T, p) s ob}"
proof
  show "{ob. cand \<Gamma> D s (T, p) ob \<and> walk f \<Gamma> D {} T c s ob}
          \<subseteq> {ob. grants \<Gamma> D \<sigma> (T, p) s ob}"
    using walker_sound[OF strat finD finK pc fuel] by blast
next
  show "{ob. grants \<Gamma> D \<sigma> (T, p) s ob}
          \<subseteq> {ob. cand \<Gamma> D s (T, p) ob \<and> walk f \<Gamma> D {} T c s ob}"
    using cand_complete[OF strat sf]
          walker_complete[OF strat finD finK pc _ fuel] by blast
qed

text \<open>And enum_spec (E1: exactness, E2: distinctness) holds of the
  model's emission -- any duplicate-free enumeration of the candidate
  set, verified or pure. E3 (determinism) is trivial for the functional
  model; the implementation's emission order rests on Datomic index
  iteration order and remains covered by the differential suite.\<close>

definition enum_spec :: "reg \<Rightarrow> db \<Rightarrow> (key \<Rightarrow> nat) \<Rightarrow> key \<Rightarrow> eid \<Rightarrow> eid list \<Rightarrow> bool" where
  "enum_spec \<Gamma> D \<sigma> k s xs \<longleftrightarrow>
     distinct xs \<and> set xs = {ob. grants \<Gamma> D \<sigma> k s ob}"

theorem enum_spec_verified:
  assumes strat: "stratified \<Gamma> \<sigma>" and sf: "safe \<Gamma>"
      and finD: "finite D" and finK: "finite (rkeys \<Gamma>)"
      and pc: "perms \<Gamma> T p = Some c"
      and fuel: "wbound \<Gamma> D {} c \<le> f"
  shows "enum_spec \<Gamma> D \<sigma> (T, p) s
           (sorted_list_of_set
              {ob. cand \<Gamma> D s (T, p) ob \<and> walk f \<Gamma> D {} T c s ob})"
proof -
  have eq: "{ob. cand \<Gamma> D s (T, p) ob \<and> walk f \<Gamma> D {} T c s ob}
              = {ob. grants \<Gamma> D \<sigma> (T, p) s ob}"
    by (rule enum_verified_exact[OF strat sf finD finK pc fuel])
  have fin: "finite {ob. cand \<Gamma> D s (T, p) ob \<and> walk f \<Gamma> D {} T c s ob}"
    using cand_finite[OF finD] by (rule rev_finite_subset) blast
  show ?thesis
    unfolding enum_spec_def using eq fin by simp
qed

theorem enum_spec_pure:
  assumes strat: "stratified \<Gamma> \<sigma>" and sf: "safe \<Gamma>"
      and finD: "finite D" and pf: "pure_from \<Gamma> k"
  shows "enum_spec \<Gamma> D \<sigma> k s (sorted_list_of_set {ob. cand \<Gamma> D s k ob})"
proof -
  have eq: "{ob. cand \<Gamma> D s k ob} = {ob. grants \<Gamma> D \<sigma> k s ob}"
    by (rule enum_pure_exact[OF strat sf pf])
  have fin: "finite {ob. cand \<Gamma> D s k ob}"
    by (rule cand_finite[OF finD])
  show ?thesis
    unfolding enum_spec_def
    using fin eq by simp
qed

end
