theory Authz_Subjects
  imports Authz_Kernel
begin

text \<open>
  The reverse enumeration ("who has access to X?") is exact — the mirror
  of Obligation E with the roles swapped. \<open>scand\<close> models the (key,
  object)-state traversal in authz.core/subjects: terminals emit their
  targets as subjects, chains move the OBJECT one hop and recurse. The
  same generating-position analysis (\<open>gterms\<close>/\<open>gchains\<close>) drives both
  directions, so completeness rides \<open>sat_gen_pos\<close> unchanged, and
  soundness on pure closures reuses \<open>gterm_sat_pure\<close>/\<open>gchain_sat_pure\<close>
  verbatim.
\<close>

inductive scand :: "reg \<Rightarrow> db \<Rightarrow> key \<Rightarrow> eid \<Rightarrow> eid \<Rightarrow> bool"
  for \<Gamma> :: reg and D :: db where
  seed: "\<lbrakk>perms \<Gamma> T p = Some c; r \<in> gterms c; (ob, s) \<in> ext D r\<rbrakk>
           \<Longrightarrow> scand \<Gamma> D (T, p) ob s"
| chain: "\<lbrakk>perms \<Gamma> T p = Some c; (r, q) \<in> gchains c; rels \<Gamma> T r = Some T';
           (ob, m) \<in> ext D r; scand \<Gamma> D (T', q) m s\<rbrakk>
           \<Longrightarrow> scand \<Gamma> D (T, p) ob s"

lemma scand_adom:
  assumes "scand \<Gamma> D k ob s"
  shows "s \<in> adom D"
  using assms by (induction rule: scand.induct) (auto intro: ext_snd_adom)

lemma scand_finite:
  assumes "finite D"
  shows "finite {s. scand \<Gamma> D k ob s}"
proof -
  have "{s. scand \<Gamma> D k ob s} \<subseteq> adom D" using scand_adom by blast
  with adom_finite[OF assms] show ?thesis using finite_subset by blast
qed

section \<open>Completeness: the reverse traversal misses no subject\<close>

lemma scand_complete_iter:
  assumes strat: "stratified \<Gamma> \<sigma>" and sf: "safe \<Gamma>"
  shows "((T, p), s, ob) \<in> iterF \<Gamma> D \<sigma> n m \<Longrightarrow> \<sigma> (T, p) = n
           \<Longrightarrow> scand \<Gamma> D (T, p) ob s"
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
      with pc show ?thesis by (blast intro: scand.seed)
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
      have "scand \<Gamma> D (T', q) m' s"
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
      with pc gc rT em show ?thesis by (blast intro: scand.chain)
    qed
  qed
qed

theorem scand_complete:
  assumes strat: "stratified \<Gamma> \<sigma>" and sf: "safe \<Gamma>"
      and g: "grants \<Gamma> D \<sigma> k s ob"
  shows "scand \<Gamma> D k ob s"
proof -
  obtain T p where k: "k = (T, p)" by (cases k) blast
  from g k have "((T, p), s, ob) \<in> strata \<Gamma> D \<sigma> (\<sigma> (T, p))"
    by (simp add: grants_def)
  then obtain m where "((T, p), s, ob) \<in> iterF \<Gamma> D \<sigma> (\<sigma> (T, p)) m"
    using strata_iter[OF strat] by blast
  from scand_complete_iter[OF strat sf this] k show ?thesis by simp
qed

section \<open>Soundness on pure closures\<close>

theorem scand_sound_pure:
  assumes strat: "stratified \<Gamma> \<sigma>"
      and c: "scand \<Gamma> D k ob s" and pf: "pure_from \<Gamma> k"
  shows "grants \<Gamma> D \<sigma> k s ob"
  using c pf
proof (induction rule: scand.induct)
  case (seed T p c r ob s)
  have pc: "pure c" using pure_from_self[OF seed.prems] seed.hyps(1) by simp
  have "sat \<Gamma> D (ginterp \<Gamma> D \<sigma>) T c s ob"
    using gterm_sat_pure[OF pc seed.hyps(2) seed.hyps(3)] .
  then show ?case using grants_iff_sat[OF strat seed.hyps(1)] by simp
next
  case (chain T p c r q T' ob m s)
  have edge: "chain_edge \<Gamma> (T, p) (T', q)"
    unfolding chain_edge_def using chain.hyps(1,2,3) by force
  have "grants \<Gamma> D \<sigma> (T', q) s m"
    using chain.IH pure_from_step[OF chain.prems edge] by simp
  then have gm: "((T', q), s, m) \<in> ginterp \<Gamma> D \<sigma>" by (simp add: ginterp_iff)
  have pc: "pure c" using pure_from_self[OF chain.prems] chain.hyps(1) by simp
  have "sat \<Gamma> D (ginterp \<Gamma> D \<sigma>) T c s ob"
    using gchain_sat_pure[OF pc chain.hyps(2,3) chain.hyps(4) gm] .
  then show ?case using grants_iff_sat[OF strat chain.hyps(1)] by simp
qed

section \<open>The reverse enumeration is exact\<close>

theorem subjects_pure_exact:
  assumes strat: "stratified \<Gamma> \<sigma>" and sf: "safe \<Gamma>" and pf: "pure_from \<Gamma> k"
  shows "{s. scand \<Gamma> D k ob s} = {s. grants \<Gamma> D \<sigma> k s ob}"
  using scand_complete[OF strat sf] scand_sound_pure[OF strat _ pf] by blast

theorem subjects_verified_exact:
  assumes strat: "stratified \<Gamma> \<sigma>" and sf: "safe \<Gamma>"
      and finD: "finite D" and finK: "finite (rkeys \<Gamma>)"
      and pc: "perms \<Gamma> T p = Some c"
      and fuel: "wbound \<Gamma> D {} c \<le> f"
  shows "{s. scand \<Gamma> D (T, p) ob s \<and> walk f \<Gamma> D {} T c s ob}
           = {s. grants \<Gamma> D \<sigma> (T, p) s ob}"
proof
  show "{s. scand \<Gamma> D (T, p) ob s \<and> walk f \<Gamma> D {} T c s ob}
          \<subseteq> {s. grants \<Gamma> D \<sigma> (T, p) s ob}"
    using walker_sound[OF strat finD finK pc fuel] by blast
next
  show "{s. grants \<Gamma> D \<sigma> (T, p) s ob}
          \<subseteq> {s. scand \<Gamma> D (T, p) ob s \<and> walk f \<Gamma> D {} T c s ob}"
    using scand_complete[OF strat sf]
          walker_complete[OF strat finD finK pc _ fuel] by blast
qed

end
