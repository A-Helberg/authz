theory Authz_Kleene
  imports Authz_Semantics
begin

text \<open>
  Finite derivations: each stratum's least fixed point is the union of
  its finite iterates (Kleene), because satisfaction is finitary -- a
  satisfying assignment touches one fact per chain node, so satisfaction
  over an increasing chain of interpretations holds at some finite
  stage. On top of this, \<open>drank\<close> assigns every granted fact its minimal
  iterate ("derivation height"), and \<open>drank_step\<close> shows the facts a
  derivation consumes at the same stratum sit strictly below it -- the
  well-founded measure the walker-completeness induction descends on.
\<close>

definition iterF :: "reg \<Rightarrow> db \<Rightarrow> (key \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> interp" where
  "iterF \<Gamma> D \<sigma> n m = ((stepF \<Gamma> D \<sigma> n (lowinterp \<Gamma> D \<sigma> n)) ^^ m) {}"

lemma iterF_0 [simp]: "iterF \<Gamma> D \<sigma> n 0 = {}"
  by (simp add: iterF_def)

lemma iterF_Suc:
  "iterF \<Gamma> D \<sigma> n (Suc m)
     = stepF \<Gamma> D \<sigma> n (lowinterp \<Gamma> D \<sigma> n) (iterF \<Gamma> D \<sigma> n m)"
  by (simp add: iterF_def)

lemma iterF_mono_step:
  assumes strat: "stratified \<Gamma> \<sigma>"
  shows "iterF \<Gamma> D \<sigma> n m \<subseteq> iterF \<Gamma> D \<sigma> n (Suc m)"
proof (induction m)
  case 0 show ?case by simp
next
  case (Suc m)
  have "stepF \<Gamma> D \<sigma> n (lowinterp \<Gamma> D \<sigma> n) (iterF \<Gamma> D \<sigma> n m)
          \<subseteq> stepF \<Gamma> D \<sigma> n (lowinterp \<Gamma> D \<sigma> n) (iterF \<Gamma> D \<sigma> n (Suc m))"
    by (rule monoD[OF stepF_mono[OF strat] Suc.IH])
  then show ?case by (simp add: iterF_Suc)
qed

lemma iterF_mono:
  assumes strat: "stratified \<Gamma> \<sigma>" and le: "i \<le> j"
  shows "iterF \<Gamma> D \<sigma> n i \<subseteq> iterF \<Gamma> D \<sigma> n j"
  using le
proof (induction j)
  case (Suc j)
  then consider "i \<le> j" | "i = Suc j" by fastforce
  then show ?case
  proof cases
    case 1
    with Suc.IH iterF_mono_step[OF strat] show ?thesis by blast
  qed simp
qed simp

lemma iterF_le_strata:
  assumes strat: "stratified \<Gamma> \<sigma>"
  shows "iterF \<Gamma> D \<sigma> n m \<subseteq> strata \<Gamma> D \<sigma> n"
proof (induction m)
  case 0 show ?case by simp
next
  case (Suc m)
  have "stepF \<Gamma> D \<sigma> n (lowinterp \<Gamma> D \<sigma> n) (iterF \<Gamma> D \<sigma> n m)
          \<subseteq> stepF \<Gamma> D \<sigma> n (lowinterp \<Gamma> D \<sigma> n) (strata \<Gamma> D \<sigma> n)"
    by (rule monoD[OF stepF_mono[OF strat] Suc.IH])
  also have "\<dots> = strata \<Gamma> D \<sigma> n"
  proof -
    have "strata \<Gamma> D \<sigma> n = lfp (stepF \<Gamma> D \<sigma> n (lowinterp \<Gamma> D \<sigma> n))"
      by (rule strata_lfp)
    then show ?thesis
      using lfp_unfold[OF stepF_mono[OF strat]] by metis
  qed
  finally show ?case by (simp add: iterF_Suc)
qed

text \<open>Satisfaction is finitary over increasing chains whose facts at
  negated keys are constant -- the same frozen-negation side condition
  as \<open>sat_mono\<close>, and the same proof skeleton.\<close>

lemma sat_chain:
  fixes J :: "nat \<Rightarrow> interp"
  assumes inc: "\<And>i j. i \<le> j \<Longrightarrow> J i \<subseteq> J j"
      and frozen: "\<And>k s' m i. (k, True) \<in> deps \<Gamma> T c \<Longrightarrow>
                     ((k, s', m) \<in> J i) = ((k, s', m) \<in> (\<Union>i. J i))"
      and st: "sat \<Gamma> D (\<Union>i. J i) T c s ob"
  shows "\<exists>i. sat \<Gamma> D (J i) T c s ob"
  using frozen st
proof (induction c arbitrary: s ob)
  case (Terminal r)
  then show ?case by auto
next
  case (AttrEq a v)
  then show ?case by auto
next
  case (Chain r q)
  from Chain.prems(2) obtain T' m where
    "rels \<Gamma> T r = Some T'" "(ob, m) \<in> ext D r" "((T', q), s, m) \<in> (\<Union>i. J i)"
    by auto
  then show ?case by auto
next
  case (CNot c)
  have agree: "\<And>k s' m. k \<in> fst ` deps \<Gamma> T c \<Longrightarrow>
                 ((k, s', m) \<in> J 0) = ((k, s', m) \<in> (\<Union>i. J i))"
  proof -
    fix k s' m assume "k \<in> fst ` deps \<Gamma> T c"
    then obtain b where "(k, b) \<in> deps \<Gamma> T c" by auto
    then have "(k, True) \<in> deps \<Gamma> T (CNot c)" by force
    then show "((k, s', m) \<in> J 0) = ((k, s', m) \<in> (\<Union>i. J i))"
      by (rule CNot.prems(1))
  qed
  have "sat \<Gamma> D (J 0) T c s ob = sat \<Gamma> D (\<Union>i. J i) T c s ob"
    by (rule sat_invariant) (rule agree)
  with CNot.prems(2) have "sat \<Gamma> D (J 0) T (CNot c) s ob" by simp
  then show ?case by blast
next
  case (CAnd c1 c2)
  have frz1: "\<And>k s' m i. (k, True) \<in> deps \<Gamma> T c1 \<Longrightarrow>
                ((k, s', m) \<in> J i) = ((k, s', m) \<in> (\<Union>i. J i))"
    by (rule CAnd.prems(1)) simp
  have frz2: "\<And>k s' m i. (k, True) \<in> deps \<Gamma> T c2 \<Longrightarrow>
                ((k, s', m) \<in> J i) = ((k, s', m) \<in> (\<Union>i. J i))"
    by (rule CAnd.prems(1)) simp
  from CAnd.prems(2) have "sat \<Gamma> D (\<Union>i. J i) T c1 s ob"
                          "sat \<Gamma> D (\<Union>i. J i) T c2 s ob" by simp_all
  with CAnd.IH(1)[OF frz1] CAnd.IH(2)[OF frz2]
  obtain i1 i2 where s1: "sat \<Gamma> D (J i1) T c1 s ob"
                 and s2: "sat \<Gamma> D (J i2) T c2 s ob" by blast
  have m1: "sat \<Gamma> D (J (max i1 i2)) T c1 s ob"
  proof (rule sat_mono)
    show "J i1 \<subseteq> J (max i1 i2)" by (rule inc) simp
  next
    fix k s' m assume "(k, True) \<in> deps \<Gamma> T c1"
    then show "((k, s', m) \<in> J i1) = ((k, s', m) \<in> J (max i1 i2))"
      using frz1 by metis
  next
    show "sat \<Gamma> D (J i1) T c1 s ob" by (fact s1)
  qed
  have m2: "sat \<Gamma> D (J (max i1 i2)) T c2 s ob"
  proof (rule sat_mono)
    show "J i2 \<subseteq> J (max i1 i2)" by (rule inc) simp
  next
    fix k s' m assume "(k, True) \<in> deps \<Gamma> T c2"
    then show "((k, s', m) \<in> J i2) = ((k, s', m) \<in> J (max i1 i2))"
      using frz2 by metis
  next
    show "sat \<Gamma> D (J i2) T c2 s ob" by (fact s2)
  qed
  from m1 m2 have "sat \<Gamma> D (J (max i1 i2)) T (CAnd c1 c2) s ob" by simp
  then show ?case by blast
next
  case (COr c1 c2)
  have frz1: "\<And>k s' m i. (k, True) \<in> deps \<Gamma> T c1 \<Longrightarrow>
                ((k, s', m) \<in> J i) = ((k, s', m) \<in> (\<Union>i. J i))"
    by (rule COr.prems(1)) simp
  have frz2: "\<And>k s' m i. (k, True) \<in> deps \<Gamma> T c2 \<Longrightarrow>
                ((k, s', m) \<in> J i) = ((k, s', m) \<in> (\<Union>i. J i))"
    by (rule COr.prems(1)) simp
  from COr.prems(2) have "sat \<Gamma> D (\<Union>i. J i) T c1 s ob \<or> sat \<Gamma> D (\<Union>i. J i) T c2 s ob"
    by simp
  with COr.IH(1)[OF frz1] COr.IH(2)[OF frz2]
  obtain i where "sat \<Gamma> D (J i) T c1 s ob \<or> sat \<Gamma> D (J i) T c2 s ob" by blast
  then show ?case by auto
qed

text \<open>Strict stratum descent through negation -- the strict companion of
  \<open>deps_stratum_le\<close>.\<close>

lemma deps_stratum_less:
  assumes strat: "stratified \<Gamma> \<sigma>" and pc: "perms \<Gamma> T p = Some c"
      and d: "(k', True) \<in> deps \<Gamma> T c"
  shows "\<sigma> k' < \<sigma> (T, p)"
  using strat[unfolded stratified_def, rule_format, OF pc d] by simp

text \<open>Kleene: each stratum is the union of its finite iterates.\<close>

theorem strata_iter:
  assumes strat: "stratified \<Gamma> \<sigma>"
  shows "strata \<Gamma> D \<sigma> n = (\<Union>m. iterF \<Gamma> D \<sigma> n m)"
proof
  show "(\<Union>m. iterF \<Gamma> D \<sigma> n m) \<subseteq> strata \<Gamma> D \<sigma> n"
    using iterF_le_strata[OF strat] by blast
next
  have closed: "stepF \<Gamma> D \<sigma> n (lowinterp \<Gamma> D \<sigma> n) (\<Union>m. iterF \<Gamma> D \<sigma> n m)
                  \<subseteq> (\<Union>m. iterF \<Gamma> D \<sigma> n m)"
  proof
    fix x
    assume "x \<in> stepF \<Gamma> D \<sigma> n (lowinterp \<Gamma> D \<sigma> n) (\<Union>m. iterF \<Gamma> D \<sigma> n m)"
    then consider (lower) "x \<in> lowinterp \<Gamma> D \<sigma> n"
      | (new) T p s ob c where "x = ((T, p), s, ob)" "\<sigma> (T, p) = n"
          "perms \<Gamma> T p = Some c"
          "sat \<Gamma> D (lowinterp \<Gamma> D \<sigma> n \<union> restr \<sigma> n (\<Union>m. iterF \<Gamma> D \<sigma> n m)) T c s ob"
      by (auto simp: stepF_def)
    then show "x \<in> (\<Union>m. iterF \<Gamma> D \<sigma> n m)"
    proof cases
      case lower
      then have "x \<in> iterF \<Gamma> D \<sigma> n (Suc 0)"
        by (simp add: iterF_Suc stepF_def)
      then show ?thesis by blast
    next
      case new
      define J where "J = (\<lambda>i. lowinterp \<Gamma> D \<sigma> n \<union> restr \<sigma> n (iterF \<Gamma> D \<sigma> n i))"
      have Jun: "(\<Union>i. J i) = lowinterp \<Gamma> D \<sigma> n \<union> restr \<sigma> n (\<Union>m. iterF \<Gamma> D \<sigma> n m)"
        by (auto simp: J_def restr_def)
      have inc: "\<And>i j. i \<le> j \<Longrightarrow> J i \<subseteq> J j"
      proof -
        fix i j :: nat assume "i \<le> j"
        then have "iterF \<Gamma> D \<sigma> n i \<subseteq> iterF \<Gamma> D \<sigma> n j"
          by (rule iterF_mono[OF strat])
        then show "J i \<subseteq> J j" by (auto simp: J_def restr_def)
      qed
      have frozen: "\<And>k s' m i. (k, True) \<in> deps \<Gamma> T c \<Longrightarrow>
                      ((k, s', m) \<in> J i) = ((k, s', m) \<in> (\<Union>i. J i))"
      proof -
        fix k s' m i assume "(k, True) \<in> deps \<Gamma> T c"
        with deps_stratum_less[OF strat new(3)] new(2) have "\<sigma> k < n" by simp
        then have "\<And>X. (k, s', m) \<notin> restr \<sigma> n X" by (auto simp: restr_def)
        then show "((k, s', m) \<in> J i) = ((k, s', m) \<in> (\<Union>i. J i))"
          unfolding J_def Jun[unfolded J_def] by blast
      qed
      from new(4) have "sat \<Gamma> D (\<Union>i. J i) T c s ob" by (simp add: Jun)
      from sat_chain[OF inc frozen this]
      obtain i where "sat \<Gamma> D (J i) T c s ob" by blast
      with new have "x \<in> stepF \<Gamma> D \<sigma> n (lowinterp \<Gamma> D \<sigma> n) (iterF \<Gamma> D \<sigma> n i)"
        by (auto simp: stepF_def J_def)
      then have "x \<in> iterF \<Gamma> D \<sigma> n (Suc i)" by (simp add: iterF_Suc)
      then show ?thesis by blast
    qed
  qed
  have "strata \<Gamma> D \<sigma> n \<subseteq> (\<Union>m. iterF \<Gamma> D \<sigma> n m)"
    unfolding strata_lfp by (rule lfp_lowerbound) (rule closed)
  then show "strata \<Gamma> D \<sigma> n \<subseteq> (\<Union>m. iterF \<Gamma> D \<sigma> n m)" .
qed

text \<open>Derivation rank: the minimal iterate containing a granted fact.\<close>

definition drank :: "reg \<Rightarrow> db \<Rightarrow> (key \<Rightarrow> nat) \<Rightarrow> key \<times> eid \<times> eid \<Rightarrow> nat" where
  "drank \<Gamma> D \<sigma> x = (LEAST m. x \<in> iterF \<Gamma> D \<sigma> (\<sigma> (fst x)) m)"

lemma drank_in:
  assumes strat: "stratified \<Gamma> \<sigma>" and g: "grants \<Gamma> D \<sigma> k s ob"
  shows "(k, s, ob) \<in> iterF \<Gamma> D \<sigma> (\<sigma> k) (drank \<Gamma> D \<sigma> (k, s, ob))"
proof -
  from g have "(k, s, ob) \<in> strata \<Gamma> D \<sigma> (\<sigma> k)" by (simp add: grants_def)
  then obtain m where "(k, s, ob) \<in> iterF \<Gamma> D \<sigma> (\<sigma> k) m"
    using strata_iter[OF strat] by blast
  then show ?thesis
    unfolding drank_def by (metis fst_conv LeastI)
qed

lemma drank_le:
  assumes "(k, s, ob) \<in> iterF \<Gamma> D \<sigma> (\<sigma> k) m"
  shows "drank \<Gamma> D \<sigma> (k, s, ob) \<le> m"
  using assms unfolding drank_def by (metis fst_conv Least_le)

lemma drank_pos:
  assumes strat: "stratified \<Gamma> \<sigma>" and g: "grants \<Gamma> D \<sigma> k s ob"
  shows "0 < drank \<Gamma> D \<sigma> (k, s, ob)"
proof (rule ccontr)
  assume "\<not> 0 < drank \<Gamma> D \<sigma> (k, s, ob)"
  then have "drank \<Gamma> D \<sigma> (k, s, ob) = 0" by simp
  with drank_in[OF strat g] show False by simp
qed

lemma drank_not_below:
  assumes "m < drank \<Gamma> D \<sigma> (k, s, ob)"
  shows "(k, s, ob) \<notin> iterF \<Gamma> D \<sigma> (\<sigma> k) m"
  using assms drank_le leD by blast

text \<open>The derivation-step lemma: a granted fact's body is satisfied one
  iterate below its rank, so every same-stratum fact a derivation
  consumes has strictly smaller rank -- the descent the completeness
  induction rides.\<close>

lemma lowinterp_stratum_bound:
  assumes strat: "stratified \<Gamma> \<sigma>" and mem: "x \<in> lowinterp \<Gamma> D \<sigma> n"
  shows "\<sigma> (fst x) < n"
proof (cases n)
  case 0 with mem show ?thesis by (simp add: lowinterp_def)
next
  case (Suc m)
  with mem have "x \<in> strata \<Gamma> D \<sigma> m" by (simp add: lowinterp_def)
  then have "\<sigma> (fst x) \<le> m" by (rule strata_stratum_bound[OF strat])
  with Suc show ?thesis by simp
qed

lemma drank_step:
  assumes strat: "stratified \<Gamma> \<sigma>" and g: "grants \<Gamma> D \<sigma> (T, p) s ob"
  obtains c where "perms \<Gamma> T p = Some c"
    and "sat \<Gamma> D (lowinterp \<Gamma> D \<sigma> (\<sigma> (T, p)) \<union>
                  restr \<sigma> (\<sigma> (T, p))
                    (iterF \<Gamma> D \<sigma> (\<sigma> (T, p)) (drank \<Gamma> D \<sigma> ((T, p), s, ob) - 1)))
             T c s ob"
proof -
  define n where "n = \<sigma> (T, p)"
  define r where "r = drank \<Gamma> D \<sigma> ((T, p), s, ob)"
  obtain r' where r_eq: "r = Suc r'"
    using drank_pos[OF strat g] r_def by (metis gr0_conv_Suc)
  have "((T, p), s, ob) \<in> iterF \<Gamma> D \<sigma> n (Suc r')"
    using drank_in[OF strat g] n_def r_def r_eq by simp
  then have "((T, p), s, ob) \<in> stepF \<Gamma> D \<sigma> n (lowinterp \<Gamma> D \<sigma> n) (iterF \<Gamma> D \<sigma> n r')"
    by (simp add: iterF_Suc)
  moreover have "((T, p), s, ob) \<notin> lowinterp \<Gamma> D \<sigma> n"
    using lowinterp_stratum_bound[OF strat] n_def by fastforce
  ultimately obtain c where "perms \<Gamma> T p = Some c"
      and "sat \<Gamma> D (lowinterp \<Gamma> D \<sigma> n \<union> restr \<sigma> n (iterF \<Gamma> D \<sigma> n r')) T c s ob"
    by (auto simp: stepF_def)
  moreover have "r' = drank \<Gamma> D \<sigma> ((T, p), s, ob) - 1"
    using r_def r_eq by simp
  ultimately show thesis
    using that n_def by simp
qed

end
