theory Authz_Sigma
  imports Authz_Enum
begin

text \<open>
  Stratification-independence: \<open>grants\<close> does not depend on the choice
  of stratification -- SEMANTICS.md section 3's "the definition is
  independent of the choice of \<sigma>", the uniqueness of the perfect model.

  Proof: a master induction on the \<sigma>1-stratum n carries two directions
  together. (A) facts granted under \<sigma>1 at stratum exactly n transfer to
  \<sigma>2, by induction over \<sigma>1's iterates; (B) facts granted under \<sigma>2 whose
  key sits at \<sigma>1-stratum at most n transfer back, by a nested induction
  over \<sigma>2's tower. Neither direction needs the other at the same
  stratum: negated keys sit strictly below n under BOTH stratifications
  (negative polarity is syntactic), where the master hypothesis supplies
  full equivalence -- that is what makes negation harmless here, exactly
  as in the walker proof.

  One structural subtlety: in direction (B) the stratum-local
  interpretation is \<sigma>2-shaped, so it contains facts of keys far above
  the current \<sigma>1-bound and the global monotonicity premise of
  \<open>sat_mono\<close> fails. Satisfaction only consults a check's own
  dependencies, so the interpretation is first restricted to consulted
  keys via \<open>sat_invariant\<close>.
\<close>

lemma sigma_master:
  assumes s1: "stratified \<Gamma> \<sigma>1" and s2: "stratified \<Gamma> \<sigma>2"
  shows "(\<forall>k s ob. \<sigma>1 k = n \<longrightarrow> grants \<Gamma> D \<sigma>1 k s ob \<longrightarrow> grants \<Gamma> D \<sigma>2 k s ob)
       \<and> (\<forall>k s ob. \<sigma>1 k \<le> n \<longrightarrow> grants \<Gamma> D \<sigma>2 k s ob \<longrightarrow> grants \<Gamma> D \<sigma>1 k s ob)"
proof (induction n rule: less_induct)
  case (less n)
  have equiv_lt: "\<And>k s ob. \<sigma>1 k < n \<Longrightarrow>
                    grants \<Gamma> D \<sigma>1 k s ob = grants \<Gamma> D \<sigma>2 k s ob"
  proof
    fix k s ob assume lt: "\<sigma>1 k < n"
    assume "grants \<Gamma> D \<sigma>1 k s ob"
    with less.IH[OF lt, THEN conjunct1] show "grants \<Gamma> D \<sigma>2 k s ob" by blast
  next
    fix k s ob assume lt: "\<sigma>1 k < n"
    assume "grants \<Gamma> D \<sigma>2 k s ob"
    with less.IH[OF lt, THEN conjunct2] show "grants \<Gamma> D \<sigma>1 k s ob" by blast
  qed

  text \<open>Direction A at stratum exactly n, over \<sigma>1's iterates.\<close>

  have AI: "\<And>m T p s ob. ((T, p), s, ob) \<in> iterF \<Gamma> D \<sigma>1 n m
              \<Longrightarrow> \<sigma>1 (T, p) = n \<Longrightarrow> grants \<Gamma> D \<sigma>2 (T, p) s ob"
  proof -
    fix m
    show "\<And>T p s ob. ((T, p), s, ob) \<in> iterF \<Gamma> D \<sigma>1 n m
            \<Longrightarrow> \<sigma>1 (T, p) = n \<Longrightarrow> grants \<Gamma> D \<sigma>2 (T, p) s ob"
    proof (induction m)
      case 0 then show ?case by simp
    next
      case (Suc m)
      from Suc.prems(1)
      have "((T, p), s, ob)
              \<in> stepF \<Gamma> D \<sigma>1 n (lowinterp \<Gamma> D \<sigma>1 n) (iterF \<Gamma> D \<sigma>1 n m)"
        by (simp add: iterF_Suc)
      moreover have "((T, p), s, ob) \<notin> lowinterp \<Gamma> D \<sigma>1 n"
        using lowinterp_stratum_bound[OF s1] Suc.prems(2) by fastforce
      ultimately obtain c where pc: "perms \<Gamma> T p = Some c"
          and st: "sat \<Gamma> D (lowinterp \<Gamma> D \<sigma>1 n \<union> restr \<sigma>1 n (iterF \<Gamma> D \<sigma>1 n m))
                     T c s ob"
        by (auto simp: stepF_def)
      have "sat \<Gamma> D (ginterp \<Gamma> D \<sigma>2) T c s ob"
      proof (rule sat_mono)
        show "lowinterp \<Gamma> D \<sigma>1 n \<union> restr \<sigma>1 n (iterF \<Gamma> D \<sigma>1 n m)
                \<subseteq> ginterp \<Gamma> D \<sigma>2"
        proof
          fix x assume xm: "x \<in> lowinterp \<Gamma> D \<sigma>1 n \<union> restr \<sigma>1 n (iterF \<Gamma> D \<sigma>1 n m)"
          obtain k' s' m' where x_eq: "x = (k', s', m')" by (metis prod_cases3)
          from xm show "x \<in> ginterp \<Gamma> D \<sigma>2"
          proof
            assume lm: "x \<in> lowinterp \<Gamma> D \<sigma>1 n"
            then have lt: "\<sigma>1 k' < n"
              using lowinterp_stratum_bound[OF s1] x_eq by fastforce
            have "grants \<Gamma> D \<sigma>1 k' s' m'"
              using low_iff[OF s1 lt] lm x_eq by blast
            then have "grants \<Gamma> D \<sigma>2 k' s' m'" using equiv_lt[OF lt] by blast
            then show ?thesis by (simp add: x_eq ginterp_iff)
          next
            assume rm: "x \<in> restr \<sigma>1 n (iterF \<Gamma> D \<sigma>1 n m)"
            then have sn: "\<sigma>1 k' = n" and im: "(k', s', m') \<in> iterF \<Gamma> D \<sigma>1 n m"
              using x_eq by (auto simp: restr_def)
            obtain T' p' where k'_eq: "k' = (T', p')" by (cases k') blast
            have "grants \<Gamma> D \<sigma>2 (T', p') s' m'"
              using Suc.IH im sn k'_eq by blast
            then show ?thesis by (simp add: x_eq k'_eq ginterp_iff)
          qed
        qed
      next
        fix k' s' m' assume neg: "(k', True) \<in> deps \<Gamma> T c"
        have lt: "\<sigma>1 k' < n"
          using deps_stratum_less[OF s1 pc neg] Suc.prems(2) by simp
        have notr: "\<And>X. (k', s', m') \<notin> restr \<sigma>1 n X"
          using lt by (auto simp: restr_def)
        have "((k', s', m') \<in> lowinterp \<Gamma> D \<sigma>1 n \<union> restr \<sigma>1 n (iterF \<Gamma> D \<sigma>1 n m))
                = grants \<Gamma> D \<sigma>1 k' s' m'"
          using low_iff[OF s1 lt] notr by blast
        also have "\<dots> = grants \<Gamma> D \<sigma>2 k' s' m'" using equiv_lt[OF lt] by blast
        also have "\<dots> = ((k', s', m') \<in> ginterp \<Gamma> D \<sigma>2)"
          by (simp add: ginterp_iff)
        finally show "((k', s', m')
                        \<in> lowinterp \<Gamma> D \<sigma>1 n \<union> restr \<sigma>1 n (iterF \<Gamma> D \<sigma>1 n m))
                        = ((k', s', m') \<in> ginterp \<Gamma> D \<sigma>2)" .
      next
        show "sat \<Gamma> D (lowinterp \<Gamma> D \<sigma>1 n \<union> restr \<sigma>1 n (iterF \<Gamma> D \<sigma>1 n m))
                T c s ob" by (fact st)
      qed
      then show ?case using grants_iff_sat[OF s2 pc] by simp
    qed
  qed

  have Apart: "\<And>k s ob. \<sigma>1 k = n \<Longrightarrow> grants \<Gamma> D \<sigma>1 k s ob
                 \<Longrightarrow> grants \<Gamma> D \<sigma>2 k s ob"
  proof -
    fix k s ob assume sn: "\<sigma>1 k = n" and g: "grants \<Gamma> D \<sigma>1 k s ob"
    obtain T p where k_eq: "k = (T, p)" by (cases k) blast
    from g have "(k, s, ob) \<in> strata \<Gamma> D \<sigma>1 (\<sigma>1 k)" by (simp add: grants_def)
    then obtain m where "(k, s, ob) \<in> iterF \<Gamma> D \<sigma>1 (\<sigma>1 k) m"
      using strata_iter[OF s1] by blast
    with AI sn k_eq show "grants \<Gamma> D \<sigma>2 k s ob" by blast
  qed

  text \<open>Direction B at \<sigma>1-stratum at most n, over \<sigma>2's tower.\<close>

  have BI: "\<And>n2 m T p s ob. ((T, p), s, ob) \<in> iterF \<Gamma> D \<sigma>2 n2 m
              \<Longrightarrow> \<sigma>2 (T, p) = n2 \<Longrightarrow> \<sigma>1 (T, p) \<le> n
              \<Longrightarrow> grants \<Gamma> D \<sigma>1 (T, p) s ob"
  proof -
    fix n2
    show "\<And>m T p s ob. ((T, p), s, ob) \<in> iterF \<Gamma> D \<sigma>2 n2 m
            \<Longrightarrow> \<sigma>2 (T, p) = n2 \<Longrightarrow> \<sigma>1 (T, p) \<le> n
            \<Longrightarrow> grants \<Gamma> D \<sigma>1 (T, p) s ob"
    proof (induction n2 rule: less_induct)
      case less2: (less n2)
      note OuterB = less2.IH
      fix m
      show "\<And>T p s ob. ((T, p), s, ob) \<in> iterF \<Gamma> D \<sigma>2 n2 m
              \<Longrightarrow> \<sigma>2 (T, p) = n2 \<Longrightarrow> \<sigma>1 (T, p) \<le> n
              \<Longrightarrow> grants \<Gamma> D \<sigma>1 (T, p) s ob"
      proof (induction m)
        case 0 then show ?case by simp
      next
        case (Suc m)
        from Suc.prems(1)
        have "((T, p), s, ob)
                \<in> stepF \<Gamma> D \<sigma>2 n2 (lowinterp \<Gamma> D \<sigma>2 n2) (iterF \<Gamma> D \<sigma>2 n2 m)"
          by (simp add: iterF_Suc)
        moreover have "((T, p), s, ob) \<notin> lowinterp \<Gamma> D \<sigma>2 n2"
          using lowinterp_stratum_bound[OF s2] Suc.prems(2) by fastforce
        ultimately obtain c where pc: "perms \<Gamma> T p = Some c"
            and st: "sat \<Gamma> D (lowinterp \<Gamma> D \<sigma>2 n2 \<union>
                       restr \<sigma>2 n2 (iterF \<Gamma> D \<sigma>2 n2 m)) T c s ob"
          by (auto simp: stepF_def)
        define I0 where "I0 = lowinterp \<Gamma> D \<sigma>2 n2 \<union> restr \<sigma>2 n2 (iterF \<Gamma> D \<sigma>2 n2 m)"
        define Jc where "Jc = {x \<in> I0. fst x \<in> fst ` deps \<Gamma> T c}"
        have stJ: "sat \<Gamma> D Jc T c s ob"
        proof -
          have "sat \<Gamma> D I0 T c s ob = sat \<Gamma> D Jc T c s ob"
            by (rule sat_invariant) (auto simp: Jc_def)
          with st show ?thesis by (simp add: I0_def)
        qed
        have "sat \<Gamma> D (ginterp \<Gamma> D \<sigma>1) T c s ob"
        proof (rule sat_mono)
          show "Jc \<subseteq> ginterp \<Gamma> D \<sigma>1"
          proof
            fix x assume xJ: "x \<in> Jc"
            obtain k' s' m' where x_eq: "x = (k', s', m')" by (metis prod_cases3)
            from xJ x_eq have con: "k' \<in> fst ` deps \<Gamma> T c"
              by (simp add: Jc_def)
            have le1: "\<sigma>1 k' \<le> n"
              using deps_stratum_le[OF s1 pc con] Suc.prems(3) by simp
            from xJ x_eq have "(k', s', m') \<in> I0" by (simp add: Jc_def)
            then have "grants \<Gamma> D \<sigma>1 k' s' m'"
              unfolding I0_def
            proof
              assume lm: "(k', s', m') \<in> lowinterp \<Gamma> D \<sigma>2 n2"
              then have lt2: "\<sigma>2 k' < n2"
                using lowinterp_stratum_bound[OF s2] by fastforce
              have "grants \<Gamma> D \<sigma>2 k' s' m'"
                using low_iff[OF s2 lt2] lm by blast
              then have "(k', s', m') \<in> strata \<Gamma> D \<sigma>2 (\<sigma>2 k')"
                by (simp add: grants_def)
              then obtain m2 where im2: "(k', s', m') \<in> iterF \<Gamma> D \<sigma>2 (\<sigma>2 k') m2"
                using strata_iter[OF s2] by blast
              obtain T' p' where k'_eq: "k' = (T', p')" by (cases k') blast
              show "grants \<Gamma> D \<sigma>1 k' s' m'"
                using OuterB[OF lt2] im2 le1 k'_eq by blast
            next
              assume rm: "(k', s', m') \<in> restr \<sigma>2 n2 (iterF \<Gamma> D \<sigma>2 n2 m)"
              then have sn2: "\<sigma>2 k' = n2"
                  and im: "(k', s', m') \<in> iterF \<Gamma> D \<sigma>2 n2 m"
                by (auto simp: restr_def)
              obtain T' p' where k'_eq: "k' = (T', p')" by (cases k') blast
              show "grants \<Gamma> D \<sigma>1 k' s' m'"
                using Suc.IH im sn2 le1 k'_eq by blast
            qed
            then show "x \<in> ginterp \<Gamma> D \<sigma>1" by (simp add: x_eq ginterp_iff)
          qed
        next
          fix k' s' m' assume neg: "(k', True) \<in> deps \<Gamma> T c"
          have con: "k' \<in> fst ` deps \<Gamma> T c" using neg by force
          have lt1: "\<sigma>1 k' < n"
            using deps_stratum_less[OF s1 pc neg] Suc.prems(3) by simp
          have lt2: "\<sigma>2 k' < n2"
            using deps_stratum_less[OF s2 pc neg] Suc.prems(2) by simp
          have notr: "\<And>X. (k', s', m') \<notin> restr \<sigma>2 n2 X"
            using lt2 by (auto simp: restr_def)
          have "((k', s', m') \<in> Jc) = ((k', s', m') \<in> I0)"
            using con by (auto simp: Jc_def)
          also have "\<dots> = grants \<Gamma> D \<sigma>2 k' s' m'"
            unfolding I0_def using low_iff[OF s2 lt2] notr by blast
          also have "\<dots> = grants \<Gamma> D \<sigma>1 k' s' m'"
            using equiv_lt[OF lt1] by blast
          also have "\<dots> = ((k', s', m') \<in> ginterp \<Gamma> D \<sigma>1)"
            by (simp add: ginterp_iff)
          finally show "((k', s', m') \<in> Jc) = ((k', s', m') \<in> ginterp \<Gamma> D \<sigma>1)" .
        next
          show "sat \<Gamma> D Jc T c s ob" by (fact stJ)
        qed
        then show ?case using grants_iff_sat[OF s1 pc] by simp
      qed
    qed
  qed

  have Bpart: "\<And>k s ob. \<sigma>1 k \<le> n \<Longrightarrow> grants \<Gamma> D \<sigma>2 k s ob
                 \<Longrightarrow> grants \<Gamma> D \<sigma>1 k s ob"
  proof -
    fix k s ob assume le: "\<sigma>1 k \<le> n" and g: "grants \<Gamma> D \<sigma>2 k s ob"
    obtain T p where k_eq: "k = (T, p)" by (cases k) blast
    from g have "(k, s, ob) \<in> strata \<Gamma> D \<sigma>2 (\<sigma>2 k)" by (simp add: grants_def)
    then obtain m where "(k, s, ob) \<in> iterF \<Gamma> D \<sigma>2 (\<sigma>2 k) m"
      using strata_iter[OF s2] by blast
    with BI le k_eq show "grants \<Gamma> D \<sigma>1 k s ob" by blast
  qed

  show ?case using Apart Bpart by blast
qed

theorem sigma_independent:
  assumes s1: "stratified \<Gamma> \<sigma>1" and s2: "stratified \<Gamma> \<sigma>2"
  shows "grants \<Gamma> D \<sigma>1 k s ob = grants \<Gamma> D \<sigma>2 k s ob"
proof
  assume "grants \<Gamma> D \<sigma>1 k s ob"
  with sigma_master[OF s1 s2, of "\<sigma>1 k" D, THEN conjunct1]
  show "grants \<Gamma> D \<sigma>2 k s ob" by blast
next
  assume "grants \<Gamma> D \<sigma>2 k s ob"
  with sigma_master[OF s1 s2, of "\<sigma>1 k" D, THEN conjunct2]
  show "grants \<Gamma> D \<sigma>1 k s ob" by blast
qed

end
