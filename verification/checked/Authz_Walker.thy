theory Authz_Walker
  imports Authz_Kleene
begin

text \<open>
  Obligation W: the visited-set walker computes \<open>grants\<close>.

  The walker model: top-down evaluation with a path-scoped visited set
  \<open>V\<close>, a revisited (key, eid) state answered False, fuel making the
  function total (the Clojure walker needs no fuel because its
  termination is intrinsic; at sufficient fuel the model and the
  implementation agree). IMPORTANT correction discovered here: soundness
  without a fuel bound is FALSE -- fuel death inside a negation flips
  False to True -- so both directions require \<open>wbound \<Gamma> D V c \<le> f\<close>.

  Proof architecture: soundness and completeness are proven
  simultaneously by well-founded induction on fuel with an inner
  structural induction on the check. No stratum induction is needed:
  every recursion either consumes fuel (chains, including descents into
  lower strata) or shrinks the check (the Not crossings between the two
  directions). Stratum structure enters only through side conditions:

    \<open>deps_le\<close>  -- every key the check consults sits at or below the
                 ambient bound n, strictly below through negation;
    \<open>vhigh\<close>    -- (soundness) every visited state sits at or above n,
                 so no state in a negation subtree (all strictly below
                 n) can ever collide with the visited set;
    \<open>vcond\<close>    -- (completeness) additionally, visited states at
                 exactly n are not derivable within the current iterate
                 level, so no state a minimal derivation needs is ever
                 blocked -- blocking is impossible, not just harmless.
\<close>

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

section \<open>Measures and side conditions\<close>

fun csize :: "check \<Rightarrow> nat" where
  "csize (Terminal r) = 1"
| "csize (Chain r q) = 1"
| "csize (AttrEq a v) = 1"
| "csize (CNot c) = Suc (csize c)"
| "csize (CAnd c1 c2) = Suc (csize c1 + csize c2)"
| "csize (COr c1 c2) = Suc (csize c1 + csize c2)"

lemma csize_pos: "1 \<le> csize c"
  by (cases c) simp_all

definition sspace :: "reg \<Rightarrow> db \<Rightarrow> (key \<times> eid) set" where
  "sspace \<Gamma> D = rkeys \<Gamma> \<times> adom D"

definition bodies :: "reg \<Rightarrow> check set" where
  "bodies \<Gamma> = {c. \<exists>T p. perms \<Gamma> T p = Some c}"

definition msize :: "reg \<Rightarrow> nat" where
  "msize \<Gamma> = Max (insert 0 (csize ` bodies \<Gamma>))"

definition wbound :: "reg \<Rightarrow> db \<Rightarrow> (key \<times> eid) set \<Rightarrow> check \<Rightarrow> nat" where
  "wbound \<Gamma> D V c = card (sspace \<Gamma> D - V) * (1 + msize \<Gamma>) + csize c"

definition deps_le :: "reg \<Rightarrow> (key \<Rightarrow> nat) \<Rightarrow> ty \<Rightarrow> check \<Rightarrow> nat \<Rightarrow> bool" where
  "deps_le \<Gamma> \<sigma> T c n \<longleftrightarrow>
     (\<forall>k' neg. (k', neg) \<in> deps \<Gamma> T c \<longrightarrow> \<sigma> k' \<le> n \<and> (neg \<longrightarrow> \<sigma> k' < n))"

definition vhigh :: "(key \<Rightarrow> nat) \<Rightarrow> (key \<times> eid) set \<Rightarrow> nat \<Rightarrow> bool" where
  "vhigh \<sigma> V n \<longleftrightarrow> (\<forall>k' m'. (k', m') \<in> V \<longrightarrow> n \<le> \<sigma> k')"

definition vcond :: "reg \<Rightarrow> db \<Rightarrow> (key \<Rightarrow> nat) \<Rightarrow> (key \<times> eid) set \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> eid \<Rightarrow> bool" where
  "vcond \<Gamma> D \<sigma> V n r s \<longleftrightarrow>
     (\<forall>k' m'. (k', m') \<in> V \<longrightarrow>
        n < \<sigma> k' \<or> (\<sigma> k' = n \<and> (k', s, m') \<notin> iterF \<Gamma> D \<sigma> n r))"

lemma vcond_vhigh: "vcond \<Gamma> D \<sigma> V n r s \<Longrightarrow> vhigh \<sigma> V n"
  by (fastforce simp: vcond_def vhigh_def)

section \<open>Small facts\<close>

lemma ext_snd_adom: "(x, y) \<in> ext D r \<Longrightarrow> y \<in> adom D"
  by (cases r) (force simp: ext_def adom_def)+

lemma bodies_finite:
  assumes "finite (rkeys \<Gamma>)"
  shows "finite (bodies \<Gamma>)"
proof -
  have "bodies \<Gamma> \<subseteq> (\<lambda>k. the (perms \<Gamma> (fst k) (snd k))) ` rkeys \<Gamma>"
    by (force simp: bodies_def rkeys_def)
  with assms show ?thesis using finite_subset by blast
qed

lemma body_size:
  assumes "finite (rkeys \<Gamma>)" and "perms \<Gamma> T p = Some c"
  shows "csize c \<le> msize \<Gamma>"
proof -
  have "c \<in> bodies \<Gamma>" using assms(2) by (auto simp: bodies_def)
  then have "csize c \<in> insert 0 (csize ` bodies \<Gamma>)" by simp
  moreover have "finite (insert 0 (csize ` bodies \<Gamma>))"
    using bodies_finite[OF assms(1)] by simp
  ultimately show ?thesis unfolding msize_def by (rule Max_ge[rotated])
qed

lemma sspace_finite:
  assumes "finite D" "finite (rkeys \<Gamma>)"
  shows "finite (sspace \<Gamma> D)"
  using assms adom_finite by (simp add: sspace_def)

lemma wbound_csize_le:
  "csize c' \<le> csize c \<Longrightarrow> wbound \<Gamma> D V c' \<le> wbound \<Gamma> D V c"
  by (simp add: wbound_def)

lemma wbound_ge_csize: "csize c \<le> wbound \<Gamma> D V c"
  by (simp add: wbound_def)

lemma wbound_step:
  assumes finD: "finite D" and finK: "finite (rkeys \<Gamma>)"
      and v: "v \<in> sspace \<Gamma> D - V"
      and pc: "perms \<Gamma> T' q = Some c'"
  shows "Suc (wbound \<Gamma> D (insert v V) c') \<le> wbound \<Gamma> D V c"
proof -
  have fin: "finite (sspace \<Gamma> D - V)" using sspace_finite[OF finD finK] by simp
  have "card (sspace \<Gamma> D - V) \<noteq> 0"
  proof
    assume "card (sspace \<Gamma> D - V) = 0"
    with fin have "sspace \<Gamma> D - V = {}" by simp
    with v show False by blast
  qed
  then obtain cd where cd: "card (sspace \<Gamma> D - V) = Suc cd"
    by (cases "card (sspace \<Gamma> D - V)") auto
  have card_eq: "card (sspace \<Gamma> D - insert v V) = cd"
  proof -
    have "sspace \<Gamma> D - insert v V = (sspace \<Gamma> D - V) - {v}" by blast
    then show ?thesis using fin v cd by simp
  qed
  have "Suc (wbound \<Gamma> D (insert v V) c')
          = Suc (cd * (1 + msize \<Gamma>) + csize c')"
    by (simp add: wbound_def card_eq)
  also have "\<dots> \<le> cd * (1 + msize \<Gamma>) + (1 + msize \<Gamma>)"
    using body_size[OF finK pc] by simp
  also have "\<dots> = Suc cd * (1 + msize \<Gamma>)" by simp
  also have "\<dots> \<le> wbound \<Gamma> D V c"
    using csize_pos[of c] by (simp add: wbound_def cd)
  finally show ?thesis .
qed

lemma wbound_fuel_Suc:
  assumes "wbound \<Gamma> D V c \<le> f"
  obtains f' where "f = Suc f'"
proof -
  have "1 \<le> csize c" by (rule csize_pos)
  also have "\<dots> \<le> wbound \<Gamma> D V c" by (rule wbound_ge_csize)
  also have "\<dots> \<le> f" by (rule assms)
  finally have "1 \<le> f" .
  then show thesis using that by (cases f) auto
qed

lemma body_deps_le:
  assumes strat: "stratified \<Gamma> \<sigma>" and pc: "perms \<Gamma> T' q = Some c'"
  shows "deps_le \<Gamma> \<sigma> T' c' (\<sigma> (T', q))"
  unfolding deps_le_def
proof (intro allI impI)
  fix k' neg assume d: "(k', neg) \<in> deps \<Gamma> T' c'"
  then have "k' \<in> fst ` deps \<Gamma> T' c'" by force
  then have "\<sigma> k' \<le> \<sigma> (T', q)" by (rule deps_stratum_le[OF strat pc])
  moreover have "neg \<longrightarrow> \<sigma> k' < \<sigma> (T', q)"
  proof
    assume neg
    with d have "(k', True) \<in> deps \<Gamma> T' c'" by simp
    then show "\<sigma> k' < \<sigma> (T', q)" by (rule deps_stratum_less[OF strat pc])
  qed
  ultimately show "\<sigma> k' \<le> \<sigma> (T', q) \<and> (neg \<longrightarrow> \<sigma> k' < \<sigma> (T', q))" by blast
qed

lemma low_iff:
  assumes strat: "stratified \<Gamma> \<sigma>" and lt: "\<sigma> k' < n"
  shows "((k', s', m') \<in> lowinterp \<Gamma> D \<sigma> n) = grants \<Gamma> D \<sigma> k' s' m'"
proof (cases n)
  case 0 with lt show ?thesis by simp
next
  case (Suc nm)
  then have "((k', s', m') \<in> lowinterp \<Gamma> D \<sigma> n) = ((k', s', m') \<in> strata \<Gamma> D \<sigma> nm)"
    by (simp add: lowinterp_def)
  also have "\<dots> = ((k', s', m') \<in> strata \<Gamma> D \<sigma> (\<sigma> k'))"
  proof -
    have "\<sigma> k' \<le> nm" using lt Suc by simp
    from key_stability[OF strat this] show ?thesis .
  qed
  also have "\<dots> = grants \<Gamma> D \<sigma> k' s' m'" by (simp add: grants_def)
  finally show ?thesis .
qed

text \<open>Inside a negation subtree every consulted key is strictly below
  the ambient stratum, so satisfaction there is invariant between the
  stratum-local interpretation (for ANY same-stratum component) and the
  full grants interpretation.\<close>

lemma subneg_agree:
  assumes strat: "stratified \<Gamma> \<sigma>"
      and bound: "\<And>k' neg. (k', neg) \<in> deps \<Gamma> T c \<Longrightarrow> \<sigma> k' < n"
  shows "sat \<Gamma> D (lowinterp \<Gamma> D \<sigma> n \<union> restr \<sigma> n X) T c s ob
           = sat \<Gamma> D (ginterp \<Gamma> D \<sigma>) T c s ob"
proof (rule sat_invariant)
  fix k' s' m' assume "k' \<in> fst ` deps \<Gamma> T c"
  then obtain neg where "(k', neg) \<in> deps \<Gamma> T c" by auto
  then have lt: "\<sigma> k' < n" by (rule bound)
  then have "(k', s', m') \<notin> restr \<sigma> n X" by (auto simp: restr_def)
  then have "((k', s', m') \<in> lowinterp \<Gamma> D \<sigma> n \<union> restr \<sigma> n X)
               = ((k', s', m') \<in> lowinterp \<Gamma> D \<sigma> n)" by blast
  also have "\<dots> = grants \<Gamma> D \<sigma> k' s' m'" by (rule low_iff[OF strat lt])
  also have "\<dots> = ((k', s', m') \<in> ginterp \<Gamma> D \<sigma>)" by (simp add: ginterp_iff)
  finally show "((k', s', m') \<in> lowinterp \<Gamma> D \<sigma> n \<union> restr \<sigma> n X)
                  = ((k', s', m') \<in> ginterp \<Gamma> D \<sigma>)" .
qed

section \<open>The simultaneous induction\<close>

lemma walk_sound_complete:
  assumes strat: "stratified \<Gamma> \<sigma>" and finD: "finite D" and finK: "finite (rkeys \<Gamma>)"
  shows "(deps_le \<Gamma> \<sigma> T c n \<longrightarrow> vhigh \<sigma> V n \<longrightarrow> wbound \<Gamma> D V c \<le> f \<longrightarrow>
            walk f \<Gamma> D V T c s ob \<longrightarrow> sat \<Gamma> D (ginterp \<Gamma> D \<sigma>) T c s ob)
       \<and> (deps_le \<Gamma> \<sigma> T c n \<longrightarrow> vcond \<Gamma> D \<sigma> V n lv s \<longrightarrow> wbound \<Gamma> D V c \<le> f \<longrightarrow>
            sat \<Gamma> D (lowinterp \<Gamma> D \<sigma> n \<union> restr \<sigma> n (iterF \<Gamma> D \<sigma> n lv)) T c s ob \<longrightarrow>
            walk f \<Gamma> D V T c s ob)"
proof (induction f arbitrary: c T n V lv ob rule: less_induct)
  case (less f)
  note SIH = less.IH[THEN conjunct1, rule_format]
  note CIH = less.IH[THEN conjunct2, rule_format]
  show ?case
  proof (induction c arbitrary: T n V lv ob)
    case (Terminal rl)
    show ?case
    proof (intro conjI impI)
      assume "walk f \<Gamma> D V T (Terminal rl) s ob"
      then show "sat \<Gamma> D (ginterp \<Gamma> D \<sigma>) T (Terminal rl) s ob"
        by (cases f) simp_all
    next
      assume "wbound \<Gamma> D V (Terminal rl) \<le> f"
        and "sat \<Gamma> D (lowinterp \<Gamma> D \<sigma> n \<union> restr \<sigma> n (iterF \<Gamma> D \<sigma> n lv))
               T (Terminal rl) s ob"
      moreover then obtain f' where "f = Suc f'"
        by (blast intro: wbound_fuel_Suc)
      ultimately show "walk f \<Gamma> D V T (Terminal rl) s ob" by simp
    qed
  next
    case (AttrEq a v)
    show ?case
    proof (intro conjI impI)
      assume "walk f \<Gamma> D V T (AttrEq a v) s ob"
      then show "sat \<Gamma> D (ginterp \<Gamma> D \<sigma>) T (AttrEq a v) s ob"
        by (cases f) simp_all
    next
      assume "wbound \<Gamma> D V (AttrEq a v) \<le> f"
        and "sat \<Gamma> D (lowinterp \<Gamma> D \<sigma> n \<union> restr \<sigma> n (iterF \<Gamma> D \<sigma> n lv))
               T (AttrEq a v) s ob"
      moreover then obtain f' where "f = Suc f'"
        by (blast intro: wbound_fuel_Suc)
      ultimately show "walk f \<Gamma> D V T (AttrEq a v) s ob" by simp
    qed
  next
    case (Chain rl q)
    show ?case
    proof (intro conjI impI)
      \<comment> \<open>SOUNDNESS at Chain\<close>
      assume dl: "deps_le \<Gamma> \<sigma> T (Chain rl q) n"
        and vh: "vhigh \<sigma> V n"
        and fb: "wbound \<Gamma> D V (Chain rl q) \<le> f"
        and w: "walk f \<Gamma> D V T (Chain rl q) s ob"
      show "sat \<Gamma> D (ginterp \<Gamma> D \<sigma>) T (Chain rl q) s ob"
      proof (cases f)
        case 0 with w show ?thesis by simp
      next
        case (Suc f')
        with w obtain T' c' m where rT: "rels \<Gamma> T rl = Some T'"
            and pc': "perms \<Gamma> T' q = Some c'"
            and em: "(ob, m) \<in> ext D rl"
            and nv: "((T', q), m) \<notin> V"
            and w': "walk f' \<Gamma> D (insert ((T', q), m) V) T' c' s m"
          by (auto split: option.splits)
        have dep: "((T', q), False) \<in> deps \<Gamma> T (Chain rl q)" using rT by simp
        with dl have leq: "\<sigma> (T', q) \<le> n" by (auto simp: deps_le_def)
        have dl': "deps_le \<Gamma> \<sigma> T' c' (\<sigma> (T', q))"
          by (rule body_deps_le[OF strat pc'])
        have vh': "vhigh \<sigma> (insert ((T', q), m) V) (\<sigma> (T', q))"
          unfolding vhigh_def
        proof (intro allI impI)
          fix k' m' assume "(k', m') \<in> insert ((T', q), m) V"
          then consider "(k', m') = ((T', q), m)" | "(k', m') \<in> V" by blast
          then show "\<sigma> (T', q) \<le> \<sigma> k'"
          proof cases
            case 1 then show ?thesis by simp
          next
            case 2
            with vh have "n \<le> \<sigma> k'" by (cases k') (auto simp: vhigh_def)
            with leq show ?thesis by simp
          qed
        qed
        have insp: "((T', q), m) \<in> sspace \<Gamma> D - V"
          using pc' ext_snd_adom[OF em] nv
          by (auto simp: sspace_def rkeys_def)
        have fb': "wbound \<Gamma> D (insert ((T', q), m) V) c' \<le> f'"
          using wbound_step[OF finD finK insp pc', where c = "Chain rl q"] fb Suc
          by linarith
        have "sat \<Gamma> D (ginterp \<Gamma> D \<sigma>) T' c' s m"
          using SIH[OF _ dl' vh' fb' w'] Suc by simp
        then have "grants \<Gamma> D \<sigma> (T', q) s m"
          using grants_iff_sat[OF strat pc'] by simp
        with rT em show ?thesis by (auto simp: ginterp_iff)
      qed
    next
      \<comment> \<open>COMPLETENESS at Chain\<close>
      assume dl: "deps_le \<Gamma> \<sigma> T (Chain rl q) n"
        and vc: "vcond \<Gamma> D \<sigma> V n lv s"
        and fb: "wbound \<Gamma> D V (Chain rl q) \<le> f"
        and st: "sat \<Gamma> D (lowinterp \<Gamma> D \<sigma> n \<union> restr \<sigma> n (iterF \<Gamma> D \<sigma> n lv))
                   T (Chain rl q) s ob"
      from fb obtain f' where fS: "f = Suc f'"
        by (rule wbound_fuel_Suc)
      from st obtain T' m where rT: "rels \<Gamma> T rl = Some T'"
          and em: "(ob, m) \<in> ext D rl"
          and fmem: "((T', q), s, m)
                       \<in> lowinterp \<Gamma> D \<sigma> n \<union> restr \<sigma> n (iterF \<Gamma> D \<sigma> n lv)"
        by auto
      have goal_walk: "walk f' \<Gamma> D (insert ((T', q), m) V) T'
                         (the (perms \<Gamma> T' q)) s m
                       \<and> perms \<Gamma> T' q \<noteq> None \<and> ((T', q), m) \<notin> V"
      proof (cases "((T', q), s, m) \<in> restr \<sigma> n (iterF \<Gamma> D \<sigma> n lv)")
        case True
        then have sn: "\<sigma> (T', q) = n"
          and imem: "((T', q), s, m) \<in> iterF \<Gamma> D \<sigma> n lv"
          by (auto simp: restr_def)
        have g: "grants \<Gamma> D \<sigma> (T', q) s m"
          using iterF_le_strata[OF strat] imem sn
          by (auto simp: grants_def)
        have nv: "((T', q), m) \<notin> V"
          using vc sn imem by (auto simp: vcond_def)
        obtain c' where pc': "perms \<Gamma> T' q = Some c'"
            and satb: "sat \<Gamma> D
                (lowinterp \<Gamma> D \<sigma> (\<sigma> (T', q)) \<union>
                 restr \<sigma> (\<sigma> (T', q))
                   (iterF \<Gamma> D \<sigma> (\<sigma> (T', q))
                     (drank \<Gamma> D \<sigma> ((T', q), s, m) - 1)))
                T' c' s m"
          by (rule drank_step[OF strat g])
        define r' where "r' = drank \<Gamma> D \<sigma> ((T', q), s, m) - 1"
        have rpos: "0 < drank \<Gamma> D \<sigma> ((T', q), s, m)"
          using drank_pos[OF strat g] by simp
        have rle: "drank \<Gamma> D \<sigma> ((T', q), s, m) \<le> lv"
          using drank_le imem sn by metis
        have dl': "deps_le \<Gamma> \<sigma> T' c' n"
          using body_deps_le[OF strat pc'] sn by simp
        have vc': "vcond \<Gamma> D \<sigma> (insert ((T', q), m) V) n r' s"
          unfolding vcond_def
        proof (intro allI impI)
          fix k' m' assume "(k', m') \<in> insert ((T', q), m) V"
          then consider (new) "(k', m') = ((T', q), m)" | (old) "(k', m') \<in> V"
            by blast
          then show "n < \<sigma> k' \<or> (\<sigma> k' = n \<and> (k', s, m') \<notin> iterF \<Gamma> D \<sigma> n r')"
          proof cases
            case new
            have "((T', q), s, m) \<notin> iterF \<Gamma> D \<sigma> n r'"
              using drank_not_below rpos r'_def sn by fastforce
            with new sn show ?thesis by simp
          next
            case old
            with vc consider "n < \<sigma> k'"
              | "\<sigma> k' = n" "(k', s, m') \<notin> iterF \<Gamma> D \<sigma> n lv"
              by (cases k') (auto simp: vcond_def)
            then show ?thesis
            proof cases
              case 2
              have "iterF \<Gamma> D \<sigma> n r' \<subseteq> iterF \<Gamma> D \<sigma> n lv"
                using iterF_mono[OF strat] rle r'_def by simp
              with 2 show ?thesis by blast
            qed blast
          qed
        qed
        have insp: "((T', q), m) \<in> sspace \<Gamma> D - V"
          using pc' ext_snd_adom[OF em] nv
          by (auto simp: sspace_def rkeys_def)
        have fb': "wbound \<Gamma> D (insert ((T', q), m) V) c' \<le> f'"
          using wbound_step[OF finD finK insp pc', where c = "Chain rl q"] fb fS
          by linarith
        have satb': "sat \<Gamma> D (lowinterp \<Gamma> D \<sigma> n \<union>
                       restr \<sigma> n (iterF \<Gamma> D \<sigma> n r')) T' c' s m"
          using satb sn r'_def by simp
        have "walk f' \<Gamma> D (insert ((T', q), m) V) T' c' s m"
          using CIH[OF _ dl' vc' fb' satb'] fS by simp
        with pc' nv show ?thesis by simp
      next
        case False
        with fmem have lmem: "((T', q), s, m) \<in> lowinterp \<Gamma> D \<sigma> n" by blast
        have sn: "\<sigma> (T', q) < n"
          using lowinterp_stratum_bound[OF strat lmem] by simp
        have g: "grants \<Gamma> D \<sigma> (T', q) s m"
          using low_iff[OF strat sn] lmem by blast
        have nv: "((T', q), m) \<notin> V"
        proof
          assume "((T', q), m) \<in> V"
          with vc have "n < \<sigma> (T', q) \<or> \<sigma> (T', q) = n" by (auto simp: vcond_def)
          with sn show False by simp
        qed
        obtain c' where pc': "perms \<Gamma> T' q = Some c'"
            and satb: "sat \<Gamma> D
                (lowinterp \<Gamma> D \<sigma> (\<sigma> (T', q)) \<union>
                 restr \<sigma> (\<sigma> (T', q))
                   (iterF \<Gamma> D \<sigma> (\<sigma> (T', q))
                     (drank \<Gamma> D \<sigma> ((T', q), s, m) - 1)))
                T' c' s m"
          by (rule drank_step[OF strat g])
        define n2 where "n2 = \<sigma> (T', q)"
        define r' where "r' = drank \<Gamma> D \<sigma> ((T', q), s, m) - 1"
        have rpos: "0 < drank \<Gamma> D \<sigma> ((T', q), s, m)"
          using drank_pos[OF strat g] by simp
        have dl': "deps_le \<Gamma> \<sigma> T' c' n2"
          using body_deps_le[OF strat pc'] n2_def by simp
        have vc': "vcond \<Gamma> D \<sigma> (insert ((T', q), m) V) n2 r' s"
          unfolding vcond_def
        proof (intro allI impI)
          fix k' m' assume "(k', m') \<in> insert ((T', q), m) V"
          then consider (new) "(k', m') = ((T', q), m)" | (old) "(k', m') \<in> V"
            by blast
          then show "n2 < \<sigma> k' \<or> (\<sigma> k' = n2 \<and> (k', s, m') \<notin> iterF \<Gamma> D \<sigma> n2 r')"
          proof cases
            case new
            have "((T', q), s, m) \<notin> iterF \<Gamma> D \<sigma> n2 r'"
              using drank_not_below rpos r'_def n2_def by fastforce
            with new n2_def show ?thesis by simp
          next
            case old
            with vc have "n \<le> \<sigma> k'"
              by (cases k') (force simp: vcond_def)
            with sn n2_def show ?thesis by simp
          qed
        qed
        have insp: "((T', q), m) \<in> sspace \<Gamma> D - V"
          using pc' ext_snd_adom[OF em] nv
          by (auto simp: sspace_def rkeys_def)
        have fb': "wbound \<Gamma> D (insert ((T', q), m) V) c' \<le> f'"
          using wbound_step[OF finD finK insp pc', where c = "Chain rl q"] fb fS
          by linarith
        have satb': "sat \<Gamma> D (lowinterp \<Gamma> D \<sigma> n2 \<union>
                       restr \<sigma> n2 (iterF \<Gamma> D \<sigma> n2 r')) T' c' s m"
          using satb n2_def r'_def by simp
        have "walk f' \<Gamma> D (insert ((T', q), m) V) T' c' s m"
          using CIH[OF _ dl' vc' fb' satb'] fS by simp
        with pc' nv show ?thesis by simp
      qed
      from goal_walk obtain c' where "perms \<Gamma> T' q = Some c'"
          and "walk f' \<Gamma> D (insert ((T', q), m) V) T' c' s m"
          and "((T', q), m) \<notin> V"
        by (cases "perms \<Gamma> T' q") auto
      with rT em fS show "walk f \<Gamma> D V T (Chain rl q) s ob" by auto
    qed
  next
    case (CNot c)
    show ?case
    proof (intro conjI impI)
      \<comment> \<open>SOUNDNESS at CNot: uses completeness of the subtree (inner IH)\<close>
      assume dl: "deps_le \<Gamma> \<sigma> T (CNot c) n"
        and vh: "vhigh \<sigma> V n"
        and fb: "wbound \<Gamma> D V (CNot c) \<le> f"
        and w: "walk f \<Gamma> D V T (CNot c) s ob"
      have subdeps: "\<And>k' neg. (k', neg) \<in> deps \<Gamma> T c \<Longrightarrow> \<sigma> k' < n"
      proof -
        fix k' neg assume "(k', neg) \<in> deps \<Gamma> T c"
        then have "(k', True) \<in> deps \<Gamma> T (CNot c)" by force
        with dl show "\<sigma> k' < n" unfolding deps_le_def by blast
      qed
      from fb obtain f' where fS: "f = Suc f'"
        by (rule wbound_fuel_Suc)
      have "\<not> sat \<Gamma> D (ginterp \<Gamma> D \<sigma>) T c s ob"
      proof
        assume sc: "sat \<Gamma> D (ginterp \<Gamma> D \<sigma>) T c s ob"
        have dl': "deps_le \<Gamma> \<sigma> T c n"
          unfolding deps_le_def
        proof (intro allI impI)
          fix k' neg assume "(k', neg) \<in> deps \<Gamma> T c"
          then have "\<sigma> k' < n" by (rule subdeps)
          then show "\<sigma> k' \<le> n \<and> (neg \<longrightarrow> \<sigma> k' < n)" by simp
        qed
        have vc0: "vcond \<Gamma> D \<sigma> V n 0 s"
          using vh by (fastforce simp: vcond_def vhigh_def)
        have fb': "wbound \<Gamma> D V c \<le> f"
        proof -
          have "wbound \<Gamma> D V c \<le> wbound \<Gamma> D V (CNot c)"
            by (rule wbound_csize_le) simp
          with fb show ?thesis by linarith
        qed
        have satb: "sat \<Gamma> D (lowinterp \<Gamma> D \<sigma> n \<union>
                      restr \<sigma> n (iterF \<Gamma> D \<sigma> n 0)) T c s ob"
        proof -
          have "sat \<Gamma> D (lowinterp \<Gamma> D \<sigma> n \<union>
                  restr \<sigma> n (iterF \<Gamma> D \<sigma> n 0)) T c s ob
                  = sat \<Gamma> D (ginterp \<Gamma> D \<sigma>) T c s ob"
            by (rule subneg_agree[OF strat]) (rule subdeps)
          with sc show ?thesis by simp
        qed
        have "walk f \<Gamma> D V T c s ob"
          using CNot.IH[THEN conjunct2, rule_format, OF dl' vc0 fb' satb] .
        with w fS show False by simp
      qed
      then show "sat \<Gamma> D (ginterp \<Gamma> D \<sigma>) T (CNot c) s ob" by simp
    next
      \<comment> \<open>COMPLETENESS at CNot: uses soundness of the subtree (inner IH)\<close>
      assume dl: "deps_le \<Gamma> \<sigma> T (CNot c) n"
        and vc: "vcond \<Gamma> D \<sigma> V n lv s"
        and fb: "wbound \<Gamma> D V (CNot c) \<le> f"
        and st: "sat \<Gamma> D (lowinterp \<Gamma> D \<sigma> n \<union>
                   restr \<sigma> n (iterF \<Gamma> D \<sigma> n lv)) T (CNot c) s ob"
      have subdeps: "\<And>k' neg. (k', neg) \<in> deps \<Gamma> T c \<Longrightarrow> \<sigma> k' < n"
      proof -
        fix k' neg assume "(k', neg) \<in> deps \<Gamma> T c"
        then have "(k', True) \<in> deps \<Gamma> T (CNot c)" by force
        with dl show "\<sigma> k' < n" unfolding deps_le_def by blast
      qed
      from fb obtain f' where fS: "f = Suc f'"
        by (rule wbound_fuel_Suc)
      have "\<not> walk f \<Gamma> D V T c s ob"
      proof
        assume wk: "walk f \<Gamma> D V T c s ob"
        have dl': "deps_le \<Gamma> \<sigma> T c n"
          unfolding deps_le_def
        proof (intro allI impI)
          fix k' neg assume "(k', neg) \<in> deps \<Gamma> T c"
          then have "\<sigma> k' < n" by (rule subdeps)
          then show "\<sigma> k' \<le> n \<and> (neg \<longrightarrow> \<sigma> k' < n)" by simp
        qed
        have vh: "vhigh \<sigma> V n" by (rule vcond_vhigh[OF vc])
        have fb': "wbound \<Gamma> D V c \<le> f"
        proof -
          have "wbound \<Gamma> D V c \<le> wbound \<Gamma> D V (CNot c)"
            by (rule wbound_csize_le) simp
          with fb show ?thesis by linarith
        qed
        have "sat \<Gamma> D (ginterp \<Gamma> D \<sigma>) T c s ob"
          using CNot.IH[THEN conjunct1, rule_format, OF dl' vh fb' wk] .
        then have "sat \<Gamma> D (lowinterp \<Gamma> D \<sigma> n \<union>
                     restr \<sigma> n (iterF \<Gamma> D \<sigma> n lv)) T c s ob"
        proof -
          assume gsat: "sat \<Gamma> D (ginterp \<Gamma> D \<sigma>) T c s ob"
          have "sat \<Gamma> D (lowinterp \<Gamma> D \<sigma> n \<union>
                  restr \<sigma> n (iterF \<Gamma> D \<sigma> n lv)) T c s ob
                  = sat \<Gamma> D (ginterp \<Gamma> D \<sigma>) T c s ob"
            by (rule subneg_agree[OF strat]) (rule subdeps)
          with gsat show ?thesis by simp
        qed
        with st show False by simp
      qed
      with fS show "walk f \<Gamma> D V T (CNot c) s ob" by simp
    qed
  next
    case (CAnd c1 c2)
    show ?case
    proof (intro conjI impI)
      assume dl: "deps_le \<Gamma> \<sigma> T (CAnd c1 c2) n"
        and vh: "vhigh \<sigma> V n"
        and fb: "wbound \<Gamma> D V (CAnd c1 c2) \<le> f"
        and w: "walk f \<Gamma> D V T (CAnd c1 c2) s ob"
      from fb obtain f' where fS: "f = Suc f'"
        by (rule wbound_fuel_Suc)
      have dl1: "deps_le \<Gamma> \<sigma> T c1 n" and dl2: "deps_le \<Gamma> \<sigma> T c2 n"
        using dl by (auto simp: deps_le_def)
      have fb1: "wbound \<Gamma> D V c1 \<le> f"
      proof -
        have "wbound \<Gamma> D V c1 \<le> wbound \<Gamma> D V (CAnd c1 c2)"
          by (rule wbound_csize_le) simp
        with fb show ?thesis by linarith
      qed
      have fb2: "wbound \<Gamma> D V c2 \<le> f"
      proof -
        have "wbound \<Gamma> D V c2 \<le> wbound \<Gamma> D V (CAnd c1 c2)"
          by (rule wbound_csize_le) simp
        with fb show ?thesis by linarith
      qed
      from w fS have w1: "walk f \<Gamma> D V T c1 s ob"
                 and w2: "walk f \<Gamma> D V T c2 s ob" by simp_all
      show "sat \<Gamma> D (ginterp \<Gamma> D \<sigma>) T (CAnd c1 c2) s ob"
        using CAnd.IH(1)[THEN conjunct1, rule_format, OF dl1 vh fb1 w1]
              CAnd.IH(2)[THEN conjunct1, rule_format, OF dl2 vh fb2 w2]
        by simp
    next
      assume dl: "deps_le \<Gamma> \<sigma> T (CAnd c1 c2) n"
        and vc: "vcond \<Gamma> D \<sigma> V n lv s"
        and fb: "wbound \<Gamma> D V (CAnd c1 c2) \<le> f"
        and st: "sat \<Gamma> D (lowinterp \<Gamma> D \<sigma> n \<union>
                   restr \<sigma> n (iterF \<Gamma> D \<sigma> n lv)) T (CAnd c1 c2) s ob"
      from fb obtain f' where fS: "f = Suc f'"
        by (rule wbound_fuel_Suc)
      have dl1: "deps_le \<Gamma> \<sigma> T c1 n" and dl2: "deps_le \<Gamma> \<sigma> T c2 n"
        using dl by (auto simp: deps_le_def)
      have fb1: "wbound \<Gamma> D V c1 \<le> f"
      proof -
        have "wbound \<Gamma> D V c1 \<le> wbound \<Gamma> D V (CAnd c1 c2)"
          by (rule wbound_csize_le) simp
        with fb show ?thesis by linarith
      qed
      have fb2: "wbound \<Gamma> D V c2 \<le> f"
      proof -
        have "wbound \<Gamma> D V c2 \<le> wbound \<Gamma> D V (CAnd c1 c2)"
          by (rule wbound_csize_le) simp
        with fb show ?thesis by linarith
      qed
      from st have s1: "sat \<Gamma> D (lowinterp \<Gamma> D \<sigma> n \<union>
                          restr \<sigma> n (iterF \<Gamma> D \<sigma> n lv)) T c1 s ob"
               and s2: "sat \<Gamma> D (lowinterp \<Gamma> D \<sigma> n \<union>
                          restr \<sigma> n (iterF \<Gamma> D \<sigma> n lv)) T c2 s ob" by simp_all
      show "walk f \<Gamma> D V T (CAnd c1 c2) s ob"
        using CAnd.IH(1)[THEN conjunct2, rule_format, OF dl1 vc fb1 s1]
              CAnd.IH(2)[THEN conjunct2, rule_format, OF dl2 vc fb2 s2] fS
        by simp
    qed
  next
    case (COr c1 c2)
    show ?case
    proof (intro conjI impI)
      assume dl: "deps_le \<Gamma> \<sigma> T (COr c1 c2) n"
        and vh: "vhigh \<sigma> V n"
        and fb: "wbound \<Gamma> D V (COr c1 c2) \<le> f"
        and w: "walk f \<Gamma> D V T (COr c1 c2) s ob"
      from fb obtain f' where fS: "f = Suc f'"
        by (rule wbound_fuel_Suc)
      have dl1: "deps_le \<Gamma> \<sigma> T c1 n" and dl2: "deps_le \<Gamma> \<sigma> T c2 n"
        using dl by (auto simp: deps_le_def)
      have fb1: "wbound \<Gamma> D V c1 \<le> f"
      proof -
        have "wbound \<Gamma> D V c1 \<le> wbound \<Gamma> D V (COr c1 c2)"
          by (rule wbound_csize_le) simp
        with fb show ?thesis by linarith
      qed
      have fb2: "wbound \<Gamma> D V c2 \<le> f"
      proof -
        have "wbound \<Gamma> D V c2 \<le> wbound \<Gamma> D V (COr c1 c2)"
          by (rule wbound_csize_le) simp
        with fb show ?thesis by linarith
      qed
      from w fS have "walk f \<Gamma> D V T c1 s ob \<or> walk f \<Gamma> D V T c2 s ob" by simp
      then show "sat \<Gamma> D (ginterp \<Gamma> D \<sigma>) T (COr c1 c2) s ob"
        using COr.IH(1)[THEN conjunct1, rule_format, OF dl1 vh fb1]
              COr.IH(2)[THEN conjunct1, rule_format, OF dl2 vh fb2]
        by auto
    next
      assume dl: "deps_le \<Gamma> \<sigma> T (COr c1 c2) n"
        and vc: "vcond \<Gamma> D \<sigma> V n lv s"
        and fb: "wbound \<Gamma> D V (COr c1 c2) \<le> f"
        and st: "sat \<Gamma> D (lowinterp \<Gamma> D \<sigma> n \<union>
                   restr \<sigma> n (iterF \<Gamma> D \<sigma> n lv)) T (COr c1 c2) s ob"
      from fb obtain f' where fS: "f = Suc f'"
        by (rule wbound_fuel_Suc)
      have dl1: "deps_le \<Gamma> \<sigma> T c1 n" and dl2: "deps_le \<Gamma> \<sigma> T c2 n"
        using dl by (auto simp: deps_le_def)
      have fb1: "wbound \<Gamma> D V c1 \<le> f"
      proof -
        have "wbound \<Gamma> D V c1 \<le> wbound \<Gamma> D V (COr c1 c2)"
          by (rule wbound_csize_le) simp
        with fb show ?thesis by linarith
      qed
      have fb2: "wbound \<Gamma> D V c2 \<le> f"
      proof -
        have "wbound \<Gamma> D V c2 \<le> wbound \<Gamma> D V (COr c1 c2)"
          by (rule wbound_csize_le) simp
        with fb show ?thesis by linarith
      qed
      from st have "sat \<Gamma> D (lowinterp \<Gamma> D \<sigma> n \<union>
                      restr \<sigma> n (iterF \<Gamma> D \<sigma> n lv)) T c1 s ob
                  \<or> sat \<Gamma> D (lowinterp \<Gamma> D \<sigma> n \<union>
                      restr \<sigma> n (iterF \<Gamma> D \<sigma> n lv)) T c2 s ob" by simp
      then show "walk f \<Gamma> D V T (COr c1 c2) s ob"
        using COr.IH(1)[THEN conjunct2, rule_format, OF dl1 vc fb1]
              COr.IH(2)[THEN conjunct2, rule_format, OF dl2 vc fb2] fS
        by auto
    qed
  qed
qed

section \<open>Obligation W, discharged\<close>

theorem walker_sound:
  assumes strat: "stratified \<Gamma> \<sigma>" and finD: "finite D" and finK: "finite (rkeys \<Gamma>)"
      and pc: "perms \<Gamma> T p = Some c"
      and fuel: "wbound \<Gamma> D {} c \<le> f"
      and w: "walk f \<Gamma> D {} T c s ob"
  shows "grants \<Gamma> D \<sigma> (T, p) s ob"
proof -
  have dl: "deps_le \<Gamma> \<sigma> T c (\<sigma> (T, p))" by (rule body_deps_le[OF strat pc])
  have vh: "vhigh \<sigma> {} (\<sigma> (T, p))" by (simp add: vhigh_def)
  have "sat \<Gamma> D (ginterp \<Gamma> D \<sigma>) T c s ob"
    using walk_sound_complete[OF strat finD finK, THEN conjunct1, rule_format,
                              OF dl vh fuel w] .
  then show ?thesis using grants_iff_sat[OF strat pc] by simp
qed

theorem walker_complete:
  assumes strat: "stratified \<Gamma> \<sigma>" and finD: "finite D" and finK: "finite (rkeys \<Gamma>)"
      and pc: "perms \<Gamma> T p = Some c"
      and g: "grants \<Gamma> D \<sigma> (T, p) s ob"
      and fuel: "wbound \<Gamma> D {} c \<le> f"
  shows "walk f \<Gamma> D {} T c s ob"
proof -
  define n where "n = \<sigma> (T, p)"
  define r' where "r' = drank \<Gamma> D \<sigma> ((T, p), s, ob) - 1"
  obtain c' where pc': "perms \<Gamma> T p = Some c'"
      and satb: "sat \<Gamma> D
          (lowinterp \<Gamma> D \<sigma> (\<sigma> (T, p)) \<union>
           restr \<sigma> (\<sigma> (T, p))
             (iterF \<Gamma> D \<sigma> (\<sigma> (T, p)) (drank \<Gamma> D \<sigma> ((T, p), s, ob) - 1)))
          T c' s ob"
    by (rule drank_step[OF strat g])
  from pc pc' have ceq: "c' = c" by simp
  have dl: "deps_le \<Gamma> \<sigma> T c n"
    using body_deps_le[OF strat pc] n_def by simp
  have vc: "vcond \<Gamma> D \<sigma> {} n r' s" by (simp add: vcond_def)
  have satb': "sat \<Gamma> D (lowinterp \<Gamma> D \<sigma> n \<union>
                 restr \<sigma> n (iterF \<Gamma> D \<sigma> n r')) T c s ob"
    using satb ceq n_def r'_def by simp
  show ?thesis
    using walk_sound_complete[OF strat finD finK, THEN conjunct2, rule_format,
                              OF dl vc fuel satb'] .
qed

end
