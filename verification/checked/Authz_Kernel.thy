theory Authz_Kernel
  imports Authz_Sigma
begin

text \<open>
  The verified kernel: an executable bottom-up evaluator over concrete
  lists, proven equal to \<open>grants\<close> -- a machine-checked twin of the
  Clojure fixpoint oracle. \<open>kernel_check\<close> validates its inputs with
  executable checkers proven equivalent to \<open>stratified\<close> and \<open>safe\<close>
  (returning None rather than a meaningless answer on bad input), then
  iterates each stratum's step function a provably sufficient number of
  times: a monotone chain inside a finite fact space stabilizes within
  card-many steps, and the stable point is the least fixed point by
  \<open>strata_iter\<close>.
\<close>

section \<open>Subject confinement\<close>

text \<open>Safety confines objects to the active domain (\<open>grants_finite\<close>);
  it confines subjects too, because every derivation bottoms out in a
  terminal whose evidence is a datom. This is what lets the executable
  step bound its subject search space.\<close>

lemma sat_subject_adom:
  assumes gen: "generative c" and st: "sat \<Gamma> D I T c s ob"
      and IH: "\<And>k' m'. (k', s, m') \<in> I \<Longrightarrow> s \<in> adom D"
  shows "s \<in> adom D"
proof -
  from sat_gen_pos[OF gen st] show ?thesis
  proof (elim disjE)
    assume "\<exists>r. r \<in> gterms c \<and> (ob, s) \<in> ext D r"
    then show ?thesis using ext_snd_adom by blast
  next
    assume "\<exists>r q T' m. (r, q) \<in> gchains c \<and> rels \<Gamma> T r = Some T' \<and>
              (ob, m) \<in> ext D r \<and> ((T', q), s, m) \<in> I"
    then show ?thesis using IH by blast
  qed
qed

lemma iterF_subject_adom:
  assumes strat: "stratified \<Gamma> \<sigma>" and sf: "safe \<Gamma>"
  shows "(k, s, ob) \<in> iterF \<Gamma> D \<sigma> n m \<Longrightarrow> s \<in> adom D"
proof (induction n arbitrary: k m ob rule: less_induct)
  case (less n)
  from less.prems show ?case
  proof (induction m arbitrary: k ob)
    case 0 then show ?case by simp
  next
    case (Suc m)
    from Suc.prems
    have "(k, s, ob) \<in> stepF \<Gamma> D \<sigma> n (lowinterp \<Gamma> D \<sigma> n) (iterF \<Gamma> D \<sigma> n m)"
      by (simp add: iterF_Suc)
    then consider (lower) "(k, s, ob) \<in> lowinterp \<Gamma> D \<sigma> n"
      | (new) T p c where "k = (T, p)" "perms \<Gamma> T p = Some c"
          "sat \<Gamma> D (lowinterp \<Gamma> D \<sigma> n \<union> restr \<sigma> n (iterF \<Gamma> D \<sigma> n m)) T c s ob"
      by (auto simp: stepF_def)
    then show ?case
    proof cases
      case lower
      then have lt: "\<sigma> k < n"
        using lowinterp_stratum_bound[OF strat] by fastforce
      then obtain n' where n_eq: "n = Suc n'" by (cases n) auto
      with lower have "(k, s, ob) \<in> strata \<Gamma> D \<sigma> n'"
        by (simp add: lowinterp_def)
      then obtain m' where mem': "(k, s, ob) \<in> iterF \<Gamma> D \<sigma> n' m'"
        using strata_iter[OF strat] by blast
      have "n' < n" using n_eq by simp
      from less.IH[OF this mem'] show ?thesis .
    next
      case new
      have gen: "generative c" using sf new(2) unfolding safe_def by blast
      show ?thesis
      proof (rule sat_subject_adom[OF gen new(3)])
        fix k' m' assume "(k', s, m') \<in> lowinterp \<Gamma> D \<sigma> n \<union>
                            restr \<sigma> n (iterF \<Gamma> D \<sigma> n m)"
        then consider "(k', s, m') \<in> lowinterp \<Gamma> D \<sigma> n"
          | "(k', s, m') \<in> iterF \<Gamma> D \<sigma> n m" by (auto simp: restr_def)
        then show "s \<in> adom D"
        proof cases
          case 1
          then have "\<sigma> k' < n" using lowinterp_stratum_bound[OF strat] by fastforce
          then obtain n' where n_eq: "n = Suc n'" by (cases n) auto
          with 1 have "(k', s, m') \<in> strata \<Gamma> D \<sigma> n'" by (simp add: lowinterp_def)
          then obtain m2 where mem2: "(k', s, m') \<in> iterF \<Gamma> D \<sigma> n' m2"
            using strata_iter[OF strat] by blast
          have "n' < n" using n_eq by simp
          from less.IH[OF this mem2] show ?thesis .
        next
          case 2 then show ?thesis by (rule Suc.IH)
        qed
      qed
    qed
  qed
qed

lemma strata_subject_adom:
  assumes strat: "stratified \<Gamma> \<sigma>" and sf: "safe \<Gamma>"
      and mem: "(k, s, ob) \<in> strata \<Gamma> D \<sigma> n"
  shows "s \<in> adom D"
proof -
  from mem obtain m where "(k, s, ob) \<in> iterF \<Gamma> D \<sigma> n m"
    using strata_iter[OF strat] by blast
  then show ?thesis by (rule iterF_subject_adom[OF strat sf])
qed

section \<open>Executable primitives\<close>

definition kext :: "datom list \<Rightarrow> rel \<Rightarrow> (eid \<times> eid) list" where
  "kext ds r = (case r of
     Fwd a \<Rightarrow> concat (map (\<lambda>(e, a', v). case v of
                  Ent y \<Rightarrow> (if a' = a then [(e, y)] else []) | Lit _ \<Rightarrow> []) ds)
   | Rev a \<Rightarrow> concat (map (\<lambda>(e, a', v). case v of
                  Ent y \<Rightarrow> (if a' = a then [(y, e)] else []) | Lit _ \<Rightarrow> []) ds))"

lemma kext_set: "set (kext ds r) = ext (set ds) r"
  by (cases r) (force simp: kext_def ext_def split: vl.splits)+

definition kadom :: "datom list \<Rightarrow> eid list" where
  "kadom ds = map (\<lambda>(e, _, _). e) ds @
              concat (map (\<lambda>(_, _, v). case v of Ent y \<Rightarrow> [y] | Lit _ \<Rightarrow> []) ds)"

lemma kadom_set: "set (kadom ds) = adom (set ds)"
  by (force simp: kadom_def adom_def split: vl.splits)

text \<open>Executable satisfaction: the chain case's unbounded existential
  becomes a scan of the relation extension.\<close>

fun ksat :: "reg \<Rightarrow> datom list \<Rightarrow> interp \<Rightarrow> ty \<Rightarrow> check \<Rightarrow> eid \<Rightarrow> eid \<Rightarrow> bool" where
  "ksat \<Gamma> ds I T (Terminal r) s ob = ((ob, s) \<in> set (kext ds r))"
| "ksat \<Gamma> ds I T (Chain r q) s ob =
     (case rels \<Gamma> T r of
        None \<Rightarrow> False
      | Some T' \<Rightarrow> list_ex (\<lambda>(x, m). x = ob \<and> ((T', q), s, m) \<in> I) (kext ds r))"
| "ksat \<Gamma> ds I T (AttrEq a v) s ob = ((ob, a, v) \<in> set ds)"
| "ksat \<Gamma> ds I T (CNot c) s ob = (\<not> ksat \<Gamma> ds I T c s ob)"
| "ksat \<Gamma> ds I T (CAnd c1 c2) s ob = (ksat \<Gamma> ds I T c1 s ob \<and> ksat \<Gamma> ds I T c2 s ob)"
| "ksat \<Gamma> ds I T (COr c1 c2) s ob = (ksat \<Gamma> ds I T c1 s ob \<or> ksat \<Gamma> ds I T c2 s ob)"

lemma ksat_sat: "ksat \<Gamma> ds I T c s ob = sat \<Gamma> (set ds) I T c s ob"
proof (induction c)
  case (Chain r q)
  show ?case
    by (auto simp: list_ex_iff kext_set split: option.splits)
qed (auto simp: kext_set)

section \<open>The registry from association lists\<close>

definition mkreg :: "((ty \<times> rel) \<times> ty) list \<Rightarrow> ((ty \<times> perm) \<times> check) list \<Rightarrow> reg" where
  "mkreg kr kp = \<lparr> rels = \<lambda>T r. map_of kr (T, r),
                   perms = \<lambda>T p. map_of kp (T, p) \<rparr>"

lemma mkreg_perms_mem:
  assumes "distinct (map fst kp)"
  shows "(perms (mkreg kr kp) T p = Some c) = (((T, p), c) \<in> set kp)"
  using assms by (simp add: mkreg_def)

lemma mkreg_rkeys:
  "rkeys (mkreg kr kp) = fst ` set kp"
proof
  show "rkeys (mkreg kr kp) \<subseteq> fst ` set kp"
  proof
    fix k assume "k \<in> rkeys (mkreg kr kp)"
    then obtain T p c where k_eq: "k = (T, p)"
        and some: "map_of kp (T, p) = Some c"
      by (cases k) (auto simp: rkeys_def mkreg_def)
    from some have "((T, p), c) \<in> set kp" by (rule map_of_SomeD)
    then have "(T, p) \<in> fst ` set kp" by force
    with k_eq show "k \<in> fst ` set kp" by simp
  qed
next
  show "fst ` set kp \<subseteq> rkeys (mkreg kr kp)"
  proof
    fix k assume "k \<in> fst ` set kp"
    then obtain c where "(k, c) \<in> set kp" by auto
    then obtain c' where "map_of kp k = Some c'"
      using weak_map_of_SomeI by force
    then show "k \<in> rkeys (mkreg kr kp)"
      by (cases k) (auto simp: rkeys_def mkreg_def)
  qed
qed

section \<open>The executable step\<close>

definition kstep :: "reg \<Rightarrow> datom list \<Rightarrow> (key \<Rightarrow> nat) \<Rightarrow> ((ty \<times> perm) \<times> check) list
                       \<Rightarrow> nat \<Rightarrow> interp \<Rightarrow> interp \<Rightarrow> interp" where
  "kstep \<Gamma> ds \<sigma> kp n L J =
     L \<union> set (concat (map (\<lambda>(k, c).
        if \<sigma> k = n
        then map (\<lambda>(s', ob). (k, s', ob))
               (filter (\<lambda>(s', ob).
                  ksat \<Gamma> ds (L \<union> Set.filter (\<lambda>y. \<sigma> (fst y) = n) J) (fst k) c s' ob)
                 (List.product (kadom ds) (kadom ds)))
        else []) kp))"

lemma restr_filter: "Set.filter (\<lambda>y. \<sigma> (fst y) = n) J = restr \<sigma> n J"
  by (auto simp: restr_def)

lemma kstep_mem:
  "x \<in> kstep \<Gamma> ds \<sigma> kp n L J \<longleftrightarrow>
     x \<in> L \<or> (\<exists>k c s' ob. x = (k, s', ob) \<and> (k, c) \<in> set kp \<and> \<sigma> k = n \<and>
        s' \<in> set (kadom ds) \<and> ob \<in> set (kadom ds) \<and>
        ksat \<Gamma> ds (L \<union> restr \<sigma> n J) (fst k) c s' ob)"
    (is "?lhs = ?rhs")
proof -
  define f :: "(ty \<times> perm) \<times> check \<Rightarrow> (key \<times> eid \<times> eid) list" where
    "f = (\<lambda>(k, c).
        if \<sigma> k = n
        then map (\<lambda>(s', ob). (k, s', ob))
               (filter (\<lambda>(s', ob).
                  ksat \<Gamma> ds (L \<union> Set.filter (\<lambda>y. \<sigma> (fst y) = n) J) (fst k) c s' ob)
                 (List.product (kadom ds) (kadom ds)))
        else [])"
  have kstep_eq: "kstep \<Gamma> ds \<sigma> kp n L J = L \<union> set (concat (map f kp))"
    by (simp add: kstep_def f_def)
  show ?thesis
  proof
    assume ?lhs
    then consider (lower) "x \<in> L" | (new) "x \<in> set (concat (map f kp))"
      using kstep_eq by blast
    then show ?rhs
    proof cases
      case lower then show ?thesis by blast
    next
      case new
      then obtain kc where kc_in: "kc \<in> set kp" and x_in: "x \<in> set (f kc)"
        by (auto simp only: set_concat set_map)
      obtain k c where kc_eq: "kc = (k, c)" by (cases kc) blast
      from x_in kc_eq have sn: "\<sigma> k = n"
        by (auto simp: f_def split: if_splits)
      from x_in kc_eq sn obtain s' ob where
          x_eq: "x = (k, s', ob)"
          and mems: "s' \<in> set (kadom ds)" "ob \<in> set (kadom ds)"
          and ks: "ksat \<Gamma> ds (L \<union> Set.filter (\<lambda>y. \<sigma> (fst y) = n) J) (fst k) c s' ob"
        by (auto simp: f_def)
      have ks': "ksat \<Gamma> ds (L \<union> restr \<sigma> n J) (fst k) c s' ob"
        using ks unfolding restr_filter .
      from x_eq kc_in kc_eq sn mems ks' show ?thesis by blast
    qed
  next
    assume ?rhs
    then consider (lower) "x \<in> L"
      | (new) k c s' ob where "x = (k, s', ob)" "(k, c) \<in> set kp" "\<sigma> k = n"
          "s' \<in> set (kadom ds)" "ob \<in> set (kadom ds)"
          "ksat \<Gamma> ds (L \<union> restr \<sigma> n J) (fst k) c s' ob"
      by blast
    then show ?lhs
    proof cases
      case lower then show ?thesis by (simp add: kstep_eq)
    next
      case new
      have ks2: "ksat \<Gamma> ds (L \<union> Set.filter (\<lambda>y. \<sigma> (fst y) = n) J) (fst k) c s' ob"
        using new(6) unfolding restr_filter .
      have "x \<in> set (f (k, c))"
        using new(1,3,4,5) ks2 by (auto simp: f_def image_iff set_product)
      then have "x \<in> set (concat (map f kp))"
        using new(2) by (auto simp only: set_concat set_map)
      then show ?thesis by (simp add: kstep_eq)
    qed
  qed
qed

lemma kstep_stepF:
  assumes dis: "distinct (map fst kp)"
      and greg: "\<Gamma> = mkreg kr kp"
      and sf: "safe \<Gamma>"
      and conf: "\<And>k' s'' m'. (k', s'', m') \<in> L \<union> restr \<sigma> n J
                   \<Longrightarrow> s'' \<in> adom (set ds)"
  shows "kstep \<Gamma> ds \<sigma> kp n L J = stepF \<Gamma> (set ds) \<sigma> n L J"
proof
  show "kstep \<Gamma> ds \<sigma> kp n L J \<subseteq> stepF \<Gamma> (set ds) \<sigma> n L J"
  proof
    fix x assume "x \<in> kstep \<Gamma> ds \<sigma> kp n L J"
    then consider (lower) "x \<in> L"
      | (new) k c s' ob where "x = (k, s', ob)" "(k, c) \<in> set kp" "\<sigma> k = n"
          "ksat \<Gamma> ds (L \<union> restr \<sigma> n J) (fst k) c s' ob"
      using kstep_mem by blast
    then show "x \<in> stepF \<Gamma> (set ds) \<sigma> n L J"
    proof cases
      case lower then show ?thesis by (simp add: stepF_def)
    next
      case new
      obtain T p where k_eq: "k = (T, p)" by (cases k) blast
      have pc: "perms \<Gamma> T p = Some c"
        using mkreg_perms_mem[OF dis] greg new(2) k_eq by blast
      have "sat \<Gamma> (set ds) (L \<union> restr \<sigma> n J) T c s' ob"
        using new(4) k_eq by (simp add: ksat_sat)
      with pc new(1,3) k_eq show ?thesis by (auto simp: stepF_def)
    qed
  qed
next
  show "stepF \<Gamma> (set ds) \<sigma> n L J \<subseteq> kstep \<Gamma> ds \<sigma> kp n L J"
  proof
    fix x assume "x \<in> stepF \<Gamma> (set ds) \<sigma> n L J"
    then consider (lower) "x \<in> L"
      | (new) T p s' ob c where "x = ((T, p), s', ob)" "\<sigma> (T, p) = n"
          "perms \<Gamma> T p = Some c"
          "sat \<Gamma> (set ds) (L \<union> restr \<sigma> n J) T c s' ob"
      by (auto simp: stepF_def)
    then show "x \<in> kstep \<Gamma> ds \<sigma> kp n L J"
    proof cases
      case lower then show ?thesis using kstep_mem by blast
    next
      case new
      have inkp: "((T, p), c) \<in> set kp"
        using mkreg_perms_mem[OF dis] greg new(3) by blast
      have gen: "generative c" using sf new(3) unfolding safe_def by blast
      have subj: "s' \<in> adom (set ds)"
        by (rule sat_subject_adom[OF gen new(4)]) (rule conf)
      have obj: "ob \<in> adom (set ds)"
        by (rule generative_sat_adom[OF gen new(4)])
      have "ksat \<Gamma> ds (L \<union> restr \<sigma> n J) T c s' ob"
        using new(4) by (simp add: ksat_sat)
      with new(1,2) inkp subj obj show ?thesis
        using kstep_mem kadom_set by fastforce
    qed
  qed
qed

section \<open>Stabilization: a monotone chain in a finite space is its union\<close>

lemma chain_stabilize:
  fixes A :: "nat \<Rightarrow> 'a set" and f :: "'a set \<Rightarrow> 'a set"
  assumes inc: "\<And>m. A m \<subseteq> A (Suc m)"
      and det: "\<And>m. A (Suc m) = f (A m)"
      and bnd: "\<And>m. A m \<subseteq> FS" and fin: "finite FS"
      and N: "card FS < N"
  shows "A N = (\<Union>m. A m)"
proof -
  have ex_stable: "\<exists>j \<le> card FS. A j = A (Suc j)"
  proof (rule ccontr)
    assume "\<not> (\<exists>j \<le> card FS. A j = A (Suc j))"
    then have strict: "\<And>j. j \<le> card FS \<Longrightarrow> A j \<subset> A (Suc j)"
      using inc by blast
    have grow: "\<And>j. j \<le> Suc (card FS) \<Longrightarrow> j \<le> card (A j)"
    proof -
      fix j show "j \<le> Suc (card FS) \<Longrightarrow> j \<le> card (A j)"
      proof (induction j)
        case 0 then show ?case by simp
      next
        case (Suc j)
        then have "j \<le> card (A j)" by simp
        moreover have "A j \<subset> A (Suc j)" using strict Suc.prems by simp
        moreover have "finite (A (Suc j))"
          using bnd fin finite_subset by blast
        ultimately show ?case
          by (meson leD le_less_trans not_less_eq_eq psubset_card_mono)
      qed
    qed
    have "Suc (card FS) \<le> card (A (Suc (card FS)))" using grow by simp
    moreover have "card (A (Suc (card FS))) \<le> card FS"
      using bnd fin card_mono by blast
    ultimately show False by simp
  qed
  then obtain j where jle: "j \<le> card FS" and stab: "A j = A (Suc j)" by blast
  have stable_from: "\<And>i. j \<le> i \<Longrightarrow> A i = A j"
  proof -
    fix i show "j \<le> i \<Longrightarrow> A i = A j"
    proof (induction i)
      case (Suc i)
      show ?case
      proof (cases "j = Suc i")
        case True then show ?thesis by simp
      next
        case False
        with Suc.prems have "j \<le> i" by simp
        with Suc.IH have "A i = A j" .
        then have "A (Suc i) = f (A j)" using det by simp
        also have "\<dots> = A (Suc j)" using det by simp
        also have "\<dots> = A j" using stab by simp
        finally show ?thesis .
      qed
    qed simp
  qed
  have mono_local: "\<And>i j'. i \<le> j' \<Longrightarrow> A i \<subseteq> A j'"
  proof -
    fix i j' show "i \<le> j' \<Longrightarrow> A i \<subseteq> A j'"
    proof (induction j')
      case (Suc j')
      then show ?case using inc by (auto simp: le_Suc_eq)
    qed simp
  qed
  have "(\<Union>m. A m) = A j"
  proof
    show "(\<Union>m. A m) \<subseteq> A j"
    proof
      fix x assume "x \<in> (\<Union>m. A m)"
      then obtain m where xm: "x \<in> A m" by blast
      have "A m \<subseteq> A (max m j)" by (rule mono_local) simp
      with xm have "x \<in> A (max m j)" by blast
      moreover have "A (max m j) = A j" by (rule stable_from) simp
      ultimately show "x \<in> A j" by simp
    qed
  next
    show "A j \<subseteq> (\<Union>m. A m)" by blast
  qed
  moreover have "A N = A j"
  proof -
    have "j \<le> N" using jle N by simp
    then show ?thesis by (rule stable_from)
  qed
  ultimately show ?thesis by simp
qed

section \<open>The executable tower\<close>

definition kiters :: "((ty \<times> perm) \<times> check) list \<Rightarrow> datom list \<Rightarrow> nat" where
  "kiters kp ds = Suc (length kp * (length (kadom ds) * length (kadom ds)))"

text \<open>Early exit: iterating past a stable point changes nothing, so the
  executable loop may stop as soon as one step makes no progress -- and
  is still extensionally the worst-case funpow the proofs reason about.\<close>

fun fixloop :: "nat \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a" where
  "fixloop 0 f X = X"
| "fixloop (Suc m) f X = (let X' = f X in if X' = X then X else fixloop m f X')"

lemma funpow_stable: "f X = X \<Longrightarrow> (f ^^ m) X = X"
  by (induction m) auto

lemma fixloop_funpow: "fixloop m f X = (f ^^ m) X"
proof (induction m arbitrary: X)
  case 0 then show ?case by simp
next
  case (Suc m)
  show ?case
  proof (cases "f X = X")
    case True
    then have "(f ^^ Suc m) X = X" by (rule funpow_stable)
    with True show ?thesis by (simp add: Let_def)
  next
    case False
    have "fixloop (Suc m) f X = fixloop m f (f X)"
      using False by (simp add: Let_def)
    also have "\<dots> = (f ^^ m) (f X)" by (rule Suc.IH)
    also have "\<dots> = (f ^^ Suc m) X" by (simp add: funpow_swap1)
    finally show ?thesis .
  qed
qed

definition kfix :: "reg \<Rightarrow> datom list \<Rightarrow> (key \<Rightarrow> nat) \<Rightarrow> ((ty \<times> perm) \<times> check) list
                      \<Rightarrow> nat \<Rightarrow> interp \<Rightarrow> interp" where
  "kfix \<Gamma> ds \<sigma> kp n L = fixloop (kiters kp ds) (\<lambda>J. kstep \<Gamma> ds \<sigma> kp n L J) {}"

lemma kfix_funpow:
  "kfix \<Gamma> ds \<sigma> kp n L = ((\<lambda>J. kstep \<Gamma> ds \<sigma> kp n L J) ^^ kiters kp ds) {}"
  by (simp add: kfix_def fixloop_funpow)

fun ktower :: "reg \<Rightarrow> datom list \<Rightarrow> (key \<Rightarrow> nat) \<Rightarrow> ((ty \<times> perm) \<times> check) list
                 \<Rightarrow> nat \<Rightarrow> interp" where
  "ktower \<Gamma> ds \<sigma> kp 0 = kfix \<Gamma> ds \<sigma> kp 0 {}"
| "ktower \<Gamma> ds \<sigma> kp (Suc n) = kfix \<Gamma> ds \<sigma> kp (Suc n) (ktower \<Gamma> ds \<sigma> kp n)"

text \<open>The global fact space bounding every stratum's chain.\<close>

definition kspace :: "((ty \<times> perm) \<times> check) list \<Rightarrow> datom list \<Rightarrow> interp" where
  "kspace kp ds = (fst ` set kp) \<times> adom (set ds) \<times> adom (set ds)"

lemma kspace_finite: "finite (kspace kp ds)"
  by (simp add: kspace_def adom_finite[of "set ds"])

lemma kspace_card: "card (kspace kp ds) < kiters kp ds"
proof -
  have "card (kspace kp ds)
          = card (fst ` set kp) * (card (adom (set ds)) * card (adom (set ds)))"
    by (simp add: kspace_def card_cartesian_product)
  also have "\<dots> \<le> length kp * (length (kadom ds) * length (kadom ds))"
  proof -
    have a: "card (fst ` set kp) \<le> length kp"
      by (metis card_length length_map set_map)
    have b: "card (adom (set ds)) \<le> length (kadom ds)"
      by (metis card_length kadom_set)
    from a b show ?thesis by (intro mult_le_mono) auto
  qed
  finally show ?thesis by (simp add: kiters_def)
qed

lemma strata_in_kspace:
  assumes strat: "stratified \<Gamma> \<sigma>" and sf: "safe \<Gamma>"
      and dis: "distinct (map fst kp)" and greg: "\<Gamma> = mkreg kr kp"
  shows "strata \<Gamma> (set ds) \<sigma> n \<subseteq> kspace kp ds"
proof
  fix x assume xs: "x \<in> strata \<Gamma> (set ds) \<sigma> n"
  obtain k s ob where x_eq: "x = (k, s, ob)" by (metis prod_cases3)
  from strata_origin[OF strat] xs x_eq
  obtain T p c I where k_eq: "k = (T, p)" and pc: "perms \<Gamma> T p = Some c"
    by blast
  have key: "k \<in> fst ` set kp"
    using pc k_eq greg mkreg_rkeys unfolding rkeys_def by force
  have subj: "s \<in> adom (set ds)"
    using strata_subject_adom[OF strat sf] xs x_eq by blast
  have obj: "ob \<in> adom (set ds)"
  proof -
    from strata_origin[OF strat] xs x_eq
    obtain T' p' c' I' s' ob' where "x = ((T', p'), s', ob')"
        and pc': "perms \<Gamma> T' p' = Some c'"
        and st': "sat \<Gamma> (set ds) I' T' c' s' ob'"
      by blast
    moreover have "generative c'" using sf pc' unfolding safe_def by blast
    ultimately show ?thesis
      using generative_sat_adom x_eq by fastforce
  qed
  show "x \<in> kspace kp ds"
    using key subj obj x_eq by (simp add: kspace_def)
qed

lemma kfix_lfp:
  assumes strat: "stratified \<Gamma> \<sigma>" and sf: "safe \<Gamma>"
      and dis: "distinct (map fst kp)" and greg: "\<Gamma> = mkreg kr kp"
      and L_eq: "L = lowinterp \<Gamma> (set ds) \<sigma> n"
  shows "kfix \<Gamma> ds \<sigma> kp n L = strata \<Gamma> (set ds) \<sigma> n"
proof -
  have conf: "\<And>J k' s'' m'. (k', s'', m') \<in> L \<union> restr \<sigma> n J
                \<Longrightarrow> J \<subseteq> strata \<Gamma> (set ds) \<sigma> n \<Longrightarrow> s'' \<in> adom (set ds)"
  proof -
    fix J k' s'' m' assume mem: "(k', s'', m') \<in> L \<union> restr \<sigma> n J"
      and Jsub: "J \<subseteq> strata \<Gamma> (set ds) \<sigma> n"
    from mem consider "(k', s'', m') \<in> L" | "(k', s'', m') \<in> J"
      by (auto simp: restr_def)
    then show "s'' \<in> adom (set ds)"
    proof cases
      case 1
      then have lt: "\<sigma> k' < n"
        using lowinterp_stratum_bound[OF strat] L_eq by fastforce
      then obtain n' where n_eq: "n = Suc n'" by (cases n) auto
      with 1 L_eq have "(k', s'', m') \<in> strata \<Gamma> (set ds) \<sigma> n'"
        by (simp add: lowinterp_def)
      then show ?thesis using strata_subject_adom[OF strat sf] by blast
    next
      case 2
      with Jsub show ?thesis using strata_subject_adom[OF strat sf] by blast
    qed
  qed
  define A where "A = (\<lambda>m. iterF \<Gamma> (set ds) \<sigma> n m)"
  have keq: "\<And>m. ((\<lambda>J. kstep \<Gamma> ds \<sigma> kp n L J) ^^ m) {} = A m"
  proof -
    fix m show "((\<lambda>J. kstep \<Gamma> ds \<sigma> kp n L J) ^^ m) {} = A m"
    proof (induction m)
      case 0 then show ?case by (simp add: A_def)
    next
      case (Suc m)
      have Asub: "A m \<subseteq> strata \<Gamma> (set ds) \<sigma> n"
        using iterF_le_strata[OF strat] A_def by simp
      have "kstep \<Gamma> ds \<sigma> kp n L (A m) = stepF \<Gamma> (set ds) \<sigma> n L (A m)"
        by (rule kstep_stepF[OF dis greg sf]) (use conf Asub in blast)
      then show ?case
        using Suc.IH by (simp add: A_def iterF_Suc L_eq)
    qed
  qed
  have "A (kiters kp ds) = (\<Union>m. A m)"
  proof (rule chain_stabilize)
    show "\<And>m. A m \<subseteq> A (Suc m)"
      using iterF_mono_step[OF strat] A_def by simp
    show "\<And>m. A (Suc m) = stepF \<Gamma> (set ds) \<sigma> n L (A m)"
      by (simp add: A_def iterF_Suc L_eq)
    show "\<And>m. A m \<subseteq> kspace kp ds"
      using iterF_le_strata[OF strat] strata_in_kspace[OF strat sf dis greg]
      unfolding A_def by blast
    show "finite (kspace kp ds)" by (rule kspace_finite)
    show "card (kspace kp ds) < kiters kp ds" by (rule kspace_card)
  qed
  also have "(\<Union>m. A m) = strata \<Gamma> (set ds) \<sigma> n"
    using strata_iter[OF strat] A_def by simp
  finally show ?thesis
    using keq by (simp add: kfix_funpow)
qed

lemma ktower_strata:
  assumes strat: "stratified \<Gamma> \<sigma>" and sf: "safe \<Gamma>"
      and dis: "distinct (map fst kp)" and greg: "\<Gamma> = mkreg kr kp"
  shows "ktower \<Gamma> ds \<sigma> kp n = strata \<Gamma> (set ds) \<sigma> n"
proof (induction n)
  case 0
  show ?case
    using kfix_lfp[OF strat sf dis greg, of "{}" ds 0]
    by (simp add: lowinterp_def)
next
  case (Suc n)
  show ?case
    using kfix_lfp[OF strat sf dis greg, of "ktower \<Gamma> ds \<sigma> kp n" ds "Suc n"] Suc.IH
    by (simp add: lowinterp_def)
qed

section \<open>Executable input validation\<close>

definition kstratified :: "reg \<Rightarrow> (key \<Rightarrow> nat) \<Rightarrow> ((ty \<times> perm) \<times> check) list \<Rightarrow> bool" where
  "kstratified \<Gamma> \<sigma> kp =
     list_all (\<lambda>(k, c). \<forall>(k', neg) \<in> deps \<Gamma> (fst k) c.
        (if neg then \<sigma> k' < \<sigma> k else \<sigma> k' \<le> \<sigma> k)) kp"

lemma kstratified_iff:
  assumes dis: "distinct (map fst kp)" and greg: "\<Gamma> = mkreg kr kp"
  shows "kstratified \<Gamma> \<sigma> kp = stratified \<Gamma> \<sigma>"
proof
  assume ks: "kstratified \<Gamma> \<sigma> kp"
  show "stratified \<Gamma> \<sigma>"
    unfolding stratified_def
  proof (intro allI impI)
    fix T p c k' neg
    assume pc: "perms \<Gamma> T p = Some c" and d: "(k', neg) \<in> deps \<Gamma> T c"
    have "((T, p), c) \<in> set kp" using mkreg_perms_mem[OF dis] greg pc by blast
    with ks d show "if neg then \<sigma> k' < \<sigma> (T, p) else \<sigma> k' \<le> \<sigma> (T, p)"
      by (fastforce simp: kstratified_def list_all_iff)
  qed
next
  assume st: "stratified \<Gamma> \<sigma>"
  show "kstratified \<Gamma> \<sigma> kp"
    unfolding kstratified_def list_all_iff
  proof
    fix kc assume inkp: "kc \<in> set kp"
    obtain k c where kc_eq: "kc = (k, c)" by (cases kc) blast
    obtain T p where k_eq: "k = (T, p)" by (cases k) blast
    have pc: "perms \<Gamma> T p = Some c"
      using mkreg_perms_mem[OF dis] greg inkp kc_eq k_eq by blast
    have "\<forall>x \<in> deps \<Gamma> T c. case x of (k', neg) \<Rightarrow>
            (if neg then \<sigma> k' < \<sigma> (T, p) else \<sigma> k' \<le> \<sigma> (T, p))"
    proof
      fix x assume xd: "x \<in> deps \<Gamma> T c"
      obtain k' neg where x_eq: "x = (k', neg)" by (cases x) blast
      from st[unfolded stratified_def, rule_format, OF pc xd[unfolded x_eq]]
      show "case x of (k', neg) \<Rightarrow>
              (if neg then \<sigma> k' < \<sigma> (T, p) else \<sigma> k' \<le> \<sigma> (T, p))"
        by (simp add: x_eq)
    qed
    then show "case kc of (k, c) \<Rightarrow> \<forall>(k', neg) \<in> deps \<Gamma> (fst k) c.
                 (if neg then \<sigma> k' < \<sigma> k else \<sigma> k' \<le> \<sigma> k)"
      by (simp add: kc_eq k_eq)
  qed
qed

definition ksafe :: "((ty \<times> perm) \<times> check) list \<Rightarrow> bool" where
  "ksafe kp = list_all (\<lambda>(k, c). generative c) kp"

lemma ksafe_iff:
  assumes dis: "distinct (map fst kp)" and greg: "\<Gamma> = mkreg kr kp"
  shows "ksafe kp = safe \<Gamma>"
proof
  assume "ksafe kp"
  then show "safe \<Gamma>"
    unfolding safe_def
    using mkreg_perms_mem[OF dis] greg by (fastforce simp: ksafe_def list_all_iff)
next
  assume "safe \<Gamma>"
  then show "ksafe kp"
    unfolding ksafe_def list_all_iff safe_def
    using mkreg_perms_mem[OF dis] greg by fastforce
qed

section \<open>The kernel\<close>

definition ksigma :: "((ty \<times> perm) \<times> nat) list \<Rightarrow> (key \<Rightarrow> nat)" where
  "ksigma ks = (\<lambda>k. case map_of ks k of Some n \<Rightarrow> n | None \<Rightarrow> 0)"

definition kernel_check :: "((ty \<times> rel) \<times> ty) list \<Rightarrow> ((ty \<times> perm) \<times> check) list
                              \<Rightarrow> ((ty \<times> perm) \<times> nat) list \<Rightarrow> datom list
                              \<Rightarrow> eid \<Rightarrow> ty \<Rightarrow> perm \<Rightarrow> eid \<Rightarrow> bool option" where
  "kernel_check kr kp ks ds s T p ob =
     (let \<Gamma> = mkreg kr kp; \<sigma> = ksigma ks in
      if distinct (map fst kp) \<and> kstratified \<Gamma> \<sigma> kp \<and> ksafe kp
      then Some (((T, p), s, ob) \<in> ktower \<Gamma> ds \<sigma> kp (\<sigma> (T, p)))
      else None)"

theorem kernel_correct:
  assumes "kernel_check kr kp ks ds s T p ob = Some b"
  shows "b = grants (mkreg kr kp) (set ds) (ksigma ks) (T, p) s ob"
proof -
  define \<Gamma> where "\<Gamma> = mkreg kr kp"
  define \<sigma> where "\<sigma> = ksigma ks"
  have guard: "distinct (map fst kp) \<and> kstratified \<Gamma> \<sigma> kp \<and> ksafe kp"
    and b_eq: "b = (((T, p), s, ob) \<in> ktower \<Gamma> ds \<sigma> kp (\<sigma> (T, p)))"
    using assms unfolding kernel_check_def \<Gamma>_def \<sigma>_def
    by (auto simp: Let_def split: if_splits)
  have dis: "distinct (map fst kp)" using guard by blast
  have strat: "stratified \<Gamma> \<sigma>"
    using guard kstratified_iff[OF dis \<Gamma>_def] by blast
  have sf: "safe \<Gamma>" using guard ksafe_iff[OF dis \<Gamma>_def] by blast
  have "ktower \<Gamma> ds \<sigma> kp (\<sigma> (T, p)) = strata \<Gamma> (set ds) \<sigma> (\<sigma> (T, p))"
    by (rule ktower_strata[OF strat sf dis \<Gamma>_def])
  with b_eq show ?thesis
    by (simp add: grants_def \<Gamma>_def \<sigma>_def)
qed

theorem kernel_defined:
  "(kernel_check kr kp ks ds s T p ob \<noteq> None)
     = (distinct (map fst kp)
        \<and> stratified (mkreg kr kp) (ksigma ks) \<and> safe (mkreg kr kp))"
proof -
  show ?thesis
    unfolding kernel_check_def Let_def
    using kstratified_iff[OF _ refl] ksafe_iff[OF _ refl]
    by (auto split: if_splits)
qed

end
