theory Authz_Syntax
  imports Main
begin

text \<open>
  The data model and check language of SEMANTICS.md section 1-2.

  Entity ids, attributes and literals are modelled as naturals -- the
  semantics never inspects them, only compares them. Values are the
  disjoint sum of eids and literals; a database is a finite-or-infinite
  set of datoms (finiteness is assumed only where a theorem needs it).
\<close>

type_synonym eid = nat
type_synonym attr = nat
type_synonym lit = nat

datatype vl = Ent eid | Lit lit

type_synonym datom = "eid \<times> attr \<times> vl"
type_synonym db = "datom set"

text \<open>Relation names: a Datomic attribute traversed forward or in
  reverse (the underscore convention). \<open>ext\<close> is [[r]]_D of SEMANTICS section 1:
  in both directions the first component is the entity on the declaring
  type's side. Literal-valued datoms contribute nothing.\<close>

datatype rel = Fwd attr | Rev attr

definition ext :: "db \<Rightarrow> rel \<Rightarrow> (eid \<times> eid) set" where
  "ext D r = (case r of
     Fwd a \<Rightarrow> {(x, y). (x, a, Ent y) \<in> D}
   | Rev a \<Rightarrow> {(x, y). (y, a, Ent x) \<in> D})"

type_synonym ty = nat
type_synonym perm = nat
type_synonym key = "ty \<times> perm"

text \<open>The normalized check language. \<open>And\<close>/\<open>Or\<close> are binary here where
  the Clojure AST is n-ary; both connectives are associative and the
  n-ary form folds to this one, so nothing is lost. Sub-checks never
  change type: the only cross-references between bodies are \<open>Chain\<close>
  nodes naming a permission of the relation's target type.\<close>

datatype check =
    Terminal rel
  | Chain rel perm
  | AttrEq attr vl
  | CNot check
  | CAnd check check
  | COr check check

record reg =
  rels  :: "ty \<Rightarrow> rel \<rightharpoonup> ty"
  perms :: "ty \<Rightarrow> perm \<rightharpoonup> check"

definition rkeys :: "reg \<Rightarrow> key set" where
  "rkeys \<Gamma> = {(T, p). perms \<Gamma> T p \<noteq> None}"

text \<open>Polarity-labelled dependencies (SEMANTICS section 2). The marking is
  sticky under \<open>CNot\<close> -- a doubly-negated chain still counts as negative,
  matching the implementation's conservative \<open>check-stratified!\<close>.\<close>

fun deps :: "reg \<Rightarrow> ty \<Rightarrow> check \<Rightarrow> (key \<times> bool) set" where
  "deps \<Gamma> T (Terminal r) = {}"
| "deps \<Gamma> T (Chain r q) = (case rels \<Gamma> T r of
     Some T' \<Rightarrow> {((T', q), False)} | None \<Rightarrow> {})"
| "deps \<Gamma> T (AttrEq a v) = {}"
| "deps \<Gamma> T (CNot c) = (\<lambda>(k, b). (k, True)) ` deps \<Gamma> T c"
| "deps \<Gamma> T (CAnd c1 c2) = deps \<Gamma> T c1 \<union> deps \<Gamma> T c2"
| "deps \<Gamma> T (COr c1 c2) = deps \<Gamma> T c1 \<union> deps \<Gamma> T c2"

definition stratified :: "reg \<Rightarrow> (key \<Rightarrow> nat) \<Rightarrow> bool" where
  "stratified \<Gamma> \<sigma> \<longleftrightarrow>
     (\<forall>T p c k' neg. perms \<Gamma> T p = Some c \<longrightarrow> (k', neg) \<in> deps \<Gamma> T c \<longrightarrow>
        (if neg then \<sigma> k' < \<sigma> (T, p) else \<sigma> k' \<le> \<sigma> (T, p)))"

text \<open>Safety (groundedness, SEMANTICS section 2): conditions and exclusions
  never generate; every \<open>Or\<close> branch must. This is Datalog
  range-restriction; it is what makes answer sets finite and
  domain-independent.\<close>

fun generative :: "check \<Rightarrow> bool" where
  "generative (Terminal r) = True"
| "generative (Chain r q) = True"
| "generative (AttrEq a v) = False"
| "generative (CNot c) = False"
| "generative (CAnd c1 c2) = (generative c1 \<or> generative c2)"
| "generative (COr c1 c2) = (generative c1 \<and> generative c2)"

definition safe :: "reg \<Rightarrow> bool" where
  "safe \<Gamma> \<longleftrightarrow> (\<forall>T p c. perms \<Gamma> T p = Some c \<longrightarrow> generative c)"

end
