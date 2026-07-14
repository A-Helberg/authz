theory Authz_Export
  imports Authz_Kernel "HOL-Library.Code_Target_Numeral"
begin

text \<open>
  Code export: the verified kernel as a Scala module. Naturals map to
  target integers (Scala BigInt) via \<open>Code_Target_Numeral\<close>; the
  conversion functions are exported so a JVM host can marshal Longs.
  Retrieve the artifact with:

    isabelle export -d verification -x "Authz.Authz_Export:**" -O <dir> Authz
\<close>

export_code kernel_check Fwd Rev Ent Lit
  Terminal Chain AttrEq CNot CAnd COr
  integer_of_nat nat_of_integer
  in Scala module_name AuthzKernel
end
