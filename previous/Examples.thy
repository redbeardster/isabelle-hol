theory Examples
  imports IMP2.IMP2_Aux_Lemmas IMP2.IMP2
begin

program_spec sum-prog
assumes n \<ge> 0 ensures s = \<Sum> {0 ..n0}
defines \<open>s = 0 ; i = 0 ;while (i < n)
@variant \<open>n0 − i\<close>
@invariant \<open>n0 = n \<and> 0 \<le> i \<and> i \<le> n \<and> s = \<Sum> {0 ..i}\<close>
{i = i + 1 ; s = s + i }\<close>
apply vcg-cs
by (simp-all add: intvs-incdec)



end