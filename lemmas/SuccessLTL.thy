theory SuccessLTL
  imports Main
begin

typedecl person
typedecl outcome

consts 
  attempts :: "person \<Rightarrow> outcome option"
  succeeds :: "outcome \<Rightarrow> bool"

text \<open>Полная формализация тезиса \<close>
theorem success_principle:
  "(\<forall>p. attempts p \<noteq> None \<longrightarrow> \<diamond>(succeeds (the (attempts p)))) \<and>
   (\<forall>p. attempts p = None \<longrightarrow> \<not>(\<diamond>(succeeds undefined)))"
  (is "?doer \<and> ?non_doer")
proof -
  have ?doer 
    by (metis option.sel eventually_def)
  have ?non_doer
    by (simp add: eventually_def)
  then show ?thesis by blast
qed