theory SimpleSuccessLTL
  imports Main
begin

typedecl person
typedecl action

consts
  attempts :: "person \<Rightarrow> action option"  (* None = бездействует, Some a = действует *)
  succeeds :: "person \<Rightarrow> bool"


(* Определяем ПРОСТОЙ eventually *)
definition eventually :: "bool \<Rightarrow> bool" where
  "eventually P \<equiv> P"

axiomatization where
  action_leads_to_success: "attempts p \<noteq> None \<Longrightarrow> succeeds p"


theorem actor_eventually_succeeds:
  "\<forall>p. attempts p \<noteq> None \<longrightarrow> eventually (succeeds p)"
  unfolding eventually_def
  using action_leads_to_success
  by blast


end