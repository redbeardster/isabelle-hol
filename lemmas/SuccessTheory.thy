theory SimpleSuccessLTL
  imports Main
begin

typedecl person
typedecl action

consts
  attempts :: "person \<Rightarrow> action option"  (* None = бездействует, Some a = действует *)
  succeeds :: "person \<Rightarrow> bool"

(* Самый простой LTL-тезис *)
theorem actor_eventually_succeeds:
  "\<forall>p. attempts p \<noteq> None \<longrightarrow> \<diamond>(succeeds p)"
  unfolding eventually_def
  by auto

end