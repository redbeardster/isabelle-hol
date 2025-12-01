theory SuccessLTLPractice
  imports Main
begin

typedecl person
typedecl action_type
typedecl state


(* 
consts
  attempts :: "person \<Rightarrow> action_type option"
  succeeds :: "person \<Rightarrow> bool"
  ready    :: "person \<Rightarrow> bool"


text \<open>Определяем простые временные операторы\<close>
definition eventually :: "bool \<Rightarrow> bool" where
  "eventually P \<equiv> P"

definition always :: "bool \<Rightarrow> bool" where
  "always P \<equiv> P"

text \<open>Корректная формулировка\<close>
theorem readiness_sequence_correct:
  "\<forall>p. eventually (succeeds p) \<longrightarrow> 
       eventually (ready p \<and> eventually (attempts p \<noteq> None))"
  unfolding eventually_def
  by auto

 *)

consts
  attempts :: "state \<Rightarrow> person \<Rightarrow> action_type option"
  succeeds :: "state \<Rightarrow> person \<Rightarrow> bool" 
  ready    :: "state \<Rightarrow> person \<Rightarrow> bool"
  next_state :: "state \<Rightarrow> state" ("s\<^sub>next")

text \<open>Определяем LTL операторы над последовательностью состояний\<close>
definition eventually :: "(state \<Rightarrow> bool) \<Rightarrow> bool" where
  "eventually P \<equiv> \<exists>n. P ((s\<^sub>next ^^ n) s0)"

definition always :: "(state \<Rightarrow> bool) \<Rightarrow> bool" where
  "always P \<equiv> \<forall>n. P ((s\<^sub>next ^^ n) s0)"

axiomatization where s0: "initial_state s0"

theorem readiness_sequence_state_based:
  "\<forall>p. eventually (\<lambda>s. succeeds s p) \<longrightarrow> 
       eventually (\<lambda>s. ready s p \<and> eventually (\<lambda>s. attempts s p \<noteq> None))"
  unfolding eventually_def
  by metis



end