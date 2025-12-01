theory SimpleSuccessExample
  imports Main
begin

typedecl person
typedecl action_type

consts
  attempts :: "person \<Rightarrow> action_type option"
  succeeds :: "person \<Rightarrow> bool"
  ready    :: "person \<Rightarrow> bool"


text \<open>Добавляем необходимые аксиомы\<close>
axiomatization where
  success_requires_attempt: "\<forall>p. succeeds p \<longrightarrow> (\<exists>a. attempts p = Some a)" and
  success_requires_readiness: "\<forall>p. succeeds p \<longrightarrow> ready p"

text \<open>Теперь теорема доказывается тривиально\<close>
theorem readiness_basic:
  "\<forall>p. succeeds p \<longrightarrow> (\<exists>a. attempts p = Some a) \<and> ready p"
  using success_requires_attempt success_requires_readiness
  by blast



text \<open>Если хотим выразить "eventually", используем кванторы существования\<close>
theorem readiness_eventual:
  "(\<exists>p. succeeds p) \<longrightarrow> (\<exists>p. ready p \<and> (\<exists>q. attempts q \<noteq> None))"
  using readiness_basic by fastforce



end