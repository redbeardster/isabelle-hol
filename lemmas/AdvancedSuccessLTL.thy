theory AdvancedSuccessLTL
  imports Main
begin

typedecl person
typedecl action_type

consts
  attempts     :: "person \<Rightarrow> action_type option"
  succeeds     :: "person \<Rightarrow> bool"
  ready        :: "person \<Rightarrow> bool"
  time_passes  :: "person \<Rightarrow> bool"

text \<open>"Чтобы получить результат, нужно сначала быть готовым и затем предпринять действие"\<close>
theorem readiness_sequence:
  "\<forall>p. \<diamond>(succeeds p) \<longrightarrow> (\<exists>a. attempts p = Some a) \<and> \<diamond>(ready p \<^bold>\<and> \<diamond>(attempts p \<noteq> None))"  unfolding eventually_def
  by metis

text \<open>"Успех требует непрерывных усилий" - используем оператор Until \<close>
theorem continuous_effort:
  "\<forall>p. attempts p \<noteq> None \<longrightarrow> 
       (attempts p \<noteq> None \<^bold>U succeeds p)"
  unfolding until_def
  by (metis option.distinct(1))

end