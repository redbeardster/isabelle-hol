theory WorkingEnergyExample
  imports "HOL-TLA.TLA" 
begin


(* axiomatization where
  system_fails: "\<turnstile> \<diamond>\<not>system_works" and
  success_when_working: "\<turnstile> system_works \<longrightarrow> (acting \<longrightarrow> \<diamond>succeeding)"   and 
  no_success_when_broken: "\<turnstile> \<not>system_works \<longrightarrow> \<box>\<not>succeeding"

definition ActionLeadsToSuccess :: temporal where
  "ActionLeadsToSuccess \<equiv> \<turnstile> acting \<leadsto>  succeeding s"

(* Теперь у нас есть настоящий контрпример! *)
lemma theorem2_holds_locally:
  assumes "\<turnstile> system_works"
  shows "\<turnstile> ActionLeadsToSuccess \<longrightarrow> (\<box>acting \<leadsto> \<diamond>succeeding)"
  using assms success_when_working
  unfolding ActionLeadsToSuccess_def
  by tla

lemma theorem1_fails_globally:
  "\<not> \<turnstile> ActionLeadsToSuccess \<longrightarrow> \<box>(\<box>acting \<leadsto> \<diamond>succeeding)"
  using system_fails no_success_when_broken
  unfolding ActionLeadsToSuccess_def
  oops *)

(* consts
  system_works :: "bool stfun"
  acting :: "bool stfun"
  succeeding :: "bool stfun"


(* Временные константы *)
consts
  SystemWorks :: temporal
  Acting :: temporal
  Succeeding :: temporal

axiomatization where
  system_fails: "\<turnstile> \<diamond>(\<not>SystemWorks)" and
  success_when_working: "\<turnstile> \<box>(SystemWorks \<longrightarrow> (Acting \<leadsto> Succeeding))" and  
  no_success_when_broken: "\<turnstile> \<box>(\<not>SystemWorks \<longrightarrow> \<box>(\<not>Succeeding))"

definition ActionLeadsToSuccess :: temporal where
  "ActionLeadsToSuccess \<equiv>  leadsto Acting Succeeding"
 *)

(* Простая модель: есть энергия / нет энергии *)
(* consts
  HasEnergy :: temporal
  Acting :: temporal
  Succeeded :: temporal

axiomatization where
  initial_energy: "\<turnstile> HasEnergy" and
  energy_depletes: "\<turnstile> Acting \<longrightarrow> \<circle>(\<not>HasEnergy)" and 
  eventual_exhaustion: "\<turnstile> \<diamond>(\<not>HasEnergy)" and
  success_requires_energy: "\<turnstile> HasEnergy \<longrightarrow> (Acting \<longrightarrow> \<diamond>Succeeded)" and
  no_success_without_energy: "\<turnstile> \<not>HasEnergy \<longrightarrow> \<box>\<not>Succeeded"

definition ActionLeadsToSuccess :: temporal where
  "ActionLeadsToSuccess \<equiv> leadsto Acting  Succeeded"
 *)


consts
  HasEnergy :: temporal
  Acting :: temporal
  Succeeded :: temporal

axiomatization where
  initial_energy: "\<turnstile> HasEnergy" and
  energy_eventually_depletes: "\<turnstile> HasEnergy \<leadsto> \<not>HasEnergy" and
  acting_consumes_energy: "\<turnstile> Acting \<leadsto> \<not> HasEnergy" and 
  success_when_energized: "\<turnstile> HasEnergy \<longrightarrow> (Acting \<longrightarrow> \<diamond>Succeeded)" and
  no_success_when_exhausted: "\<turnstile> \<not>HasEnergy \<longrightarrow> \<box>\<not>Succeeded"

definition ActionLeadsToSuccess :: temporal where
  "ActionLeadsToSuccess \<equiv> leadsto Acting  Succeeded"

lemma energy_counterexample:
  "(\<turnstile> ActionLeadsToSuccess \<longrightarrow> (\<box>Acting \<leadsto> \<diamond>Succeeded)) \<and> 
   \<not>( \<turnstile> ActionLeadsToSuccess \<longrightarrow> \<box>(\<box>Acting \<leadsto> \<diamond>Succeeded))"
  using energy_eventually_depletes no_success_when_exhausted acting_consumes_energy
  unfolding ActionLeadsToSuccess_def
proof -
  have False
    by (smt (z3) Init.Init_simps(1) InitDmd energy_eventually_depletes initial_energy int_simps(14,4,9) inteq_reflection leadsto_def temp_simps(1,2) unl_lift)
  then show "(\<turnstile> (Acting \<leadsto> Succeeded) \<longrightarrow> (\<box>Acting \<leadsto> \<diamond>Succeeded)) \<and> \<not> (\<turnstile> (Acting \<leadsto> Succeeded) \<longrightarrow> \<box>(\<box>Acting \<leadsto> \<diamond>Succeeded))"
    by fastforce
qed








end