theory DiscreteEnergyModel
  imports "HOL-TLA.TLA"
begin

consts
  EnergyHigh :: temporal
  EnergyMedium :: temporal  
  EnergyLow :: temporal
  EnergyZero :: temporal
  Acting :: temporal
  Succeeded :: temporal
(* Только три состояния для простоты *)
consts
  HasEnergy :: temporal


axiomatization where
  initial_energy: "\<turnstile> HasEnergy" and
  energy_depletes: "\<turnstile> HasEnergy \<leadsto> \<not>HasEnergy" and
  success_with_energy: "\<turnstile> HasEnergy \<longrightarrow> (Acting \<longrightarrow> \<diamond>Succeeded)" and
  no_success_without_energy: "\<turnstile> \<not>HasEnergy \<longrightarrow> \<box>\<not>Succeeded"

definition ActionLeadsToSuccess :: temporal where
  "ActionLeadsToSuccess \<equiv> leadsto Acting  Succeeded"

theorem local_success_guarantee:
  "\<turnstile> ActionLeadsToSuccess \<longrightarrow> (\<box>Acting \<leadsto> \<diamond>Succeeded)"
  unfolding ActionLeadsToSuccess_def
  using success_with_energy initial_energy
  by (metis Init.Init_simps(1) energy_depletes int_simps(14,2,8) inteq_reflection leadsto_def more_temp_simps3(4,6) temp_simps(1))  

theorem no_global_success_guarantee:
  "\<not> (\<turnstile> ActionLeadsToSuccess \<longrightarrow> \<box>(\<box>Acting \<leadsto> \<diamond>Succeeded))"
  using energy_depletes no_success_without_energy local_success_guarantee
  unfolding ActionLeadsToSuccess_def
  using Init.Init_simps energy_depletes int_simps inteq_reflection leadsto_def more_temp_simps3 temp_simps
  by (metis (mono_tags, lifting) initial_energy)


end