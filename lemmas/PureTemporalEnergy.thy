theory PureTemporalEnergy
  imports "HOL-TLA.TLA"
begin

consts
  EnergyHigh :: temporal
  EnergyMedium :: temporal  
  EnergyLow :: temporal
  EnergyZero :: temporal
  Acting :: temporal
  Succeeded :: temporal

axiomatization where
  initial_state: "\<turnstile> EnergyHigh" and
  
  (* Взаимоисключающие состояния *)
  exclusivity: "\<turnstile> 
    (EnergyHigh \<longrightarrow> \<not>EnergyMedium \<and> \<not>EnergyLow \<and> \<not>EnergyZero) \<and>
    (EnergyMedium \<longrightarrow> \<not>EnergyHigh \<and> \<not>EnergyLow \<and> \<not>EnergyZero) \<and>
    (EnergyLow \<longrightarrow> \<not>EnergyHigh \<and> \<not>EnergyMedium \<and> \<not>EnergyZero) \<and>
    (EnergyZero \<longrightarrow> \<not>EnergyHigh \<and> \<not>EnergyMedium \<and> \<not>EnergyLow)" and
  
  (* Детерминированные временные переходы *)
  high_to_medium: "\<turnstile> EnergyHigh \<leadsto> EnergyMedium" and
  medium_to_low: "\<turnstile> EnergyMedium \<leadsto> EnergyLow" and
  low_to_zero: "\<turnstile> EnergyLow \<leadsto> EnergyZero" and
  zero_permanent: "\<turnstile> EnergyZero \<longrightarrow> \<box>EnergyZero" and
    
  (* Ускорение при действиях *)
  action_acceleration: "\<turnstile> Acting \<longrightarrow> 
    (EnergyHigh \<leadsto> EnergyLow) \<and>
    (EnergyMedium \<leadsto> EnergyZero)" and
    
  (* Условия успеха *)
  success_possible: "\<turnstile> EnergyHigh \<longrightarrow> (Acting \<longrightarrow> \<diamond>Succeeded)" and
  success_impossible: "\<turnstile> \<not>EnergyHigh \<longrightarrow> \<box>\<not>Succeeded"

end