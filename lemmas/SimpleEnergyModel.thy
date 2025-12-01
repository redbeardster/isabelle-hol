theory SimpleEnergyModel
  imports "HOL-TLA.TLA"
begin

(* Булева энергия - есть/нет *)
consts
  has_energy :: "bool stfun"
  acting :: "bool stfun"
  succeeding :: "bool stfun"

axiomatization where
  initial_energy: "\<turnstile> has_energy"

(* Энергия eventually кончается *)
axiomatization where
  energy_fails: "\<turnstile> \<diamond>\<not>has_energy"

(* Успех требует энергии *)
axiomatization where
  success_requires_energy: "\<turnstile> has_energy \<longrightarrow> (acting \<longrightarrow> \<diamond>succeeding)"

(* Без энергии успех невозможен *)
axiomatization where
  no_success_without_energy: "\<turnstile> \<not>has_energy \<longrightarrow> \<box>\<not>succeeding"

(* Основные теоремы *)
definition ActionLeadsToSuccess :: temporal where
  "ActionLeadsToSuccess \<equiv> acting \<leadsto> succeeding"

(* Контрпример: успех работает пока есть энергия *)
lemma energy_based_counterexample:
  "\<turnstile> ActionLeadsToSuccess \<longrightarrow> (\<box>acting \<leadsto> \<diamond>succeeding)"
  unfolding ActionLeadsToSuccess_def
  using success_requires_energy
  by tla

lemma not_always_success:
  "\<not> \<turnstile> ActionLeadsToSuccess \<longrightarrow> \<box>(\<box>acting \<leadsto> \<diamond>succeeding)"
  using energy_fails no_success_without_energy
  unfolding ActionLeadsToSuccess_def
  oops

end