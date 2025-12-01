theory ComputationalEnergyModel
  imports "HOL-TLA.TLA" "HOL-Library.Extended_Nat"
begin

(* Используем extended natural numbers для энергии *)
type_synonym energy_type = enat

consts
  energy :: "energy_type stfun"
  acting :: "bool stfun" 
  succeeding :: "bool stfun"

(* ===== ВЫЧИСЛИТЕЛЬНЫЕ АКСИОМЫ ===== *)

(* Начальная энергия *)
axiomatization where
  initial_energy: "\<turnstile> energy = 10"

(* Энергия уменьшается на каждом шаге - ВЫЧИСЛЕНИЕ! *)
axiomatization where
  energy_depletes: "\<turnstile> energy$ = (if energy > 0 then energy - 1 else 0)"

(* Действие ускоряет расход энергии *)
axiomatization where
  action_accelerates_depletion: "\<turnstile> acting \<longrightarrow> energy$ = (if energy > 1 then energy - 2 else 0)"

(* Успех требует минимального уровня энергии *)
axiomatization where
  success_requires_energy: "\<turnstile> energy \<ge> 3 \<longrightarrow> (acting \<longrightarrow> \<diamond>succeeding)"

(* При низкой энергии успех невозможен *)
axiomatization where
  exhaustion: "\<turnstile> energy < 3 \<longrightarrow> \<box>\<not>succeeding"

(* ===== ВЫЧИСЛИТЕЛЬНЫЕ СВОЙСТВА ===== *)

(* Энергия всегда неотрицательна *)
lemma energy_non_negative: "\<turnstile> energy \<ge> 0"
  using energy_depletes initial_energy
  by tla

(* Энергия eventually достигает нуля *)
lemma eventual_exhaustion: "\<turnstile> \<diamond>(energy = 0)"
  using energy_depletes initial_energy
proof -
  have "\<turnstile> energy = 10 \<leadsto> energy = 0"
    unfolding leadsto_def
    by (smt (verit) energy_depletes enat_ord_simps(2) int_simps(1) tempI)
  then show ?thesis
    using initial_energy by tla
qed

(* ===== ОСНОВНОЙ АНАЛИЗ ===== *)

definition ActionLeadsToSuccess :: temporal where
  "ActionLeadsToSuccess \<equiv> leadsto acting  succeeding"

(* Локальная гарантия: пока энергия высокая *)
lemma local_success_guarantee:
  assumes "\<turnstile> energy \<ge> 5"
  shows "\<turnstile> ActionLeadsToSuccess \<longrightarrow> (\<box>acting \<leadsto> \<diamond>succeeding)"
  using assms success_requires_energy
  unfolding ActionLeadsToSuccess_def
  by tla

(* Глобальная гарантия нарушается из-за истощения *)
theorem global_guarantee_fails:
  "\<not>( \<turnstile> ActionLeadsToSuccess \<longrightarrow> \<box>(\<box>acting \<leadsto> \<diamond>succeeding))"
  using eventual_exhaustion exhaustion
  unfolding ActionLeadsToSuccess_def
  oops

(* ===== ВЫЧИСЛИТЕЛЬНЫЙ ЭКСПЕРИМЕНТ ===== *)

(* Траектория энергии: 10 \<rightarrow> 8 \<rightarrow> 6 \<rightarrow> 4 \<rightarrow> 2 \<rightarrow> 0 *)
lemma energy_trajectory:
  assumes "\<turnstile> acting"  (* Постоянно действуем *)
  shows "\<turnstile> energy = 10 \<leadsto> energy = 8 \<leadsto> energy = 6 \<leadsto> energy = 4 \<leadsto> energy = 2 \<leadsto> energy = 0"
  using assms action_accelerates_depletion energy_depletes
  unfolding leadsto_def
  oops

end