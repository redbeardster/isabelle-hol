theory EnergySuccessModel
  imports "HOL-TLA.TLA" "HOL-Library.Extended_Nat"
begin

(* Используем extended natural numbers для энергии *)
type_synonym energy_type = enat

consts
  energy :: "energy_type stfun"
  acting :: "bool stfun" 
  succeeding :: "bool stfun"

(* Начальное состояние *)
axiomatization where
  initial_energy: "\<turnstile> energy = 10"

(* Энергия уменьшается на каждом шаге, но не ниже 0 *)
axiomatization where
  energy_depletes: "\<turnstile> energy$ = (if energy > 0 then energy - 1 else 0)"

(* Успех требует энергии *)
axiomatization where  
  success_requires_energy: "\<turnstile> energy > 0 \<longrightarrow> (acting \<longrightarrow> \<diamond>succeeding)"

(* При нулевой энергии успех невозможен *)
axiomatization where
  exhaustion: "\<turnstile> energy = 0 \<longrightarrow> \<box>\<not>succeeding"

(* Действия тоже消耗 энергию *)
axiomatization where
  action_consumes_energy: "\<turnstile> acting \<longrightarrow> energy > 0"

end