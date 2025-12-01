theory ThermostatSystem
imports
  Main
  "HOL-Library.Stream"
begin


definition always :: "('a stream \<Rightarrow> bool) \<Rightarrow> 'a stream \<Rightarrow> bool" ("\<box>") where
  "\<box> P s = (\<forall>n. P (sdrop n s))"

definition eventually :: "('a stream \<Rightarrow> bool) \<Rightarrow> 'a stream \<Rightarrow> bool" ("\<diamond>") where  
  "\<diamond> P s = (\<exists>n. P (sdrop n s))"

locale thermostat =
  fixes temp :: "nat stream"
    and min_temp :: nat
    and max_temp :: nat
  assumes invariant: "\<box> (\<lambda>s. min_temp \<le> shd s \<and> shd s \<le> max_temp) temp"
begin

(*  Безопасность: температура всегда \<ge> min_temp *)
theorem safety: "\<box> (\<lambda>s. min_temp \<le> shd s) temp"
  using invariant unfolding always_def by auto

(* -- Идеальная температура достигается бесконечно часто *)  
definition ideal_temperature :: "nat \<Rightarrow> bool" where
  "ideal_temperature ideal = \<box> (\<diamond> (\<lambda>s. shd s = ideal)) temp"

(* -- Система стабилизируется на идеальной температуре *)
definition stabilizes_at_ideal :: "nat \<Rightarrow> bool" where
  "stabilizes_at_ideal ideal = \<diamond> (\<box> (\<lambda>s. shd s = ideal)) temp"

(* -- Докажем, что стабилизация влечет идеальную температуру *)
theorem stabilization_implies_ideal:
  assumes "stabilizes_at_ideal ideal"
  shows "ideal_temperature ideal"
proof -
  from assms obtain n where 
    always_ideal: "\<forall>m. shd (sdrop (n + m) temp) = ideal"
    unfolding stabilizes_at_ideal_def eventually_def always_def
    by auto
  
  show ?thesis unfolding ideal_temperature_def always_def eventually_def
  proof
    fix k
    show "\<exists>m. shd (sdrop m (sdrop k temp)) = ideal"
(*       using always_ideal[of "k"] by (intro exI[of _ "n + k"]) simp *)
     by (metis add.commute always_ideal sdrop_simps(1) sdrop_snth)
  qed
qed

(* -- locale thermostat *)
primcorec simple_cycle :: "nat \<Rightarrow> nat list \<Rightarrow> nat stream" where
  "simple_cycle n lst = 
    (if lst = [] then undefined
     else (lst ! (n mod length lst)) ## simple_cycle (n + 1) lst)"

definition example_thermostat :: "nat stream" where
  "example_thermostat = simple_cycle 0 [20, 21, 22, 21]"

lemma "stake 8 example_thermostat = [20, 21, 22, 21, 20, 21, 22, 21]"
  unfolding stake_def
  using example_thermostat_def stake_def
  sorry


lemma example_thermostat_valid: 
  "thermostat example_thermostat 18 25"
proof
  show "\<box> (\<lambda>s. 18 \<le> shd s \<and> shd s \<le> 25) example_thermostat"
    using always_def example_thermostat_def  
(*     by blast *)
    sorry
qed

(* -- Использование с конкретным термостатом *)
interpretation example: 
  thermostat "example_thermostat" 18 25
  by (rule example_thermostat_valid)

lemma "example.ideal_temperature 21" 
  unfolding example.ideal_temperature_def
  sorry

end 


end