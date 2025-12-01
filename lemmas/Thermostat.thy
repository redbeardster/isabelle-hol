theory Thermostat
imports
  Main
  "HOL-Library.Stream"
begin


definition always :: "('a stream \<Rightarrow> bool) \<Rightarrow> 'a stream \<Rightarrow> bool" ("\<box>") where
  "\<box> P s = (\<forall>n. P (sdrop n s))"

definition eventually :: "('a stream \<Rightarrow> bool) \<Rightarrow> 'a stream \<Rightarrow> bool" ("\<diamond>") where  
  "\<diamond> P s = (\<exists>n. P (sdrop n s))"

(*  notation "\<box>" ("\<box>")
notation "\<diamond>" ("\<diamond>")
 *) 

record 'a thermostat =
  temp :: "'a stream"
  min_temp :: nat
  max_temp :: nat
(*   invariant :: "always (\<lambda>s. min_temp \<le> shd s \<and> shd s \<le> max_temp) (temp :: 'a stream)" *)


locale thermostat =
  fixes temp :: "nat stream"
    and min_temp max_temp :: nat
  assumes invariant: "\<box> (\<lambda>s. min_temp \<le> shd s \<and> shd s \<le> max_temp) temp"
begin

(* lemma "thermostat_safety":
  assumes "thermostat temp min_t max_t inv"
  shows "\<box> (\<lambda>s. min_t \<le> shd s) temp" *)

theorem safety: "\<box> (\<lambda>s. min_temp \<le> shd s) temp"
  using invariant unfolding always_def by auto



end
