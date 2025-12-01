theory WorkingFiniteSystem
imports Main
begin

datatype finite_state = S1 | S2 | S3 | S4 | Done

(* Определяем переходы *)
inductive_set finite_transitions :: "(finite_state \<times> finite_state) set" where
  step1: "(S1, S2) \<in> finite_transitions"
| step2: "(S2, S3) \<in> finite_transitions"
| step3: "(S3, S4) \<in> finite_transitions"
| step4: "(S4, Done) \<in> finite_transitions"

(* Терминальные состояния *)
definition terminal_states :: "finite_state set" where
  "terminal_states = {s. \<not> (\<exists>s'. (s, s') \<in> finite_transitions)}"

(* Достижимые состояния *)
definition reachable_states :: "finite_state set" where
  "reachable_states = {s. (S1, s) \<in> finite_transitions\<^sup>*}"






end