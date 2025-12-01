theory FiniteStateMachine
  imports Main
begin

(* Define states and input alphabet *)
type_synonym state = nat
type_synonym input = char

(* Transition function: state * input -> state *)
type_synonym transition = "(state \<times> input) \<Rightarrow> state"

(* Example: states: {0, 1, 2} and inputs: {a, b} *)
consts
  fsm_init :: state  (* Initial state *)
  fsm_tran :: transition  (* Transition function *)
  fsm_final :: "state set"  (* Final (accepting) states *)

(* Specify the initial state as state 0 *)
axiomatization where
  fsm_init: "fsm_init = 0"

abbreviation "fsm_transition s a \<equiv> fsm_tran (s, a)"  (* Transition function definition *)

(* Example transition function *)
lemma transition_example:
  assumes "s = 0" "a = ''a''"
  shows "fsm_transition s a = 1"  (* Transition from state 0 to state 1 on input 'a' *)
  using assms by (auto)

(* Optionally, you can define a function to simulate the FSM *)
fun fsm_process :: "state \<Rightarrow> input list \<Rightarrow> state" where
  "fsm_process s [] = s" |
  "fsm_process s (a # as) = fsm_process (fsm_transition s a) as"

(* Define final states *)
definition is_final :: "state \<Rightarrow> bool" where
  "is_final s = (s \<in> fsm_final)"

(* Example of a property you might want to prove *)
lemma fsm_acceptance:
  assumes "fsm_process fsm_init [''a'', ''b''] = 1"  (* Example trace *)
  shows "is_final 1"  (* State 1 is final *)
  using assms by (auto)

end