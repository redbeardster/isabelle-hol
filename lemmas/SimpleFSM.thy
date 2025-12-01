theory SimpleFSM
  imports Main
begin

(* Define states *)
datatype state = s0 | s1 | s2

(* Define events *)
datatype event = a | b

(* Define transition function *)
fun transition :: "state \<Rightarrow> event \<Rightarrow> state" where
  "transition s0 a = s1" |
  "transition s1 a = s2" |
  "transition s2 a = s0" |
  "transition s0 b = s0" |
  "transition s1 b = s1" |
  "transition s2 b = s2"

(* Define initial state *)
definition initial_state :: state where
  "initial_state = s0"

(* Define an execution of the FSM with a list of events *)
fun execute :: "state \<Rightarrow> event list \<Rightarrow> state" where
  "execute s [] = s" |
  "execute s (e # es) = execute (transition s e) es"


value "execute s2 [a]"

theorem execute_empty: "execute initial_state [] = initial_state"
  by (simp add: initial_state_def)

theorem execute_single_a: "execute initial_state [a] = s1"
  by (simp add: initial_state_def)

theorem execute_single_b: "execute initial_state [b] = s0"
  by (simp add: initial_state_def)

theorem execute_two_a: "execute initial_state [a, a] = s2"
  by (simp add: initial_state_def)

theorem execute_three_a: "execute initial_state [a, a, a] = s0"
  by (simp add: initial_state_def)

theorem execute_a_b_a: "execute initial_state [a, b, a] = s2"
  by (simp add: initial_state_def)


end