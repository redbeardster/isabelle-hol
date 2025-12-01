theory PingPong
  imports Main
begin

(*
    Message and Process State Types:
        message defines the two possible messages: Ping and Pong.
        process_state defines the two possible states a process can be in: WaitingForPing or WaitingForPong.

    System State:
        The system state is represented as a pair of process states, one for each process.

    Initial State:
        The initial state is defined as (WaitingForPing, WaitingForPong), meaning the first process is waiting for a Ping and the second process is waiting for a Pong.

    Transition Function:
        The transition function defines how the system state changes when a message is received. It alternates the states of the two processes based on the message.

    System Transitions:
        The system_transitions inductive set defines the possible transitions in the system. Each transition is a triple (s, m, s') where s is the current state, m is the message, and s' is the next state.

    Lemmas:
        alternates: The system alternates between WaitingForPing and WaitingForPong states.
        returns_to_initial: The system eventually returns to the initial state after two transitions.
        deterministic: The system is deterministic; given a state and a message, there is only one possible next state.
*)

(* Define the types for messages and processes *)
datatype message = Ping | Pong

(* Define the state of a process *)
datatype process_state = 
  WaitingForPing 
| WaitingForPong

thm process_state.splits

(* Define the system state as a pair of process states *)
type_synonym system_state = "process_state \<times> process_state"

(* Define the initial state of the system *)
definition initial_state :: system_state where
  "initial_state \<equiv> (WaitingForPing, WaitingForPong)"


thm initial_state_def



(* Define the transition function for the system *)
fun transition :: "system_state \<Rightarrow> message \<Rightarrow> system_state" where
  "transition (WaitingForPing, WaitingForPong) Ping = (WaitingForPong, WaitingForPing)"
| "transition (WaitingForPong, WaitingForPing) Pong = (WaitingForPing, WaitingForPong)"
| "transition s _ = s" (* Invalid transitions leave the state unchanged *)

(* Define the system as a transition system *)
inductive_set system_transitions :: "(system_state \<times> message \<times> system_state) set" where
  step1: "(s, Ping, s') \<in> system_transitions" if "s' = transition s Ping"
| step2: "(s, Pong, s') \<in> system_transitions" if "s' = transition s Pong"

(* Lemma: The system alternates between WaitingForPing and WaitingForPong *)
lemma alternates:
  assumes "(s, m, s') \<in> system_transitions"
  shows "fst s \<noteq> fst s' \<and> snd s \<noteq> snd s'"
  using assms
(*   by  try *)
  sorry
(*(cases s; cases s'; cases m; auto simp: initial_state_def split: process_state.splits) *)

(* Lemma: The system eventually returns to the initial state *)
lemma returns_to_initial:
  assumes "(s, m, s') \<in> system_transitions"
  shows "\<exists>m'. (s', m', initial_state) \<in> system_transitions"
  using assms
(*   by (cases s; cases m; auto simp: initial_state_def split: process_state.splits) *)
  sorry

(* Lemma: The system is deterministic *)
lemma deterministic:
  assumes "(s, m, s1) \<in> system_transitions" and "(s, m, s2) \<in> system_transitions"
  shows "s1 = s2"
  using assms
(*   by (cases s; cases m; auto simp: initial_state_def split: process_state.splits) *)
  using system_transitions.simps by fastforce


end