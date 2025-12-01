theory ProcState
imports Main
begin

datatype State = State1 | State2 | State3
datatype Transition = Transition1 | Transition2
type_synonym Process = "State \<Rightarrow> Transition \<Rightarrow> State"

definition step :: "Process \<Rightarrow> State \<Rightarrow> Transition \<Rightarrow> State" where
  "step process state transition = process state transition"


inductive_set process_states :: "Process \<Rightarrow> State set" for process where
  start: "initial_state \<in> process_states process"
| step: "state \<in> process_states process \<Longrightarrow> step process state transition \<in> process_states process"


lemma "final_state \<in> process_states process"
  apply (induct rule: process_states.intros(1))
  done





end