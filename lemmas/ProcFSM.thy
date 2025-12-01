theory ProcFSM
imports Main 
begin

datatype State = On | Off
datatype Transition = Toggle

definition toggle :: "State \<Rightarrow> Transition \<Rightarrow> State" where
  "toggle state transition = (case transition of Toggle \<Rightarrow> (case state of On \<Rightarrow> Off | Off \<Rightarrow> On))" 

inductive_set process_states :: "State set" where
  start: "On \<in> process_states"
| step: "state \<in> process_states \<Longrightarrow> toggle state Toggle \<in> process_states"

lemma "Off \<in> process_states"
  using process_states.start process_states.step toggle_def by fastforce





end