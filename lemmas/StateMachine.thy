theory StateMachine
imports Main
begin

datatype state = S0 | S1 | S2 | S3
datatype action = A | B | C

inductive transition :: "state \<Rightarrow> action \<Rightarrow> state \<Rightarrow> bool" where
  "transition S0 A S1"
| "transition S1 B S2" 
| "transition S2 C S3"

notation transition ("_ \<rightarrow>[_] _" [60, 0, 60] 55)

definition no_transition :: "state \<Rightarrow> action \<Rightarrow> state \<Rightarrow> bool" where
  "no_transition s a s' \<equiv> \<not>(s \<rightarrow>[a] s')"

notation no_transition ("_ ↛[_] _" [60, 0, 60] 55)

(* -- Доказываем свойства недостижимости *)
lemma cannot_skip_states:
  "S0 ↛[B] S2" 
  unfolding no_transition_def
proof
  assume "S0 \<rightarrow>[B] S2"
  thus False  by (cases rule: transition.cases)
qed

lemma deadlock_in_s3:
  "\<forall>a s'. S3 ↛[a] s'"
  unfolding no_transition_def
proof (intro allI)
  fix a s'
  show "\<not>(S3 \<rightarrow>[a] s')"
    using state.exhaust transition.cases by blast  
qed



end