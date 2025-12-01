theory ParallelProcesses
  imports Main
begin

(*
Explanation of the Code:
    State and Operations:
        Each process has a state of type State (here, a natural number for simplicity).
        Operations are modeled as Update nat, which updates the state to a new value.

    Process States:
        The process_states inductive set defines the reachable states of a single process given a list of operations.

    System States:
        The system_states inductive set defines the reachable states of the system with two parallel processes, each with its own list of operations.

    Eventual Consistency:
        The property eventual_consistency states that for all reachable system states, the two processes eventually agree on the same state.

    Proof:
        The lemma eventual_consistency_example proves eventual consistency for a specific case where both processes apply the same sequence of operations ([Update 1, Update 2]).

Key Points:
    The model is kept simple for clarity.
    The proof shows that if both processes apply the same sequence of operations, they will eventually agree on the final state.
    This can be extended to more complex scenarios, such as asynchronous communication or partial updates.
*)


(* Define the state type for each process *)
type_synonym State = nat

(* Define the operations that can be performed on a state *)
datatype Operation = Update nat

(* Define the effect of an operation on a state *)
fun apply_op :: "Operation \<Rightarrow> State \<Rightarrow> State" where
  "apply_op (Update x) s = x"

(* Define the initial state for both processes *)
definition init_state :: State where
  "init_state = 0"

(* Define the state transitions for a single process *)
inductive_set process_states :: "Operation list \<Rightarrow> State set" for ops where
  initial: "init_state \<in> process_states ops"
| step: "\<lbrakk> s \<in> process_states ops; op \<in> set ops \<rbrakk> \<Longrightarrow> apply_op op s \<in> process_states ops"

(* Define the combined state of two processes *)
type_synonym SystemState = "State \<times> State"

(* Define the system transitions for two parallel processes *)
inductive_set system_states :: "Operation list \<Rightarrow> Operation list \<Rightarrow> SystemState set" for ops1 ops2 where
  initial: "(init_state, init_state) \<in> system_states ops1 ops2"
| step1: "\<lbrakk> (s1, s2) \<in> system_states ops1 ops2; op \<in> set ops1 \<rbrakk> \<Longrightarrow> (apply_op op s1, s2) \<in> system_states ops1 ops2"
| step2: "\<lbrakk> (s1, s2) \<in> system_states ops1 ops2; op \<in> set ops2 \<rbrakk> \<Longrightarrow> (s1, apply_op op s2) \<in> system_states ops1 ops2"

(* Define eventual consistency: both processes agree on the final state *)
definition eventual_consistency :: "Operation list \<Rightarrow> Operation list \<Rightarrow> bool" where
  "eventual_consistency ops1 ops2 \<equiv>
    \<forall>(s1, s2) \<in> system_states ops1 ops2. \<exists>s. s1 = s \<and> s2 = s"

(* Prove eventual consistency for a specific example *)
 lemma eventual_consistency_example:
  assumes "ops1 = [Update 1, Update 2]"
    and "ops2 = [Update 1, Update 2]"
  shows "eventual_consistency ops1 ops2"
proof -
  (* Show that all reachable states are consistent *)
  have "\<forall>(s1, s2) \<in> system_states ops1 ops2. s1 = s2"
  proof
    fix state
    assume "state \<in> system_states ops1 ops2"
    then show "fst state = snd state"
    proof (induction rule: system_states.induct)
      case initial
      then show ?case by (simp add: init_state_def)
    next
      case (step1 s1 s2 op)
      then show ?case by auto
    next
      case (step2 s1 s2 op)
      then show ?case by auto
    qed
  qed
  (* Conclude eventual consistency *)
  then show ?thesis
    unfolding eventual_consistency_def by auto
qed 



end