theory AdvancedFSM
imports Main "HOL-Library.LaTeXsugar"
begin

datatype protocol_state = 
    Idle | WaitAck | Processing | Error | Success | Retrying nat

datatype event = 
    Send | Ack | Nack | Timeout | ProcessComplete | ErrorOccurred | Retry


inductive protocol_fsm :: "protocol_state \<Rightarrow> event \<Rightarrow> protocol_state \<Rightarrow> bool" where
  send_msg:    "protocol_fsm Idle Send WaitAck"
| initial_ack: "protocol_fsm WaitAck Ack Processing"
| initial_nack: "protocol_fsm WaitAck Nack (Retrying 1)"
| processing_timeout: "protocol_fsm Processing Timeout (Retrying 0)"
| processing_complete: "protocol_fsm Processing ProcessComplete Success"
| processing_error: "protocol_fsm Processing ErrorOccurred Error"
| retry_success: "n \<le> 3 \<Longrightarrow> protocol_fsm (Retrying n) Ack Processing"       
| retry_again: "n < 3 \<Longrightarrow> protocol_fsm (Retrying n) Nack (Retrying (n+1))"
| retry_timeout: "n \<le> 3 \<Longrightarrow> protocol_fsm (Retrying n) Timeout (Retrying n)" 
| retry_fatal: "n \<ge> 3 \<Longrightarrow> protocol_fsm (Retrying n) Nack Error"
| reset_from_error: "protocol_fsm Error Retry Idle"
| reset_from_success: "protocol_fsm Success Send WaitAck"


definition max_retries_exceeded :: "protocol_state \<Rightarrow> bool" where
  "max_retries_exceeded s \<equiv> case s of Retrying n \<Rightarrow> n > 3 | _ \<Rightarrow> False"


lemma no_transitions_to_working_after_max_retries:
  "\<lbrakk> protocol_fsm s e s'; max_retries_exceeded s; s' \<noteq> Error \<rbrakk> \<Longrightarrow> False"
  unfolding max_retries_exceeded_def
  apply (erule protocol_fsm.cases)
  apply (auto split: protocol_state.split nat.splits)
  done

lemma only_error_transitions_after_max_retries:
  "\<lbrakk> protocol_fsm s e s'; max_retries_exceeded s \<rbrakk> \<Longrightarrow> s' = Error"
  unfolding max_retries_exceeded_def
  apply (erule protocol_fsm.cases)
  apply (auto split: protocol_state.split nat.splits)
  done


lemma transitions_when_max_retries_exceeded:
  "max_retries_exceeded s \<Longrightarrow> 
   \<nexists>e s'. protocol_fsm s e s' \<and> s' \<noteq> Error"
  unfolding max_retries_exceeded_def
  apply (auto split: protocol_state.split)
  apply (erule protocol_fsm.cases)
  apply (auto split: nat.splits)
  done


(* 
inductive reachable_state :: "protocol_state \<Rightarrow> bool" where
  start: "reachable_state Idle"
| step:  "\<lbrakk> reachable_state s; protocol_fsm s e s' \<rbrakk> \<Longrightarrow> reachable_state s'"

 *)


definition retry_count_invariant :: "protocol_state \<Rightarrow> bool" where
  "retry_count_invariant s \<equiv> case s of Retrying n \<Rightarrow> n \<le> 3 | _ \<Rightarrow> True"

lemma retry_invariant_preserved:
  "\<lbrakk> protocol_fsm s e s'; retry_count_invariant s \<rbrakk> \<Longrightarrow> retry_count_invariant s'"
  unfolding retry_count_invariant_def
  apply (erule protocol_fsm.cases)
  apply (auto split: protocol_state.split)
  done

lemma retry_count_bounded:
  "protocol_fsm s e s' \<Longrightarrow> 
   case s' of Retrying n \<Rightarrow> n \<le> 4 | _ \<Rightarrow> True"
  apply (erule protocol_fsm.cases)
  apply (auto split: protocol_state.split)
  done

inductive reachable :: "protocol_state \<Rightarrow> bool" where
  start: "reachable Idle"
| step:  "\<lbrakk> reachable s; protocol_fsm s e s' \<rbrakk> \<Longrightarrow> reachable s'"

(* -- Свойство прогресса: из любого состояния кроме Error есть переход *)
lemma reachable_progress:
  assumes "reachable s" "s \<noteq> Error"
  shows "\<exists>e s'. protocol_fsm s e s'"
  using assms
proof (induction rule: reachable.induct)
  case start
  then show ?case by (auto intro: protocol_fsm.intros)
next
  case (step s e s')
  then show ?case   by (metis initial_nack nat_le_linear processing_timeout protocol_state.exhaust reset_from_success retry_fatal retry_success send_msg)
qed

lemma reachable_Retrying: "\<exists>n. reachable (Retrying n)"
proof -
  have "reachable Idle" by (rule reachable.intros)
  moreover have "protocol_fsm Idle Send WaitAck" by (rule protocol_fsm.intros)
  moreover have "protocol_fsm WaitAck Nack (Retrying 1)" by (rule protocol_fsm.intros)
  ultimately show ?thesis  using reachable.step by blast
qed



lemma reachable_states_characterization:
  "reachable s \<longleftrightarrow> 
   s = Idle \<or> s = WaitAck \<or> s = Processing \<or> s = Success \<or> s = Error \<or>
   (\<exists>n. s = Retrying n \<and> n \<le> 3)"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  then show ?rhs
    by (induction rule: reachable.induct)
       (auto elim!: protocol_fsm.cases simp: less_Suc_eq)
next
  assume ?rhs
  then show ?lhs
  proof (elim disjE exE conjE)
    assume "s = Idle"
    then show ?thesis by (auto intro: reachable.intros)
  next
    assume "s = WaitAck"
    then show ?thesis 
      by (metis reachable.intros(1) protocol_fsm.intros(1) reachable.intros(2))
  next
    assume "s = Processing"
    then show ?thesis
      by (metis reachable.intros(1) protocol_fsm.intros(1) protocol_fsm.intros(2) reachable.intros(2))
  next
    assume "s = Success"
    then show ?thesis
      by (metis reachable.intros(1) protocol_fsm.intros(1) protocol_fsm.intros(2) 
                protocol_fsm.intros(5) reachable.intros(2))
  next
    assume "s = Error"
    then show ?thesis
      by (metis reachable.intros(1) protocol_fsm.intros(1) protocol_fsm.intros(2) 
                protocol_fsm.intros(6) reachable.intros(2))
  next
    fix n
    assume "s = Retrying n" and "n \<le> 3"
    then show ?thesis
    proof (induction n rule: nat_less_induct)
      case (1 n)
      show ?case
      proof (cases n)
        case 0
        have "reachable Idle" by (rule reachable.intros)
        moreover have "protocol_fsm Idle Send WaitAck" by (rule protocol_fsm.intros)
        moreover have "protocol_fsm WaitAck Ack Processing" by (rule protocol_fsm.intros)
        moreover have "protocol_fsm Processing Timeout (Retrying 0)" by (rule protocol_fsm.intros)
        ultimately show ?thesis using \<open>s = Retrying n\<close> 0
          by (metis reachable.intros(2))
      next
        case (Suc k)
        have "k < n" using Suc by simp
        with 1 have "reachable (Retrying k)" using \<open>n \<le> 3\<close> Suc  by (metis Suc_eq_plus1 bot_nat_0.not_eq_extremum initial_ack less_Suc_eq linorder_not_le not_less_eq numeral_3_eq_3 processing_timeout reachable.step retry_again send_msg start)
        moreover have "k < 3" using \<open>n \<le> 3\<close> Suc by auto
        then have "protocol_fsm (Retrying k) Nack (Retrying n)"
          using Suc protocol_fsm.intros        by auto
        ultimately show ?thesis using \<open>s = Retrying n\<close>
          by (auto intro: reachable.intros)
      qed
    qed
  qed
qed




end