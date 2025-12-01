theory twopc
  imports Main
begin

(* Data types for participants and transactions *)
datatype participant = P nat
datatype transaction = T nat

(* Protocol states for coordinator *)
datatype coord_state = 
    CoordInit
  | CoordPreparing  
  | CoordCommitted
  | CoordAborted

(* Protocol states for participants *)
datatype part_state =
    PartInit
  | PartPrepared
  | PartCommitted  
  | PartAborted

(* Messages in the protocol *)
datatype message =
    Prepare transaction
  | PrepareOK transaction participant
  | PrepareNO transaction participant  
  | Commit transaction
  | Abort transaction
  | CommitOK transaction participant
  | AbortOK transaction participant

(* System state *)
record system_state =
  coord_states :: "transaction ⇒ coord_state"
  part_states :: "participant ⇒ transaction ⇒ part_state"
  messages :: "message set"
  participants :: "participant set"

(* Initial system state *)
definition init_state :: "participant set ⇒ system_state" where
"init_state parts = ⦇
  coord_states = λt. CoordInit,
  part_states = λp t. PartInit,
  messages = {},
  participants = parts \<rparr>"

(* Coordinator actions *)
inductive coord_step :: "system_state ⇒ transaction ⇒ system_state ⇒ bool" where

(* Coordinator starts transaction by sending Prepare messages *)
coord_prepare: "
  coord_states s t = CoordInit ⟹
  coord_step s t (s⦇
    coord_states := (coord_states s)(t := CoordPreparing),
    messages := messages s ∪ {Prepare t}
  ⦇)"

(* Coordinator commits if all participants prepared *)
| coord_commit: "
  coord_states s t = CoordPreparing ⟹
  (∀p ∈ participants s. PrepareOK t p ∈ messages s) ⟹
  coord_step s t (s⦇
    coord_states := (coord_states s)(t := CoordCommitted),
    messages := messages s ∪ {Commit t}
  ⦇)"

(* Coordinator aborts if any participant votes no or times out *)
| coord_abort: "
  coord_states s t = CoordPreparing ⟹
  (∃p ∈ participants s. PrepareNO t p ∈ messages s) ⟹
  coord_step s t (s⦇
    coord_states := (coord_states s)(t := CoordAborted),
    messages := messages s ∪ {Abort t}
  ⦇)"(* P
articipant actions *)
inductive part_step :: "system_state ⇒ participant ⇒ transaction ⇒ system_state ⇒ bool" where

(* Participant receives Prepare and votes YES *)
part_prepare_ok: "
  part_states s p t = PartInit ⟹
  Prepare t ∈ messages s ⟹
  part_step s p t (s⦇
    part_states := λp' t'. if p' = p ∧ t' = t then PartPrepared else part_states s p' t',
    messages := messages s ∪ {PrepareOK t p}
  ⦇)"

(* Participant receives Prepare and votes NO *)
| part_prepare_no: "
  part_states s p t = PartInit ⟹
  Prepare t ∈ messages s ⟹
  part_step s p t (s⦇
    part_states := λp' t'. if p' = p ∧ t' = t then PartAborted else part_states s p' t',
    messages := messages s ∪ {PrepareNO t p}
  ⦇)"

(* Participant commits after receiving Commit *)
| part_commit: "
  part_states s p t = PartPrepared ⟹
  Commit t ∈ messages s ⟹
  part_step s p t (s⦇
    part_states := λp' t'. if p' = p ∧ t' = t then PartCommitted else part_states s p' t',
    messages := messages s ∪ {CommitOK t p}
  ⦇)"

(* Participant aborts after receiving Abort *)
| part_abort: "
  part_states s p t ∈ {PartInit, PartPrepared} ⟹
  Abort t ∈ messages s ⟹
  part_step s p t (s⦇
    part_states := λp' t'. if p' = p ∧ t' = t then PartAborted else part_states s p' t',
    messages := messages s ∪ {AbortOK t p}
  ⦇)"

(* Combined system step *)
inductive system_step :: "system_state ⇒ system_state ⇒ bool" where
  coord_step_rule: "coord_step s t s' ⟹ system_step s s'"
| part_step_rule: "part_step s p t s' ⟹ system_step s s'"

(* Reachable states *)
inductive reachable :: "participant set ⇒ system_state ⇒ bool" where
  init_reachable: "reachable parts (init_state parts)"
| step_reachable: "reachable parts s ⟹ system_step s s' ⟹ reachable parts s'"

(* Safety properties *)

(* Atomicity: All participants have the same outcome *)
definition atomicity :: "system_state ⇒ transaction ⇒ bool" where
"atomicity s t ≡ 
  (∀p q. p ∈ participants s ⟹ q ∈ participants s ⟹
    (part_states s p t = PartCommitted ⟷ part_states s q t = PartCommitted) ∧
    (part_states s p t = PartAborted ⟷ part_states s q t = PartAborted))"

(* Consistency: If coordinator commits, all participants must commit *)
definition consistency :: "system_state ⇒ transaction ⇒ bool" where
"consistency s t ≡
  coord_states s t = CoordCommitted ⟹
  (∀p ∈ participants s. part_states s p t ∈ {PartPrepared, PartCommitted})"

(* Isolation: Committed participants must have been prepared first *)
definition isolation :: "system_state ⇒ transaction ⇒ bool" where
"isolation s t ≡
  ∀p ∈ participants s. part_states s p t = PartCommitted ⟹
  (∃s'. reachable (participants s) s' ∧ part_states s' p t = PartPrepared)"

(* Durability: Once committed, stays committed *)
definition durability :: "system_state ⇒ system_state ⇒ transaction ⇒ bool" where
"durability s s' t ≡
  (∀p ∈ participants s. part_states s p t = PartCommitted ⟹ part_states s' p t = PartCommitted) ∧
  (coord_states s t = CoordCommitted ⟹ coord_states s' t = CoordCommitted)"(*
 Main safety theorem: Atomicity is preserved *)
theorem atomicity_preserved:
  "reachable parts s ⟹ atomicity s t"
proof (induction rule: reachable.induct)
  case (init_reachable parts)
  show "atomicity (init_state parts) t"
    unfolding atomicity_def init_state_def
    by simp
next
  case (step_reachable parts s s')
  assume IH: "atomicity s t"
  assume step: "system_step s s'"
  
  from step show "atomicity s' t"
  proof (cases rule: system_step.cases)
    case (coord_step_rule)
    then show ?thesis
      using IH
      by (cases rule: coord_step.cases) (auto simp: atomicity_def)
  next
    case (part_step_rule)
    then show ?thesis
      using IH
      by (cases rule: part_step.cases) (auto simp: atomicity_def)
  qed
qed

(* Consistency preservation *)
theorem consistency_preserved:
  "reachable parts s ⟹ consistency s t"
proof (induction rule: reachable.induct)
  case (init_reachable parts)
  show "consistency (init_state parts) t"
    unfolding consistency_def init_state_def
    by simp
next
  case (step_reachable parts s s')
  assume IH: "consistency s t"
  assume step: "system_step s s'"
  
  from step show "consistency s' t"
  proof (cases rule: system_step.cases)
    case (coord_step_rule)
    then show ?thesis
      using IH
      by (cases rule: coord_step.cases) (auto simp: consistency_def)
  next
    case (part_step_rule)
    then show ?thesis
      using IH
      by (cases rule: part_step.cases) (auto simp: consistency_def)
  qed
qed

(* Helper lemmas for protocol correctness *)

lemma coord_commit_requires_all_prepared:
  "coord_step s t s' ⟹ coord_states s' t = CoordCommitted ⟹
   ∀p ∈ participants s. PrepareOK t p ∈ messages s"
  by (cases rule: coord_step.cases) auto

lemma part_commit_requires_coord_commit:
  "part_step s p t s' ⟹ part_states s' p t = PartCommitted ⟹
   Commit t ∈ messages s"
  by (cases rule: part_step.cases) auto

lemma no_mixed_outcomes:
  "reachable parts s ⟹
   ¬(∃p q. p ∈ participants s ∧ q ∈ participants s ∧
           part_states s p t = PartCommitted ∧ part_states s q t = PartAborted)"
  using atomicity_preserved
  unfolding atomicity_def
  by blast

(* Liveness properties would require fairness assumptions *)
(* This is a basic framework - full liveness proofs need additional assumptions *)

end
