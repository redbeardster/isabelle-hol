theory PAT
imports Main
begin

datatype role = User | Admin | Guest
datatype operation = Read | Write | Execute | Delete

type_synonym user_id = string
type_synonym permission = "role \<Rightarrow> operation \<Rightarrow> bool"

record system_state =
  users :: "user_id \<rightharpoonup> role"
  files :: "string \<rightharpoonup> (user_id \<times> bool)"  (* владелец \<times> публичный *)
  perms :: permission

function has_access :: "system_state \<Rightarrow> user_id \<Rightarrow> operation \<Rightarrow> string \<Rightarrow> bool" where
  "has_access sys user op file = 
    (case (users sys user, files sys file) of
       (Some role, Some (owner, is_public)) \<Rightarrow>
         if perms sys role op then
           if op = Read \<and> is_public then True
           else user = owner
         else False
     | _ \<Rightarrow> False)"
  by pat_completeness auto


(* 

function security_invariant :: "system_state \<Rightarrow> bool" where
  "security_invariant sys = 
    (\<forall>user role file owner. 
       users sys user = Some role \<and> 
       files sys file = Some (owner, False) \<and> 
       user \<noteq> owner \<longrightarrow> 
       \<not>has_access sys user Write file)"
  by pat_completeness auto
 *)
(* 
theorem "security_invariant initial_state"
  apply (unfold security_invariant_def)
  apply (rule allI)+
  apply (case_tac "users initial_state user")
 *)







end