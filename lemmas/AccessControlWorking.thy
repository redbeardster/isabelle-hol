theory AccessControlWorking
imports Main
begin

datatype role = User | Admin | Guest
datatype operation = Read | Write | Execute | Delete

type_synonym user_id = string
type_synonym permission = "role \<Rightarrow> operation \<Rightarrow> bool"

record system_state =
  users :: "user_id \<rightharpoonup> role"
  files :: "string \<rightharpoonup> (user_id \<times> bool)"
  perms :: permission

function has_access :: "system_state \<Rightarrow> user_id \<Rightarrow> operation \<Rightarrow> string \<Rightarrow> bool" where
  "has_access sys user action file = 
    (case (users sys user, files sys file) of
       (Some role, Some (owner, is_public)) \<Rightarrow>
         if perms sys role action then
           if action = Read \<and> is_public then True
           else user = owner
         else False
     | _ \<Rightarrow> False)"
  apply pat_completeness
  apply auto
  done

termination by lexicographic_order

(* Явно генерируем code equations *)
lemma has_access_code [code]:
  "has_access sys user action file = 
    (case (users sys user, files sys file) of
       (Some role, Some (owner, is_public)) \<Rightarrow>
         if perms sys role action then
           if action = Read \<and> is_public then True
           else user = owner
         else False
     | _ \<Rightarrow> False)"
  by (simp add: has_access.simps)

definition default_perms :: permission where
  "default_perms = (\<lambda>role action.
    (role = Admin) \<or> 
    (role = User \<and> (action = Read \<or> action = Write)) \<or> 
    (role = Guest \<and> action = Read))"

definition test_system :: system_state where
  "test_system = \<lparr>
    users = [''alice'' \<mapsto> User, ''bob'' \<mapsto> User, ''admin'' \<mapsto> Admin, ''visitor'' \<mapsto> Guest],
    files = [''public.txt'' \<mapsto> (''alice'', True), 
             ''secret.txt'' \<mapsto> (''alice'', False),
             ''bob_file.txt'' \<mapsto> (''bob'', False)],
    perms = default_perms
  \<rparr>"

(* Теперь должно работать *)
value "has_access test_system ''alice'' Read ''public.txt''"      (* True *)
value "has_access test_system ''bob'' Write ''secret.txt''"       (* False *)
value "has_access test_system ''admin'' Delete ''bob_file.txt''"  (* True *)

end