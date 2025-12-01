theory AccessControlExamples
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
  by pat_completeness auto

(* ИСПРАВЛЕНО: используем if-then-else вместо case-of *)
definition default_perms :: permission where
  "default_perms role action = 
    (if role = Admin then True
     else if role = User then (action = Read \<or> action = Write)
     else if role = Guest then (action = Read)
     else False)"

(* Альтернативный вариант с явным перебором: *)
definition default_perms_alt :: permission where
  "default_perms_alt role action =
    (case role of
       Admin \<Rightarrow> True
     | User \<Rightarrow> (action = Read \<or> action = Write)
     | Guest \<Rightarrow> (action = Read))"

definition test_system :: system_state where
  "test_system = \<lparr>
    users = [''alice'' \<mapsto> User, ''bob'' \<mapsto> User, ''admin'' \<mapsto> Admin, ''visitor'' \<mapsto> Guest],
    files = [''public.txt'' \<mapsto> (''alice'', True), 
             ''secret.txt'' \<mapsto> (''alice'', False),
             ''bob_file.txt'' \<mapsto> (''bob'', False)],
    perms = default_perms
  \<rparr>"

(* Тестируем *)
value "has_access test_system ''alice'' Read ''public.txt''"
value "has_access test_system ''bob'' Read ''public.txt''"  
value "has_access test_system ''visitor'' Read ''public.txt''"
value "has_access test_system ''alice'' Read ''secret.txt''"
value "has_access test_system ''bob'' Read ''secret.txt''"
value "has_access test_system ''admin'' Read ''secret.txt''"

end