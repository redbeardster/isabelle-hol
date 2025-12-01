theory AccessControl
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


definition default_perms :: permission where
  "default_perms role op = 
    case (role, op) of
      (Admin, _) \<Rightarrow> True
    | (User, Read) \<Rightarrow> True
    | (User, Write) \<Rightarrow> True
    | (Guest, Read) \<Rightarrow> True
    | _ \<Rightarrow> False"

definition test_system :: system_state where
  "test_system = \<lparr>
    users = [''alice'' \<mapsto> User, ''bob'' \<mapsto> User, ''admin'' \<mapsto> Admin, ''visitor'' \<mapsto> Guest],
    files = [''public.txt'' \<mapsto> (''alice'', True), 
             ''secret.txt'' \<mapsto> (''alice'', False),
             ''bob_file.txt'' \<mapsto> (''bob'', False)],
    perms = default_perms
  \<rparr>"


(* 
lemma "has_access test_system ''visitor'' Read ''public.txt''"
  unfolding has_access_def test_system_def default_perms_def
  by auto  (* Гость может читать публичный файл *)

lemma "has_access test_system ''bob'' Read ''public.txt''"  
  unfolding has_access_def test_system_def default_perms_def
  by auto  (* Боб тоже может читать публичный файл *)

lemma "\<not> has_access test_system ''bob'' Write ''public.txt''"
  unfolding has_access_def test_system_def default_perms_def
  by auto  (* Боб не владелец, не может писать *)

lemma "has_access test_system ''alice'' Write ''secret.txt''"
  unfolding has_access_def test_system_def default_perms_def
  by auto  (* Алиса - владелец, может писать *)

lemma "has_access test_system ''admin'' Write ''secret.txt''"
  unfolding has_access_def test_system_def default_perms_def
  by auto  (* Админ может всё *)

lemma "has_access test_system ''admin'' Delete ''bob_file.txt''"
  unfolding has_access_def test_system_def default_perms_def
  by auto  (* Админ может удалять чужие файлы *)

theorem public_files_readable:
  "\<forall>sys user file. 
     (files sys file = Some (owner, True) \<and> users sys user \<noteq> None) 
     \<longrightarrow> has_access sys user Read file"
  unfolding has_access_def
  apply auto
  apply (case_tac "users sys user")
  apply auto
  apply (case_tac "perms sys aa Read")
  apply auto
  done


theorem only_owners_can_write:
  "\<forall>sys user file. 
     has_access sys user Write file \<longrightarrow> 
     (\<exists>owner is_public. files sys file = Some (owner, is_public) \<and> user = owner)"
  unfolding has_access_def
  apply auto
  apply (case_tac "users sys user")
  apply auto
  apply (case_tac "perms sys aa Write")
  apply auto
  done


theorem admin_has_full_access:
  "\<forall>sys user file op. 
     users sys user = Some Admin \<longrightarrow> perms sys Admin op \<longrightarrow> has_access sys user op file"
  unfolding has_access_def
  apply auto
  apply (case_tac "files sys file")
  apply auto
  done

(* Функция для изменения прав *)
definition change_perms :: "system_state \<Rightarrow> permission \<Rightarrow> system_state" where
  "change_perms sys new_perms = sys\<lparr>perms := new_perms\<rparr>"

(* Функция для добавления файла *)
definition add_file :: "system_state \<Rightarrow> string \<Rightarrow> user_id \<Rightarrow> bool \<Rightarrow> system_state" where
  "add_file sys filename owner is_public = 
    sys\<lparr>files := (files sys)(filename \<mapsto> (owner, is_public))\<rparr>"

(* Пример: создаём систему, где гости не могут читать *)
definition restricted_perms :: permission where
  "restricted_perms role op = 
    case (role, op) of
      (Admin, _) \<Rightarrow> True
    | (User, Read) \<Rightarrow> True
    | (User, Write) \<Rightarrow> True
    | _ \<Rightarrow> False"

definition restricted_system :: system_state where
  "restricted_system = test_system\<lparr>perms := restricted_perms\<rparr>"

(* Теперь гость не может читать даже публичные файлы *)
lemma "\<not> has_access restricted_system ''visitor'' Read ''public.txt''"
  unfolding has_access_def restricted_system_def restricted_perms_def test_system_def
  by auto


definition shared_doc_system :: system_state where
  "shared_doc_system = \<lparr>
    users = [''alice'' \<mapsto> User, ''bob'' \<mapsto> User, ''charlie'' \<mapsto> User],
    files = [''project.doc'' \<mapsto> (''alice'', False)],  (* приватный, но... *)
    perms = \<lambda>role op. case op of 
        Read \<Rightarrow> True   (* ...все могут читать *)
      | Write \<Rightarrow> role = User  (* ...все пользователи могут писать *)
      | _ \<Rightarrow> False
  \<rparr>"

lemma "has_access shared_doc_system ''bob'' Read ''project.doc''"
  unfolding has_access_def shared_doc_system_def
  by auto

lemma "has_access shared_doc_system ''bob'' Write ''project.doc''"  
  unfolding has_access_def shared_doc_system_def
  by auto

lemma "\<not> has_access shared_doc_system ''bob'' Delete ''project.doc''"
  unfolding has_access_def shared_doc_system_def
  by auto


definition corporate_system :: system_state where
  "corporate_system = \<lparr>
    users = [''ceo'' \<mapsto> Admin, ''manager'' \<mapsto> User, ''intern'' \<mapsto> Guest],
    files = [''budget.xlsx'' \<mapsto> (''ceo'', False), 
             ''meeting_notes.txt'' \<mapsto> (''manager'', True)],
    perms = \<lambda>role op. 
      case (role, op) of
        (Admin, _) \<Rightarrow> True
      | (User, Read) \<Rightarrow> True
      | (User, Write) \<Rightarrow> True
      | (Guest, Read) \<Rightarrow> True
      | _ \<Rightarrow> False
  \<rparr>"

(* Стажёр может читать заметки о встрече *)
lemma "has_access corporate_system ''intern'' Read ''meeting_notes.txt''"
  unfolding has_access_def corporate_system_def
  by auto

(* Но не может читать бюджет *)
lemma "\<not> has_access corporate_system ''intern'' Read ''budget.xlsx''"
  unfolding has_access_def corporate_system_def
  by auto


(* Автоматическая проверка политик доступа *)
definition check_access_policy :: "system_state \<Rightarrow> bool" where
  "check_access_policy sys = 
    (\<forall>user file. 
       users sys user = Some Guest \<longrightarrow> 
       \<not>has_access sys user Write file \<and>
       \<not>has_access sys user Delete file)"

lemma "check_access_policy test_system"
  unfolding check_access_policy_def
  apply auto
  apply (unfold has_access_def test_system_def default_perms_def)
  apply auto
  done






 *)








end