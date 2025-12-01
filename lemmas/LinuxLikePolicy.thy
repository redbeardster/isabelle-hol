theory LinuxLikePolicy
imports Main
begin

subsection \<open>Типы данных (сорта в Z3)\<close>

typedecl User
typedecl Role  
typedecl Type
typedecl Class
typedecl Permission

subsection \<open>Функции уникальных идентификаторов\<close>

consts
  user_id :: "User \<Rightarrow> nat"
  role_id :: "Role \<Rightarrow> nat" 
  type_id :: "Type \<Rightarrow> nat"

axiomatization where
  user_id_injective: "inj user_id"
and
  role_id_injective: "inj role_id"  
and
  type_id_injective: "inj type_id"

subsection \<open>Отношения контекста\<close>

consts
  user_has_role :: "User \<Rightarrow> Role \<Rightarrow> bool"
  role_has_type :: "Role \<Rightarrow> Type \<Rightarrow> bool" 
  type_has_attribute :: "Type \<Rightarrow> Type \<Rightarrow> bool"
  role_has_attribute_role :: "Role \<Rightarrow> Role \<Rightarrow> bool"

subsection \<open>Векторы доступа (Access Vectors)\<close>

consts
  av_allow :: "Type \<Rightarrow> Type \<Rightarrow> Class \<Rightarrow> Permission \<Rightarrow> bool"
  av_neverallow :: "Type \<Rightarrow> Type \<Rightarrow> Class \<Rightarrow> Permission \<Rightarrow> bool"

subsection \<open>Аксиомы системы\<close>

axiomatization where
  role_type_inheritance:
    "\<forall>r1 r2 t. role_has_attribute_role r1 r2 \<and> role_has_type r2 t 
               \<longrightarrow> role_has_type r1 t"
and  
  source_attribute_inheritance:
    "\<forall>t1 t2 tt c p. type_has_attribute t1 t2 \<and> av_allow t2 tt c p 
                    \<longrightarrow> av_allow t1 tt c p"
and
  target_attribute_inheritance:
    "\<forall>st t1 t2 c p. type_has_attribute t1 t2 \<and> av_allow st t2 c p 
                    \<longrightarrow> av_allow st t1 c p"
and
  neverallow_supersedes:
    "\<forall>st tt c p. av_allow st tt c p \<and> av_neverallow st tt c p 
                 \<longrightarrow> \<not> av_allow st tt c p"

subsection \<open>Конкретные экземпляры для тестирования\<close>

consts
  user1 :: User
  user2 :: User
  admin_role :: Role
  user_role :: Role  
  process_type :: Type
  file_type :: Type
  file_class :: Class
  read_perm :: Permission

axiomatization where
  user1_has_admin: "user_has_role user1 admin_role"
and
  admin_has_process: "role_has_type admin_role process_type"
and  
  process_to_file_allow: "av_allow process_type file_type file_class read_perm"

subsection \<open>Модель пользовательской сессии\<close>

record UserSession =
  current_user :: User
  active_roles :: "Role set"
  acquired_types :: "Type set"

definition initialize_session :: "User \<Rightarrow> UserSession" where
  "initialize_session u = \<lparr>
    current_user = u,
    active_roles = {r. user_has_role u r},
    acquired_types = {t. \<exists>r \<in> {r. user_has_role u r}. role_has_type r t}
  \<rparr>"

definition check_access :: "UserSession \<Rightarrow> Type \<Rightarrow> Class \<Rightarrow> Permission \<Rightarrow> bool" where
  "check_access session target_type class perm \<equiv>
   \<exists>source_type \<in> acquired_types session. 
     av_allow source_type target_type class perm \<and>
     \<not> av_neverallow source_type target_type class perm"

subsection \<open>Тестирование политики\<close>

lemma user1_can_read_files:
  assumes "session = initialize_session user1"
  shows "check_access session file_type file_class read_perm"
proof -
  have "user_has_role user1 admin_role" by (rule user1_has_admin)
  have "role_has_type admin_role process_type" by (rule admin_has_process)
  have "av_allow process_type file_type file_class read_perm" 
    by (rule process_to_file_allow)    
  show ?thesis
    using assms user1_has_admin admin_has_process process_to_file_allow
    using initialize_session_def check_access_def 
    using neverallow_supersedes by auto
qed

lemma neverallow_blocks_access:
  assumes "av_neverallow process_type file_type file_class read_perm"
  assumes "session = initialize_session user1" 
  shows "\<not> check_access session file_type file_class read_perm"
  using assms neverallow_supersedes  check_access_def initialize_session_def
  using process_to_file_allow by blast

end