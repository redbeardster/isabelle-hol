theory SELinuxLikePolicy
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
  user_id_injective: "inj user_id" and
  role_id_injective: "inj role_id" and 
  type_id_injective: "inj type_id"

lemma unique_user_ids:
  "\<forall>u1 u2. user_id u1 = user_id u2 \<longrightarrow> u1 = u2"
  using user_id_injective unfolding inj_def by blast

lemma unique_role_ids:  
  "\<forall>r1 r2. role_id r1 = role_id r2 \<longrightarrow> r1 = r2"
  using role_id_injective unfolding inj_def by blast

lemma unique_type_ids:
  "\<forall>t1 t2. type_id t1 = type_id t2 \<longrightarrow> t1 = t2"
  using type_id_injective unfolding inj_def by simp

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

axiomatization where  
  source_attribute_inheritance:
    "\<forall>t1 t2 tt c p. type_has_attribute t1 t2 \<and> av_allow t2 tt c p 
                    \<longrightarrow> av_allow t1 tt c p"

axiomatization where
  target_attribute_inheritance:
    "\<forall>st t1 t2 c p. type_has_attribute t1 t2 \<and> av_allow st t2 c p 
                    \<longrightarrow> av_allow st t1 c p"

axiomatization where
  neverallow_supersedes:
    "\<forall>st tt c p. av_allow st tt c p \<and> av_neverallow st tt c p 
                 \<longrightarrow> \<not> av_allow st tt c p"

subsection \<open>Дополнительные свойства системы\<close>

lemma role_type_transitive:
  assumes "role_has_attribute_role r1 r2" 
          "role_has_attribute_role r2 r3"
          "role_has_type r3 t"
  shows "role_has_type r1 t"
  using assms role_type_inheritance by blast

theorem neverallow_effective:
  assumes "av_neverallow st tt c p"
  shows "\<not> av_allow st tt c p"
proof (rule ccontr)
  assume "\<not> \<not> av_allow st tt c p"
  then have "av_allow st tt c p" by simp
  with assms have "av_allow st tt c p \<and> av_neverallow st tt c p" by simp
  with neverallow_supersedes show False by blast
qed

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

subsection \<open>Пример политики\<close>

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
  user1_has_admin: "user_has_role user1 admin_role" and 
  admin_has_process: "role_has_type admin_role process_type" and 
  process_to_file_allow: "av_allow process_type file_type file_class read_perm"

lemma user1_can_read_files:
  assumes "session = initialize_session user1"
  shows "check_access session file_type file_class read_perm"
  using assms user1_has_admin admin_has_process process_to_file_allow
  using initialize_session_def check_access_def using neverallow_effective by auto

end