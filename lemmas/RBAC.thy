theory RBAC
 imports Main
begin

(* Определение типов для пользователей, ролей и разрешений *)
typedecl User
typedecl Role
typedecl Permission

(* Определение функций для назначения ролей пользователям и разрешений ролям *)
consts
  assigned_roles :: "User \<Rightarrow> Role set"
  role_permissions :: "Role \<Rightarrow> Permission set"

(* Определение функции для проверки, имеет ли пользователь разрешение *)
definition has_permission :: "User \<Rightarrow> Permission \<Rightarrow> bool" where
  "has_permission u p \<longleftrightarrow> (\<exists>r \<in> assigned_roles u. p \<in> role_permissions r)"

(* Пример пользователей, ролей и разрешений *)
consts
  user1 :: User
  user2 :: User
  role1 :: Role
  role2 :: Role
  perm1 :: Permission
  perm2 :: Permission

(* Пример назначения ролей пользователям *)
axiomatization where
  user1_roles: "assigned_roles user1 = {role1, role2}" and
  user2_roles: "assigned_roles user2 = {role2}"

(* Пример назначения разрешений ролям *)
axiomatization where
  role1_perms: "role_permissions role1 = {perm1}" and
  role2_perms: "role_permissions role2 = {perm1, perm2}"

(* Свойство: пользователь имеет разрешение, если хотя бы одна из его ролей имеет это разрешение *)
lemma user1_has_perm1: "has_permission user1 perm1"
  unfolding has_permission_def
  using user1_roles role1_perms role2_perms by auto

lemma user2_has_perm2: "has_permission user2 perm2"
  unfolding has_permission_def
  using user2_roles role2_perms by auto

(* Доказательство, что user1 имеет perm1 *)
theorem user1_has_perm1_proof: "has_permission user1 perm1"
  by (simp add: user1_has_perm1)

(* Доказательство, что user2 имеет perm2 *)
theorem user2_has_perm2_proof: "has_permission user2 perm2"
  by (simp add: user2_has_perm2)




end