theory RBAC_Model
  imports Main
begin

(* Базовые типы данных *)
datatype user = User nat
datatype role = Role nat  
datatype permission = Permission nat
datatype object = Object nat
datatype operation = Read | Write | Execute | Delete

(* Определение ацикличности *)
definition acyclic :: "('a \<times> 'a) set \<Rightarrow> bool" where
  "acyclic r \<equiv> \<forall>x. (x, x) \<notin> r\<^sup>+"

(* RBAC система *)
record rbac_system =
  users :: "user set"
  roles :: "role set"
  permissions :: "permission set"
  objects :: "object set"
  
  (* Основные отношения RBAC *)
  user_assignment :: "(user \<times> role) set"     (* UA: Users assigned to Roles *)
  permission_assignment :: "(permission \<times> role) set"  (* PA: Permissions assigned to Roles *)
  role_hierarchy :: "(role \<times> role) set"      (* RH: Role Hierarchy (senior, junior) *)
  
  (* Дополнительные отношения *)
  permission_object :: "(permission \<times> object \<times> operation) set"

(* Вспомогательные функции *)

(* Получить все роли пользователя (включая унаследованные) *)
definition user_roles :: "rbac_system \<Rightarrow> user \<Rightarrow> role set" where
  "user_roles sys u = {r. (u, r) \<in> user_assignment sys} \<union> 
                     {r'. \<exists>r. (u, r) \<in> user_assignment sys \<and> (r, r') \<in> (role_hierarchy sys)\<^sup>*}"

(* Получить все разрешения роли *)
definition role_permissions :: "rbac_system \<Rightarrow> role \<Rightarrow> permission set" where
  "role_permissions sys r = {p. (p, r) \<in> permission_assignment sys}"

(* Получить все разрешения пользователя *)
definition user_permissions :: "rbac_system \<Rightarrow> user \<Rightarrow> permission set" where
  "user_permissions sys u = \<Union>{role_permissions sys r | r. r \<in> user_roles sys u}"

(* Проверка доступа *)
definition has_access :: "rbac_system \<Rightarrow> user \<Rightarrow> object \<Rightarrow> operation \<Rightarrow> bool" where
  "has_access sys u obj op \<equiv> 
    \<exists>p. p \<in> user_permissions sys u \<and> (p, obj, op) \<in> permission_object sys"

(* Корректность RBAC системы *)
definition well_formed :: "rbac_system \<Rightarrow> bool" where
  "well_formed sys \<equiv>
    (\<forall>u r. (u, r) \<in> user_assignment sys \<longrightarrow> u \<in> users sys \<and> r \<in> roles sys) \<and>
    (\<forall>p r. (p, r) \<in> permission_assignment sys \<longrightarrow> p \<in> permissions sys \<and> r \<in> roles sys) \<and>
    (\<forall>r1 r2. (r1, r2) \<in> role_hierarchy sys \<longrightarrow> r1 \<in> roles sys \<and> r2 \<in> roles sys) \<and>
    (\<forall>p obj op. (p, obj, op) \<in> permission_object sys \<longrightarrow> p \<in> permissions sys \<and> obj \<in> objects sys)"

(* Иерархия ролей должна быть ациклической *)
definition acyclic_hierarchy :: "rbac_system \<Rightarrow> bool" where
  "acyclic_hierarchy sys \<equiv> acyclic (role_hierarchy sys)"

(* Основные леммы *)

lemma user_roles_contains_direct:
  "well_formed sys \<Longrightarrow> (u, r) \<in> user_assignment sys \<Longrightarrow> r \<in> user_roles sys u"
  unfolding user_roles_def well_formed_def by auto

lemma user_roles_transitive:
  "well_formed sys \<Longrightarrow> r1 \<in> user_roles sys u \<Longrightarrow> (r1, r2) \<in> (role_hierarchy sys)\<^sup>* \<Longrightarrow> 
   r2 \<in> user_roles sys u"
  unfolding user_roles_def by auto

lemma permission_inheritance:
  "well_formed sys \<Longrightarrow> (u, r1) \<in> user_assignment sys \<Longrightarrow> (r1, r2) \<in> (role_hierarchy sys)\<^sup>* \<Longrightarrow>
   p \<in> role_permissions sys r2 \<Longrightarrow> p \<in> user_permissions sys u"
  unfolding user_permissions_def user_roles_def role_permissions_def
  by blast

(* Теоремы безопасности *)

theorem least_privilege:
  "well_formed sys \<Longrightarrow> has_access sys u obj op \<Longrightarrow>
   \<exists>r p. r \<in> user_roles sys u \<and> p \<in> role_permissions sys r \<and> (p, obj, op) \<in> permission_object sys"
  unfolding has_access_def user_permissions_def well_formed_def
  by auto

(* Разделение обязанностей *)
definition mutually_exclusive_roles :: "rbac_system \<Rightarrow> role \<Rightarrow> role \<Rightarrow> bool" where
  "mutually_exclusive_roles sys r1 r2 \<equiv>
    r1 \<in> roles sys \<and> r2 \<in> roles sys \<and> 
    (\<forall>u. u \<in> users sys \<longrightarrow> \<not>(r1 \<in> user_roles sys u \<and> r2 \<in> user_roles sys u))"

lemma separation_of_duties:
  "well_formed sys \<Longrightarrow> mutually_exclusive_roles sys r1 r2 \<Longrightarrow>
   \<forall>u. u \<in> users sys \<longrightarrow> \<not>(r1 \<in> user_roles sys u \<and> r2 \<in> user_roles sys u)"
  unfolding mutually_exclusive_roles_def by simp

(* Аксиома наследования разрешений в иерархии ролей *)
definition role_inheritance :: "rbac_system \<Rightarrow> bool" where
  "role_inheritance sys \<equiv> 
    \<forall>r1 r2. (r1, r2) \<in> role_hierarchy sys \<longrightarrow> 
            role_permissions sys r1 \<subseteq> role_permissions sys r2"

(* Альтернативно: более сильное условие корректности *)
definition well_formed_hierarchy :: "rbac_system \<Rightarrow> bool" where
  "well_formed_hierarchy sys \<equiv>
    well_formed sys \<and> 
    acyclic_hierarchy sys \<and> 
    role_inheritance sys"

theorem hierarchy_monotonicity:
  assumes "well_formed sys" 
          "acyclic_hierarchy sys" 
          "role_inheritance sys"
          "(r1, r2) \<in> (role_hierarchy sys)\<^sup>*"
  shows "role_permissions sys r1 \<subseteq> role_permissions sys r2"
using assms(4)
proof (induct rule: rtrancl_induct)
  case base
  show ?case by simp
next
  case (step y z)
  from `role_inheritance sys` `(y, z) \<in> role_hierarchy sys`
  have "role_permissions sys y \<subseteq> role_permissions sys z"
    unfolding role_inheritance_def by blast
  with step(3) show ?case by blast
qed



(* Корректность контроля доступа *)
theorem access_control_correctness:
  "well_formed sys \<Longrightarrow> has_access sys u obj op \<Longrightarrow>
   u \<in> users sys \<and> obj \<in> objects sys"
  unfolding has_access_def user_permissions_def well_formed_def 
  using user_roles_def by fastforce

(* Операции с системой *)

lemma add_user_preserves_wellformed:
  "well_formed sys \<Longrightarrow> u \<notin> users sys \<Longrightarrow>
   well_formed (sys\<lparr>users := users sys \<union> {u}\<rparr>)"
  unfolding well_formed_def by auto

lemma add_user_assignment_wellformed:
  "well_formed sys \<Longrightarrow> u \<in> users sys \<Longrightarrow> r \<in> roles sys \<Longrightarrow>
   well_formed (sys\<lparr>user_assignment := user_assignment sys \<union> {(u, r)}\<rparr>)"
  unfolding well_formed_def by auto

(* Удаление пользователя *)
definition remove_user :: "rbac_system \<Rightarrow> user \<Rightarrow> rbac_system" where
  "remove_user sys u = sys\<lparr>
    users := users sys - {u},
    user_assignment := user_assignment sys - {(u, r) | r. True}
  \<rparr>"

lemma remove_user_wellformed:
  "well_formed sys \<Longrightarrow> well_formed (remove_user sys u)"
  unfolding well_formed_def remove_user_def by auto

(* Свойства безопасности при изменениях *)
(* lemma add_role_monotonic:
  "well_formed sys \<Longrightarrow> u \<in> users sys \<Longrightarrow> r \<in> roles sys \<Longrightarrow>
   user_permissions sys u \<subseteq> 
   user_permissions (sys\<lparr>user_assignment := user_assignment sys \<union> {(u, r)}\<rparr>) u"
  unfolding user_permissions_def user_roles_def by simp
 *)
lemma add_role_monotonic:
  "well_formed sys \<Longrightarrow> u \<in> users sys \<Longrightarrow> r \<in> roles sys \<Longrightarrow>
   user_permissions sys u \<subseteq> 
   user_permissions (sys\<lparr>user_assignment := user_assignment sys \<union> {(u, r)}\<rparr>) u"
  unfolding user_permissions_def user_roles_def role_permissions_def
  apply auto
  done

(* 
lemma remove_permission_restrictive:
  "well_formed sys \<Longrightarrow> (p, r) \<in> permission_assignment sys \<Longrightarrow>
   user_permissions (sys\<lparr>permission_assignment := permission_assignment sys - {(p, r)}\<rparr>) u \<subseteq>
   user_permissions sys u"
  unfolding user_permissions_def role_permissions_def by auto *)

lemma remove_permission_restrictive:
  "well_formed sys \<Longrightarrow> (p, r) \<in> permission_assignment sys \<Longrightarrow>
   user_permissions (sys\<lparr>permission_assignment := permission_assignment sys - {(p, r)}\<rparr>) u \<subseteq>
   user_permissions sys u"
proof -
  assume wf: "well_formed sys"
  assume p_in_pa: "(p, r) \<in> permission_assignment sys"
  
  have "\<forall>role. role_permissions (sys\<lparr>permission_assignment := permission_assignment sys - {(p, r)}\<rparr>) role \<subseteq> 
                role_permissions sys role"
    unfolding role_permissions_def by auto
  
  moreover have "user_roles (sys\<lparr>permission_assignment := permission_assignment sys - {(p, r)}\<rparr>) u = 
                 user_roles sys u"
    unfolding user_roles_def by simp
  
  ultimately show ?thesis
    unfolding user_permissions_def by blast
qed


(* Пример системы *)
definition example_rbac :: "rbac_system" where
  "example_rbac = \<lparr>
    users = {User 1, User 2, User 3},
    roles = {Role 1, Role 2, Role 3},
    permissions = {Permission 1, Permission 2, Permission 3},
    objects = {Object 1, Object 2},
    user_assignment = {(User 1, Role 1), (User 2, Role 2), (User 3, Role 3)},
    permission_assignment = {
      (Permission 1, Role 3),
      (Permission 1, Role 2), (Permission 2, Role 2),
      (Permission 1, Role 1), (Permission 2, Role 1), (Permission 3, Role 1)
    },
    role_hierarchy = {(Role 3, Role 2), (Role 2, Role 1)},
    permission_object = {
      (Permission 1, Object 1, Read), (Permission 1, Object 2, Read),
      (Permission 2, Object 1, Write), (Permission 2, Object 2, Write),
      (Permission 3, Object 1, Delete), (Permission 3, Object 2, Delete)
    }
  \<rparr>"

(* Проверка примера *)
lemma example_wellformed: "well_formed example_rbac"
  unfolding well_formed_def example_rbac_def by auto

lemma example_acyclic: "acyclic_hierarchy example_rbac"
  unfolding acyclic_hierarchy_def acyclic_def example_rbac_def
  by (smt (z3) Pair_inject insertE numeral_One numeral_eq_iff role.inject select_convs(7) semiring_norm(89) singleton_iff tranclE verit_eq_simplify(10,12))


(* Примеры проверки доступа *)
lemma admin_has_delete_access:
  "has_access example_rbac (User 1) (Object 1) Delete"
  unfolding has_access_def user_permissions_def user_roles_def 
            role_permissions_def example_rbac_def
  by auto

(* lemma employee_no_delete_access:
  "\<not>has_access example_rbac (User 3) (Object 1) Delete"
  unfolding has_access_def user_permissions_def user_roles_def 
            role_permissions_def example_rbac_def
  by auto
 *)
(* 
lemma employee_no_delete_access:
  "\<not>has_access example_rbac (User 3) (Object 1) Delete"
  unfolding has_access_def user_permissions_def user_roles_def 
            role_permissions_def example_rbac_def
  apply auto
  apply (simp_all add: rtrancl_insert)
  apply (metis Role.inject One_nat_def Suc_1 Suc_eq_plus1_left empty_iff insert_iff)
  done
 *)


(* Инварианты безопасности *)
theorem no_access_to_nonexistent_object:
  "well_formed sys \<Longrightarrow> obj \<notin> objects sys \<Longrightarrow> \<not>has_access sys u obj op"
  unfolding has_access_def well_formed_def by blast

theorem no_roles_no_permissions:
  "well_formed sys \<Longrightarrow> user_roles sys u = {} \<Longrightarrow> user_permissions sys u = {}"
  unfolding user_permissions_def by auto

theorem remove_all_roles_removes_permissions:
  "well_formed sys \<Longrightarrow> 
   user_permissions (sys\<lparr>user_assignment := user_assignment sys - {(u, r) | r. True}\<rparr>) u = {}"
  unfolding user_permissions_def user_roles_def by auto

end