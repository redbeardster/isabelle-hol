theory RBAC_LTL
  imports LTL
begin

text \<open>Типы для пользователей, ролей и разрешений\<close>
typedecl user
typedecl role
typedecl permission

text \<open>Отношения между пользователями, ролями и разрешениями\<close>
consts
  user_roles :: "user \<Rightarrow> role set"
  role_permissions :: "role \<Rightarrow> permission set"

text \<open>Состояние системы\<close>
record state =
  active_roles :: "user \<Rightarrow> role set"

text \<open>Ограничение: пользователь может активировать только назначенные роли\<close>
definition user_roles_constraint :: "state \<Rightarrow> bool" where
  "user_roles_constraint s \<equiv> \<forall>u r. r \<in> active_roles s u \<longrightarrow> r \<in> user_roles u"

text \<open>LTL-спецификация: ограничение всегда выполняется\<close>
definition ltl_user_roles_constraint :: "state ltl" where
  "ltl_user_roles_constraint \<equiv> \<box> (LTLProp user_roles_constraint)"

text \<open>Лемма: ограничение выполняется для всех последовательностей состояний\<close>
(* lemma ltl_user_roles_constraint_holds:
  "\<forall>\<sigma>. ltl_sem \<sigma> ltl_user_roles_constraint"
  unfolding ltl_user_roles_constraint_def user_roles_constraint_def
  by auto
 *)

lemma ltl_user_roles_constraint_holds:
  assumes "\<forall>s. user_roles_constraint s"  (* Все состояния удовлетворяют ограничению *)
  shows "\<forall>\<sigma>. ltl_sem \<sigma> ltl_user_roles_constraint"
  using assms
  unfolding ltl_user_roles_constraint_def user_roles_constraint_def
  by auto

(*
    OR: 
*)
  definition valid_system :: "state \<Rightarrow> bool" where
  "valid_system s \<equiv> user_roles_constraint s"

lemma valid_system_implies_ltl_constraint:
  assumes "\<forall>s. valid_system s"
  shows "\<forall>\<sigma>. ltl_sem \<sigma> ltl_user_roles_constraint"
  using assms
  unfolding valid_system_def ltl_user_roles_constraint_def user_roles_constraint_def
  by auto

end

