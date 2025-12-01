theory Hierarchy_Proof
  imports Main RBAC_Model
begin

(* Сначала нужно уточнить семантику иерархии ролей *)
(* В RBAC иерархия обычно означает: если (r1, r2) ∈ role_hierarchy, 
   то r2 наследует все разрешения r1 (r2 "старше" r1) *)

(* Переопределим role_permissions с учетом иерархии *)
definition role_permissions_with_hierarchy :: "rbac_system ⇒ role ⇒ permission set" where
"role_permissions_with_hierarchy sys r = 
  {p. (p, r) ∈ permission_assignment sys} ∪
  ⋃{role_permissions_with_hierarchy sys r' | r'. (r', r) ∈ role_hierarchy sys}"

(* Альтернативное определение через транзитивное замыкание *)
definition role_permissions_inherited :: "rbac_system ⇒ role ⇒ permission set" where
"role_permissions_inherited sys r = 
  ⋃{p. ∃r'. (r', r) ∈ (role_hierarchy sys)⇧* ∧ (p, r') ∈ permission_assignment sys}"

(* Основная лемма: монотонность иерархии *)
theorem hierarchy_monotonicity:
  assumes wf: "well_formed sys" 
  assumes acyc: "acyclic_hierarchy sys"
  assumes hier: "(r1, r2) ∈ (role_hierarchy sys)⇧*"
  shows "role_permissions_inherited sys r1 ⊆ role_permissions_inherited sys r2"
proof -
  (* Используем определение role_permissions_inherited *)
  have "role_permissions_inherited sys r1 = 
        ⋃{p. ∃r'. (r', r1) ∈ (role_hierarchy sys)⇧* ∧ (p, r') ∈ permission_assignment sys}"
    unfolding role_permissions_inherited_def by simp
  
  also have "... ⊆ 
        ⋃{p. ∃r'. (r', r2) ∈ (role_hierarchy sys)⇧* ∧ (p, r') ∈ permission_assignment sys}"
  proof (rule UN_least)
    fix p
    assume "∃r'. (r', r1) ∈ (role_hierarchy sys)⇧* ∧ (p, r') ∈ permission_assignment sys"
    then obtain r' where r'_props: "(r', r1) ∈ (role_hierarchy sys)⇧*" "(p, r') ∈ permission_assignment sys"
      by auto
    
    (* Используем транзитивность: r' →* r1 →* r2, значит r' →* r2 *)
    from r'_props(1) hier have "(r', r2) ∈ (role_hierarchy sys)⇧*"
      by (rule rtrancl_trans)
    
    with r'_props(2) show "p ∈ ⋃{p. ∃r'. (r', r2) ∈ (role_hierarchy sys)⇧* ∧ (p, r') ∈ permission_assignment sys}"
      by auto
  qed
  
  also have "... = role_permissions_inherited sys r2"
    unfolding role_permissions_inherited_def by simp
  
  finally show ?thesis .
qed

(* Вспомогательные леммы *)

lemma rtrancl_refl: "(r, r) ∈ R⇧*"
  by simp

lemma direct_permissions_included:
  "well_formed sys ⟹ 
   {p. (p, r) ∈ permission_assignment sys} ⊆ role_permissions_inherited sys r"
  unfolding role_permissions_inherited_def
  using rtrancl_refl by auto

(* Лемма о том, что прямые разрешения сохраняются при наследовании *)
lemma hierarchy_preserves_direct:
  assumes "well_formed sys"
  assumes "(r1, r2) ∈ (role_hierarchy sys)⇧*"
  assumes "(p, r1) ∈ permission_assignment sys"
  shows "p ∈ role_permissions_inherited sys r2"
  using assms unfolding role_permissions_inherited_def
  by auto

(* Альтернативное доказательство через индукцию *)
theorem hierarchy_monotonicity_inductive:
  assumes "well_formed sys"
  assumes "acyclic_hierarchy sys" 
  assumes "(r1, r2) ∈ (role_hierarchy sys)⇧*"
  shows "role_permissions_inherited sys r1 ⊆ role_permissions_inherited sys r2"
  using assms(3)
proof (induction rule: rtrancl_induct)
  case base
  (* Базовый случай: r1 = r2 *)
  show "role_permissions_inherited sys r1 ⊆ role_permissions_inherited sys r1"
    by simp
next
  case (step r1 r_mid r2)
  (* Индуктивный шаг: r1 →* r_mid → r2 *)
  assume IH: "role_permissions_inherited sys r1 ⊆ role_permissions_inherited sys r_mid"
  assume step_rel: "(r_mid, r2) ∈ role_hierarchy sys"
  
  (* Нужно показать: role_permissions_inherited sys r1 ⊆ role_permissions_inherited sys r2 *)
  
  (* Сначала покажем: role_permissions_inherited sys r_mid ⊆ role_permissions_inherited sys r2 *)
  have mid_to_r2: "role_permissions_inherited sys r_mid ⊆ role_permissions_inherited sys r2"
  proof
    fix p
    assume "p ∈ role_permissions_inherited sys r_mid"
    then obtain r' where 
      "(r', r_mid) ∈ (role_hierarchy sys)⇧*" 
      "(p, r') ∈ permission_assignment sys"
      unfolding role_permissions_inherited_def by auto
    
    (* Используем транзитивность: r' →* r_mid → r2 *)
    from step_rel have "(r_mid, r2) ∈ (role_hierarchy sys)⇧*" by simp
    with `(r', r_mid) ∈ (role_hierarchy sys)⇧*` 
    have "(r', r2) ∈ (role_hierarchy sys)⇧*" by (rule rtrancl_trans)
    
    with `(p, r') ∈ permission_assignment sys`
    show "p ∈ role_permissions_inherited sys r2"
      unfolding role_permissions_inherited_def by auto
  qed
  
  (* Комбинируем с индуктивной гипотезой *)
  from IH mid_to_r2 show "role_permissions_inherited sys r1 ⊆ role_permissions_inherited sys r2"
    by (rule subset_trans)
qed

end