theory Corrected_Hierarchy_Lemma
  imports Main
begin

(* Исправленная версия леммы hierarchy_monotonicity *)

(* Сначала нужно правильно определить семантику иерархии *)
(* В стандартной RBAC: если (junior, senior) ∈ role_hierarchy, 
   то senior наследует все разрешения junior *)

datatype role = Role nat
datatype permission = Permission nat

record simple_rbac =
  roles :: "role set"
  permissions :: "permission set"
  permission_assignment :: "(permission × role) set"
  role_hierarchy :: "(role × role) set"  (* (junior, senior) *)

definition role_permissions :: "simple_rbac ⇒ role ⇒ permission set" where
"role_permissions sys r = {p. (p, r) ∈ permission_assignment sys}"

definition inherited_permissions :: "simple_rbac ⇒ role ⇒ permission set" where
"inherited_permissions sys r = 
  ⋃{role_permissions sys r' | r'. (r', r) ∈ (role_hierarchy sys)⇧*}"

definition well_formed_simple :: "simple_rbac ⇒ bool" where
"well_formed_simple sys ≡
  (∀p r. (p, r) ∈ permission_assignment sys ⟹ p ∈ permissions sys ∧ r ∈ roles sys) ∧
  (∀r1 r2. (r1, r2) ∈ role_hierarchy sys ⟹ r1 ∈ roles sys ∧ r2 ∈ roles sys)"

definition acyclic_simple :: "simple_rbac ⇒ bool" where
"acyclic_simple sys ≡ acyclic (role_hierarchy sys)"

(* ПРАВИЛЬНАЯ лемма о монотонности иерархии *)
theorem hierarchy_monotonicity_correct:
  assumes wf: "well_formed_simple sys"
  assumes acyc: "acyclic_simple sys"
  assumes hier: "(r1, r2) ∈ (role_hierarchy sys)⇧*"
  shows "inherited_permissions sys r1 ⊆ inherited_permissions sys r2"
proof
  fix p
  assume "p ∈ inherited_permissions sys r1"
  
  (* Разворачиваем определение inherited_permissions *)
  then obtain r' where 
    r'_in_r1: "(r', r1) ∈ (role_hierarchy sys)⇧*" and
    p_in_r': "p ∈ role_permissions sys r'"
    unfolding inherited_permissions_def by auto
  
  (* Используем транзитивность: r' →* r1 →* r2 *)
  from r'_in_r1 hier have "(r', r2) ∈ (role_hierarchy sys)⇧*"
    by (rule rtrancl_trans)
  
  (* Следовательно, p ∈ inherited_permissions sys r2 *)
  with p_in_r' show "p ∈ inherited_permissions sys r2"
    unfolding inherited_permissions_def by auto
qed

(* Альтернативное доказательство через индукцию по транзитивному замыканию *)
theorem hierarchy_monotonicity_inductive:
  assumes "well_formed_simple sys"
  assumes "acyclic_simple sys"
  shows "∀r1 r2. (r1, r2) ∈ (role_hierarchy sys)⇧* ⟹ 
         inherited_permissions sys r1 ⊆ inherited_permissions sys r2"
proof (intro allI impI)
  fix r1 r2
  assume "(r1, r2) ∈ (role_hierarchy sys)⇧*"
  thus "inherited_permissions sys r1 ⊆ inherited_permissions sys r2"
  proof (induction rule: rtrancl_induct)
    case base
    (* r1 = r2 *)
    show "inherited_permissions sys r1 ⊆ inherited_permissions sys r1" by simp
  next
    case (step r1 r_mid r2)
    (* r1 →* r_mid → r2 *)
    assume IH: "inherited_permissions sys r1 ⊆ inherited_permissions sys r_mid"
    assume step_rel: "(r_mid, r2) ∈ role_hierarchy sys"
    
    (* Покажем: inherited_permissions sys r_mid ⊆ inherited_permissions sys r2 *)
    have "inherited_permissions sys r_mid ⊆ inherited_permissions sys r2"
    proof
      fix p
      assume "p ∈ inherited_permissions sys r_mid"
      then obtain r' where
        "(r', r_mid) ∈ (role_hierarchy sys)⇧*"
        "p ∈ role_permissions sys r'"
        unfolding inherited_permissions_def by auto
      
      (* r' →* r_mid → r2, значит r' →* r2 *)
      from step_rel have "(r_mid, r2) ∈ (role_hierarchy sys)⇧*" by simp
      with `(r', r_mid) ∈ (role_hierarchy sys)⇧*`
      have "(r', r2) ∈ (role_hierarchy sys)⇧*" by (rule rtrancl_trans)
      
      with `p ∈ role_permissions sys r'`
      show "p ∈ inherited_permissions sys r2"
        unfolding inherited_permissions_def by auto
    qed
    
    (* Комбинируем с IH *)
    with IH show "inherited_permissions sys r1 ⊆ inherited_permissions sys r2"
      by (rule subset_trans)
  qed
qed

(* Вспомогательные леммы *)

lemma direct_permissions_inherited:
  "role_permissions sys r ⊆ inherited_permissions sys r"
  unfolding inherited_permissions_def role_permissions_def
  using rtrancl_refl by auto

lemma hierarchy_step_monotonic:
  assumes "(r1, r2) ∈ role_hierarchy sys"
  shows "inherited_permissions sys r1 ⊆ inherited_permissions sys r2"
proof
  fix p
  assume "p ∈ inherited_permissions sys r1"
  then obtain r' where
    "(r', r1) ∈ (role_hierarchy sys)⇧*"
    "p ∈ role_permissions sys r'"
    unfolding inherited_permissions_def by auto
  
  from assms have "(r1, r2) ∈ (role_hierarchy sys)⇧*" by simp
  with `(r', r1) ∈ (role_hierarchy sys)⇧*`
  have "(r', r2) ∈ (role_hierarchy sys)⇧*" by (rule rtrancl_trans)
  
  with `p ∈ role_permissions sys r'`
  show "p ∈ inherited_permissions sys r2"
    unfolding inherited_permissions_def by auto
qed

end