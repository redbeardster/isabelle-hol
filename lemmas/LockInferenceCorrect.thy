theory LockInferenceCorrect
  imports Main
begin

subsection \<open>Базовые определения\<close>

type_synonym var = string
type_synonym val = int
type_synonym lock = string
type_synonym state = "var \<Rightarrow> val"

datatype expr = 
    Var var
  | Const val
  | Add expr expr

datatype stmt =
    Assign var expr
  | Seq stmt stmt
  | Atomic "lock set" stmt
  | Skip

subsection \<open>Семантика программ\<close>

inductive exec :: "stmt \<Rightarrow> state \<Rightarrow> lock set \<Rightarrow> state \<Rightarrow> lock set \<Rightarrow> bool" where
  Assign: "exec (Assign x e) s L s' L'"
  if "s' = s(x := eval e s)" and "L' = L"
  
| Seq: "exec (Seq s1 s2) s L s'' L''"
  if "exec s1 s L s' L'" and "exec s2 s' L' s'' L''"
  
| Atomic: "exec (Atomic locks s) s L s' L'"
  if "exec s s (L \<union> locks) s' L'" and "disjoint L locks"
  
| Skip: "exec Skip s L s L"

inductive_cases [elim!]: "exec Skip s L t M" "exec (Assign x e) s L t M"

subsection \<open>Анализ переменных и конфликтов\<close>

primrec vars_expr :: "expr \<Rightarrow> var set" where
  "vars_expr (Var x) = {x}"
| "vars_expr (Const _) = {}"
| "vars_expr (Add e1 e2) = vars_expr e1 \<union> vars_expr e2"

primrec shared_vars :: "stmt \<Rightarrow> var set" where
  "shared_vars (Assign x e) = {x} \<union> vars_expr e"
| "shared_vars (Seq s1 s2) = shared_vars s1 \<union> shared_vars s2"
| "shared_vars (Atomic _ s) = shared_vars s"
| "shared_vars Skip = {}"

definition conflicts :: "stmt \<Rightarrow> (var \<times> var) set" where
  "conflicts s = {(x,y) | x y. x \<in> shared_vars s \<and> y \<in> shared_vars s \<and> x \<noteq> y}"

subsection \<open>Алгоритм вывода блокировок\<close>

definition minimal_clique_cover :: "(var \<times> var) set \<Rightarrow> (var \<Rightarrow> lock set)" where
  "minimal_clique_cover E = (
    let all_vars = \<Union> {{x,y} | (x,y) \<in> E};
        locks = if all_vars = {} then {} else {''lock''}
    in (\<lambda>x. if x \<in> all_vars then locks else {})
  )"

primrec infer_locks :: "stmt \<Rightarrow> stmt" where
  "infer_locks (Assign x e) = (
    let L = minimal_clique_cover (conflicts (Assign x e))
    in Atomic (L x \<union> (\<Union>v \<in> vars_expr e. L v)) (Assign x e))"
| "infer_locks (Seq s1 s2) = Seq (infer_locks s1) (infer_locks s2)"
| "infer_locks (Atomic L s) = Atomic L (infer_locks s)"
| "infer_locks Skip = Skip"

subsection \<open>Корректность блокировок\<close>

definition well_locked :: "stmt \<Rightarrow> bool" where
  "well_locked s \<equiv> \<forall>x \<in> shared_vars s. \<forall>p. access_at p s x \<longrightarrow> 
    (\<exists>L. atomic_at p s \<and> L x \<subseteq> locks_at p s)"

theorem lock_inference_correct:
  "well_locked (infer_locks s)"
proof (induct s)
  case (Assign x e)
  let ?L = "minimal_clique_cover (conflicts (Assign x e))"
  let ?locks = "?L x \<union> (\<Union>v \<in> vars_expr e. ?L v)"
  have 1: "x \<in> shared_vars (Assign x e)" by simp
  have 2: "vars_expr e \<subseteq> shared_vars (Assign x e)" by auto
  show ?case
    unfolding well_locked_def
  proof (intro allI impI)
    fix y p
    assume "y \<in> shared_vars (infer_locks (Assign x e))"
       and "access_at p (infer_locks (Assign x e)) y"
    then consider
        (x_access) "y = x" 
      | (e_access) "y \<in> vars_expr e"
      using \<open>y \<in> shared_vars (infer_locks (Assign x e))\<close> by auto
    then show "\<exists>L. atomic_at p (infer_locks (Assign x e)) \<and> 
                  ?L y \<subseteq> locks_at p (infer_locks (Assign x e))"
    proof cases
      case x_access
      have "atomic_at () (infer_locks (Assign x e))"
        by (simp add: Atomic_atomic_at)
      moreover have "?L x \<subseteq> ?locks"
        by auto
      ultimately show ?thesis using x_access by blast
    next
      case e_access
      have "atomic_at () (infer_locks (Assign x e))"
        by (simp add: Atomic_atomic_at)
      moreover have "?L y \<subseteq> ?locks"
        using e_access by auto
      ultimately show ?thesis by blast
    qed
  qed
next
  case (Seq s1 s2)
  then show ?case
    unfolding well_locked_def
    by (auto simp add: access_at_Seq atomic_at_Seq)
next
  case (Atomic L s)
  then show ?case
    unfolding well_locked_def
    by (auto simp add: access_at_Atomic atomic_at_Atomic)
next
  case Skip
  then show ?case
    unfolding well_locked_def by simp
qed

subsection \<open>Отсутствие взаимоблокировок\<close>

definition acyclic_lock_order :: "stmt \<Rightarrow> bool" where
  "acyclic_lock_order s \<equiv> 
    \<forall>s1 s2 L1 L2. exec s s1 L1 s2 L2 \<longrightarrow> 
      (\<forall>l1 l2. l1 \<in> L1 \<and> l2 \<in> L2 \<longrightarrow> l1 \<noteq> l2)"

theorem no_deadlocks:
  "acyclic_lock_order (infer_locks s)"
proof (induct s)
  case (Assign x e)
  let ?L = "minimal_clique_cover (conflicts (Assign x e))"
  show ?case
    unfolding acyclic_lock_order_def
    by (auto intro: exec.intros)
next
  case (Seq s1 s2)
  then show ?case
    unfolding acyclic_lock_order_def
    by (metis exec_SeqE)
next
  case (Atomic L s)
  then show ?case
    unfolding acyclic_lock_order_def
    by (metis Un_iff exec_AtomicE)
next
  case Skip
  then show ?case
    unfolding acyclic_lock_order_def
    by auto
qed

end