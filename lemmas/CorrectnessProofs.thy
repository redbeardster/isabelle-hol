theory CorrectnessProofs
imports Main
begin

(* Спецификация стека *)
type_synonym 'a Stack = "'a list"
type_synonym User = string

definition empty_stack :: "'a Stack" where
  "empty_stack = []"

definition push :: "'a \<Rightarrow> 'a Stack \<Rightarrow> 'a Stack" where
  "push x s = x # s"

definition pop :: "'a Stack \<Rightarrow> ('a \<times> 'a Stack) option" where
  "pop s = (case s of [] \<Rightarrow> None | x # xs \<Rightarrow> Some (x, xs))"

(* Доказательство корректности *)
lemma push_pop_identity:
  "\<forall>s x. pop (push x s) = Some (x, s)"
  unfolding push_def pop_def
  by simp

lemma empty_stack_property:
  "pop empty_stack = None"
  unfolding empty_stack_def pop_def
  by simp

(* Более сложное доказательство инварианта *)
definition stack_invariant :: "'a Stack \<Rightarrow> bool" where
  "stack_invariant s \<equiv> True"  (* упрощенно *)

lemma operations_preserve_invariant:
  assumes "stack_invariant s"
  shows "stack_invariant (push x s) \<and>
         (case pop s of None \<Rightarrow> True | Some (_, s') \<Rightarrow> stack_invariant s')"
  using assms
  unfolding stack_invariant_def push_def pop_def
  by (simp add: option.case_eq_if)

(* Доказательство для системы с состоянием *)
record SystemState =
  users :: "User set"
  active_sessions :: "User set"

definition login_operation :: "User \<Rightarrow> SystemState \<Rightarrow> SystemState" where
  "login_operation user state =
    state\<lparr>active_sessions := active_sessions state \<union> {user}\<rparr>"

lemma login_preserves_users:
  "users (login_operation user state) = users state"
  unfolding login_operation_def
  by simp

end