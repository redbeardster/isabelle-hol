theory LTS
imports Main
begin
typedecl state
typedecl label

(* Конкретные состояния и метки *)
consts
  s1 :: state
  s2 :: state
  s3 :: state
  a  :: label
  b  :: label

(* Определяем тип для переходов *)
type_synonym transition = "state \<times> label \<times> state"

(* Задаем LTS как множество переходов *)
definition LTS :: "transition set" where
  "LTS = {(s1, a, s2), (s2, b, s3)}"

(* Пример леммы: проверка, что переход (s1, a, s2) принадлежит LTS *)
lemma example_lemma:
  "(s1, a, s2) \<in> LTS"
  unfolding LTS_def by simp


lemma transition_in_LTS:
  assumes "(s1, a, s2) \<in> LTS"
  shows "\<exists>s1 a s2. (s1, a, s2) \<in> LTS"
  using assms by auto

(* 
definition deterministic :: "transition set \<Rightarrow> bool" where
  "deterministic LTS \<equiv> 
    \<forall>s1 a s2 s2'. (s1, a, s2) \<in> LTS \<and> (s1, a, s2') \<in> LTS \<longrightarrow> s2 = s2'"
 *)

definition deterministic :: "transition set \<Rightarrow> bool" where
  "deterministic T \<equiv> 
    \<forall>s1 a s2 s2'. (s1, a, s2) \<in> T \<and> (s1, a, s2') \<in> T \<longrightarrow> s2 = s2'"

lemma deterministic_LTS:
  assumes "\<forall>s1 a s2 s2'. (s1, a, s2) \<in> LTS \<and> (s1, a, s2') \<in> LTS \<longrightarrow> s2 = s2'"
  shows "deterministic LTS"
  using assms unfolding deterministic_def by auto




end