theory ExampleTLA
  imports  "HOL-TLA.TLA"
begin

(* Определение переменной для сохранения состояния двух процессов *)
typedecl state

consts
  state1 :: "state \<Rightarrow> nat"
  state2 :: "state \<Rightarrow> nat"

(* Начальное состояние *)
definition InitState :: "state \<Rightarrow> bool" where
  "InitState s \<longleftrightarrow> (state1 s = 0 \<and> state2 s = 0)"

(* Определение переходов *)
definition NextState :: "state \<Rightarrow> state \<Rightarrow> bool" where
  "NextState s s' \<longleftrightarrow> (state1 s' = state1 s + 1 \<and> state2 s' = state2 s) \<or> 
                     (state1 s' = state1 s \<and> state2 s' = state2 s + 1) \<or> 
                     (state1 s' = state1 s + 1 \<and> state2 s' = state2 s + 1)"

(* Спецификация системы *)
definition Spec :: "state \<Rightarrow> bool" where
  "Spec s \<longleftrightarrow> InitState s \<and> (\<forall> s'. NextState s s' \<longrightarrow> Spec s')"

(* Для подтверждения корректности, добавьте лемму *)
lemma "\<exists> s. Spec s"
  using Spec_def InitState_def NextState_def by auto



end