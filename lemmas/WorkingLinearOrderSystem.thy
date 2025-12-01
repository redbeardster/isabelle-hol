theory WorkingLinearOrderSystem
imports Main
begin

(* 1. Определяем тип состояний *)
datatype linear_state = 
    S0 | S1 | S2 | S3 | S4 | S5 | DONE

(* 2. Вручную определяем порядок (без deriving!) *)
instantiation linear_state :: linorder
begin

fun less_linear_state where
  "S0 < S1 \<longleftrightarrow> True"
| "S0 < S2 \<longleftrightarrow> True"
| "S0 < S3 \<longleftrightarrow> True"  
| "S0 < S4 \<longleftrightarrow> True"
| "S0 < S5 \<longleftrightarrow> True"
| "S0 < DONE \<longleftrightarrow> True"
| "S1 < S2 \<longleftrightarrow> True"
| "S1 < S3 \<longleftrightarrow> True"
| "S1 < S4 \<longleftrightarrow> True"
| "S1 < S5 \<longleftrightarrow> True"
| "S1 < DONE \<longleftrightarrow> True"
| "S2 < S3 \<longleftrightarrow> True"
| "S2 < S4 \<longleftrightarrow> True"
| "S2 < S5 \<longleftrightarrow> True"
| "S2 < DONE \<longleftrightarrow> True"
| "S3 < S4 \<longleftrightarrow> True"
| "S3 < S5 \<longleftrightarrow> True"
| "S3 < DONE \<longleftrightarrow> True"
| "S4 < S5 \<longleftrightarrow> True"
| "S4 < DONE \<longleftrightarrow> True"
| "S5 < DONE \<longleftrightarrow> True"
| "_ < _ \<longleftrightarrow> False"

definition "less_eq_linear_state (x :: linear_state) y \<longleftrightarrow> x < y \<or> x = y"

instance
proof
  fix x y z :: linear_state
  show "x \<le> x" by (simp add: less_eq_linear_state_def)
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z" 
    by (auto simp add: less_eq_linear_state_def)
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    by (auto simp add: less_eq_linear_state_def)
  show "x \<le> y \<or> y \<le> x"
    by (cases x; cases y; auto simp: less_eq_linear_state_def)
  show "x < y \<longleftrightarrow> x \<le> y \<and> \<not> y \<le> x"
    by (auto simp add: less_eq_linear_state_def)
qed

end

(* 3. Определяем locale *)
locale linear_order_system =
  fixes transitions :: "('state \<times> 'state) set"
    and initial :: "'state set"
  assumes
    order_preserving: "\<forall>s s'. (s, s') \<in> transitions \<longrightarrow> s < s'"
begin

(* Теоремы внутри locale *)
lemma no_cycles: "\<not> (\<exists>s. (s, s) \<in> transitions\<^sup>+)"
  using order_preserving
  by (metis less_irrefl tranclD)

lemma reachable_monotonic:
  assumes "(s, s') \<in> transitions\<^sup>*"
  shows "s \<le> s'"
  using assms
  by (induction rule: rtrancl_induct)
     (auto simp: order_preserving less_eq_linear_state_def)

end

(* 4. Instantiate для нашего типа *)
definition linear_transitions :: "(linear_state \<times> linear_state) set" where
  "linear_transitions = {(S0, S1), (S1, S2), (S2, S3), (S3, S4), (S4, S5), (S5, DONE)}"

definition linear_initial :: "linear_state set" where
  "linear_initial = {S0}"

interpretation linear_system: linear_order_system 
  linear_transitions linear_initial
proof
  show "\<forall>s s'. (s, s') \<in> linear_transitions \<longrightarrow> s < s'"
    unfolding linear_transitions_def
    by auto
qed

(* 5. Используем теоремы из locale *)
lemma "linear_system.no_cycles" 
  by (rule linear_system.no_cycles)

lemma "S0 \<le> DONE"
  using linear_system.reachable_monotonic
  by (metis linear_initial_def linear_transitions_def rtrancl.simps singletonI)

end