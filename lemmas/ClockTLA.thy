theory ClockTLA
imports Main "HOL-Library.LaTeXsugar"
begin

consts c :: nat
 
axiomatization where 
  c_range: "c \<ge> 1 \<and> c \<le> 12"

record clock_state = 
  hr :: nat

definition Init :: "clock_state \<Rightarrow> bool" where
  "Init s \<equiv> hr s = c"

definition add1 :: "nat \<Rightarrow> nat" where
  "add1 p = p + 1"

definition Inc :: "clock_state \<Rightarrow> clock_state \<Rightarrow> bool" where
  "Inc s s' \<equiv> hr s < 12 \<and> hr s' = add1 (hr s)"
  
definition Reset :: "clock_state \<Rightarrow> clock_state \<Rightarrow> bool" where
  "Reset s s' \<equiv> hr s = 12 \<and> hr s' = 1"

definition Next :: "clock_state \<Rightarrow> clock_state \<Rightarrow> bool" where
  "Next s s' \<equiv> Inc s s' \<or> Reset s s'"

definition hr_invariant :: "clock_state \<Rightarrow> bool" where
  "hr_invariant s \<equiv> hr s \<ge> 1 \<and> hr s \<le> 12"

lemma safety_property:
  fixes s :: "nat \<Rightarrow> clock_state" 
  assumes initial: "Init (s 0)"   
  assumes transitions: "\<And>i. Next (s i) (s (Suc i))" 
  shows "hr_invariant (s i)"     
proof (induct i)
  case 0
  show ?case 
    using initial c_range 
    by (auto simp: Init_def hr_invariant_def)
next
  case (Suc i)
  have "hr_invariant (s i)" by (rule Suc)
  moreover have "Next (s i) (s (Suc i))" by (rule transitions)
  ultimately show ?case
    by (auto simp: Next_def hr_invariant_def Inc_def Reset_def add1_def)
qed  

lemma safety_property_auto:
  fixes s :: "nat \<Rightarrow> clock_state"
  assumes "Init (s 0)"
  assumes "\<And>i. Next (s i) (s (Suc i))"
  shows "hr_invariant (s i)"
  using assms
proof (induct i)
  case 0
  then show ?case using Init_def hr_invariant_def  using c_range by auto
next
  case (Suc i)
  then show ?case 
    using Next_def Inc_def Reset_def add1_def hr_invariant_def  using safety_property by blast
qed

lemma Init_establishes_invariant:
  assumes "Init s"
  shows "hr_invariant s"
  using assms c_range
  by (auto simp: Init_def hr_invariant_def)

lemma Inc_preserves_invariant:
  assumes "hr_invariant s"
  assumes "Inc s s'"
  shows "hr_invariant s'"
proof -
  from assms(2) have "hr s < 12" and "hr s' = hr s + 1"
    by (auto simp: Inc_def add1_def)
  with assms(1) show ?thesis
    by (auto simp: hr_invariant_def)
qed

lemma Reset_preserves_invariant:
  assumes "hr_invariant s" 
  assumes "Reset s s'"
  shows "hr_invariant s'"
  using assms
  by (auto simp: Reset_def hr_invariant_def)

theorem Next_preserves_invariant:
  assumes "hr_invariant s"
  assumes "Next s s'"
  shows "hr_invariant s'"
  using assms Inc_preserves_invariant Reset_preserves_invariant  Next_def
  by blast

definition always_invariant :: "(nat \<Rightarrow> clock_state) \<Rightarrow> bool" where
  "always_invariant path \<equiv> \<forall>i. hr_invariant (path i)"

theorem system_safety:
  assumes initial: "Init (path 0)"
  assumes transitions: "\<And>i. Next (path i) (path (Suc i))"
  shows "always_invariant path"
proof -
  fix i
  have "hr_invariant (path i)"
  proof (induct i)
    case 0
    then show ?case using initial Init_establishes_invariant by blast
  next
    case (Suc i)
    then show ?case 
      using transitions Next_preserves_invariant by auto
  qed
  then show ?thesis using safety_property  by (simp add: always_invariant_def initial transitions)  
qed

definition can_progress :: "clock_state \<Rightarrow> bool" where
  "can_progress s \<equiv> \<exists>s'. Next s s'"

theorem always_can_progress:
  assumes "hr_invariant s"
  shows "can_progress s"
proof -
  have "hr s \<le> 12" using assms by (simp add: hr_invariant_def)
  then consider 
      (inc) "hr s < 12" 
    | (reset) "hr s = 12"
    by linarith
  then show ?thesis
  proof cases
    case inc
    then show ?thesis 
      using can_progress_def Next_def Inc_def add1_def by (meson select_convs(1))
  next
    case reset
    then show ?thesis  using can_progress_def Next_def Reset_def 
    by (meson select_convs(1))
  qed
qed

definition example_trace :: "nat \<Rightarrow> clock_state" where
  "example_trace n = \<lparr> hr = ((c + n - 1) mod 12) + 1 \<rparr>"

(* lemma example_trace_correct_auto:
  assumes "c \<ge> 1" "c \<le> 12"
  shows "Init (example_trace 0)"
    and "\<And>i. Next (example_trace i) (example_trace (Suc i))"
proof -
  show "Init (example_trace 0)"
    using Init_def example_trace_def  using c_range by force
  fix i
  show "Next (example_trace i) (example_trace (Suc i))"
    unfolding Next_def Inc_def Reset_def add1_def example_trace_def
    using simp: mod_Suc_eq  by (smt (verit) Nat.add_diff_assoc2 One_nat_def add_Suc_right add_diff_cancel_left' assms(1) le_neq_implies_less less_eq_Suc_le mod_Suc_eq mod_if mod_less_divisor nat_arith.rule0 select_convs(1)
      zero_less_numeral)
qed *)

definition eventually_reset :: "(nat \<Rightarrow> clock_state) \<Rightarrow> bool" where
  "eventually_reset path \<equiv> \<exists>i. hr (path i) = 1"

lemma liveness_property:
  assumes "hr (path i) = 12"
  assumes "always_invariant path"
  assumes "\<And>i. Next (path i) (path (Suc i))"
  shows "\<exists>j>i. hr (path j) = 1"
  by (metis Inc_def Next_def Reset_def assms(1,3) lessI less_irrefl_nat)


datatype Action = Inc | Reset

lemma example:
  fixes action :: Action
  shows "P action"
proof (cases action)  
  case Inc
  then show ?thesis  sorry
next
  case Reset  
  then show ?thesis sorry
qed



end (*end of theory file*)