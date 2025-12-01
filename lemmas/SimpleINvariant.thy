theory SimpleInvariant
  imports TLA
begin

definition Init :: "nat \<Rightarrow> bool" where
  "Init x \<equiv> x = 0"

definition Next :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "Next x x' \<equiv> x' = x + 1"

definition Invariant :: "nat \<Rightarrow> bool" where
  "Invariant x \<equiv> x \<ge> 0"

lemma inv_always_holds:
  assumes "Init x0"
  assumes "\<And>x x'. Next x x' \<Longrightarrow> Invariant x \<Longrightarrow> Invariant x'"
  shows "Invariant x0"
  using assms
  unfolding Init_def Next_def Invariant_def
  by auto

end