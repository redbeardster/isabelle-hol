theory Util
  imports Main "HOL-Library.Monad_Syntax"
begin

definition kleisli :: "('b \<Rightarrow> 'b option) \<Rightarrow> ('b \<Rightarrow> 'b option) \<Rightarrow> ('b \<Rightarrow> 'b option)" (infixr "\<Zrres>" 65 ) where
  "f \<Zrres> g \<equiv> \<lambda>x. (f x >>= (\<lambda>y. g y))"

lemma kleisli_comm_ong:
assumes "x \<Zrres> y = y \<Zrres> x"
shows "z \<Zrres> x \<Zrres> y = z \<Zrres>x \<Zrres> y"
  using assms by (clarsimp simp add: kleisli_def)




end

