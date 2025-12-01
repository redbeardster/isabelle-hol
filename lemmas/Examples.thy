theory Examples
imports Main
begin
 
type_synonym state = nat
type_synonym behavior = "nat \<Rightarrow> state"

\<comment> \<open>Определения темпоральных операторов \<close>
definition always :: "(behavior \<Rightarrow> bool) \<Rightarrow> behavior \<Rightarrow> bool" where
  "always P \<omega> \<equiv> \<forall>n. P (\<lambda>k. \<omega> (n + k))"

definition eventually :: "(behavior \<Rightarrow> bool) \<Rightarrow> behavior \<Rightarrow> bool" where  
  "eventually P \<omega> \<equiv> \<exists>n. P (\<lambda>k. \<omega> (n + k))"

\<comment> \<open>Определение свойства "все состояния положительны" \<close>
definition always_positive :: "behavior \<Rightarrow> bool" where
  "always_positive \<omega> \<equiv> \<forall>k. \<omega> k > 0"

\<comment> \<open>Исправленный пример 1 \<close>
lemma example1:
  assumes "\<forall>k. \<omega> k > 0"
  shows "always always_positive \<omega>"
  unfolding always_def always_positive_def assms
  using assms by blast
  
\<comment> \<open>Альтернативная запись с using \<close>

lemma example1_alt:
  assumes "\<forall>k. \<omega> k > 0"
  shows "always always_positive \<omega>"
  unfolding always_def always_positive_def
  using assms by auto

\<comment> \<open>Пример 2: Свойство "достигается состояние 10" \<close>
definition reaches_10 :: "behavior \<Rightarrow> bool" where
  "reaches_10 \<omega> \<equiv> \<exists>k. \<omega> k = 10"

lemma example2:
  assumes "\<exists>k. \<omega> k = 10"
  shows "eventually reaches_10 \<omega>"
  unfolding eventually_def reaches_10_def
  using assms by  (metis add_0)

\<comment> \<open>Пример 3: Более сложное темпоральное свойство \<close>

definition eventually_always_positive :: "behavior \<Rightarrow> bool" where
  "eventually_always_positive \<omega> \<equiv> 
    eventually (\<lambda>\<omega>'. always always_positive \<omega>') \<omega>"

lemma example3:
  assumes "\<exists>n. \<forall>k. \<omega> (n + k) > 0"
  shows "eventually_always_positive \<omega>"
  unfolding eventually_always_positive_def eventually_def always_def always_positive_def
  using assms by auto

\<comment> \<open>Пример 4: Всегда в конце концов достигается 10 (не всегда истинно) \<close>
definition always_eventually_10 :: "behavior \<Rightarrow> bool" where
  "always_eventually_10 \<omega> \<equiv> 
    always (\<lambda>\<omega>'. eventually reaches_10 \<omega>') \<omega>"

lemma example4:
  assumes "\<forall>n. \<exists>k. \<omega> (n + k) = 10"
  shows "always_eventually_10 \<omega>"
  unfolding always_eventually_10_def always_def eventually_def reaches_10_def
  using assms  by (metis add_0)

\<comment> \<open>Контрпример для демонстрации \<close>
definition counterexample_behavior :: "behavior" where
  "counterexample_behavior \<equiv> (\<lambda>k. 1)"  \<comment> \<open>Всегда 1, никогда 10 \<close>

lemma counterexample:
  "\<not> always_eventually_10 counterexample_behavior"
  unfolding always_eventually_10_def always_def eventually_def 
            reaches_10_def counterexample_behavior_def
  by auto

\<comment> \<open>Доказательство двойственности операторов \<close>
theorem duality_always_eventually:
  "always P \<omega> \<longleftrightarrow> \<not> (eventually (\<lambda>\<omega>. \<not> P \<omega>) \<omega>)"
  unfolding always_def eventually_def by auto

theorem duality_eventually_always:
  "eventually P \<omega> \<longleftrightarrow> \<not> (always (\<lambda>\<omega>. \<not> P \<omega>) \<omega>)"  
  unfolding always_def eventually_def by auto

\<comment> \<open>Пример с конкретным поведением \<close>
definition concrete_behavior :: "behavior" where
  "concrete_behavior n \<equiv> if n < 5 then n + 1 else 10"

lemma concrete_example:
  "always_eventually_10 concrete_behavior"
  unfolding always_eventually_10_def always_def eventually_def 
            reaches_10_def concrete_behavior_def
  by (metis add_0 not_add_less2) 
 

lemma first_property: "\<forall>x::nat. (x + 1) > x"
proof (intro allI)
  fix x::nat
  show "x + 1 > x" by simp
qed

end