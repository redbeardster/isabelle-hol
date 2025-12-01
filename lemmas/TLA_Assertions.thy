theory TLA_Assertions
imports Main
begin

section \<open>TLA+ Concepts and Assertions in Isabelle/HOL\<close>

subsection \<open>Basic TLA+ Types and Operators\<close>

type_synonym 'state behavior = "nat \<Rightarrow> 'state"

text \<open>Corrected TLA+ always operator with proper syntax \<close>
definition always :: "('state behavior \<Rightarrow> bool) \<Rightarrow> 'state behavior \<Rightarrow> bool" where
  "always P \<omega> \<equiv> \<forall>n. P (\<lambda>k. \<omega> (n + k))"

syntax "_always" :: "pttrn \<Rightarrow> 'a behavior \<Rightarrow> bool \<Rightarrow> bool" ("\<box>\<langle>_\<rangle> _" [0, 0] 100)
translations "\<box>\<langle>\<omega>\<rangle> P" \<rightharpoonup> "CONST always (\<lambda>\<omega>. P) \<omega>"

text \<open>TLA+ eventually operator \<close>  
definition eventually :: "('state behavior \<Rightarrow> bool) \<Rightarrow> 'state behavior \<Rightarrow> bool" ("\<diamond>\<langle>_\<rangle> _" [0, 0] 100) where
  "\<diamond> P \<omega> \<equiv> \<exists>n. P (\<lambda>k. \<omega> (n + k))"

syntax "_eventually" :: "pttrn \<Rightarrow> 'a behavior \<Rightarrow> bool \<Rightarrow> bool" ("\<diamond>\<langle>_\<rangle> _" [0, 0] 100)
translations "\<diamond>\<langle>\<omega>\<rangle> P" \<rightharpoonup> "CONST eventually (\<lambda>\<omega>. P) \<omega>"

text \<open>Alternative approach with explicit suffix \<close>
definition suffix :: "nat \<Rightarrow> 'state behavior \<Rightarrow> 'state behavior" where
  "suffix n \<omega> = (\<lambda>k. \<omega> (n + k))"

lemma always_alt: "\<box> P \<omega> = (\<forall>n. P (suffix n \<omega>))"
  unfolding always_def suffix_def by simp

lemma eventually_alt: "\<diamond> P \<omega> = (\<exists>n. P (suffix n \<omega>))"
  unfolding eventually_def suffix_def by simp

text \<open>TLA+ leads-to operator \<close>
definition leads_to :: 
  "('state behavior \<Rightarrow> bool) \<Rightarrow> ('state behavior \<Rightarrow> bool) \<Rightarrow> 'state behavior \<Rightarrow> bool" 
where
  "(P \<leadsto> Q) \<omega> \<equiv> \<box> (\<lambda>\<omega>'. P \<omega>' \<longrightarrow> \<diamond> Q \<omega>') \<omega>"

text \<open>TLA+ enabled operator \<close>
definition enabled :: "('state \<Rightarrow> 'state \<Rightarrow> bool) \<Rightarrow> 'state \<Rightarrow> bool" where
  "enabled A s \<equiv> \<exists>s'. A s s'"

subsection \<open>TLA+ Action Formulas\<close>

type_synonym 'state predicate = "'state \<Rightarrow> bool"
type_synonym 'state action = "'state \<Rightarrow> 'state \<Rightarrow> bool"

text \<open>Conjunction of actions \<close>
definition conj_action :: "'state action \<Rightarrow> 'state action \<Rightarrow> 'state action" where
  "A \<and>\<and> B = (\<lambda>s s'. A s s' \<and> B s s')"

text \<open>Disjunction of actions \<close>
definition disj_action :: "'state action \<Rightarrow> 'state action \<Rightarrow> 'state action" where  
  "A \<or>\<or> B = (\<lambda>s s'. A s s' \<or> B s s')"

text \<open>Stuttering action (no change) \<close>
definition stutter :: "'state action" where
  "stutter = (\<lambda>s s'. s' = s)"

subsection \<open>TLA+ Temporal Formulas\<close>

text \<open>Box and diamond for actions \<close>
definition Box_act :: "'state action \<Rightarrow> 'state behavior \<Rightarrow> bool" where
  "\<box>\<langle>A\<rangle> \<omega> \<equiv> \<forall>n. A (\<omega> n) (\<omega> (Suc n))"

definition Diamond_act :: "'state action \<Rightarrow> 'state behavior \<Rightarrow> bool" where  
  "\<diamond>\<langle>A\<rangle> \<omega> \<equiv> \<exists>n. A (\<omega> n) (\<omega> (Suc n))"

subsection \<open>TLA+ Specification Patterns\<close>

definition TLA_spec :: 
  "'state predicate \<Rightarrow> 'state action \<Rightarrow> 'state predicate set \<Rightarrow> 'state behavior \<Rightarrow> bool" 
where
  "TLA_spec Init Next L \<omega> \<equiv> 
    Init (\<omega> 0) \<and> 
    \<box>\<langle>Next \<or>\<or> stutter\<rangle> \<omega> \<and>
    (\<forall>\<phi> \<in> L. \<phi> \<omega>)"

subsection \<open>Basic Temporal Logic Theorems\<close>

theorem always_mono: 
  assumes "\<forall>\<omega>. P \<omega> \<longrightarrow> Q \<omega>"
  shows "\<box> P \<omega> \<longrightarrow> \<box> Q \<omega>"
  using assms unfolding always_def by auto

theorem eventually_mono:
  assumes "\<forall>\<omega>. P \<omega> \<longrightarrow> Q \<omega>" 
  shows "\<diamond> P \<omega> \<longrightarrow> \<diamond> Q \<omega>"
  using assms unfolding eventually_def by auto

theorem always_eventually_duality: 
  "\<box> P \<omega> \<longleftrightarrow> \<not> \<diamond> (\<lambda>\<omega>. \<not> P \<omega>) \<omega>"
  unfolding always_def eventually_def by auto

theorem eventually_always_duality: 
  "\<diamond> P \<omega> \<longleftrightarrow> \<not> \<box> (\<lambda>\<omega>. \<not> P \<omega>) \<omega>"  
  unfolding always_def eventually_def by auto

text \<open>Distribution laws \<close>
theorem always_conj: 
  "\<box> (\<lambda>\<omega>. P \<omega> \<and> Q \<omega>) \<omega> \<longleftrightarrow> \<box> P \<omega> \<and> \<box> Q \<omega>"
  unfolding always_def by auto

theorem eventually_disj: 
  "\<diamond> (\<lambda>\<omega>. P \<omega> \<or> Q \<omega>) \<omega> \<longleftrightarrow> \<diamond> P \<omega> \<or> \<diamond> Q \<omega>"
  unfolding eventually_def by auto

subsection \<open>Simple Example\<close>

definition increasing :: "(nat \<Rightarrow> nat) \<Rightarrow> bool" where
  "increasing f \<equiv> \<forall>n. f n \<le> f (Suc n)"

definition always_increasing :: "(nat behavior) \<Rightarrow> bool" where
  "always_increasing \<omega> \<equiv> \<box> (\<lambda>\<omega>'. increasing (\<lambda>\<omega>. \<omega> 0)) \<omega>"

lemma example_always:
  assumes "always_increasing \<omega>"
  shows "\<forall>n k. \<omega> n \<le> \<omega> (n + k)"
  using assms 
  unfolding always_increasing_def always_def increasing_def suffix_def
  by (metis add.commute le_add1)

end