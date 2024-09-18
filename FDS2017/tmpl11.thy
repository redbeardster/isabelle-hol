(*<*)
theory tmpl11
imports 
    "../../../Public/Thys/Heap_Prelim"    
begin
(*>*)  
text {* \ExerciseSheet{11}{7.~7.~2017} *}

text \<open>
  \Exercise{Sparse Binary Numbers}

  Implement operations carry, inc, and add on sparse binary numbers,
  analogously to the operations link, ins, and meld on binomial heaps.

  Show that the operations have logarithmic worst-case complexity. 
\<close>  

type_synonym rank = nat
type_synonym snat = "rank list"

abbreviation invar :: "snat \<Rightarrow> bool" where "invar s \<equiv> strictly_ascending s"  
definition \<alpha> :: "snat \<Rightarrow> nat" where "\<alpha> s = (\<Sum>i\<leftarrow>s. 2^i)"
  
    
fun carry :: "rank \<Rightarrow> snat \<Rightarrow> snat" 
  where
  "carry r [] = [r]"
  
lemma carry_invar[simp]: True oops
    
lemma carry_\<alpha>: True oops
    
definition inc :: "snat \<Rightarrow> snat" 
  where "inc rs = undefined"    
    
lemma inc_invar[simp]: "invar rs \<Longrightarrow> invar (inc rs)" 
oops
  
lemma inc_\<alpha>[simp]: "invar rs \<Longrightarrow> \<alpha> (inc rs) = Suc (\<alpha> rs)"
  oops
  
fun add :: "snat \<Rightarrow> snat \<Rightarrow> snat" 
  where
  "add rs [] = rs"
    
    
lemma add_invar[simp]:
  assumes "invar rs\<^sub>1"
  assumes "invar rs\<^sub>2"
  shows "invar (add rs\<^sub>1 rs\<^sub>2)"  
    oops

lemma add_\<alpha>[simp]:
  assumes "invar rs\<^sub>1"
  assumes "invar rs\<^sub>2"
  shows "\<alpha> (add rs\<^sub>1 rs\<^sub>2) = \<alpha> rs\<^sub>1 + \<alpha> rs\<^sub>2"
    oops
    
lemma size_snat:  
  assumes "invar rs"
  shows "2^length rs \<le> \<alpha> rs + 1"
    oops
  
fun t_carry :: "rank \<Rightarrow> snat \<Rightarrow> nat" 
  where
  "t_carry r [] = 1"
  
definition t_inc :: "snat \<Rightarrow> nat"
  where "t_inc = undefined"
  
lemma t_inc_bound: 
  assumes "invar rs"
  shows "t_inc rs \<le> log 2 (\<alpha> rs + 1) + 1"  
    oops
  
fun t_add :: "snat \<Rightarrow> snat \<Rightarrow> nat" 
  where
  "t_add rs _ = undefined"
    
lemma t_add_bound:
  fixes rs\<^sub>1 rs\<^sub>2
  defines "n\<^sub>1 \<equiv> \<alpha> rs\<^sub>1"    
  defines "n\<^sub>2 \<equiv> \<alpha> rs\<^sub>2"
  assumes INVARS: "invar rs\<^sub>1" "invar rs\<^sub>2"
  shows "t_add rs\<^sub>1 rs\<^sub>2 \<le> 4*log 2 (n\<^sub>1 + n\<^sub>2 + 1) + 2"
  oops
    
  
text \<open>
  \NumHomework{Largest Representable Number}{14.~7.~2017}

  Assume we use numbers \<open>{0..<K}\<close> to represent the ranks in a sparse binary number.
  Define \<open>max_snat K\<close> to be the largest representable sparse binary number (its value should be \<open>2\<^sup>K-1\<close>), and
  prove that your definition is correct.
\<close>  

definition max_snat :: "nat \<Rightarrow> snat" 
  where "max_snat K = undefined"
  
lemma "invar (max_snat K)" sorry
  
lemma \<alpha>_max_snat: "\<alpha> (max_snat K) = 2^K - 1" sorry

lemma max_snat_bounded: "set (max_snat K) \<subseteq> {0..<K}" sorry
  
lemma max_snat_max:
  assumes "invar rs"
  assumes "set rs \<subseteq> {0..<K}"  
  shows "\<alpha> rs \<le> \<alpha> (max_snat K)"
  sorry  
  
text \<open>
  \NumHomework{Be Original!}{28.~7.~2017}

  Develop a nice Isabelle formalization yourself!

  \<^item> This homework is for 3 weeks, and will yield 15 points + 15 bonus points.
  \<^item> You may develop a formalization from all areas, not only functional data structures.
  \<^item> Set yourself a time frame and some intermediate/minimal goals. 
    Your formalization needs not be universal and complete after 3 weeks.
  \<^item> You are welcome to discuss the realizability of your project with the tutor!
  \<^item> In case you should need inspiration to find a project: Sparse matrices, skew binary numbers, 
    arbitrary precision arithmetic (on lists of bits), interval data structures (e.g. interval lists), 
    spatial data structures (quad-trees, oct-trees), Fibonacci heaps, etc.
\<close>  
    
(*<*)
end
(*>*)
