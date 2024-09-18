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

lemma [simp]:
  "\<alpha> [] = 0"
  "\<alpha> (r#rs) = 2^r + \<alpha> rs"
  unfolding \<alpha>_def by auto  

function (sequential) add :: "rank option \<Rightarrow> snat \<Rightarrow> snat \<Rightarrow> snat" where
  "add (Some rc) [] [] = [rc]"
| "add (Some rc) [] (r2#rest2) = (
      if rc=r2 then add (Some (rc+1)) [] rest2 else rc#r2#rest2)"
| "add None [] r2 = r2"  
| "add c r1 [] = add c [] r1"
| "add None (r1#rest1) (r2#rest2) = (
    if r1=r2 then add (Some (r1+1)) rest1 rest2 
    else if r1<r2 then r1#add None rest1 (r2#rest2)
    else r2#add None (r1#rest1) rest2
  )"  
| "add (Some rc) (r1#rest1) (r2#rest2) = (
    if rc=r1 \<and> r1=r2 then r1#add (Some (rc+1)) rest1 rest2
    else if rc < r1 \<and> rc < r2 then rc#add None (r1#rest1) (r2#rest2)
    else if rc=r1 then add (Some (rc+1)) rest1 (r2#rest2)
    else add (Some (rc+1)) (r1#rest1) rest2
  )"  
by pat_completeness auto  
termination apply size_change done  


lemma add_rank_bound_gen:
  assumes "x' \<in> set (add c s\<^sub>1 s\<^sub>2)"
  assumes "\<forall>x'\<in>set s\<^sub>1. t < x'"
  assumes "\<forall>x'\<in>set s\<^sub>2. t < x'"
  assumes "case c of None \<Rightarrow> True | Some rc \<Rightarrow> t < rc"  
  shows "t < x'"
  using assms  
  apply (induction c s\<^sub>1 s\<^sub>2 rule: add.induct)
  apply (auto split: if_splits)  
  done  
    
lemma add_rank_bound:
  assumes "x' \<in> set (add None s\<^sub>1 s\<^sub>2)"
  assumes "\<forall>x'\<in>set s\<^sub>1. t < x'"
  assumes "\<forall>x'\<in>set s\<^sub>2. t < x'"
  shows "t < x'"
  using add_rank_bound_gen[OF assms] by auto
    

lemma add_rank_bound_carry:
  assumes "x' \<in> set (add (Some c) s\<^sub>1 s\<^sub>2)"
  assumes "\<forall>x'\<in>set s\<^sub>1. t < x'"
  assumes "\<forall>x'\<in>set s\<^sub>2. t < x'"
  assumes "t < c"  
  shows "t < x'"
  using add_rank_bound_gen[OF assms(1-3)] assms(4) by auto
    
    
lemma add_invar:
  assumes "invar s1"  
  assumes "invar s2"
  assumes "\<forall>rc. c=Some rc \<longrightarrow> (\<forall>i\<in>set s1 \<union> set s2. rc\<le>i)"  
  shows "invar (add c s1 s2)"
  using assms  
  apply (induction c s1 s2 rule: add.induct)
  apply simp 
  apply force [] 
  apply simp 
  apply simp 
  apply simp 
  subgoal
    apply clarsimp
    apply (fastforce elim: add_rank_bound)
    done  
  subgoal
    apply (clarsimp split: if_splits) 
    apply safe  
    apply force  
    apply force  
    apply force  
    subgoal
      apply (force elim!: add_rank_bound_carry)
      (*   apply clarsimp
      apply (erule add_rank_bound_carry)  
      apply fastforce+
      oops (fastforce elim: add_rank_bound_carry)*)
    done  
    subgoal by (force elim!: add_rank_bound_carry)
    apply force  
    apply force  
    done    
  done    
      
    
lemma 
  assumes "invar s1" "invar s2"
  assumes "\<forall>rc. c=Some rc \<longrightarrow> (\<forall>i\<in>set s1 \<union> set s2. rc\<le>i)"  
  shows "\<alpha> (add c s1 s2) = \<alpha> s1 + \<alpha> s2 + (case c of None \<Rightarrow> 0 | Some rc \<Rightarrow> 2^rc)"  
  using assms  
  apply (induction c s1 s2 rule: add.induct)
  apply fastforce
  apply fastforce
  apply fastforce
  apply fastforce
  apply fastforce
  apply force
  apply (clarsimp; safe; force)
  done
  
    
(*<*)
end
(*>*)
