(*<*)
theory tut08
  imports 
    Complex_Main 
    "../../Material/Demos/BST_Demo"
    "~~/src/HOL/Library/Multiset" 
    "~~/src/HOL/Data_Structures/Tree23_Set"
begin
(*>*)  
text {* \ExerciseSheet{8}{16.~6.~2017} *}

text \<open>\Exercise{Abstract Set Interface}

  In Isabelle/HOL we can use a so called \<open>locale\<close> to model
  the abstract set interface.

  The locale fixes the operations as parameters, and makes assumptions on them.
\<close>
  
lemma "Set.insert x s = {x} \<union> s" by auto 
  
locale set_interface =
  fixes invar :: "'s \<Rightarrow> bool" and \<alpha> :: "'s \<Rightarrow> 'a set"
  fixes empty :: 's
  assumes empty_invar: "invar empty" and empty_\<alpha>: "\<alpha> empty = {}"
  
  fixes is_in :: "'s \<Rightarrow> 'a \<Rightarrow> bool"  
  assumes is_in_\<alpha>: "invar s \<Longrightarrow> is_in s x \<longleftrightarrow> x \<in> \<alpha> s"
    
  fixes ins :: "'a \<Rightarrow> 's \<Rightarrow> 's"  
  assumes ins_invar: "invar s \<Longrightarrow> invar (ins x s)" 
      and ins_\<alpha>: "invar s \<Longrightarrow> \<alpha> (ins x s) = Set.insert x (\<alpha> s)"
   
  fixes to_list :: "'s \<Rightarrow> 'a list" 
  assumes to_list_\<alpha>: "invar s \<Longrightarrow> set (to_list s) = \<alpha> s"
begin  

text \<open>
    Inside the locale, all the assumptions are available
  \<close>
  thm empty_invar empty_\<alpha> is_in_\<alpha> ins_invar ins_\<alpha> to_list_\<alpha>
    
  text \<open>
    Note that you know nothing about the structure of the fixed parameters 
    or the types @{typ 'a} and @{typ 's}!
  \<close>  

  text \<open>We can define a union function as follows:\<close>  
  definition union :: "'s \<Rightarrow> 's \<Rightarrow> 's" where
    "union A B = fold ins (to_list A) B"
  
  
  text \<open>Show the interface specification for union: \<close>  
  lemma union_invar: 
    assumes "invar A"  
    assumes "invar B"  
    shows "invar (union A B)"
    unfolding union_def
  proof -
    define xs where "xs = to_list A"
    (*obtain xs where xs_def: "xs = to_list A" by auto*)

    from \<open>invar B\<close>    
    have "invar (fold ins xs B)"
      apply (induction xs arbitrary: B)
      apply (auto simp: ins_invar)
      done
    then show "invar (fold ins (to_list A) B)"
      unfolding xs_def by simp
  qed      

  lemma 
    assumes "invar A"  
    assumes "invar B"  
    shows "invar (union A B)"
    unfolding union_def
  proof -
    {
      fix xs
      from \<open>invar B\<close>    
      have "invar (fold ins xs B)"
        apply (induction xs arbitrary: B)
        apply (auto simp: ins_invar)
        done
    } note aux=this      
    
    from \<open>invar B\<close>    
    have "invar (fold ins xs B)" for xs
      apply (induction xs arbitrary: B)
      apply (auto simp: ins_invar)
      done
    then show "invar (fold ins (to_list A) B)"
      by simp
  qed      
    
    
    
  lemma union_\<alpha>:  
    assumes "invar A"  
    assumes "invar B"  
    shows "\<alpha> (union A B) = \<alpha> A \<union> \<alpha> B"
    unfolding union_def
  proof -
    from \<open>invar B\<close>
    have "\<alpha> (fold ins xs B) = set xs \<union> \<alpha> B" for xs
      apply (induction xs arbitrary: B)
      apply (auto simp: ins_\<alpha> ins_invar)
      done
    from this[of "to_list A"]    
    show "\<alpha> (fold ins (to_list A) B) = \<alpha> A \<union> \<alpha> B"
      thm to_list_\<alpha>[OF \<open>invar A\<close>]
      by (simp add: to_list_\<alpha>[OF \<open>invar A\<close>])
  qed  
        
  text \<open>Define an intersection function and show its interface specification\<close>  
    
  definition intersect :: "'s \<Rightarrow> 's \<Rightarrow> 's"
    where
    "intersect A B \<equiv> fold 
      (\<lambda>x res. if is_in B x then ins x res else res) 
      (to_list A) 
      empty"
    
  lemma intersect_invar: 
    assumes "invar A" and "invar B"
    shows "invar (intersect A B)"  
  proof -  
    have "invar (fold 
      (\<lambda>x res. if is_in B x then ins x res else res) xs s)"
      if invs: "invar s" for xs s
      using invs
      apply (induction xs arbitrary: s)
      apply (auto simp: ins_invar) 
      done
    from this[OF empty_invar]    
    show ?thesis        
      unfolding intersect_def .
  qed    
    
  lemma intersect_\<alpha>:
    assumes "invar A"  
    assumes "invar B"  
    shows "\<alpha> (intersect A B) = \<alpha> A \<inter> \<alpha> B"
  proof -
    have "\<alpha> (fold (\<lambda>x res. if is_in B x then ins x res else res) xs s) =
      \<alpha> s \<union> (set xs \<inter> \<alpha> B)" if "invar s" for s xs
      using that
      apply (induction xs arbitrary: s)
      apply (auto simp: ins_\<alpha> ins_invar is_in_\<alpha> \<open>invar B\<close>)  
      done
    from this[OF empty_invar] to_list_\<alpha>[OF \<open>invar A\<close>] show ?thesis    
      unfolding intersect_def
      by (auto simp: empty_\<alpha>)  
  qed    
        
end  

text \<open>Having defined the locale, we can instantiate it for implementations of 
  the set interface. For example for BSTs:\<close>  
                                                
interpretation bst_set: set_interface bst set_tree Tree.Leaf "BST_Demo.isin" "BST_Demo.ins" Tree.inorder
  apply unfold_locales
  text \<open>Show the goals\<close>  
  apply auto
  subgoal 
    by (simp add: set_tree_isin)  
  subgoal 
    by (simp add: set_tree_isin)  
  subgoal 
    by (simp add: bst_ins)  
  subgoal 
    by (simp add: set_tree_ins)  
  subgoal 
    by (simp add: set_tree_ins)  
  subgoal 
    by (simp add: set_tree_ins)  
  done  
text \<open>Now we also have instantiated versions of union and intersection\<close>    
term bst_set.union 
thm bst_set.union_\<alpha> bst_set.union_invar
  
term bst_set.intersect
thm bst_set.intersect_\<alpha> bst_set.intersect_invar
  
text \<open>
  Instantiate the set interface also for:
  \<^item> Distinct lists 
  \<^item> 2-3-Trees
\<close>  

term List.insert  
  
export_code List.insert in SML   
  
interpretation dl_set: set_interface distinct set "[]" "List.member" "List.insert" "\<lambda>x. x"
  apply unfold_locales
  apply (auto simp: in_set_member)
  done  
  
term dl_set.union
thm dl_set.union_\<alpha>  
    
(*<*)
end
(*>*)
