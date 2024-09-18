(*<*)
theory tmpl08_ex
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
  
locale set_interface =
  fixes invar :: "'s \<Rightarrow> bool" and \<alpha> :: "'s \<Rightarrow> 'a set"
  fixes empty :: 's
  assumes empty_invar: "invar empty" and empty_\<alpha>: "\<alpha> empty = {}"
  
  fixes is_in :: "'s \<Rightarrow> 'a \<Rightarrow> bool"  
  assumes is_in_\<alpha>: "invar s \<Longrightarrow> is_in s x \<longleftrightarrow> x \<in> \<alpha> s"
    
  fixes ins :: "'a \<Rightarrow> 's \<Rightarrow> 's"  
  assumes ins_invar: "invar s \<Longrightarrow> invar (ins x s)" and ins_\<alpha>: "invar s \<Longrightarrow> \<alpha> (ins x s) = Set.insert x (\<alpha> s)"
   
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
    sorry
  
  lemma union_\<alpha>:  
    assumes "invar A"  
    assumes "invar B"  
    shows "\<alpha> (union A B) = \<alpha> A \<union> \<alpha> B"
    sorry
    
  text \<open>Define an intersection function and show its interface specification\<close>  
    
  definition intersect :: "'s \<Rightarrow> 's \<Rightarrow> 's"
    where
    "intersect A B \<equiv> undefined"
    
  lemma intersect_invar: "True" sorry
  lemma intersect_\<alpha>: "True" sorry
end  

text \<open>Having defined the locale, we can instantiate it for implementations of 
  the set interface. For example for BSTs:\<close>  
                                                
interpretation bst_set: set_interface bst set_tree Tree.Leaf "BST_Demo.isin" "BST_Demo.ins" Tree.inorder
  apply unfold_locales
  text \<open>Show the goals\<close>  
    sorry
  
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
  
(*<*)
end
(*>*)
