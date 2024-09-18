(*<*)
theory sol08
  imports 
    Complex_Main 
    "../../Material/Demos/BST_Demo"
    "~~/src/HOL/Library/Multiset" 
    (*"~~/src/HOL/Library/List_lexord"*)
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
  (*<*)      
  proof -
    have union_invar_aux: "invar (fold ins list B)" for list
      using \<open>invar B\<close>
      by (induction list arbitrary: B) (auto simp: ins_invar)
    
    show ?thesis unfolding union_def using union_invar_aux by auto
  qed
  (*>*)  
  
  lemma union_\<alpha>:  
    assumes "invar A"  
    assumes "invar B"  
    shows "\<alpha> (union A B) = \<alpha> A \<union> \<alpha> B"
  (*<*)
  proof -
    have "\<alpha> (fold ins list B) = \<alpha> B \<union> set list" for list
      using \<open>invar B\<close>
      by (induction list arbitrary: B) (auto simp: ins_\<alpha> ins_invar)
    also have "set (to_list A) = \<alpha> A" using to_list_\<alpha>[OF \<open>invar A\<close>] .   
    finally show ?thesis unfolding union_def by auto
  qed
  (*>*)  
    
  text \<open>Define an intersection function and show its interface specification\<close>  
    
  definition intersect :: "'s \<Rightarrow> 's \<Rightarrow> 's"
  (*<*)  
    where
    "intersect A B \<equiv> fold (\<lambda>x s. if is_in A x then ins x s else s) (to_list B) empty"
  (*>*)  
  lemma intersect_invar: 
  (*<*)  
    assumes "invar A"  
    assumes "invar B"  
    shows "invar (intersect A B)"
  proof -
    have "invar (fold (\<lambda>x s. if is_in A x then ins x s else s) list S)" if \<open>invar S\<close> for list S
      using that
      by (induction list arbitrary: S) (auto simp: ins_invar)  
    thus ?thesis unfolding intersect_def by (auto simp: empty_invar)    
  qed  
  (*>*)  
  lemma intersect_\<alpha>:
  (*<*)  
    assumes "invar A"  
    assumes "invar B"  
    shows "\<alpha> (intersect A B) = \<alpha> A \<inter> \<alpha> B"
  proof -
    have "\<alpha> (fold (\<lambda>x s. if is_in A x then ins x s else s) list S) = \<alpha> S \<union> (set list \<inter> \<alpha> A)"
      if \<open>invar S\<close> for list S
      using that
      by (induction list arbitrary: S) (auto simp: is_in_\<alpha>[OF \<open>invar A\<close>] ins_\<alpha> ins_invar)  
    from this[OF empty_invar] show ?thesis 
      unfolding intersect_def
      by (auto simp: empty_\<alpha> to_list_\<alpha>[OF \<open>invar B\<close>])
  qed  
  (*>*)  
end  

text \<open>Having defined the locale, we can instantiate it for implementations of 
  the set interface. For example for BSTs:\<close>  
                                                
interpretation bst_set: set_interface bst set_tree Tree.Leaf "BST_Demo.isin" "BST_Demo.ins" Tree.inorder
  apply unfold_locales
  text \<open>Show the goals\<close>  
(*<*)    
  apply (auto simp: set_tree_isin bst_ins set_tree_ins)  
  done  
(*>*)    
  
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


definition "dlist_ins x l \<equiv> if x\<in>set l then l else x#l"  
  
interpretation dlist_set: set_interface "distinct" set "[]" "\<lambda>l x. x\<in>set l" dlist_ins "\<lambda>x. x"
  apply unfold_locales
  unfolding dlist_ins_def  
  apply (auto)  
  done  
  
term dlist_set.union 
thm dlist_set.union_\<alpha> dlist_set.union_invar
  
term dlist_set.intersect
thm dlist_set.intersect_\<alpha> dlist_set.intersect_invar

  
  
interpretation set23: set_interface "\<lambda>t. bal t \<and> sorted (inorder t)" "elems o inorder" "\<langle>\<rangle>::_ tree23" "isin" "insert" "inorder"
proof (unfold_locales; clarify?)
  show "bal \<langle>\<rangle> \<and> Sorted_Less.sorted (Tree23.inorder \<langle>\<rangle>)" by simp
next      
  show "(elems \<circ> Tree23.inorder) \<langle>\<rangle> = {}" by simp
next      
  fix t x
  assume "bal t" "Sorted_Less.sorted (Tree23.inorder t)" 
  then show "Tree23_Set.isin t x = (x \<in> (elems \<circ> Tree23.inorder) t)"
    by (auto simp: isin_set)
next
  fix t x
  assume "bal t" "Sorted_Less.sorted (Tree23.inorder t)" 
  then show "bal (Tree23_Set.insert x t) \<and> Sorted_Less.sorted (Tree23.inorder (Tree23_Set.insert x t))"
    apply (auto simp: bal_insert)
    by (simp add: invar_insert)  
next      
  fix t x
  assume "bal t" "Sorted_Less.sorted (Tree23.inorder t)" 
  then show "(elems \<circ> Tree23.inorder) (Tree23_Set.insert x t) = Set.insert x ((elems \<circ> Tree23.inorder) t)"
    by (auto simp: set_ins_list inorder_insert)
next
  fix t x
  assume "bal t" "Sorted_Less.sorted (Tree23.inorder t)" 
  then show "set (Tree23.inorder t) = (elems \<circ> Tree23.inorder) t"
    by (auto simp: elems_eq_set)
qed    
  
term set23.union 
thm set23.union_\<alpha> set23.union_invar
  
term set23.intersect
thm set23.intersect_\<alpha> set23.intersect_invar
  
(*>*)  
  
(*<*)
end
(*>*)
