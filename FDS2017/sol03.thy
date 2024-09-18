(*<*)
theory sol03
  imports "../../fds_ss17/Demos/BST_Demo"
begin
(*>*)

text {* \ExerciseSheet{3}{12.~5.~2017} *}

text \<open>
  \Exercise{Insert with Less Comparisons}
  
  \<^item> Define a function \<open>ins2\<close> that inserts into a binary search tree, using only 
    one comparison per node. Use the same idea as @{const isin2}.

  \<^item> Show that your function is equal to @{const ins} on binary search trees.
    Hint: You may need an auxiliary lemma of the form:
      @{text [display] "\<lbrakk> bst t;  \<forall>x \<in> set_tree t. y < x \<rbrakk> \<Longrightarrow> ins2 x (Some y) t = \<dots>"}
\<close>
      
fun ins2 :: "'a::linorder \<Rightarrow> 'a option \<Rightarrow> 'a tree \<Rightarrow> 'a tree" 
  (*<*)
  where
  "ins2 x z Leaf =
    (case z of
       None \<Rightarrow> Node Leaf x Leaf |
       Some y \<Rightarrow> if x=y then Leaf else Node Leaf x Leaf)" 
| "ins2 x z (Node l a r) =
    (if x < a then Node (ins2 x z l) a r else Node l a (ins2 x (Some a) r))"
  (*>*)

(*<*)  
lemma ins2_Some:
  "\<lbrakk> bst t;  \<forall>x \<in> set_tree t. y < x \<rbrakk>
  \<Longrightarrow> ins2 x (Some y) t = (if x=y then t else ins x t)"
apply(induction t arbitrary: y)
apply auto
done
(*>*)  

lemma ins2_None: "bst t \<Longrightarrow> ins2 x None t = ins x t"
(*<*)
apply(induction t)
apply (auto simp: ins2_Some)
done
(*>*)  
      
text \<open>
  \Exercise{Height-Preserving In-Order Join}
  Moved to exercise sheet 4!
\<close>  
  
text \<open>\Exercise{Sorting with BSTs}\<close>

text \<open>
  \<^item> Define a function to create a binary search tree from a list. Hint: Use @{const fold}.
  \<^item> Show that your function returns a binary search tree with the correct elements
  \<^item> We define \<open>bst_sort\<close> as the inorder traversal of the tree created from a list.
    Show that it contains the right elements, is distinct, and sorted.
\<close>  
  
(*
    Bonus: this implies that we exactly compute "remdups (sort l)". Prove that!
*)    
    
definition mk_tree :: "'a::linorder list \<Rightarrow> 'a tree" 
(*<*)  
  where "mk_tree l = fold ins l Leaf"  
(*>*)    

(*<*)    
lemma bst_mk_tree_aux: "bst t \<Longrightarrow> bst (fold ins l t)"
  apply (induction l arbitrary: t) 
  apply (auto simp: bst_ins) 
  done
    
lemma set_mk_tree_aux: "set_tree (fold ins l t) = set l \<union> set_tree t"
  apply (induction l arbitrary: t)    
  apply (auto simp: set_tree_ins)  
  done  
(*>*)    
  
lemma bst_mk_tree: "bst (mk_tree l)"
(*<*)    
  by (simp add: mk_tree_def bst_mk_tree_aux)
(*>*)    

lemma set_mk_tree: "set_tree (mk_tree l) = set l"
(*<*)    
  by (auto simp: set_mk_tree_aux mk_tree_def)
(*>*)    
      
    
definition "bst_sort l = inorder (mk_tree l)"
  
lemma bst_sort_set: "set (bst_sort l) = set l"
(*<*)    
  by (auto simp: bst_sort_def set_mk_tree)
(*>*)    
    
lemma bst_sort_sorted: "sorted (bst_sort l)"
(*<*)    
  by (auto simp: bst_sort_def bst_mk_tree bst_eq_imp_sorted[OF bst_eq_if_bst])  
(*>*)    
    
lemma bst_sort_distinct: "distinct (bst_sort l)"    
(*<*)    
  by (simp add: bst_sort_def bst_mk_tree distinct_inorder_if_bst)  
(*>*)    
    
(*<*)    
lemma "bst_sort l = sort (remdups l)"
  by (simp add: bst_sort_distinct bst_sort_set bst_sort_sorted sorted_distinct_set_unique)  
(*>*)    
    
(*<*)
end
(*>*)

