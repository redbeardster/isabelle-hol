theory tut03
imports "../../fds_ss17/Demos/BST_Demo"
begin
  
  term isin2
  
  fun ins2 :: "'a::linorder \<Rightarrow> 'a option \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
    "ins2 x z Leaf = (
      case z of 
        None \<Rightarrow> \<langle> Leaf, x, Leaf \<rangle>
      | Some y \<Rightarrow> (if x=y then Leaf else Node Leaf x Leaf))"
  | "ins2 x z (Node l a r) = (if x<a then Node (ins2 x z l) a r else Node l a (ins2 x (Some a) r))" 
    
  
  lemma aux: "\<lbrakk> bst t; \<forall>x\<in>set_tree t. y < x \<rbrakk> \<Longrightarrow> ins2 x (Some y) t = (if x=y then t else ins x t)"  
    apply (induction t arbitrary: y)
    apply auto
    done  
    
  lemma "bst t \<Longrightarrow> ins2 x None t = ins x t"
    apply (induction t)
    apply (auto simp: aux)  
    done    
    
  
  definition mk_tree :: "'a::linorder list \<Rightarrow> 'a tree" where
    "mk_tree l = fold ins l Leaf"
      
  lemma aux2: "bst t \<Longrightarrow> bst (fold ins l t)"  
    by (induction l arbitrary: t) (auto simp: bst_ins)  
    
  lemma bst_mk_tree: "bst (mk_tree l)"
    unfolding mk_tree_def by (simp add: aux2)

  lemma aux3: "bst t \<Longrightarrow> set_tree (fold ins l t) = set_tree t \<union> set l"  
    by (induction l arbitrary: t) (auto simp: bst_ins set_tree_ins)  
      
  lemma set_mk_tree: "set_tree (mk_tree l) = set l"
    unfolding mk_tree_def by (simp add: aux3)
      
  definition "bst_sort l = inorder (mk_tree l)"

  lemma "set (bst_sort l) = set l"
    unfolding bst_sort_def
    by (simp add: set_mk_tree)  

  lemma "distinct (bst_sort l)"    
    unfolding bst_sort_def
    by (simp add: bst_mk_tree distinct_inorder_if_bst)  

  lemma "sorted (bst_sort l)"
    unfolding bst_sort_def
    thm bst_eq_imp_sorted bst_eq_if_bst
    by (simp add: bst_mk_tree bst_eq_imp_sorted bst_eq_if_bst)  
    
      
      
end