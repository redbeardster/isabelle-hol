theory tut04
imports "../../fds_ss17/Demos/BST_Demo"
begin

  fun join :: "'a tree \<Rightarrow> 'a tree \<Rightarrow> 'a tree"
  where
    "join Leaf t = t"
  | "join t Leaf = t"
  | "join (Node l1 x1 r1) (Node l2 x2 r2) = (
      case (join r1 l2) of 
        Leaf \<Rightarrow> Node l1 x1 (Node Leaf x2 r2)
      | Node lj xj rj \<Rightarrow> Node (Node l1 x1 lj) xj (Node rj x2 r2) 
    )" 

  lemma "inorder (join t1 t2) = inorder t1 @ inorder t2"  
    apply (induction t1 t2 rule: join.induct)
    apply (auto split: tree.splits)
    done  
    
  lemma "height (join t1 t2) \<le> max (height t1) (height t2) + 1"
    apply (induction t1 t2 rule: join.induct)
    apply (auto split: tree.splits)
    done  

      
  fun in_range :: "'a::linorder tree \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a list" where
    "in_range \<langle>\<rangle> u v = []"
  | "in_range \<langle>l,x,r\<rangle> u v = 
         (if u<x then in_range l u v else [])
        @(if u\<le>x \<and> x\<le>v then [x] else [])        
        @(if x<v then in_range r u v else [])
    "
      
  lemma "bst t \<Longrightarrow> set (in_range t u v) = { x\<in>set_tree t. u\<le>x \<and> x\<le>v }"
    apply (induction t)
    apply auto
    done  
      
  lemma [simp]: "[a] = l1@b#l2 \<longleftrightarrow> a=b \<and> l1=[] \<and> l2=[]"
    apply (cases l1)
    apply auto
    done  
      
    (*by (metis Nil_is_append_conv append_self_conv2 butlast.simps(2) butlast_append list.discI nth_Cons_0)
    *)

  lemma [simp]: "[] = filter P l \<longleftrightarrow> filter P l = []" by auto  
      
  lemma "bst t \<Longrightarrow> in_range t u v = filter (\<lambda>x. u\<le>x \<and> x\<le>v) (inorder t)"  
    apply (induction t)
    apply simp  
    apply clarsimp 
    (*apply (intro conjI impI)*) apply safe
    apply (auto simp: filter_empty_conv)
    done      
      

  fun tree2 :: "'a tree \<Rightarrow> 'b tree \<Rightarrow> bool" where
    "tree2 \<langle>\<rangle> \<langle>\<rangle> \<longleftrightarrow> True"
  | "tree2 \<langle>l,x,r\<rangle> \<langle>ll,xx,rr\<rangle> \<longleftrightarrow> tree2 l ll \<and> tree2 r rr"
  | "tree2 _ _ \<longleftrightarrow> False"   
      
  print_statement tree2.induct
    
  datatype 'a tchar = L | N 'a 
    
  fun pretty :: "'a tree \<Rightarrow> 'a tchar list" where
    "pretty \<langle>\<rangle> = [L]"
  | "pretty \<langle>l,x,r\<rangle> = N x#pretty l@pretty r" 

  lemma aux: "pretty t1@xs = pretty t2@ys\<Longrightarrow> t1 = t2"
    apply (induction t1 t2 arbitrary: xs ys rule: tree2.induct)
    apply auto
    apply fastforce
    done  
    
    
  lemma "pretty t1 = pretty t2 \<Longrightarrow> t1 = t2"
    by (simp add: aux)
      
    (*using aux[of _ "[]" _ "[]"] 
    by simp *)
      
end