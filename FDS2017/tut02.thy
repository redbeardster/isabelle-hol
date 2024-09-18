theory tut02
imports Main
begin

 
  datatype 'a ltree = Leaf "'a" | Node "'a ltree" "'a ltree"
    
  fun inorder :: "'a ltree \<Rightarrow> 'a list" where
    "inorder (Leaf x) = [x]" 
  | "inorder (Node l r) = inorder l @ inorder r"

  value "inorder (Node (Node (Leaf 1) (Leaf 2)) (Node (Leaf 3) (Node (Leaf 4) (Leaf (5::int)))))"

  thm fold.simps
  thm fold_simps
    
  lemma 
    "fold f [] s = s"
    "fold f (x#xs) s = fold f xs (f x s)" 
    by auto
    

  definition "fold_ltree_spec f t s \<equiv> fold f (inorder t) s"    
      
  fun fold_ltree :: "('b \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'b ltree \<Rightarrow> 'a \<Rightarrow> 'a"  where
    "fold_ltree f (Leaf x) s = f x s"
  | "fold_ltree f (Node l r) s = fold_ltree f r (fold_ltree f l s)" 
    
  lemma "fold_ltree f t s = fold_ltree_spec f t s"  
    unfolding fold_ltree_spec_def
    apply (induction t arbitrary: s)
    apply auto
    done  
    
  term "l@[x]" 
    
  term "map (\<lambda>l. l@[x]) " 
    
    
  fun shuffles :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list list" where
    "shuffles xs [] = [xs]" 
  | "shuffles [] ys = [ys]" 
  | "shuffles (x#xs) (y#ys) = map (\<lambda>l. x#l) (shuffles xs (y#ys)) @ map (\<lambda>l. y#l) (shuffles (x#xs) ys)"
      
   
  lemma "l \<in> set (shuffles xs ys) \<Longrightarrow> length l = length xs + length ys"  
    apply (induction xs ys arbitrary: l rule: shuffles.induct)
    apply auto  
    done  
    

  fun lsum :: "nat list \<Rightarrow> nat" where
    "lsum [] = 0" | "lsum (x#xs) = x + lsum xs"       
      
  definition "lsum' l = fold (op +) l 0" 
    
  lemma aux: "fold op + l a = a + lsum l"  
    apply (induction l arbitrary: a)
    apply auto  
    done  
    
  lemma "lsum' l = lsum l"  
    unfolding lsum'_def
    (*using aux[where a=0] apply simp *)
    apply (simp add: aux)  
    done  

      
  term "f x y = (let z=x+y; zz=z+y+y in z+zz)"    
      
end
  