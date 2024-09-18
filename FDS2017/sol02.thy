(*<*)
theory sol02
imports Complex_Main
begin
(*>*)



text {* \ExerciseSheet{2}{5.~5.~2017} *}

text {* \Exercise{Folding over Trees}

Define a datatype for binary trees that store data only at leafs.

*}
datatype 'a ltree = 
  (*<*)Leaf 'a | Node "'a ltree" "'a ltree"(*>*)
  
text \<open>Define a function that returns the list of elements resulting 
  from an in-order traversal of the tree.\<close>
fun inorder :: "'a ltree \<Rightarrow> 'a list" 
(*<*)  
  where
    "inorder (Leaf x) = [x]"
  | "inorder (Node l r) = inorder l @ inorder r"  
(*>*)
  
text \<open>Have a look at Isabelle/HOL's standard function @{const \<open>fold\<close>}. \<close>  
thm fold.simps  
    
text \<open>In order to fold over the elements of a tree, we could use @{term \<open>fold f (inorder t) s\<close>}.
  However, from an efficiency point of view, this has a problem. Which?
\<close>

text \<open>Define a more efficient function \<open>fold_ltree\<close>, and show that it is correct\<close>  
fun fold_ltree :: "('a \<Rightarrow> 's \<Rightarrow> 's) \<Rightarrow> 'a ltree \<Rightarrow> 's \<Rightarrow> 's" 
(*<*)  
  where
  "fold_ltree f (Leaf x) s = f x s"
| "fold_ltree f (Node l r) s = fold_ltree f r (fold_ltree f l s)"
(*>*)  

lemma "fold f (inorder t) s = fold_ltree f t s"  
(*<*)  by (induction t arbitrary: s) auto (*>*)

(*<*)    
fun mirror where
  "mirror (Node l r) = Node (mirror r) (mirror l)"
| "mirror (Leaf x) = Leaf x"  
(*>*)      
    
text \<open>Define a function \<open>mirror\<close> that reverses the order of the leafs, i.e., that
  satisfies the following specification:\<close>
    
lemma "inorder (mirror t) = rev (inorder t)"  
(*<*)  by (induction t) auto (*>*)
    
    

text {* \Exercise{Shuffle Product}

To shuffle two lists, we repeat the following step until both lists are empty:
  Take the first element from one of the lists, and append it to the result.

That is, a shuffle of two lists contains exactly the elements of both lists in 
the right order.

Define a function \<open>shuffles\<close> that returns a list of all shuffles of two given lists
*}

fun shuffles :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list list" 
(*<*)  
  where
  "shuffles xs [] = [xs]"
| "shuffles [] ys = [ys]"  
| "shuffles (x#xs) (y#ys) = map (op # x) (shuffles xs (y#ys)) @ map (op # y) (shuffles (x#xs) ys)"  
(*>*)  
   
text \<open>Show that the length of any shuffle of two lists is the sum of the length
 of the original lists.\<close>  
lemma "l\<in>set (shuffles xs ys) \<Longrightarrow> length l = length xs + length ys"
(*<*)  
  apply (induction xs ys arbitrary: l rule: shuffles.induct)
  apply auto  
  done  
(*>*)    
text \<open>Note: The @{const set} function converts a list to the set of its elements.\<close>  

text \<open>\Exercise{Fold function}
  The fold function is a very generic function, that can be used to express 
  multiple other interesting functions over lists.

  Write a function to compute the sum of the elements of a list. 
  Specify two versions, one direct recursive specification, and one using fold.
  Show that both are equal.
\<close>  
  
fun list_sum :: "nat list \<Rightarrow> nat" 
(*<*)  
  where
  "list_sum [] = 0"
| "list_sum (x#xs) = x + list_sum xs"  
(*>*)  
  
definition list_sum' :: "nat list \<Rightarrow> nat"
(*<*)  
  where "list_sum' l \<equiv> fold op+ l 0"
(*>*)    

(*<*)    
lemma aux: "fold op+ l a = list_sum l + a"  
  by (induction l arbitrary: a) auto
(*>*)    
  
lemma "list_sum l = list_sum' l"
(*<*)    
  by (simp add: aux list_sum'_def)
(*>*)    
    
(*<*)
end
(*>*)

