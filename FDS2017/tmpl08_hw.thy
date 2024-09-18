(*<*)
theory tmpl08_hw
  imports 
    Complex_Main 
    "~~/src/HOL/Library/Multiset" 
    (*"~~/src/HOL/Library/List_lexord"*)
    "~~/src/HOL/Library/Tree"
    "~~/src/HOL/Data_Structures/Tree23_Set"
begin
(*>*)  
text {* \ExerciseSheet{8}{16.~6.~2017} *}


  
text \<open>
  \NumHomework{Estimating the Size of 2-3-Trees}{23.~6.~2017}

    Show that for 2-3-trees, we have:
    @{text [display] \<open> log\<^sub>3 ( s(t) + 1 ) \<le> h(t) \<le> log\<^sub>2 (s(t) + 1)\<close>}

    Hint: It helps to first raise the two sides of the 
      inequation to the 2nd/3rd power. 
      Use sledgehammer and find-theorems to search for the appropriate lemmas.
\<close>  

lemma height_est_upper: "bal t \<Longrightarrow> height t \<le> log 2 (size t + 1)"
  sorry

lemma height_est_lower: "bal t \<Longrightarrow> log 3 (size t + 1) \<le> height t"
  sorry

text \<open>Define a function to count the number of leaves of a 2-3-tree\<close>  
fun num_leaves :: "_ tree23 \<Rightarrow> nat" 
  where
  "num_leaves \<langle>\<rangle> = undefined"
  
text \<open>Define a function to determine whether a tree only consists of 2-nodes 
  and leaves:\<close>  
fun is_2_tree :: "_ tree23 \<Rightarrow> bool" 
  where
  "is_2_tree \<langle>\<rangle> \<longleftrightarrow> undefined"


text \<open>Show that a 2-3-tree has only 2 nodes, if and only if its number of leafs is 2 to the power of its height!

  Hint: The \<open>\<longrightarrow>\<close> direction is quite easy, the \<open>\<longleftarrow>\<close> direction requires a bit more work!
\<close>    
lemma "bal t \<Longrightarrow> is_2_tree t \<longleftrightarrow> num_leaves t = 2^height t" 
  sorry
    
  
text \<open>
  \NumHomework{Deforestation}{23.~6.~2017}

    A disadvantage of using the generic algorithms from the set interface for 
    binary trees (and other data structures) is that they construct an 
    intermediate list containing the elements of one tree.

    Define a function that folds over the in-order traversal of a binary tree 
    directly, without constructing an intermediate list, and show that it is 
    correct.

    Note: Optimizations like this are called deforestation, as they get rid 
      of intermediate tree-structured data (in our case: lists which are degenerated trees).
\<close>  
  
fun fold_tree :: "('a \<Rightarrow> 's \<Rightarrow> 's) \<Rightarrow> 'a tree \<Rightarrow> 's \<Rightarrow> 's" 
  where
  "fold_tree f \<langle>\<rangle> s = undefined"
  
lemma "fold_tree f t s = fold f (Tree.inorder t) s" sorry
  
  
text \<open>
  \NumHomework{Bit-Vectors}{23.~6.~2017}
  {\bf Bonus Homework (3p)}

  A bit-vector is a list of Booleans that encodes a finite set of 
  natural numbers as follows: A number \<open>i\<close> is in the set, 
  if \<open>i\<close> is less than the length of the list and the \<open>i\<close>th element of the list 
  is true.

  For 3 bonus points, define the operations empty, member, insert, and to-list
  on bit-vectors, and instantiate the set-interface from Exercise~1!
\<close>  

(* Set interface for bonus homework *)  
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

end  
  
  
type_synonym bv = "bool list"
  
definition bv_\<alpha> :: "bv \<Rightarrow> nat set" 
  where "bv_\<alpha> l = { i. i<length l \<and> l!i }"
    
definition bv_empty :: bv 
  where "bv_empty = undefined"  
    
definition bv_member :: "bv \<Rightarrow> nat \<Rightarrow> bool" 
  where "bv_member l x \<longleftrightarrow> undefined"
    
definition bv_ins :: "nat \<Rightarrow> bv \<Rightarrow> bv" 
  where "bv_ins x l = undefined"  
    
definition bv_to_list :: "bv \<Rightarrow> nat list" 
  where "bv_to_list l \<equiv> undefined"
    
    
interpretation bv_set: set_interface "\<lambda>_. True" bv_\<alpha> bv_empty bv_member bv_ins bv_to_list
  (* Hint: Show auxiliary lemmas stating the correctness of each operation first \<dots> *)
  sorry
  
(*<*)
end
(*>*)
