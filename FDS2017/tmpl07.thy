(*<*)
theory tmpl07
  imports 
    Complex_Main 
    "~~/src/HOL/Library/Tree"
begin
(*>*)  
text {* \ExerciseSheet{7}{9.~6.~2017} *}


text \<open>\Exercise{Round wrt.\ Binary Search Tree}
  The distance between two integers \<open>x\<close> and \<open>y\<close> is @{term \<open>abs (x-y)\<close>}.

  \<^enum> Define a function \<open>round :: int tree \<Rightarrow> int \<Rightarrow> int option\<close>, such that
    \<open>round t x\<close> returns an element of a {\bf binary search tree} \<open>t\<close> with minimum 
    distance to \<open>x\<close>, and \<open>None\<close> if and only if \<open>t\<close> is empty.
  
    Define your function such that it does no unnecessary recursions 
    into branches of the tree that are known to not contain a minimum distance 
    element.

  \<^enum> Specify and prove that your function is correct. 
    Note: You are required to phrase the correctness properties yourself!
  
    Hint: Specify 3 properties: 
      \<^item> None is returned only for the empty tree.
      \<^item> Only elements of the tree are returned.
      \<^item> The returned element has minimum distance.

  \<^enum> Estimate the time of your round function to be linear in the height of the tree
\<close>  
  
fun round :: "int tree \<Rightarrow> int \<Rightarrow> int option" 
  where "round _ _ = undefined"

fun t_round :: "int tree \<Rightarrow> int \<Rightarrow> nat" 
  where "t_round _ _ = undefined"
  
  
text \<open>
  \Homework{Cost for \<open>remdups\<close>}{16.~6.~2017}

  The following function removes all duplicates from a list.
  It uses the auxiliary function \<open>member\<close> to determine 
  whether an element is contained in a list.
\<close>  

fun member :: "'a \<Rightarrow> 'a list \<Rightarrow> bool" where
  "member x [] \<longleftrightarrow> False"
| "member x (y#ys) \<longleftrightarrow> (if x=y then True else member x ys)"
  
fun rem_dups :: "'a list \<Rightarrow> 'a list" where
  "rem_dups [] = []" |
  "rem_dups (x # xs) = (if member x xs then rem_dups xs else x # rem_dups xs)"
  
text \<open>
  Show that this function is equal to the HOL standard function @{const \<open>remdups\<close>}
\<close>  
lemma rem_dups_correct: "rem_dups xs = remdups xs" sorry

text \<open>Define the timing functions for @{const \<open>member\<close>} and @{const rem_dups}, 
  as described on the slides:\<close>
fun t_member :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" 
  where "t_member _ _ = undefined"
  
fun t_rem_dups :: "'a list \<Rightarrow> nat" 
  where "t_rem_dups _ = undefined"
    
text \<open>Estimate \<open>t_rem_dups xs\<close> to be quadratic in the length of \<open>xs\<close>.
  Hint: The estimate @{term \<open>(length xs + 1)\<^sup>2\<close>} should work.
\<close>
lemma "t_rem_dups xs \<le> (length xs+1)\<^sup>2" sorry
  
(*<*)
end
(*>*)
