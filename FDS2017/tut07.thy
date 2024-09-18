(*<*)
theory tut07
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
  
definition "select x a res \<equiv> 
  case res of 
    None \<Rightarrow> a 
  | Some b \<Rightarrow>
      if ( \<bar>b-x\<bar> < \<bar>a-x\<bar>) then b else a
"  

hide_const round  
  
fun round :: "int tree \<Rightarrow> int \<Rightarrow> int option" 
  where 
    "round \<langle>\<rangle> _ = None"
  | "round \<langle>l,a,r\<rangle> x = (
      if x=a then Some a
      else if x<a then Some (select x a (round l x))
      else Some (select x a (round r x))
    )"

lemma [simp]:
  shows "round t x = None \<longleftrightarrow> t = \<langle>\<rangle>"  
  by (induction t) auto  

lemma round_in_set:
  assumes "round t x = Some a"  
  shows "a \<in> set_tree t"  
  using assms
  apply (induction t x arbitrary: a rule: round.induct) 
  apply (auto split: if_splits option.splits simp: select_def)    
  done    

    
lemma "bst t \<Longrightarrow> round t x = Some a \<Longrightarrow> (\<forall>b\<in>set_tree t. abs (x-b) \<ge> abs (x-a))"
proof (induction t arbitrary: x a)
  case Leaf
  then show ?case by auto
next
  case (Node l b r)

  show ?case proof (cases)
    assume "x=b" thus ?thesis using Node.prems by auto
  next
    assume "x\<noteq>b"
    show ?thesis proof (cases)
      assume XLB: "x<b"
      show ?thesis proof (cases)
        assume "l=Leaf"
        then show ?thesis using Node.prems XLB by (auto simp: select_def)
      next
        assume "l\<noteq>Leaf"
        then obtain c where [simp]: "round l x = Some c" 
          by (cases "round l x") auto
        from Node.IH(1)[OF _ this] \<open>bst \<langle>l, b, r\<rangle>\<close> 
        have IH: "\<forall>b\<in>set_tree l. \<bar>x - c\<bar> \<le> \<bar>x - b\<bar>" by auto
        then show ?thesis using Node.prems XLB 
          apply (auto simp: select_def)
          apply force+
          done  
      qed
    next    
      assume "\<not>(x<b)"
      with \<open>x\<noteq>b\<close> have BLX: "b<x" by auto
      (* Analogous \<dots> or use fastforce shortcut \<dots>*)    
      with Node show ?thesis 
        by (fastforce simp: select_def split: option.split)
        
    qed
  qed
qed    
    
    
    
(*    
lemma
  assumes "bst t"
  assumes "round t x = Some c"  
  assumes "b\<in>set_tree t"  
  shows "\<bar>c-x\<bar> \<le> \<bar>b-x\<bar>"  
  using assms  
proof (induction t x arbitrary: c rule: round.induct)
  case (1 uu)
  then show ?case by simp
next
  case (2 l a r x)
    
  from "2.prems" have "bst l" and "bst r" by simp_all 
    
  from round_in_set[OF \<open>round \<langle>l, a, r\<rangle> x = Some c\<close>]
    have C_IN_TREE: "c \<in> set_tree \<langle>l,a,r\<rangle>" by auto
      
  show ?case proof (cases)
    assume "x=a"
    with \<open>round \<langle>l, a, r\<rangle> x = Some c\<close> have "x=c" by simp
    then show ?thesis by simp
  next
    assume "x\<noteq>a"
    show ?thesis proof cases 
      assume "x<a" 
      from \<open>x<a\<close> 2 have "c = (select x a (round l x))" by simp
      hence C_LEFT_EQ: "c\<in>set_tree l \<or> c=a"  
        unfolding select_def using round_in_set
        by (auto split: option.split)
      hence "c \<le> a" using \<open>bst \<langle>l,a,r\<rangle>\<close> by auto
          
          
      show ?thesis proof cases
        assume "b\<in>set_tree l"
          
        (*from "2.IH"(1)[OF \<open>x\<noteq>a\<close> \<open>x<a\<close> \<open>bst l\<close>]    *)
        show ?thesis sorry
      next
        assume "b \<notin> set_tree l"
        with \<open>bst \<langle>l,a,r\<rangle>\<close> \<open>b\<in>set_tree \<langle>l,a,r\<rangle>\<close> have "a \<le> b" by auto  
        with \<open>x<a\<close> have "x<b" by auto
            
        have "b>a" "x<a" "c\<le>a" sorry
        thus ?thesis apply auto sledgehammer     
            
            
            
            
            
            
            
        thus ?thesis using \<open>c\<le>a\<close> \<open>a\<le>b\<close>
          apply auto
          
          
    
  then show ?case sorry
qed    
*)    

fun t_round :: "int tree \<Rightarrow> int \<Rightarrow> nat" 
  where 
    "t_round \<langle>\<rangle> _ = 1"
  | "t_round \<langle>l,a,r\<rangle> x = (
      if x=a then 1
      else if x<a then 1 + t_round l x
      else 1 + t_round r x
    )"
  
lemma "t_round t x \<le> height t + 1"
  apply (induction t) apply auto done
  
text \<open>
  \Homework{Cost for \<open>remdups\<close>}{16.~6.~2017}

  The following function removes all duplicates from a list.
  It uses the auxiliary function \<open>member\<close> to determine 
  whether an element is contained in a list.
\<close>  

term remdups  
  
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
