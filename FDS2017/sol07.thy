(*<*)
theory sol07
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
  
(*<*)  
  
definition best :: "int \<Rightarrow> int \<Rightarrow> int option \<Rightarrow> int" where
"best x a b = (
  case b of None \<Rightarrow> a 
| Some b \<Rightarrow> if abs (x-a) < abs (x-b) then a else b)"
(*>*)  
    
fun round :: "int tree \<Rightarrow> int \<Rightarrow> int option" 
(*<*)  
  where
  "round \<langle>\<rangle> _ = None"
| "round \<langle>l,a,r\<rangle> x = (
    if a=x then Some x
    else if x<a then Some (best x a (round l x))
    else Some (best x a (round r x))
    )"  

(* None iff empty tree *)  
lemma [simp]: "round t x = None \<longleftrightarrow> t=\<langle>\<rangle>"    
  by (induction t arbitrary: x) auto

(* Only elements of the tree are returned *)    
lemma "round t x = Some a \<Longrightarrow> a \<in> set_tree t"    
  apply (induction t arbitrary: x)
  apply (auto split: if_splits option.splits simp: best_def)
  done
    
(* Minimum distance element is returned *)    
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
        then show ?thesis using Node.prems XLB by (auto simp: best_def)
      next
        assume "l\<noteq>Leaf"
        then obtain c where [simp]: "round l x = Some c" 
          by (cases "round l x") auto
        from Node.IH(1)[OF _ this] \<open>bst \<langle>l, b, r\<rangle>\<close> 
        have IH: "\<forall>b\<in>set_tree l. \<bar>x - c\<bar> \<le> \<bar>x - b\<bar>" by auto
        then show ?thesis using Node.prems XLB by (auto simp: best_def)
      qed
    next    
      assume "\<not>(x<b)"
      with \<open>x\<noteq>b\<close> have BLX: "b<x" by auto
      (* Analogous \<dots> or use fastforce shortcut \<dots>*)    
      with Node show ?thesis 
        by (fastforce simp: best_def split: option.split)
        
    qed
  qed
qed    

(* Short proof for third lemma *)  
lemma "bst t \<Longrightarrow> round t x = Some a \<Longrightarrow> (\<forall>b\<in>set_tree t. abs (x-b) \<ge> abs (x-a))"
  apply (induction t arbitrary: x a)
  apply simp  
  apply (fastforce split: if_splits option.splits simp: best_def)  
  done  
  
(*>*)  
    
fun t_round :: "int tree \<Rightarrow> int \<Rightarrow> nat" 
(*<*)    
  where
  "t_round \<langle>\<rangle> _ = 1"
| "t_round \<langle>l,a,r\<rangle> x = (
    if a=x then 1
    else if x<a then 1 + t_round l x
    else 1 + t_round r x
    )"  
   
lemma "t_round t x \<le> height t + 1"  
  apply (induction t x rule: t_round.induct)
  apply auto  
  done
    
(*>*)    
  
(*<*)
end
(*>*)
