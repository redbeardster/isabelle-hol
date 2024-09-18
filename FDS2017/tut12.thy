(*<*)
theory tut12
imports Complex_Main
begin
(*>*)  

text {* \ExerciseSheet{12}{14.~7.~2017} *}
  
text \<open>
  \Exercise{Balanced Queues}
  
  Consider locale \<open>Queue\<close> in file \<open>Thys/Amortized_Examples\<close>. A call of \<open>deq (xs,[])\<close>
  requires the reversal of \<open>xs\<close>, which may be very long. We can reduce that impact
  by shifting \<open>xs\<close> over to \<open>ys\<close> whenever \<open>length xs > length ys\<close>. This does not improve
  the amortized complexity (in fact it increases it by 1) but reduces the worst case complexity
  of individual calls of \<open>deq\<close>. Modify locale \<open>Queue\<close> as follows:\<close>
  
locale Queue begin

type_synonym 'a queue = "'a list * 'a list"

definition "init = ([],[])"
fun balance :: "'a queue \<Rightarrow> 'a queue" where
"balance(xs,ys) = (if size xs \<le> size ys then (xs,ys) else ([], ys @ rev xs))"
fun enq :: "'a \<Rightarrow> 'a queue \<Rightarrow> 'a queue" where
"enq a (xs,ys) = balance (a#xs, ys)"
fun deq :: "'a queue \<Rightarrow> 'a queue" where
"deq (xs,ys) = balance (xs, tl ys)"

text \<open>Again, we count only the newly allocated list cells.\<close>
fun t_balance :: "'a queue \<Rightarrow> nat" where
  "t_balance (xs,ys) = (if size xs \<le> size ys then 0 else size xs + size ys)"
fun t_enq :: "'a \<Rightarrow> 'a queue \<Rightarrow> nat" where
"t_enq a (xs,ys) = 1 + t_balance (a#xs, ys)"
fun t_deq :: "'a queue \<Rightarrow> nat" where
"t_deq (xs,ys) = t_balance (xs, tl ys)"

text \<open>
  \<^item> Start over with showing functional correctness. Hint: You will require an invariant.
\<close>  

fun invar :: "'a queue \<Rightarrow> bool" 
(*<*)  
  where
  "invar (xs,ys) \<longleftrightarrow> size xs \<le> size ys"
(*>*)  
  
fun abs :: "'a queue \<Rightarrow> 'a list" 
(*<*)  
  where
  "abs (xs,ys) = xs@rev ys"
(*>*)  
  
lemma [simp]: "invar init"  
  by (simp add: init_def)
    
lemma [simp]: "invar q \<Longrightarrow> invar (enq x q)"
  by (cases q) auto
  
    
lemma [simp]: "invar q \<Longrightarrow> invar (deq q)"
  by (cases q) auto
   
lemma [simp]: "abs init = []"
  by (auto simp: init_def)
  
lemma [simp]: "invar q \<Longrightarrow> abs (enq x q) = x#abs q"
  by (cases q) auto
    
lemma [simp]: "length a \<le> length b \<Longrightarrow> a @ rev (tl b) = butlast (a @ rev b)"    
  apply (induction b) apply (auto simp: butlast_append)
  done  
    
lemma [simp]: "invar q \<Longrightarrow> abs (deq q) = butlast (abs q)"
  apply (cases q) 
  apply auto
  done  



text \<open>
  \<^item> Next, define a suitable potential function \<open>\<Phi>\<close>, and prove
    that the amortized complexity of \<open>enq\<close> is \<open> \<le> 3\<close> and of \<open>deq\<close> is \<open> \<le> 0\<close>.
\<close>

fun \<Phi> :: "'a queue \<Rightarrow> int" 
(*<*)
  where "\<Phi> (xs,ys) = 2*length xs"
(*>*)

lemma \<Phi>_non_neg: "\<Phi> t \<ge> 0" by (cases t) auto

lemma \<Phi>_init: "\<Phi> init = 0" unfolding init_def by auto

lemma a_enq: " t_enq a q + \<Phi>(enq a q) - \<Phi> q \<le> 3"
  by (cases q) auto
  

lemma a_deq: " t_deq q + \<Phi>(deq q) - \<Phi> q \<le> 0"
  by (cases q) auto
  

text \<open>Finally, show that a sequence of enqueue and dequeue operations requires 
  linear cost in its length:
\<close>  
  
(*<*)  
(* Establish abstraction boundary *)  
lemmas [simp del] = \<Phi>.simps enq.simps deq.simps t_enq.simps t_deq.simps
(*>*)  

datatype 'a opr = ENQ 'a | DEQ    
    
fun execute :: "'a queue \<Rightarrow> 'a opr list \<Rightarrow> 'a queue" 
  where
  "execute q [] = q"
| "execute q (ENQ x#ops) = execute (enq x q) ops"  
| "execute q (DEQ#ops) = execute (deq q) ops"  
  
text \<open>Count only list cell allocations! \<close>  
fun t_execute :: "'a queue \<Rightarrow> 'a opr list \<Rightarrow> nat" 
  where
  "t_execute q [] = 0"
| "t_execute q (ENQ x#ops) = t_execute (enq x q) ops + t_enq x q"
| "t_execute q (DEQ#ops) = t_execute (deq q) ops + t_deq q"
  
lemma t_execute_aux: "t_execute q ops \<le> 3*length ops + \<Phi> q - \<Phi> (execute q ops)"
proof (induction q ops rule: execute.induct)
  case (1 q)
  then show ?case by simp
next
  case (2 q x ops)
  then show ?case using a_enq[of x q] by auto
next
  case (3 q ops)
  then show ?case using a_deq[of q] by auto
qed

term init  

lemma t_execute: "t_execute init ops \<le> 3*length ops"
  using t_execute_aux[of init ops] \<Phi>_non_neg[of "execute init ops"] 
  by (auto simp: \<Phi>_init)
  
  
lemma "t_execute (init::'b queue) ops \<le> 3*length ops"
  using t_execute_aux[of init ops] \<Phi>_non_neg[of "execute init ops"] 
    \<Phi>_init[where ?'a='b]
  by (auto)


end

(*<*)  
end
(*>*)  
