(*<*)
theory tmpl12
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
  "invar (xs,ys) \<longleftrightarrow> undefined"
(*>*)  
  
fun abs :: "'a queue \<Rightarrow> 'a list" 
(*<*)  
  where
  "abs (xs,ys) = undefined"
(*>*)  
  
lemma [simp]: "invar init"  
(*<*)  
  sorry
(*>*)  
    
lemma [simp]: "invar q \<Longrightarrow> invar (enq x q)"
(*<*)  
  sorry
(*>*)  
    
lemma [simp]: "invar q \<Longrightarrow> invar (deq q)"
(*<*)  
  sorry
(*>*)  
   
lemma [simp]: "abs init = []"
(*<*)  
  sorry
(*>*)  
    
lemma [simp]: "invar q \<Longrightarrow> abs (enq x q) = x#abs q"
(*<*)  
  sorry
(*>*)  
    
lemma [simp]: "invar q \<Longrightarrow> abs (deq q) = butlast (abs q)"
(*<*)  
  sorry
(*>*)  
  



text \<open>
  \<^item> Next, define a suitable potential function \<open>\<Phi>\<close>, and prove
    that the amortized complexity of \<open>enq\<close> is \<open> \<le> 3\<close> and of \<open>deq\<close> is \<open> \<le> 0\<close>.
\<close>

fun \<Phi> :: "'a queue \<Rightarrow> int" 
(*<*)
  where "\<Phi> (xs,ys) = undefined"
(*>*)

lemma \<Phi>_non_neg: "\<Phi> t \<ge> 0" sorry

lemma \<Phi>_init: "\<Phi> init = 0" sorry

lemma a_enq: " t_enq a q + \<Phi>(enq a q) - \<Phi> q \<le> 3" sorry

lemma a_deq: " t_deq q + \<Phi>(deq q) - \<Phi> q \<le> 0" sorry

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
  "t_execute q _ = undefined"
  
  
lemma t_execute_aux: "t_execute q ops \<le> 3*length ops + \<Phi> q - \<Phi> (execute q ops)"
sorry  
  
lemma t_execute: "t_execute init ops \<le> 3*length ops"
sorry  
end

(*<*)  
end
(*>*)  
