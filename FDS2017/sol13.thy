(*<*)
theory sol13
imports "../../../Public/Thys/Skew_Heap"
begin
(*>*)
  
text {* \ExerciseSheet{13}{21.~7.~2017} *}
  
text  \<open>{
  \large\bf Presentation of Mini-Projects}

  You are invited, on a voluntary basis, to give a short presentation
  of your mini-projects in the tutorial on July 28.

  Depending on how many presentations we have, the time slots 
  will be 5 to 10 minutes, plus 2 minutes for questions.
    
  If you are interested, please write me a short email until Thursday, July 27.
\<close>  

(* FIXME: Should there be a hint about function "abs" for the use in \<Phi>? *)

text \<open>
\Exercise{Double-Ended Queues}

Design a double-ended queue where all operations have constant-time amortized
complexity. Prove functional correctness and constant-time amortized complexity.

For your proofs, it is enough to count the number of newly allocated list cells.
You may assume that operations @{term \<open>rev xs\<close>} and @{term \<open>xs@ys\<close>} allocate \<open>O(|xs|)\<close> 
cells.

Explanation: A double-ended queue is like a queue with two further operations:
Function \<open>enq_front\<close> adds an element at the front (whereas \<open>enq\<close> adds an element at the back).
Function \<open>deq_back\<close> removes an element at the back (whereas \<open>deq\<close> removes an element at the front).
Here is a formal specification where the double ended queue is just a list:
\<close>

abbreviation (input) enq_list :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"enq_list x xs \<equiv> xs @ [x]"

abbreviation (input) enq_front_list :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"enq_front_list x xs \<equiv> x # xs"

abbreviation (input) deq_list :: "'a list \<Rightarrow> 'a list" where
"deq_list xs \<equiv> tl xs"

abbreviation (input) deq_back_list :: "'a list \<Rightarrow> 'a list" where
"deq_back_list xs \<equiv> butlast xs"

text\<open>
Hint: You may want to start with the \<open>Queue\<close> implementation in \<open>Thys/Amortized_Examples\<close>.\<close>

(*<*)  
  
type_synonym 'a queue = "'a list * 'a list"
  
fun list_of :: "'a queue \<Rightarrow> 'a list" where
"list_of(xs,ys) = ys @ rev xs"

(*>*)

(*<*)

(* Definitions *)

definition init :: "'a queue" where
"init = ([],[])"

fun enq :: "'a \<Rightarrow> 'a queue \<Rightarrow> 'a queue" where
"enq x (xs,ys) = (x#xs, ys)"

fun enq_front :: "'a \<Rightarrow> 'a queue \<Rightarrow> 'a queue" where
"enq_front x (xs,ys) = (xs, x#ys)"

fun deq :: "'a queue \<Rightarrow> 'a queue" where
"deq (xs,ys) =
  (if ys = []
   then let n = length xs div 2
        in (take n xs, tl(rev (drop n xs)))
   else (xs, tl ys))"

fun deq_back :: "'a queue \<Rightarrow> 'a queue" where
"deq_back (xs,ys) =
  (if xs = []
   then let n = length ys div 2
        in (tl(rev (drop n ys)), take n ys)
   else (tl xs, ys))"

(*>*)
(* Functional Correctness *)

lemma "list_of init = []"
(*<*)  
  by (auto simp: init_def)
(*>*)

lemma "list_of(enq x q) = enq_list x (list_of q)"
(*<*)  
by(cases q) auto
(*>*)

lemma "list_of(enq_front x q) = enq_front_list x (list_of q)"
(*<*)  
by(cases q) auto
(*>*)

lemma "list_of q \<noteq> [] \<Longrightarrow> list_of(deq q) = deq_list (list_of q)"
(*<*)  
proof (cases q)
  case [simp]: (Pair a b)
    
  assume "list_of q \<noteq> []" 
  hence "\<not> length a \<le> length a div 2" and [simp]: "a\<noteq>[]" if "b=[]" using that
    by (cases a; auto)+

  then show ?thesis  
    by (auto simp: Let_def rev_drop rev_take tl_append2[symmetric] 
             simp del: tl_append2)
    
qed
(*>*)

(*<*)  
lemma rev_tl_butlast_rev: "rev (tl xs) = butlast(rev xs)"
by (metis One_nat_def butlast_conv_take drop_0 drop_Suc drop_rev rev_swap)

lemma butlast_append2: "b\<noteq>[] \<Longrightarrow> butlast (a@b) = a@butlast b"
  by (auto simp: butlast_append)
  
lemma [simp]: "b \<noteq> [] \<Longrightarrow> \<not> length b \<le> length b div 2" by (cases b) auto
(*>*)
    
lemma "list_of q \<noteq> [] \<Longrightarrow> list_of(deq_back q) = deq_back_list (list_of q)"
(*<*)  
  apply (cases q)
  apply (auto simp: Let_def rev_tl_butlast_rev butlast_append2[symmetric])
  done  
(*>*)


(*<*)
    
fun t_enq :: "'a \<Rightarrow> 'a queue \<Rightarrow> int" where
(*<*)  
"t_enq x (xs,ys) = 1"
(*>*)  

fun t_enq_front :: "'a \<Rightarrow> 'a queue \<Rightarrow> int" where
(*<*)  
"t_enq_front x (xs,ys) = 1"
(*>*)  


fun t_deq :: "'a queue \<Rightarrow> int" where
(*<*)  
"t_deq (xs,ys) =
  (if ys = []
   then let n = length xs div 2
        in int(n + (length xs - n))
   else 0)"
(*>*)  

fun t_deq_back :: "'a queue \<Rightarrow> int" where
(*<*)  
"t_deq_back (xs,ys) =
  (if xs = []
   then let n = length ys; m = n div 2
        in int((length ys - n) + n)
   else 0)"
(*>*)  

fun \<Phi> :: "'a queue \<Rightarrow> int" 
(*<*)  
  where
"\<Phi> (xs,ys) = abs(int(length xs) - int(length ys))"
(*>*)  

lemma "\<Phi> q \<ge> 0"
(*<*)  
by(cases q) simp
(*>*)  

lemma "\<Phi> init = 0"
(*<*)  
by(simp add: init_def)
(*>*)  

lemma "t_enq x q + \<Phi>(enq x q) - \<Phi> q \<le> 2"
(*<*)  
by(cases q) auto
(*>*)  

lemma "t_enq_front x q + \<Phi>(enq_front x q) - \<Phi> q \<le> 2"
(*<*)  
by(cases q) auto
(*>*)  

lemma "t_deq q + \<Phi>(deq q) - \<Phi> q \<le> 2"
(*<*)  
by(cases q) (auto simp: Let_def)
(*>*)  

lemma "t_deq_back q + \<Phi>(deq_back q) - \<Phi> q \<le> 2"
(*<*)  
by(cases q) (auto simp: Let_def)
(*>*)  

(*>*)  

(*<*)  
end
(*>*)
