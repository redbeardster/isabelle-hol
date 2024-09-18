(*<*)
theory tut13
imports "../../../Public/Thys/Skew_Heap"
  Complex_Main
begin
(*>*)
  
text {* \ExerciseSheet{13}{21.~7.~2017} *}
  
  
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

type_synonym 'a queue = "'a list \<times> 'a list"
  
fun list_of :: "'a queue \<Rightarrow> 'a list" where
  "list_of (xs,ys) = ys@rev xs"
  
(* Definitions *)

definition init :: "'a queue"
  where "init = ([],[])"
  
    
fun enq :: "'a \<Rightarrow> 'a queue \<Rightarrow> 'a queue"
  where "enq x (xs,ys) = (x#xs,ys)" 

fun enq_front :: "'a \<Rightarrow> 'a queue \<Rightarrow> 'a queue"
  where "enq_front x (xs,ys) = (xs,x#ys)"
  
fun deq :: "'a queue \<Rightarrow> 'a queue"
  where "deq (xs,ys) = (
    if ys=[] then 
      let n = length xs div 2 in
        (take n xs, tl (rev (drop n xs))) 
    else (xs,tl ys))"

fun deq_back :: "'a queue \<Rightarrow> 'a queue"
  where "deq_back (xs,ys) = (
    if xs=[] then
      let n = length ys div 2 in
        (tl (rev (drop n ys)), take n ys) 
    else (tl xs,ys)
  )"

lemma "list_of init = []"
  by (auto simp: init_def)

lemma "list_of(enq x q) = enq_list x (list_of q)"
  by (cases q) auto

lemma "list_of(enq_front x q) = enq_front_list x (list_of q)"
  by (cases q) auto

lemma X1: "\<not> length a \<le> length a div 2" if "a\<noteq>[]" for a :: "'a list"  
  using that by (cases a) auto 

lemma 
  fixes q :: "'a queue"
  shows "list_of q \<noteq> [] \<Longrightarrow> list_of(deq q) = deq_list (list_of q)"
proof -
  assume A: "list_of q \<noteq> []"
  
    
  note [simp del] = tl_append2 rev_append    
  note [symmetric,simp] = tl_append2 rev_append    
      
  from A show ?thesis
    apply (cases q)
    by (auto simp: Let_def X1 )
qed      
  
lemma [simp]: "rev (tl a) = butlast (rev a)"
  by (induction a) auto
  
lemma butlast_append2: "b\<noteq>[] \<Longrightarrow> a@butlast b = butlast (a@b)"
  by (auto simp: butlast_append)
    
  
lemma "list_of q \<noteq> [] \<Longrightarrow> list_of(deq_back q) = deq_back_list (list_of q)"
  apply (cases q)
  apply (auto simp: Let_def butlast_append2 X1)
  done  
  
    
(* Define timing functions, counting number of allocated list cells *)

fun t_enq :: "'a \<Rightarrow> 'a queue \<Rightarrow> nat"
  where "t_enq x (xs,ys) = 1" 

fun t_enq_front :: "'a \<Rightarrow> 'a queue \<Rightarrow> nat"
  where "t_enq_front x (xs,ys) = 1"
  
fun t_deq :: "'a queue \<Rightarrow> nat"
  where "t_deq (xs,ys) = (
    if ys=[] then length xs else 0)"

fun t_deq_back :: "'a queue \<Rightarrow> nat"
  where "t_deq_back (xs,ys) = (
    if xs=[] then length ys else 0
  )"
    
(* Define \<Phi>, and show the standard lemmas, and estimate the amortized 
  complexity of the operations to be constant time *)    

fun \<Phi> :: "'a queue \<Rightarrow> int" where 
  "\<Phi> (xs,ys) = abs (length xs - int (length ys))"
  
lemma "\<Phi> init = 0" unfolding init_def by auto  
lemma "\<Phi> q \<ge> 0" by (cases q) auto  
  
lemma a_enq: "t_enq x q + \<Phi> (enq x q) - \<Phi> q \<le> 2"
  apply (cases q) apply auto done
lemma a_enq_front: "t_enq_front x q + \<Phi> (enq_front x q) - \<Phi> q \<le> 2"
  apply (cases q) apply auto done
  
lemma a_deq: "t_deq q + \<Phi> (deq q) - \<Phi> q \<le> 1"
  apply (cases q) apply (auto simp: Let_def) done
    
lemma a_deq_front: "t_deq_back q + \<Phi> (deq_back q) - \<Phi> q \<le> 1"
  apply (cases q) apply (auto simp: Let_def) done
    
    
text \<open>
  \Homework{Pairing Heap}{28.~07.~2017}

The datatype of pairing heaps defined in the theory \verb!Thys/Pairing_Heap!
comes with the unstated invariant that \<open>Empty\<close> occurs only at the root.
We can avoid this invariant by a slightly different representation:
\<close>

datatype 'a hp = Hp 'a "'a hp list"
type_synonym 'a heap = "'a hp option"

text \<open>Carry out the development with this new representation. 
Restrict  yourself to the \<open>get_min\<close> and \<open>delete_min\<close> operations.
That is, define the following functions (and any auxiliary function required)
\<close>

consts get_min  :: "('a :: linorder) heap \<Rightarrow> 'a"

consts del_min :: "'a :: linorder heap \<Rightarrow> 'a heap"

consts php :: "('a :: linorder) hp \<Rightarrow> bool" 

consts mset_hp :: "'a hp \<Rightarrow>'a multiset" 
consts mset_heap :: "'a heap \<Rightarrow>'a multiset" 

(* HINT: Start with a copy of the original lemmas, and modify as needed *)  
  
theorem get_min_in: "php h \<Longrightarrow> get_min (Some h) \<in> set_hp(h)" 
  oops

lemma get_min_min: "\<lbrakk> php h; x \<in> set_hp(h) \<rbrakk> \<Longrightarrow> get_min (Some h) \<le> x"
  oops
  
lemma mset_del_min: 
  "php h \<Longrightarrow> mset_heap (del_min (Some h)) = mset_hp h - {#get_min(Some h)#}"
  oops

(*<*)  
end
(*>*)
