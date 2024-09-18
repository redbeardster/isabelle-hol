(*<*)
theory tmpl13
imports "../../../Public/Thys/Skew_Heap"
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

type_synonym 'a queue = unit
  
consts list_of :: "'a queue \<Rightarrow> 'a list" 
  
(* Definitions *)

consts 
  init :: "'a queue"
  enq :: "'a \<Rightarrow> 'a queue \<Rightarrow> 'a queue"
  enq_front :: "'a \<Rightarrow> 'a queue \<Rightarrow> 'a queue"
  deq :: "'a queue \<Rightarrow> 'a queue"
  deq_back :: "'a queue \<Rightarrow> 'a queue"

lemma "list_of init = []" oops

lemma "list_of(enq x q) = enq_list x (list_of q)" oops

lemma "list_of(enq_front x q) = enq_front_list x (list_of q)" oops

lemma "list_of q \<noteq> [] \<Longrightarrow> list_of(deq q) = deq_list (list_of q)" oops

lemma "list_of q \<noteq> [] \<Longrightarrow> list_of(deq_back q) = deq_back_list (list_of q)" oops

    
(* Define timing functions, counting number of allocated list cells *)

(* Define \<Phi>, and show the standard lemmas, and estimate the amortized 
  complexity of the operations to be constant time *)    

  
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
