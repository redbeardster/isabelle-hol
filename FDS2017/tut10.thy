(*<*)
theory tut10
imports 
    "../../../Public/Thys/Leftist_Heap"    
begin
(*>*)  
text {* \ExerciseSheet{10}{30.~6.~2017} *}

  
text \<open>
  \Exercise{Insert for Leftist Heap}

  \<^item> Define a function to directly insert an element into a leftist heap.
    Do not construct an intermediate heap like insert via meld does!
    
  \<^item> Show that your function is correct

  \<^item> Define a timing function for your insert function, and show that it is 
    linearly bounded by the rank of the tree.
\<close>  
  
fun lh_insert :: "'a::ord \<Rightarrow> 'a lheap \<Rightarrow> 'a lheap" 
  where
  "lh_insert a \<langle>\<rangle> = \<langle>1,\<langle>\<rangle>,a,\<langle>\<rangle>\<rangle>"
| "lh_insert a \<langle>h,l,b,r\<rangle> = (
    if a\<le>b then 
      node l a (lh_insert b r)
    else 
      node l b (lh_insert a r)
    )"  

find_theorems node ltree 
find_theorems node heap
find_theorems node mset_tree  

lemma mset_tree_node[simp]: 
  "mset_tree (node l a r) = mset_tree l + {#a#} + mset_tree r"
  unfolding node_def by auto
  
lemma mset_lh_insert[simp]: 
  shows "mset_tree (lh_insert x t) = mset_tree t + {# x #}"
  apply (induction x t rule: lh_insert.induct)
  apply (auto)  
  done  
  
declare heap_node[simp]    
    
lemma heap_lh_insert[intro, simp]: "heap t \<Longrightarrow> heap (lh_insert x t)"
  by (induction x t rule: lh_insert.induct) force+
  
lemma "heap t \<Longrightarrow> heap (lh_insert x t)"
  apply (induction x t rule: lh_insert.induct)
  subgoal by (simp)  
  subgoal by (force)
  done  
  
declare ltree_node[simp]    
    
lemma "ltree t \<Longrightarrow> ltree (lh_insert x t)"    
  by (induction x t rule: lh_insert.induct) auto

    
fun t_lh_insert :: "'a::ord \<Rightarrow> 'a lheap \<Rightarrow> nat" 
  where
  "t_lh_insert a \<langle>\<rangle> = 1"
| "t_lh_insert a \<langle>h,l,b,r\<rangle> = 1 + (
    if a\<le>b then 
      1+t_lh_insert b r
    else 
      1+t_lh_insert a r
    )"  
    
lemma "t_lh_insert x t \<le> 2*rank t + 1"
  by (induction x t rule: lh_insert.induct) auto

    
    
text \<open>
  \Exercise{Bootstrapping a Priority Queue}

  Given a generic priority queue implementation with
  \<open>O(1)\<close> \<open>empty\<close>, \<open>is_empty\<close> operations, \<open>O(f\<^sub>1 n)\<close> insert, 
  and \<open>O(f\<^sub>2 n)\<close> \<open>get_min\<close> and \<open>del_min\<close> operations.

  Derive an implementation with \<open>O(1)\<close> \<open>get_min\<close>, and the
  asymptotic complexities of the other operations unchanged!

  Hint: Store the current minimal element! As you know nothing 
    about \<open>f\<^sub>1\<close> and \<open>f\<^sub>2\<close>, you must not use \<open>get_min/del_min\<close> 
    in your new \<open>insert\<close> operation, and vice versa!
\<close>

text \<open>For technical reasons, you have to define the new implementations type 
      outside the locale!\<close>
datatype ('a,'s) bs_pq = Empty | Heap 'a 's 
  
locale Bs_Priority_Queue = 
  orig: Priority_Queue orig_empty orig_is_empty orig_insert orig_get_min orig_del_min orig_invar orig_mset
  for orig_empty orig_is_empty orig_insert orig_get_min orig_del_min orig_invar 
  and orig_mset :: "'s \<Rightarrow> 'a::linorder multiset"
begin
  text \<open>In here, the original implementation is available with the prefix \<open>orig\<close>, e.g. \<close>
  term orig_empty term orig_invar  
  thm orig.invar_empty  

  fun mset :: "('a,'s) bs_pq \<Rightarrow> 'a multiset" 
    where
    "mset Empty = {#}"
  | "mset (Heap a h) = orig_mset h"  
    
    
    
  definition empty :: "('a,'s) bs_pq" 
    where "empty = Empty"
      
  fun is_empty :: "('a,'s) bs_pq \<Rightarrow> bool" 
    where 
    "is_empty Empty \<longleftrightarrow> True"
  | "is_empty _ \<longleftrightarrow> False"
    
  fun insert :: "'a \<Rightarrow> ('a,'s) bs_pq \<Rightarrow> ('a,'s) bs_pq" 
    where
    "insert a Empty = Heap a (orig_insert a orig_empty)"
  | "insert a (Heap b h) = Heap (min a b) (orig_insert a h)"  
    
  fun get_min :: "('a,'s) bs_pq \<Rightarrow> 'a" 
    where
    "get_min (Heap a _) = a"

  fun del_min :: "('a,'s) bs_pq \<Rightarrow> ('a,'s) bs_pq" 
    where
    "del_min (Heap a h) = (let 
      h = orig_del_min h in 
      if orig_is_empty h then
        Empty
      else
        Heap (orig_get_min h) h
    )"
    
  fun invar :: "('a,'s) bs_pq \<Rightarrow> bool" where 
      "invar Empty = True"
    | "invar (Heap a h) 
      \<longleftrightarrow> orig_invar h 
        \<and> orig_mset h \<noteq> {#} 
        \<and> a = Min_mset (orig_mset h)"
    
  text \<open>Show that your new implementation satisfies the priority queue interface!\<close>  
  sublocale Priority_Queue empty is_empty insert get_min del_min invar mset  
    apply unfold_locales
  proof goal_cases
    case 1
    then show ?case by (auto simp: empty_def)
  next
    case (2 q)
    then show ?case by (cases q) (auto)
  next
    case (3 q x)
    then show ?case by (cases q) (auto)
  next
    case (4 q)
    then show ?case by (cases q) (auto)
  next
    case (5 q)
    then show ?case by (cases q) (auto)
  next
    case 6
    then show ?case by (auto simp: empty_def)
  next
    case (7 q x)
    then show ?case by (cases q) (auto)
  next
    case (8 q)
    then show ?case by (cases q) (auto)
  qed
end
  
text\<open>
\Homework{Constructing a Heap from a List of Elements}{7.~7.~2017}

The naive solution of starting with the empty heap and inserting the elements one by one
can be improved by repeatedly merging heaps of roughly equal size.
Start by turning the list of elements into a list of singleton heaps.
Now make repeated passes over the list,
merging adjacent pairs of heaps in each pass (thus halving the list length)
until only a single heap is left.
It can be shown that this takes linear time.

Define a function \<open>heap_of_list ::\<close> @{typ "'a list \<Rightarrow> 'a lheap"} and prove its functional
correctness.
\<close>

  
definition heap_of_list :: "'a::ord list \<Rightarrow> 'a lheap" 
  where "heap_of_list _ = undefined"

lemma mset_heap_of_list: "mset_tree (heap_of_list xs) = mset xs"
  sorry
  
lemma heap_heap_of_list: "heap (heap_of_list xs)"  
  sorry
    
lemma ltree_ltree_of_list: "ltree (heap_of_list xs)"  
  sorry
    
(*<*)
end
(*>*)
