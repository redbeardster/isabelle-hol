(*<*)
theory tmpl10
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
  "lh_insert _ _ = undefined"
  
lemma mset_lh_insert: "mset_tree (lh_insert x t) = mset_tree t + {# x #}"
  oops
  
lemma "heap t \<Longrightarrow> heap (lh_insert x t)"
  oops
    
lemma "ltree t \<Longrightarrow> ltree (lh_insert x t)"    
  oops
    
fun t_lh_insert :: "'a::ord \<Rightarrow> 'a lheap \<Rightarrow> nat" 
  where
  "t_lh_insert _ _ = undefined"
    
lemma "t_lh_insert x t \<le> rank t + 1"
  oops  
    
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
datatype ('a,'s) bs_pq = Foo_Bar 

locale Bs_Priority_Queue = 
  orig: Priority_Queue orig_empty orig_is_empty orig_insert orig_get_min orig_del_min orig_invar orig_mset
  for orig_empty orig_is_empty orig_insert orig_get_min orig_del_min orig_invar 
  and orig_mset :: "'s \<Rightarrow> 'a::linorder multiset"
begin
  text \<open>In here, the original implementation is available with the prefix \<open>orig\<close>, e.g. \<close>
  term orig_empty term orig_invar  
  thm orig.invar_empty  
  
  definition empty :: "('a,'s) bs_pq" 
    where "empty = undefined"
      
  fun is_empty :: "('a,'s) bs_pq \<Rightarrow> bool" 
    where 
    "is_empty _ \<longleftrightarrow> undefined"
    
  fun insert :: "'a \<Rightarrow> ('a,'s) bs_pq \<Rightarrow> ('a,'s) bs_pq" 
    where
    "insert _ _ = undefined"
    
  fun get_min :: "('a,'s) bs_pq \<Rightarrow> 'a" 
    where
    "get_min _ = undefined"

  fun del_min :: "('a,'s) bs_pq \<Rightarrow> ('a,'s) bs_pq" 
    where
    "del_min _ = undefined"
    
  fun invar :: "('a,'s) bs_pq \<Rightarrow> bool" where 
      "invar _ = undefined"
    
  fun mset :: "('a,'s) bs_pq \<Rightarrow> 'a multiset" 
    where
    "mset _ = undefined"
    
  text \<open>Show that your new implementation satisfies the priority queue interface!\<close>  
  sublocale Priority_Queue empty is_empty insert get_min del_min invar mset  
    apply unfold_locales
  proof goal_cases
    case 1
    then show ?case sorry
  next
    case (2 q)
    then show ?case sorry
  next
    case (3 q x)
    then show ?case sorry
  next
    case (4 q)
    then show ?case sorry
  next
    case (5 q)
    then show ?case sorry
  next
    case 6
    then show ?case sorry
  next
    case (7 q x)
    then show ?case sorry
  next
    case (8 q)
    then show ?case sorry
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
