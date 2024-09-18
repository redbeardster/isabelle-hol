(*<*)
theory sol10
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
(*<*)  
  where
  "lh_insert x \<langle>\<rangle> = \<langle>1,\<langle>\<rangle>,x,\<langle>\<rangle>\<rangle>"
| "lh_insert x \<langle>s,l,y,r\<rangle> = (
    if x\<le>y then node l x (lh_insert y r)
    else node l y (lh_insert x r)
)"  
(*>*)  
  
lemma mset_lh_insert: "mset_tree (lh_insert x t) = mset_tree t + {# x #}"
(*<*)  
  apply (induction t arbitrary: x)
  apply (auto simp: node_def)
  done  
(*>*)
  
lemma "heap t \<Longrightarrow> heap (lh_insert x t)"
(*<*)  
  by (induction t arbitrary: x) (auto simp: node_def ball_Un mset_lh_insert)  
(*>*)
    
lemma "ltree t \<Longrightarrow> ltree (lh_insert x t)"    
(*<*)  
  apply (induction t arbitrary: x)
  apply (auto simp: node_def)  
  done
(*>*)

    
fun t_lh_insert :: "'a::ord \<Rightarrow> 'a lheap \<Rightarrow> nat" 
(*<*)  
  where
  "t_lh_insert x \<langle>\<rangle> = 1"
| "t_lh_insert x \<langle>s,l,y,r\<rangle> = 1 + (
    if x\<le>y then t_lh_insert y r
    else (t_lh_insert x r)
)"  
(*>*)
    
lemma "t_lh_insert x t \<le> rank t + 1"
(*<*)  
  by (induction t arbitrary: x) auto  
(*>*)
  
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
datatype ('a,'s) bs_pq = (*<*)Empty | Heap 'a 's(*>*)

locale Bs_Priority_Queue = 
  orig: Priority_Queue orig_empty orig_is_empty orig_insert orig_get_min orig_del_min orig_invar orig_mset
  for orig_empty orig_is_empty orig_insert orig_get_min orig_del_min orig_invar 
  and orig_mset :: "'s \<Rightarrow> 'a::linorder multiset"
begin
  text \<open>In here, the original implementation is available with the prefix \<open>orig\<close>, e.g. \<close>
  term orig_empty term orig_invar  
  thm orig.invar_empty  
  
  definition empty :: "('a,'s) bs_pq" 
  (*<*)  
    where "empty = Empty"
  (*>*)    
      
  fun is_empty :: "('a,'s) bs_pq \<Rightarrow> bool" 
  (*<*)  
    where 
    "is_empty Empty \<longleftrightarrow> True"
  | "is_empty (Heap _ _) \<longleftrightarrow> False"
  (*>*)    
    
  fun insert :: "'a \<Rightarrow> ('a,'s) bs_pq \<Rightarrow> ('a,'s) bs_pq" 
  (*<*)  
    where
    "insert x Empty = Heap x orig_empty"
  | "insert x (Heap m h) = (if x<m then Heap x (orig_insert m h) else Heap m (orig_insert x h))"
  (*>*)    
    
  fun get_min :: "('a,'s) bs_pq \<Rightarrow> 'a" 
  (*<*)  
    where
    "get_min (Heap m _) = m"
  (*>*)    

  fun del_min :: "('a,'s) bs_pq \<Rightarrow> ('a,'s) bs_pq" 
  (*<*)  
    where
    "del_min (Heap m h) = (
      if orig_is_empty h then Empty
      else Heap (orig_get_min h) (orig_del_min h)
      )"
  (*>*)    
    
  fun invar :: "('a,'s) bs_pq \<Rightarrow> bool" 
  (*<*)  
    where
    "invar Empty = True"
  | "invar (Heap m h) = (orig_invar h \<and> (\<forall>x\<in>#orig_mset h. m\<le>x))"
  (*>*)    
    
  fun mset :: "('a,'s) bs_pq \<Rightarrow> 'a multiset" 
  (*<*)  
    where
    "mset Empty = {#}"
  | "mset (Heap m h) = add_mset m (orig_mset h)"
  (*>*)    
    
  text \<open>Show that your new implementation satisfies the priority queue interface!\<close>  
  sublocale Priority_Queue empty is_empty insert get_min del_min invar mset  
    apply unfold_locales
  proof goal_cases
    case 1
    then show ?case 
  (*<*)  
      by (simp add: empty_def)
  (*>*)    
  next
    case (2 q) -- \<open>and so on\<close>
  (*<*)  
    then show ?case by (cases q) auto
  next
    case (3 q x)
    then show ?case by (cases q) (auto)
  next
    case (4 q)
    then show ?case by (cases q; auto simp: min_def)
  next
    case (5 q)
    then show ?case 
      by (cases q; simp add: Min_mset_alt)
  next
    case 6
    then show ?case by (simp add: empty_def)
  next
    case (7 q x)
    then show ?case by (cases q; auto)
  next
    case (8 q)
    then show ?case by (cases q) (auto dest: in_diffD)
  (*>*)    
  qed
end
  
    
(*<*)
end
(*>*)
