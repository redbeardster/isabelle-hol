(*<*)
theory tmpl06
  imports 
    Complex_Main 
    "~~/src/HOL/Library/Multiset" 
begin

(* From Sorting.thy *)  
hide_const List.sorted List.insort List.insort_key

fun sorted :: "'a::linorder list \<Rightarrow> bool" where
"sorted [] = True" |
"sorted (x # xs) = ((\<forall>y\<in>set xs. x \<le> y) & sorted xs)"

lemma sorted_append:
  "sorted (xs@ys) = (sorted xs & sorted ys & (\<forall>x \<in> set xs. \<forall>y \<in> set ys. x\<le>y))"
by (induct xs) (auto)
  
  
(*>*)
  
text {* \ExerciseSheet{6}{2.~6.~2017} *}

text \<open>\Exercise{Selection Sort}
  Selection sort (also known as MinSort) sorts a list by repeatedly moving 
  the smallest element of the remaining list to the front.
\<close>  
  

text \<open>
  Define a function that takes a non-empty list, and returns the minimum 
  element and the list with the minimum element removed
\<close>
consts find_min :: "'a::linorder list \<Rightarrow> 'a \<times> 'a list" (* Use fun here! *)
    
text \<open>Show that \<open>find_min\<close> returns the minimum element\<close>  
lemma find_min_min: 
  assumes "find_min xs = (y,ys)"
  assumes "xs\<noteq>[]"  
  shows "a\<in>set xs \<Longrightarrow> y \<le> a"  
  oops
    
text \<open>Show that \<open>find_min\<close> returns exactly the elements from the list\<close>
lemma find_min_mset: 
  assumes "find_min xs = (y,ys)"
  assumes "xs\<noteq>[]"  
  shows "mset xs = add_mset y (mset ys)"  
  oops
      
text \<open>Show the following lemma on the length of the returned list, and register it as \<open>[dest]\<close>.
     The function package will require this to show termination of the selection sort function\<close>
lemma find_min_snd_len_decr[dest]: 
  assumes "(y,ys) = find_min (x#xs)"
  shows "length ys < length (x#xs)"
  sorry

text \<open>Selection sort can now be written as follows:\<close>
fun sel_sort where
  "sel_sort [] = []"
| "sel_sort xs = (let (y,ys) = find_min xs in y#sel_sort ys)"
    
text \<open>Show that selection sort is a sorting algorithm:\<close>
lemma sel_sort_mset[simp]: "mset (sel_sort xs) = mset xs"  
  oops
      
lemma "sorted (sel_sort xs)"
  oops
    
text \<open>Define cost functions for the number of comparisons of \<open>find_min\<close> and \<open>sel_sort\<close>. \<close>
      
  fun c_find_min :: "'a list \<Rightarrow> nat" 
  where
    "c_find_min _ = undefined"

  fun c_sel_sort :: "'a list \<Rightarrow> nat"
  where
    "c_sel_sort _ = undefined"
    
  text \<open>Try to find a closed formula for \<open>c_sel_sort\<close>! 
    If you do not succeed, try to find a good estimate. (Hint: Should be \<open>O(n\<^sup>2)\<close>)

    To find a closed formula: On paper: 
      \<^item> Put up a recurrence equation (depending only on the length of the list)
      \<^item> Solve the equation (Assume that the solution is an order-2 polynomial)
    In Isabelle:
      \<^item> Insert the solution into the lemma below, and try to prove it
  \<close>  
  lemma c_sel_sort_cmpx: "c_sel_sort xs = undefined" oops
    
  (* Mention: Alternative solution: Explicit recurrence equation! *)  
      
text \<open>\Homework{Quicksort}{2.~6.~2017}
  We extend the notion of a sorting algorithm, by 
  providing a key function that maps the actual list elements to a linearly 
  ordered type. The elements shall be sorted according to their keys.
\<close>

fun sorted_key :: "('a \<Rightarrow> 'b::linorder) \<Rightarrow> 'a list \<Rightarrow> bool" where
  "sorted_key k [] = True"
| "sorted_key k (x # xs) = ((\<forall>y\<in>set xs. k x \<le> k y) & sorted_key k xs)"

text \<open>Quicksort can be defined as follows: 
  (Note that we use \<open>nat\<close> for the keys, as this causes less trouble when 
  writing Isar proofs than a generic \<open>'b::linorder\<close>)\<close>
fun qsort :: "('a \<Rightarrow> nat) \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "qsort k [] = []"
| "qsort k (p#xs) = qsort k [x\<leftarrow>xs. k x<k p]@p#qsort k [x\<leftarrow>xs. \<not>k x<k p]"
text \<open>The syntax @{term \<open>[x\<leftarrow>xs. P x]\<close>} is a shortcut 
  notation for @{term \<open>filter (\<lambda>x. P x) xs\<close>}.\<close>
  
text \<open>Show that quicksort is a sorting algorithm:\<close>  
lemma qsort_preserves_mset: "mset (qsort k xs) = mset xs"
  sorry
       
lemma qsort_sorts: "sorted_key k (qsort k xs)"
  sorry


text \<open>The following is a cost function for the comparsions of quicksort: \<close>    
fun c_qsort :: "('a \<Rightarrow> nat) \<Rightarrow> 'a list \<Rightarrow> nat" where
  "c_qsort k [] = 0"
| "c_qsort k (p#xs) 
    = c_qsort k [x\<leftarrow>xs. k x<k p] + c_qsort k [x\<leftarrow>xs. k x\<ge>k p] + 2*length xs"


text \<open>Show that the number of required comparisons is at most \<open>(length xs)\<^sup>2\<close>.

  Hints: 
    \<^item> Do an induction on the length of the list,
      and, afterwards, a case distinction on the list constructors.
    \<^item> It might be useful to prove \<open>a\<^sup>2+b\<^sup>2 \<le> (a+b)\<^sup>2\<close> for \<open>a b :: nat\<close>
    \<^item> Have a look at the lemma @{thm [source] sum_length_filter_compl}
\<close>  
  
lemmas length_induct_rule = measure_induct_rule[where f=length, case_names shorter]
  
lemma "c_qsort k xs \<le> (length xs)\<^sup>2"
proof (induction xs rule: length_induct_rule)
  case (shorter xs) thm shorter.IH
  show ?case proof (cases xs)
    case Nil
    then show ?thesis by auto
  next
    case (Cons x xs')
    text \<open>Insert your proof here\<close>  
    show ?thesis sorry  
  qed
qed
    
text \<open>For 3 bonus points, show that quicksort is stable. 
  You will probably run into subgoals containing terms like  
  @{term \<open>[x\<leftarrow>xs . k x < k p \<and> k x = a]\<close>}.
  Try to find a simpler form for them. (Cases on \<open>a<k p\<close>)!
\<close>     
lemma qsort_stable: "[x\<leftarrow>qsort k xs . k x = a] = [x\<leftarrow>xs . k x = a]"  sorry
    
(*<*)
end
(*>*)
