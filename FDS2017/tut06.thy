(*<*)
theory tut06
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
fun find_min :: "'a::linorder list \<Rightarrow> 'a \<times> 'a list" (* Use fun here! *)
  where 
    "find_min [x] = (x,[])"
  | "find_min (x#xs) = (let 
        (y,ys) = find_min xs 
      in 
        if x<y then (x,y#ys)
        else (y,x#ys)
    )" 
  | "find_min [] = undefined"  
    
fun find_min' :: "'a::linorder list \<Rightarrow> 'a \<times> 'a list" (* Use fun here! *)
  where 
    "find_min' [x] = (x,[])"
  | "find_min' (x#xs) = (let 
        (y,ys) = find_min' xs 
      in 
        if x<y then (x,xs)
        else (y,x#ys)
    )" 
  | "find_min' [] = undefined"  

lemma find_min_min': 
  assumes "find_min' xs = (y,ys)"
  assumes "xs\<noteq>[]"  
  shows "a\<in>set xs \<Longrightarrow> y \<le> a"  
  using assms  
  apply (induction xs arbitrary: y ys rule: find_min'.induct)
  apply (fastforce split: prod.splits if_splits)+
  done  
    
    
text \<open>Show that \<open>find_min\<close> returns the minimum element\<close>  
lemma find_min_min: 
  assumes "find_min xs = (y,ys)"
  assumes "xs\<noteq>[]"  
  shows "a\<in>set xs \<Longrightarrow> y \<le> a"  
  using assms  
  apply (induction xs arbitrary: y ys rule: find_min.induct)
  apply (fastforce split: if_splits prod.splits)+
  done  

    
    
text \<open>Show that \<open>find_min\<close> returns exactly the elements from the list\<close>
lemma find_min_mset: 
  assumes "find_min xs = (y,ys)"
  assumes "xs\<noteq>[]"  
  shows "mset xs = add_mset y (mset ys)"  
  using assms  
  apply (induction xs arbitrary: y ys rule: find_min.induct)
  apply (fastforce split: prod.splits if_splits)+
  done  

lemma find_min_set:    
  assumes "find_min xs = (y,ys)"
  assumes "xs\<noteq>[]"  
  shows "set xs = insert y (set ys)"  
  using find_min_mset[OF assms]
  by (metis set_mset_add_mset_insert set_mset_mset)  
    
    
lemma find_min_mset': 
  assumes "find_min' xs = (y,ys)"
  assumes "xs\<noteq>[]"  
  shows "mset xs = add_mset y (mset ys)"  
  using assms  
  apply (induction xs arbitrary: y ys rule: find_min'.induct)
  apply (fastforce split: prod.splits if_splits)+
  done  
    
    
text \<open>Show the following lemma on the length of the returned list, and register it as \<open>[dest]\<close>.
     The function package will require this to show termination of the selection sort function\<close>
lemma find_min_snd_len_decr[dest]: 
  assumes "(y,ys) = find_min (x#xs)"
  shows "length ys < length (x#xs)"
  using assms  
  apply (induction xs arbitrary: x y ys)
  apply (auto split: prod.splits if_splits)
  apply metis+
  done  

lemma find_min_snd_len_decr'[dest]: 
  assumes "(y,ys) = find_min' (x#xs)"
  shows "length ys < length (x#xs)"
  using assms  
  apply (induction xs arbitrary: y ys rule: find_min'.induct)
  apply (auto split: prod.splits if_splits)
  done  
    
    
text \<open>Selection sort can now be written as follows:\<close>
fun sel_sort where
  "sel_sort [] = []"
| "sel_sort xs = (let (y,ys) = find_min xs in y#sel_sort ys)"
    
text \<open>Show that selection sort is a sorting algorithm:\<close>
lemma sel_sort_mset[simp]: "mset (sel_sort xs) = mset xs"  
  apply (induction xs rule: sel_sort.induct)
  apply (auto split: prod.split)
  using find_min_mset by force  
(*
  apply (drule find_min_mset)  
  apply simp
  apply simp  
  thm find_min_mset  
  apply (subst find_min_mset)
  apply assumption  
  using find_min_mset  
  apply (force split: prod.split)+ 
  done  
*)

lemma sel_sort_set[simp]: "set (sel_sort xs) = set xs"  
  apply (rule mset_eq_setD) by simp
    
    
lemma "sorted (sel_sort xs)"
proof (induction xs rule: sel_sort.induct)
  case 1
  then show ?case by auto
next
  case (2 v va)
  
  obtain y ys where A[simp]: "find_min (v # va) = (y, ys)" 
    by (cases "find_min (v # va)") 

  note IH = "2.IH"[OF refl, OF sym, OF A]  
      
  have "set ys \<subseteq> set (v#va)" using find_min_set[OF A]
    by auto  
  then have G1: "a \<in> set ys \<Longrightarrow> y \<le> a" for a    
    using find_min_min[OF A] by auto   
    
  show ?case
    by (auto split: prod.split simp: G1 IH)
qed  
  
    
text \<open>Define cost functions for the number of comparisons of \<open>find_min\<close> and \<open>sel_sort\<close>. \<close>

  fun c_find_min :: "'a list \<Rightarrow> nat" 
  where
    "c_find_min [x] = 0"
  | "c_find_min (x#xs) = c_find_min xs + 1" 

  fun c_sel_sort :: "'a::linorder list \<Rightarrow> nat"
  where
    "c_sel_sort [] = 0"
  | "c_sel_sort xs = (
      let (y,ys) = find_min xs in 
        c_find_min xs + c_sel_sort ys)"

  lemma c_find_min_len: "xs \<noteq> [] \<Longrightarrow> c_find_min xs = length xs - 1"  
    by (induction xs rule: c_find_min.induct) auto
    
  text \<open>Try to find a closed formula for \<open>c_sel_sort\<close>! 
    If you do not succeed, try to find a good estimate. (Hint: Should be \<open>O(n\<^sup>2)\<close>)

    To find a closed formula: On paper: 
      \<^item> Put up a recurrence equation (depending only on the length of the list)
      \<^item> Solve the equation (Assume that the solution is an order-2 polynomial)
    In Isabelle:
      \<^item> Insert the solution into the lemma below, and try to prove it
  \<close>  
    
  lemma c_sel_sort_cmpx: "c_sel_sort xs = ((length xs)\<^sup>2 - length xs) / 2"
  proof (induction xs rule: c_sel_sort.induct)
    case 1
    then show ?case by auto
  next
    case (2 v va)
      
    obtain y ys where A[simp]: "find_min (v # va) = (y, ys)" 
      by (cases "find_min (v # va)") 
  
    from A have LEN_VA: "length va = length ys"
      apply (induction va arbitrary: v y ys)
      apply (auto split: prod.splits if_splits)   
      done  
        
    note IH = "2.IH"[OF refl, OF sym, OF A]  

    (*
      An argument was missing that \<open>real (a\<^sup>2 - a)\<close> can be split:
    *)  
    have AUX: "real (a\<^sup>2 - a) = (real a)\<^sup>2 - real a" for a :: nat
    proof -
      have "a\<^sup>2 \<ge> a" by (auto simp: eval_nat_numeral)
      from of_nat_diff[OF this] show ?thesis by simp    
    qed
      
    have "(c_sel_sort (v # va)) = c_find_min (v # va) + c_sel_sort ys"  
      by simp
    also have "\<dots> = length va + c_sel_sort ys" by (simp add: c_find_min_len)
    also have "\<dots> = length va + ((length va)\<^sup>2 - length va) / 2" by (simp add: IH LEN_VA)
    also have "\<dots> = (2*(length va) + (length va)\<^sup>2 - length va) / 2" 
      by (simp add: field_simps AUX)
    also have "\<dots> = ((length (v # va))\<^sup>2 - length (v # va)) / 2"        
      by (simp add: field_simps eval_nat_numeral)
    finally show ?case .
  qed  
    
    
(*<*)
end
(*>*)
