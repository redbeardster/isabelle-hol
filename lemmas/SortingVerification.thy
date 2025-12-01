theory SortingVerification
imports Main "HOL-Library.Multiset"
begin

definition is_sorted :: "'a::linorder list \<Rightarrow> bool" where
  "is_sorted xs \<equiv> \<forall>i j. i < j \<and> j < length xs \<longrightarrow> xs!i \<le> xs!j"

definition is_permutation :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "is_permutation xs ys \<equiv> mset xs = mset ys"

 lemma example_permutation:
  "is_permutation [1,2,3] [3,2,1]"
  unfolding is_permutation_def
  by simp
 
(* Способ 1: Используем simp с multiset_eq_iff *)

 lemma example_not_permutation_eval:
  "\<not> is_permutation [1::nat,2,3] [1,2,4]"
  unfolding is_permutation_def
  by eval
 
definition correct_sort :: "('a::linorder list \<Rightarrow> 'a list) \<Rightarrow> bool" where
  "correct_sort sort_fn \<equiv> \<forall>xs. is_sorted (sort_fn xs) \<and> is_permutation (sort_fn xs) xs"

(* Определяем quicksort с завершением *)
function quicksort :: "'a::linorder list \<Rightarrow> 'a list" where
  "quicksort [] = []"
| "quicksort (x#xs) = 
    quicksort [y \<leftarrow> xs. y < x] @ [x] @ quicksort [y \<leftarrow> xs. y \<ge> x]"
  by pat_completeness auto

(* Доказываем termination *)
termination quicksort
  apply (relation "measure length")
  apply auto
   apply (simp add: le_imp_less_Suc)
  by (simp add: less_Suc_eq_le)

lemma quicksort_permutation_simple:
  "is_permutation (quicksort xs) xs"
proof (induction xs rule: length_induct)
  case (1 xs)
  show ?case
  proof (cases xs)
    case Nil
    then show ?thesis
      unfolding is_permutation_def by simp
  next
    case (Cons x xs')
    have "mset (quicksort (x#xs')) = 
          mset (quicksort [y\<leftarrow>xs'. y < x]) + mset [x] + mset (quicksort [y\<leftarrow>xs'. y \<ge> x])"
      by (simp add: mset_append)
    also have "... = mset [y\<leftarrow>xs'. y < x] + {#x#} + mset [y\<leftarrow>xs'. y \<ge> x]"
      using 1[rule_format, of "[y\<leftarrow>xs'. y < x]"] 1[rule_format, of "[y\<leftarrow>xs'. y \<ge> x]"] Cons
    by (metis impossible_Cons is_permutation_def length_filter_le linorder_not_less mset_single_iff order_trans)
    also have "... = mset (x#xs')"
      using mset_filter 
    by (simp add: add.commute linorder_not_less)
    finally show ?thesis
      unfolding Cons is_permutation_def .
  qed
qed



end
