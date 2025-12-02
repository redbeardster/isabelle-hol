theory SeparationLogicTutorial
imports
  Main
  "HOL-Hoare.Hoare_Logic"
begin

section \<open>Часть 1: Основы сепарационной логики\<close>

subsection \<open>Базовые определения\<close>

type_synonym heap = "nat \<rightharpoonup> nat"
type_synonym assn = "heap \<Rightarrow> bool"

definition emp :: assn where
  "emp h \<equiv> (h = Map.empty)"

definition points_to :: "nat \<Rightarrow> nat \<Rightarrow> assn" where
  "points_to x v h \<equiv> (h = [x \<mapsto> v])"

\<comment> \<open>Определение непересекающихся куч\<close>
definition heaps_disjoint :: "heap \<Rightarrow> heap \<Rightarrow> bool" where
  "heaps_disjoint h1 h2 \<equiv> dom h1 \<inter> dom h2 = {}"

\<comment> \<open>Сепарационная конъюнкция - без infix notation сначала\<close>
definition sep_conj :: "assn \<Rightarrow> assn \<Rightarrow> assn" where
  "sep_conj P Q = (\<lambda>h. \<exists>h1 h2. heaps_disjoint h1 h2 \<and> h = h1 ++ h2 \<and> P h1 \<and> Q h2)"

\<comment> \<open>Теперь объявляем инфиксную нотацию\<close>
notation sep_conj (infixr "**" 35)

definition sep_impl :: "assn \<Rightarrow> assn \<Rightarrow> assn" where  
  "sep_impl P Q = (\<lambda>h. \<forall>h'. heaps_disjoint h h' \<and> P h' \<longrightarrow> Q (h ++ h'))"

notation sep_impl (infixr "--*" 25)

subsection \<open>Свойства сепарационной логики\<close>

lemma emp_neutral: "(P ** emp) = P"
  unfolding sep_conj_def emp_def heaps_disjoint_def
  apply (rule ext)
  apply auto
  done

lemma sep_comm: "sep_conj P Q = sep_conj Q P"
  unfolding sep_conj_def heaps_disjoint_def
  apply (rule ext)
  by (metis inf_commute map_add_comm)

lemma sep_assoc: "sep_conj (sep_conj P Q) R = sep_conj P (sep_conj Q R)"
  unfolding sep_conj_def heaps_disjoint_def
  apply (rule ext)
  apply auto
  apply (metis (no_types, lifting) Int_Un_distrib2 Un_empty dom_map_add inf_sup_distrib1 map_add_assoc)
  by (metis Int_Un_distrib2 Un_empty dom_map_add inf_sup_distrib1)  
  
lemma basic_allocation:
  "sep_conj (points_to 10 5) (points_to 11 7) = 
   (\<lambda>h. h = [10 \<mapsto> 5, 11 \<mapsto> 7])"
  unfolding sep_conj_def points_to_def heaps_disjoint_def
  apply (rule ext)
  apply auto
  done

lemma separation_example:
  assumes "x \<noteq> y"
  shows "sep_conj (points_to x a) (points_to y b) = 
         sep_conj (points_to y b) (points_to x a)"
  using assms
  unfolding sep_conj_def points_to_def heaps_disjoint_def
  by (metis Int_commute map_add_comm)

lemmas sep_neutral = emp_neutral
lemmas sep_commutative = sep_comm  
lemmas sep_associative = sep_assoc


section \<open>Часть 2: Операторы выбора (LEAST, SOME, THE)\<close>

subsection \<open>Примеры с LEAST\<close>

lemma least_basic: "(LEAST n::nat. n \<ge> 5) = 5"
  by (simp add: Least_equality)

lemma least_squared: "(LEAST n::nat. n * n \<ge> 10) = 4"
proof (rule Least_equality)
  show "(4::nat) * 4 \<ge> 10" by simp
next
  fix y :: nat
  assume "y * y \<ge> 10"
  show "4 \<le> y"
  proof (rule ccontr)
    assume "\<not> 4 \<le> y"
    then have "y \<le> 3" by simp
    then have "y * y \<le> 9"  using mult_le_mono by fastforce
    with \<open>y * y \<ge> 10\<close> show False by simp
  qed
qed

lemma test_quantifier: "\<not>(\<exists>n::nat. n < 0) \<Longrightarrow> \<forall>n::nat. \<not>(n < 0)"
  by auto  

lemma least_ge: "(LEAST n::nat. n \<ge> k) = k"
  by (simp add: Least_equality)

lemma least_gt: "(LEAST n::nat. n > k) = k + 1"
  by (simp add: Least_equality)

definition min_free_address :: "heap \<Rightarrow> nat" where
  "min_free_address h = (LEAST n. n \<notin> dom h)"


lemma min_free_of_empty_heap:
  assumes "h = Map.empty"
  shows "min_free_address h = 0"
  unfolding min_free_address_def
  using assms by simp



subsection \<open>Примеры с SOME\<close>

definition choose_even :: "nat set \<Rightarrow> nat" where
  "choose_even A = (SOME n. n \<in> A \<and> even n)"

lemma some_basic_example_explicit:
  assumes "A = {1, 2, 3, 4, 5}"
  shows "choose_even A = 2 \<or> choose_even A = 4"
proof -
  have "2 \<in> A \<and> even 2" using assms by simp
  then have ex: "\<exists>n. n \<in> A \<and> even n" by blast
  show ?thesis
    unfolding choose_even_def
    using ex assms using someI2_ex by (smt (verit, ccfv_threshold) insert_iff odd_numeral odd_one singleton_iff)
qed


definition ambiguous_choice :: "nat \<Rightarrow> nat" where
  "ambiguous_choice y = (SOME x. x^2 = y)"

subsection \<open>Примеры с THE\<close>

lemma the_unique_solution: "(THE x::nat. x + 2 = 5) = 3"
proof (rule the_equality)
  show "3 + 2 = (5::nat)" by simp
  fix x :: nat
  assume "x + 2 = 5"
  then show "x = 3" by simp
qed

definition inverse_function :: "('a \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a" where
  "inverse_function f y = (THE x. f x = y)"

lemma inverse_correct:
  assumes "bij f" "f x = y"
  shows "inverse_function f y = x"
  unfolding inverse_function_def
  using assms bij_def the_equality by (metis (mono_tags, lifting) inj_on_contraD iso_tuple_UNIV_I)

section \<open>Часть 3: Сепарационная логика с программами\<close>

subsection \<open>Модель простых команд\<close>

datatype com = 
    Alloc nat nat      \<comment> \<open>x := alloc(v)\<close>
  | Write nat nat      \<comment> \<open>[x] := v\<close>
  | Read nat "nat \<Rightarrow> com" \<comment> \<open>let y = [x] in c\<close>
  | Free nat           \<comment> \<open>free(x)\<close>
  | Seq com com        \<comment> \<open>c1; c2\<close>

inductive exec :: "heap \<Rightarrow> com \<Rightarrow> heap \<Rightarrow> bool" where
  alloc: "h' = h(x \<mapsto> v) \<Longrightarrow> exec h (Alloc x v) h'"
| write_it: "h x = Some _ \<Longrightarrow> h' = h(x \<mapsto> v) \<Longrightarrow> exec h (Write x v) h'"
| read: "h x = Some v \<Longrightarrow> exec h (c v) h'' \<Longrightarrow> exec h (Read x c) h''"
| free: "h x = Some _ \<Longrightarrow> h' = h(x := None) \<Longrightarrow> exec h (Free x) h'"
| seq: "exec h c1 h' \<Longrightarrow> exec h' c2 h'' \<Longrightarrow> exec h (Seq c1 c2) h''"

definition hoare_triple :: "assn \<Rightarrow> com \<Rightarrow> assn \<Rightarrow> bool" ("\<turnstile> {_} _ {_}") where
  "\<turnstile> {P} c {Q} \<equiv> \<forall>h. P h \<longrightarrow> (\<exists>h'. exec h c h' \<and> Q h')"

subsection \<open>Пример: обмен значений\<close>

definition linked_pair :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> assn" where
  "linked_pair x v1 y v2 \<equiv> points_to x v1 ** points_to y v2"

definition swap_values :: "nat \<Rightarrow> nat \<Rightarrow> com" where
  "swap_values x y \<equiv> 
     Read x (\<lambda>vx.
     Read y (\<lambda>vy.
     Seq (Write x vy) (Write y vx)))"

lemma swap_verification:
  assumes "x \<noteq> y"
  shows "\<turnstile> {linked_pair x a y b} swap_values x y {linked_pair x b y a}"
  unfolding hoare_triple_def swap_values_def linked_pair_def 
            points_to_def sep_conj_def[abs_def] heaps_disjoint_def
  apply (intro allI impI)
  apply (erule exE)+
  apply (erule conjE)+
  apply (rule_tac x="[x \<mapsto> b, y \<mapsto> a]" in exI)
  apply (intro conjI)
  apply (auto intro!: exec.intros simp: map_add_def assms)[1] 
  apply (rule exI[of _ "[x \<mapsto> b]"])
  apply (rule exI[of _ "[y \<mapsto> a]"])
  apply (auto simp: map_add_def assms)
  done



section \<open>Часть 4: Работа со списками и структурами данных\<close>

subsection \<open>Связанные списки в памяти\<close>

fun list_pred :: "nat list \<Rightarrow> nat \<Rightarrow> assn" where
  "list_pred [] null = emp"
| "list_pred (x#xs) ptr = 
     (\<lambda>h. \<exists>next. \<exists>h1 h2 h3. 
        heaps_disjoint h1 h2 \<and> heaps_disjoint (h1 ++ h2) h3 \<and>
        h = h1 ++ h2 ++ h3 \<and>
        points_to ptr x h1 \<and>
        points_to (ptr + 1) next h2 \<and>
        list_pred xs next h3)"



subsection \<open>Утверждения о сортированных списках\<close>

theorem "sorted xs \<and> xs \<noteq> [] \<Longrightarrow> Min (set xs) = hd xs"
  by (metis List.finite_set Min_eqI list.sel(1) list.set_sel(1) min_list.cases nle_le sorted2 sorted_wrt.simps(2))

subsection \<open>Бинарное дерево\<close>

datatype tree = Leaf | Node nat tree tree

function tree_pred :: "nat \<Rightarrow> tree \<Rightarrow> assn" where
  "tree_pred ptr Leaf = points_to ptr 0"  \<comment> \<open>0 означает лист\<close>
| "tree_pred ptr (Node value left right) = 
     (\<lambda>h. \<exists>left_ptr right_ptr.
        (points_to ptr 1 **           \<comment> \<open>1 означает узел\<close>
         points_to (ptr + 1) value **
         points_to (ptr + 2) left_ptr **
         points_to (ptr + 3) right_ptr **
         tree_pred left_ptr left **
         tree_pred right_ptr right) h)"
  by pat_completeness auto


section \<open>Часть 5: Практические применения операторов выбора\<close>

subsection \<open>Аллокатор памяти\<close>



definition first_fit_alloc :: "heap \<Rightarrow> nat \<Rightarrow> nat" where
  "first_fit_alloc = (\<lambda>h size. 
     (LEAST start :: nat. \<forall>i::nat. start \<le> i \<and> i < start + size \<longrightarrow> h i = None))"


definition random_fit_alloc :: "heap \<Rightarrow> nat \<Rightarrow> nat" where
  "random_fit_alloc = (\<lambda>h size. 
     (SOME start :: nat. \<forall>i::nat. start \<le> i \<and> i < start + size \<longrightarrow> h i = None))"

definition best_fit_alloc :: "heap \<Rightarrow> nat \<Rightarrow> nat" where
  "best_fit_alloc = (\<lambda>h size.
     (THE start :: nat. 
        (\<forall>i::nat. start \<le> i \<and> i < start + size \<longrightarrow> h i = None) \<and>
        (\<forall>other_start :: nat. 
           (\<forall>i::nat. other_start \<le> i \<and> i < other_start + size \<longrightarrow> h i = None) 
           \<longrightarrow> start \<le> other_start)))"

(*
  duplicate definition
*)
(* definition min_free_address :: "heap \<Rightarrow> nat" where  
  "min_free_address = (\<lambda>h. (LEAST n :: nat. h n = None))"
 *)



subsection \<open>Свойства аллокаторов\<close>

lemma first_fit_correct:
  fixes h :: heap and size :: nat
  assumes "\<exists>start. \<forall>i. start \<le> i \<and> i < start + size \<longrightarrow> h i = None"
  shows "\<forall>i. first_fit_alloc h size \<le> i \<and> i < first_fit_alloc h size + size \<longrightarrow> h i = None"
  unfolding first_fit_alloc_def
  using assms by (rule LeastI_ex)


lemma random_fit_correct:
  fixes h :: heap and size :: nat
  assumes "\<exists>start. \<forall>i. start \<le> i \<and> i < start + size \<longrightarrow> h i = None"
  shows "\<forall>i. random_fit_alloc h size \<le> i \<and> i < random_fit_alloc h size + size \<longrightarrow> h i = None"
  unfolding random_fit_alloc_def
  using assms by (rule someI_ex)


section \<open>Часть 6: Дополнительные примеры и упражнения\<close>


lemma least_exercise1: "(LEAST n::nat. n > 10 \<and> even n) = 12"
proof (rule Least_equality)
  show "(12::nat) > 10 \<and> even 12" by simp
next
  fix n :: nat
  assume "n > 10 \<and> even n"
  then have "n \<ge> 12"
  proof (cases "n = 11") 
    case True then show ?thesis using \<open>10 < n \<and> even n\<close> by auto
  next
    case False
    with \<open>n > 10\<close> have "n \<ge> 12" using False \<open>10 < n \<and> even n\<close> by linarith
    then show ?thesis by simp
  qed
  then show "(12::nat) \<le> n" by simp
qed


definition prime :: "nat \<Rightarrow> bool" where
  "prime n \<equiv> n > 1 \<and> (\<forall>m. m dvd n \<longrightarrow> m = 1 \<or> m = n)"

lemma some_exercise:
  assumes "\<exists>x. prime x \<and> x > n"
  shows "prime (SOME x. prime x \<and> x > n) \<and> (SOME x. prime x \<and> x > n) > n"
  using assms someI_ex by (metis (no_types, lifting))

lemma the_exercise:
  assumes "\<exists>!x. x^2 = y \<and> x \<ge> 0"
  shows "(THE x. x^2 = y \<and> x \<ge> 0) \<ge> 0"
  using assms theI' by (metis (mono_tags, lifting))

end