theory Try
  imports Main (* "HOL-Library.Countable_Set" *)  
(* Main "HOL-Lattice.Orders"  HOL.Real *) 
begin 

(*    
lemma sum_gauss_2: "\<Sum>{1..n::nat} = n*(n+1) div 2"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case by simp
qed


lemma test:
shows True
ML_prf \<open> writeln "Trivial!" \<close>
oops

definition
maximum :: "('a::linear_order) \<Rightarrow> 'a \<Rightarrow> 'a" where
"maximum x y = (if x \<sqsubseteq> y then y else x)"


term "x"
term "Suc x"
term "Succ x"
term "Suc x = Succ y"
term "\<lambda>x . x"

term "\<lambda>x. Suc x < y"
prop "map (\<lambda>n . Suc n + 1) [0,1] = [2,3]"


(*declare [[show_types]]*)
term "Suc x = Succ y"


 lemma " B \<and> A \<longrightarrow> A \<and> B"
  apply (rule impI) thm impI
  apply (erule conjE)
  apply (rule conjI)
   apply assumption
  apply assumption
  done

lemma "B \<or> A \<longrightarrow> A \<or> B" 
  apply (rule impI) thm disjE
  apply (erule disjE)
   apply (rule disjI2)
   apply assumption
  apply (rule disjI1)
  apply assumption
  done


lemma "\<lbrakk> B \<longrightarrow> C; A \<longrightarrow> B \<rbrakk> \<Longrightarrow> A \<longrightarrow>C "
  apply ( rule impI)
  apply (erule impE)
   apply (erule impE)
    apply assumption
   apply assumption
  apply assumption
  done

thm refl

thm allI
thm allE
thm exI
thm exE


lemma "\<forall>a. \<exists>b. a = b"
  apply (rule allI)
  apply (rule_tac x ="a" in exI)
  thm refl
  apply (rule refl)
  done
 

lemma "\<exists>b. \<forall>a. P a b \<Longrightarrow> \<forall>a. \<exists>b. P a b"
  apply (rule allI)
  apply (erule exE)
  apply (erule_tac x="a" in allE)
  apply (rule_tac x="b" in exI)
  by assumption

lemma "\<forall>x. P x \<Longrightarrow> P 37"
  apply (erule_tac x="37" in allE)
  by assumption


lemma "\<forall>x. P x \<Longrightarrow> \<forall>x. \<forall>x. P x"
(*    apply (rule allI)
  apply (rule allI)
  apply (rename_tac y)
  apply (erule_tac x=y in allE)
  by assumption 
 *)
  by blast

thm dvd_add dvd_refl

thm dvd_add [OF dvd_refl]
thm dvd_add [OF dvd_refl dvd_refl]


definition xor :: "bool \<Rightarrow> bool \<Rightarrow> bool" where
  "xor A B \<equiv> (A \<and> \<not>B) \<or> (\<not>A \<and> B) "

thm xor_def

lemma xorI: 
  "A \<or> B \<Longrightarrow> \<not>(A \<or> B) \<Longrightarrow> xor A B"
  apply (unfold xor_def)
  by blast

lemma xorE[elim!]:
  "\<lbrakk> xor A B; \<lbrakk> A; \<not>B\<rbrakk> \<Longrightarrow> R; \<lbrakk>\<not> A;B \<rbrakk> \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
  apply(unfold xor_def)
  by blast
  
lemma "xor A A = False"
  apply (blast elim: xorE)
  done

definition
  a :: "nat list" where 
  "a \<equiv> []"

lemma n[simp] : "xs @ a = xs" using [[simp_trace]]
  apply (simp add: a_def)
  done

lemma "xs @a @a @a = xs"
  apply (simp only: a_def append_Nil2)
  done

lemma "1 \<le> (case ns of [] \<Rightarrow> 1 | n#_ \<Rightarrow> Suc n)"
  by (simp split: list.split)

thm if_split_asm


lemma 
  fixes f ::  "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infix "\<odot>" 70)
  assumes A: "\<And>x y z. (x \<odot> y) \<odot> z = x \<odot> (y \<odot> z)"
  assumes C: "\<And>x y. x \<odot> y = y \<odot> x"
  assumes AC: "\<And>x y z.  x \<odot> (y \<odot> z) = y \<odot> (x \<odot> z)"
  shows "(z \<odot> x) \<odot> (y \<odot> v) = t"
  apply (simp only: C)
  apply (simp only: A C)
  apply (simp only: AC)
  oops

(* declare [[simp_trace]] *)

lemma "A \<and> (A \<longrightarrow> B)"
  apply (simp cong: conj_cong)
  oops



type_synonym 'a myrel = "'a \<Rightarrow> 'a \<Rightarrow> bool" 

definition eq :: "'a myrel"
  where
  "eq x y \<equiv> (x = y)"


typedef three = "{0::nat,1,2}"
  apply(rule_tac x=1 in exI)
  by simp

definition Prd :: "('a \<Rightarrow> 'b \<Rightarrow> bool) set" 
  where
  "Prd \<equiv> {f . \<exists>a b. f = (\<lambda>x y. x = a \<and> y =b)}"

typedef ('a, 'b) prd = "Prd :: ('a \<Rightarrow> 'b \<Rightarrow> bool) set"
  by (auto simp: Prd_def)

datatype Status = Inactive | InProgress | Finished

(* datatype even = EvenZero | Suc odd
  and odd = OddZero | Suc even
 *)
thm even.induct

fun rev1 :: "'a list \<Rightarrow> 'a list" where 
  "rev1 Nil = Nil"
| "rev1 (x#xs) = (rev1 xs) @ (x#Nil)"

lemma app_nil: "xs @ [] = xs"
  apply (induction xs)
  apply auto
  done 

value "[1::nat,2,3] @ []"

value "rev1 [1::nat,2,3]"


lemma app_assoc: "(xs @ ys) @ zs  = xs @ (ys @ zs)"
   apply (induction xs)
   apply auto
  done 


lemma rev_app: "rev1 (xs @ ys) = (rev1 ys) @ (rev1 xs)"
   apply (induction xs)
  using [[simp_trace]]
  apply simp 
  apply simp
  done

 lemma rev_rev: "rev1 (rev1 xs) = xs"
  apply (induction xs)
   apply (auto simp add: rev_app)
  done 
 
datatype ('a, 'b) tree  = Tip | Node "('a, 'b) tree" 'b "('a, 'b) tree"
print_theorems

lemma "Tip \<noteq> Node l x r" by simp

lemma "(1::nat) \<le> (case t of Tip \<Rightarrow> 1 | Node l x r \<Rightarrow> x + 1)"
  apply (case_tac t)
   apply auto
  done

primrec 
  itrev :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where 
  "itrev [] ys = ys"
| "itrev (x#xs) ys = itrev xs (x#ys)"

lemma itrev_rev_app: "itrev xs ys = rev xs @ ys"
  apply (induct xs arbitrary: ys)
   apply simp
  using [[simp_trace]]
  apply auto
  done

lemma "itrev xs [] = rev xs"
  using [[simp_trace]]
  apply (induct xs)
   apply simp
  apply (clarsimp simp: itrev_rev_app)   (* or: apply (auto simp add: itrev__rev_app)*)
  done

primrec lsum:: "nat list \<Rightarrow> nat"
  where 
"lsum [] = 0"
| "lsum (x#xs) = x + lsum xs"

value "lsum [1,2,3]"

lemma lsum_app: "lsum (xs @ ys) = lsum xs + lsum ys"
  using [[simp_trace]]
  by (induct xs arbitrary: ys, auto)


lemma "2 * lsum [0..< Suc n] = n* (n+1)"
  using [[simp_trace]]
  apply(induct n)
   apply (auto simp add: lsum_app)
  done

primrec myreplicate :: "nat \<Rightarrow> nat \<Rightarrow> nat list" where
myreplicate_0: "myreplicate 0 x = []" |
myreplicate_Suc: "myreplicate (Suc n) x = x # myreplicate n x"

value "myreplicate 2 3"
value "lsum [3,3]"


lemma "lsum (replicate j y) = j * y"
  using [[simp_trace]]
  apply (induct j)
   apply auto
  done


primrec lsumT :: "nat list \<Rightarrow> nat \<Rightarrow> nat" where
"lsumT [] s  = s"
| "lsumT (x#xs) s = lsumT xs (x + s)"


lemma lsumT_gen: "lsumT xs s = lsum xs +s"
  by (induct xs arbitrary: s,auto)

lemma lsum_correct: 
  "lsumT xs 0 = lsum xs"
  apply (induct xs)
   apply simp
  apply (simp add: lsumT_gen)
  done
 

inductive ev ::"nat \<Rightarrow> bool" where
ev0: "ev 0" | 
evSS: "ev n \<Longrightarrow> ev (Suc(Suc n))"

thm ev0 evSS
thm ev.intros

print_theorems

lemma "ev (Suc(Suc(Suc(Suc 0))))"
  apply (rule evSS)+
  apply (rule ev0)
  done

thm evSS[OF evSS [OF ev0]]

fun evn:: "nat \<Rightarrow> bool" where
"evn 0 = True" |
"evn (Suc 0) = False" |
"evn (Suc(Suc n)) = evn n"

thm ev.induct

lemma "ev n \<Longrightarrow> evn n"
  apply (induction rule: ev.induct)
   apply simp
   apply simp
  done
  
thm evn.induct

lemma "evn n \<Longrightarrow> ev n"
  apply (induction rule: evn.induct)
    apply (simp add: ev0)
   apply simp
  apply (simp add: evSS)
  done

declare ev.intros[simp, intro]
lemma "evn n \<Longrightarrow> ev n" 
  apply (induction n rule: evn.induct)
    apply (simp_all)
  done

lemma "ev n \<Longrightarrow> \<exists>k . n = 2*k"
  using [[simp_trace]]
  apply (induction rule: ev.induct)
   apply (simp)
  apply arith
  done

inductive 
  star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
  for r where 
  refl:   "star r x x " | 
  step: "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

thm star.induct

lemma star_trans: "star r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"
  apply (induction rule: star.induct)
   apply assumption
  apply (rename_tac u x y)
  by (simp add: star.intros)

lemma "\<not> surj (f ::'a \<Rightarrow> 'a set)"
proof
  assume 0: "surj f"
  from 0 have 1: "\<exists>a . {x. x\<notin> f x} = f a" by (auto simp: surj_def)
  from 1 show "False" by blast
qed

lemma "\<not> surj (f :: 'a \<Rightarrow> 'a set)"
proof 
  assume 0: "surj f"
  from 0 have 1: "\<forall>A. \<exists>a. A = f a" by (simp add: surj_def)
  from 1 have 2: "\<exists>a. {x. x\<notin> f x} = f a" by blast
  from 2 show "False" by blast
qed

lemma "\<not> surj (f :: 'a \<Rightarrow> 'a set)"
proof 
  assume "surj f"
  hence "\<exists>a. {x. x\<notin> f x} = f a" by (auto simp: surj_def)
  thus "False" by blast
qed
 

lemma 
  fixes f :: "'a \<Rightarrow> 'a set"
  assumes s: "surj f"
  shows "False"
proof-
  have "\<exists>a. {x. x\<notin> f x} = f a" using s
    by (auto simp: surj_def)
  thus "False"  by blast
qed

lemma "\<not> surj (f :: 'a \<Rightarrow> 'a set)"
proof 
  assume "surj f"
  hence "\<exists>a. {x. x\<notin> f x} = f a" by (auto simp: surj_def)
(*   then obtain a where "{x. x\<notin> f x} = f a" by blast
  hence "a \<notin> f a \<longleftrightarrow> a \<in> f a " by blast *)
  thus "False"  by blast
qed
 
lemma "\<exists> xs . length xs = 0 " (is "\<exists> xs. ?P xs")
proof
  show "?P([])" by simp
qed

lemma "\<exists> x y :: int . x < z & z < y" (is "\<exists> x y . ?P x y")
proof-
  have "?P(z-1)(z+1)" by arith
  thus ?thesis by blast
qed

lemma "(0::real) \<le> x^2 + y^2 -2*x*y" 
proof-
  have "0 \<le> (x-y)^2" by simp
  also have "... = x^2 +y^2 - 2*x*y" 
    by (simp add: numeral_eq_Suc algebra_simps)
  finally show "0 \<le> x^2 + y^2 -2*x*y" .
  qed


lemma assumes "\<exists>x . \<forall>y. P x y " shows "\<forall>y . \<exists>x . P x y"
proof 
  fix b 
  thm assms 
  from assms obtain a where 0: "\<forall>y. P a y" by blast
  show "\<exists>x . P x b"
  proof 
    show "P a b" using 0 by blast
  qed
qed


value "drop 2 [1::nat,2,3,4,5,6]"
 
lemma "\<exists>ys zs . xs = ys @ zs \<and> (length ys = length zs \<or> length ys = length zs +1)"
proof cases 
  assume "\<exists>n . length xs = n + n"
  then obtain n where  "length xs = n +n" by blast
  let ?ys = "take n xs"
  let ?zs = "take n (drop n xs)"
  have "xs = ?ys @ ?zs \<and> length ?ys = length ?zs"
    by (simp add: `length xs = n + n`)
  thus ?thesis by blast
next 
  assume "\<not> (\<exists>n. length xs = n + n)"
  hence "\<exists>n. length xs = Suc(n+n)" by arith
  then obtain n where l: "length xs = Suc(n+n)" by blast
  let ?ys = "take (Suc n) xs"
  let ?zs = "take n (drop (Suc n) xs)"
  have "xs = ?ys @ ?zs \<and> length ?ys = length ?zs + 1" by (simp add: l)
  thus ?thesis by blast
qed

lemma "length (tl xs) = length xs -1"
proof (cases xs)
  assume "xs = []" thus ?thesis by simp
next
(*   fix y ys assume "xs = y#ys" *)
 (*  thus *) 
  show ?thesis by simp 
qed


lemma "length (tl xs) = length xs -1"
proof (cases xs)
  case Nil
  thus ?thesis by simp
next
  case (Cons y ys)
    thus ?thesis by simp
qed

(* lemma split_list: "x : set xs \<Longrightarrow> \<exists>ys zs . xs = ys@x#zs"
  by (simp add: split_list)
 *)

lemma split_list: "x : set xs \<Longrightarrow> \<exists>ys zs . xs = ys@x#zs"
 proof (induction xs)
   case Nil
   thus ?case by simp
 next
   case (Cons a xs)
   from Cons.prems have "x = a \<or> x : set xs" by simp
   thus ?case 
   proof
     assume "x = a"
     hence "a#xs = [] @ x#xs" by simp
     thus ?thesis by blast 
   next 
     assume "x : set xs"
     then obtain ys zs where "xs = ys @ x #zs " using Cons.IH by auto
     hence "a#xs = (a#ys) @ x #zs" by simp 
     thus ?thesis by blast
   qed
 qed


locale partial_order = 
  fixes le :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "\<sqsubseteq>" 50)
  assumes refl [intro, simp]: "x \<sqsubseteq> x"
    and anti_sym[intro]: "\<lbrakk>x \<sqsubseteq>y; y \<sqsubseteq> x \<rbrakk> \<Longrightarrow> x = y" 
    and trans[trans]: "\<lbrakk> x \<sqsubseteq>y; y\<sqsubseteq> z\<rbrakk> \<Longrightarrow> x \<sqsubseteq>z"

thm partial_order_def
thm partial_order.trans
thm partial_order.anti_sym
thm partial_order.refl

definition (in partial_order)
  less :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "\<sqsubset>" 50)
    where "(x \<sqsubset> y) = (x \<sqsubseteq>y \<and> x \<noteq> y)"

thm partial_order.less_def
print_locale! partial_order

lemma (in partial_order) less_le_trans [trans]: 
  "\<lbrakk>x \<sqsubset>y; y \<sqsubseteq>z \<rbrakk> \<Longrightarrow> x \<sqsubset>z"
  unfolding less_def by (blast intro: trans)

context partial_order
begin

definition 
  is_inf where "is_inf x y i =  
      (i \<sqsubseteq> x \<and> i \<sqsubseteq> y \<and> (\<forall> z. z \<sqsubseteq> x \<and> z \<sqsubseteq>y \<longrightarrow> z \<sqsubseteq> i))"
end
 
fun insert:: "nat \<Rightarrow> nat list \<Rightarrow> nat list" where
  "insert a [] = [a]" |
  "insert a (x#xs) = (if a \<le> x then a#x#xs else x # insert a xs)"

value "insert 7 [1,6,9]"

fun insertion_sort:: "nat list \<Rightarrow> nat list" where
  "insertion_sort [] = []" | 
  "insertion_sort (x#xs) = insert x (insertion_sort xs)"

value "insertion_sort [6,3,9,1,10]"
  
fun le:: "nat \<Rightarrow> nat list \<Rightarrow> bool" where 
  "le a [] = True" | 
  "le a (x#xs) =  (a \<le> x & le a xs) "

fun ord:: "nat list \<Rightarrow> bool" where 
  "ord [] = True" | 
  "ord (x#xs) = (le x xs & ord xs)"

lemma h1: "x \<le> y \<Longrightarrow> le y xs \<longrightarrow> le x xs"
  apply (induction xs)
   apply auto
  done

lemma h2: "le x (insert a xs) = (x \<le> a & le x xs)"
  apply (induction xs)
   apply auto
  done

thm iffD1

 lemma in_ord [THEN iffD1, simp]: "ord xs = ord (insert x xs)"  (* `lemma in_ord [simp]: "ord xs = ord (insert x xs)"` works too*)
  apply (induct xs)
   apply simp+
  apply (simp add: h2)
  using h1 by blast 

thm in_ord

lemma sorted: "ord (insertion_sort xs)"
  apply (induct xs)
  apply simp
  apply (simp add: insertion_sort.cases)
  done
  

definition xor :: "bool \<Rightarrow> bool \<Rightarrow> bool" where
"xor A B \<equiv> (A \<and> \<not>B) \<or> (\<not>A \<and> B)"

lemma "xor A (\<not>A)"
  using [[simp_trace]]
  apply(simp add: xor_def)
  done

thm Let_def

lemma "(let xs = [] in xs@ys@xs) = ys"
apply(simp add: Let_def)
  done

(* lemma hd_Cons_tl[simp]: "xs \<noteq> [] \<Longrightarrow> hd xs # tl xs = xs"
apply(case_tac xs, simp, simp)
done *)

lemma "\<forall> xs. if xs = [] then rev xs = [] else rev xs \<noteq> []"
  apply (split if_split)
  apply simp
  done


lemma "(case xs of [] \<Rightarrow> zs | y#ys \<Rightarrow> y#(ys@zs)) = xs@zs"
  apply (split list.split)
  apply simp
  done

lemma "if xs = [] then ys \<noteq> [] else ys = [] \<Longrightarrow> xs @ ys \<noteq> []"
  apply (split if_split_asm)
   apply auto
  done


(* find_theorems simp: "_ * (_ + _)" *)

primrec itrev :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "itrev [] ys = ys" |
  "itrev (x#xs) ys = itrev xs (x#ys)"



fun sep :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"sep a [] = []" |
"sep a [x] = [x]" |
"sep a (x#y#zs) = x # a # sep a (y#zs)"


lemma "map f (sep x xs) = sep (f x) (map f xs)"
  apply(induct_tac x xs rule: sep.induct)
    apply simp_all
  done


datatype currency =
Euro nat ("\<euro>")
| Pounds nat ("\<pounds>")
| Yen nat ("\<yen>")
| Dollar nat ("$")

value "Euro 10"


consts 
sim :: "('a \<times> 'a) set"

abbreviation sim2 :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<approx>" 50)
where "x \<approx> y \<equiv> (x, y) \<in> sim"


lemma "\<lbrakk>x = f x; triple (f x) (f x) x \<rbrakk> \<Longrightarrow> triple x x x"
  apply (erule ssubst)
  back
  back
  back
  back
  apply assumption
  done

lemma "2 \<le> u \<Longrightarrow> u*m \<noteq> Suc(u*n)"
  by (metis One_nat_def Suc_1 Suc_times_mod_eq linorder_not_le mod_mult_self1_is_0 not_less_eq_eq)
(* 
lemma not_zero_example:
  assumes "x + y \<noteq> 0" and "y = 0"
  shows "x \<noteq> 0" 
proof -
  from assumption (* x + y \<noteq> 0 *) 
  have "x + 0 \<noteq> 0" (* Substitute y = 0 into the equation *)
  by (simp only: assms(2))
  then have "x \<noteq> 0" by simp (* Subtract 0 from both sides to isolate x *)
  thus "x \<noteq> 0" (* Conclude the proof *)
  by this
qed  
   *)
(* 
 lemma mylemma1: 
  assumes "x + y \<noteq> 0" and "y = 0"
  shows "x \<noteq> 0"
proof -
  from assms(1) have "x + 0 \<noteq>0"
  using assms(1) assms(2) by auto
  thus "x \<noteq> 0 " by this
qed 
 *)

lemma "\<lbrakk>c \<in> A; c \<in> B\<rbrakk> \<Longrightarrow> c \<in> A \<inter> B"
  by (simp add: Set.IntI)


lemma "{x. P x \<or> x \<in> A} = { x. P x} \<union> A"
  by auto

lemma "{x. P x \<longrightarrow> Q x} = -{x. P x} \<union> {x. Q x}"
  by (simp add: Set.Collect_imp_eq)

lemma "(\<forall> x. f x = g x) \<Longrightarrow> f = g"
  by auto

thm fun_upd_apply

lemma "y \<in> set ( x#xs ) \<Longrightarrow> length(remove1 y ( x#xs ) ) < length( x#xs )"
  by (metis One_nat_def diff_Suc_less length_greater_0_conv length_remove1 list.discI)


(* lemma "set_elem_nth": 
  assumes "x \<in> set xs"
  shows "\<exists> m. m < length xs \<and> xs ! m = x"
  by (meson assms in_set_conv_nth)
 *)

inductive_set evens :: "nat set"
  where
    base: "0 \<in> evens" |
    step: "x \<in> evens \<Longrightarrow> Suc (Suc x) \<in> evens" *)

(* datatype mynat = Zero | Suc mynat

fun add :: "mynat \<Rightarrow> mynat \<Rightarrow> mynat" where
"add Zero n = n" |
"add (Suc m) n = Suc (add m n)"

inductive_set even :: "mynat set"
where
zero[intro!]: "Zero \<in> even" |
step[intro!]: "n \<in> even \<Longrightarrow> Suc (Suc n) \<in> even"

thm mynat.simps
 *)


fun itrev :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"itrev [] ys = ys" |
"itrev (x #xs) ys = itrev xs (x #ys)"

lemma "itrev xs [] = rev xs"
  apply (induction xs)
   apply auto
  sorry

lemma "itrev xs ys = rev xs @ ys"
  apply(induction xs arbitrary: ys)
   apply auto
  done
  

lemma "P (if A then s else t ) = ((A \<longrightarrow> P s) \<and> (\<not> A \<longrightarrow> P t ))"
  apply (simp)
  done


fun sorted :: "('a::linorder) list \<Rightarrow> bool"
  where 
  "sorted [] = True"
| "sorted (x # ys) = ((\<forall> y\<in>set ys. x \<le> y) \<and> sorted ys)"


lemma "\<lbrakk> xs @ ys = ys @ xs; length xs = length ys \<rbrakk> \<Longrightarrow> xs = ys"
  by (metis append_eq_conv_conj)


lemma "\<lbrakk> (a::nat ) \<le> b; b \<le> c; c \<le> d; d \<le> e \<rbrakk> \<Longrightarrow> a \<le> e"
  by auto

lemma x_not_zero:
  fixes x y :: nat
  assumes "x + y \<noteq> 0" "y = 0"
  shows "x \<noteq> 0"
proof -
  from assms(2) have "x + y = x" by simp
  from assms(1) have "x \<noteq> 0" using `x + y \<noteq> 0` `x + y = x` by simp
  thus ?thesis by auto
qed

lemma "length(tl xs) = length xs - 1"
proof (cases xs)
  case Nil
  then show ?thesis by simp
next
  case (Cons y ys)
  then show ?thesis by simp
qed

lemma "\<Sum> {0..n::nat} = n*(n+1) div 2"
proof (induction n)
  case 0
  show ?case by simp
next
  case (Suc n)
  thus ?case by simp
qed


lemma even_or_succ_even:
  fixes x :: int
  shows "even x \<or> even (x + 1)"
proof -
  consider (even) "even x" | (odd) "odd x"
  by auto  
  then show ?thesis
  proof cases
    case even
    then show ?thesis by simp  (* Если x четное, то первое условие выполнено *)
  next
    case odd
    then have "even (x + 1)" by simp  (* Если x нечетное, то x + 1 четное *)
    then show ?thesis by simp
  qed
qed

lemma square_of_sum:
  fixes x y :: int
  shows "(x + y)^2 = x^2 + 2 * x * y + y^2"
proof -
  let ?sum = "x + y"          (* Локальное определение: ?sum = x + y *)
  let ?square_sum = "?sum^2"  (* Локальное определение: ?square_sum = (x + y)^2 *)
  have "?square_sum = (x + y) * (x + y)"   by (simp add: power2_eq_square)
  also have "... = x * x + x * y + y * x + y * y" by (simp add: algebra_simps)
  also have "... = x^2 + 2 * x * y + y^2" by (simp add: power2_eq_square)
  finally show ?thesis by simp
qed

fun erlang_fact :: "nat \<Rightarrow> nat" where
  "erlang_fact 0 = 1"
| "erlang_fact n = (if n > 0 then n * erlang_fact (n - 1) else undefined)"

lemma fact_positive: "n > 0 \<Longrightarrow> erlang_fact n > 0"
 proof (induction n rule: erlang_fact.induct)
  case 1
  then show ?case by simp
next
  case (2 n)
  then show ?case   by fastforce
qed 

lemma fact_non_zero: "n \<ge> 0 \<Longrightarrow> erlang_fact n \<noteq> 0"
  using fact_positive by fastforce

lemma fact_correct: "n \<ge> 0 \<Longrightarrow> erlang_fact n = fact n"
  proof (induction n rule: erlang_fact.induct)
  case 1
  then show ?case by simp
next
  case (2 n)
  then show ?case by simp
qed


inductive_set Evens :: "nat set" where
zero: "0 \<in> Evens" 
| plus_two: "n \<in> Evens \<Longrightarrow> (n + 2) \<in> Evens" 


inductive_set EvenLengthLists :: "'a list set" where
  empty: "[] \<in> EvenLengthLists"  
| append_two: "xs \<in> EvenLengthLists \<Longrightarrow> x # y # xs \<in> EvenLengthLists"  


inductive_set R :: "(nat \<times> nat) set" where
  base: "(0, 0) \<in> R"  
| step: "(x, y) \<in> R \<Longrightarrow> (x + 1, y + 2) \<in> R"  


lemma " \<forall> x. \<not> rich x \<longrightarrow> rich (father x) \<Longrightarrow> \<exists> x. rich (father (father x)) \<and> rich x"
  by auto



fun list_to_option :: "'a list \<Rightarrow> 'a option"
where
"list_to_option [x] = Some x"
| "list_to_option _ = None"

thm list_to_option.cases
list_to_option.simps

lemma lto: "list_to_option [] = None"
  by simp

lemma single_val: "list_to_option xs = Some x \<Longrightarrow>  length(xs) = 1"
  by (metis One_nat_def length_0_conv length_Cons list_to_option.elims not_Some_eq)

thm list_to_option.elims

fun_cases list_to_option_SomeE[elim]: "list_to_option xs = Some y"
thm list_to_option_SomeE

lemma "list_to_option xs = y \<Longrightarrow> P"
proof (erule list_to_option.elims)
fix x assume "xs = [x]" "y = Some x" thus P sorry
next
assume "xs = []" "y = None" thus P sorry
next
fix a b xs' assume "xs = a # b # xs'" "y = None" thus P sorry
qed


(* lemma "(case xs of [] \<Rightarrow> [] | y#ys \<Rightarrow> xs) = xs"
  apply (case_tac xs)
   apply auto
  done
 *)

lemma "(case xs of [] \<Rightarrow>zs | y#ys \<Rightarrow>y#(ys@zs)) = xs@zs"
  apply(split list.split)
  apply(simp)
done

lemma "(xs@ys) @ zs = xs @ (ys@zs)"
  apply (induction xs)
  apply auto
  done


lemma "\<forall>ys. itrev xs ys = rev xs @ ys"
  apply(induct_tac xs, simp_all)
  done


lemma "xs \<noteq>[] \<longrightarrow>hd(rev xs) = last xs"
apply(induct_tac xs)
   apply auto
  done

lemma some_lemma[simp]:
fixes A :: "bool" 
assumes AnA: "A \<and> A"
shows "A"
  using AnA by simp


fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add 0 n = n" |
"add (Suc m) n = Suc(add m n)"


lemma add_assoc: "add (add m n) p = add m (add n p)"
  apply (induct m)
  by auto

lemma add_02 [simp] : "add m 0 = m" 
  apply(induction m)
apply(auto)
done

lemma add_plus1 [simp] : "Suc (add q p) = add q (Suc p)"
  apply(induction q)
   apply(auto)
  done

lemma add_comm : "add m n = add n m"
  apply(induction m)
   apply(auto)
  done
(* 
lemma set_membership_equality_technicalD:
assumes "{x} \<union> (set xs) = {y} \<union> (set ys)"
shows "x = y \<or> y \<in> set xs"
  using assms by(induction xs, auto)

typedef mytype = "{x::nat. x < 10}"
  by (metis lessI mem_Collect_eq numeral_eq_Suc)


lemma mytype_le_10: "Rep_mytype x < 10"
proof -
  have "Rep_mytype x \<in> {x::nat. x < 10}"
    using Rep_mytype by simp
   hence "Rep_mytype x < 10" by simp 
  then show ?thesis  by linarith 
qed *)






end