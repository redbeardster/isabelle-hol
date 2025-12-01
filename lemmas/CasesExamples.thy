theory CasesExamples
imports Main
begin


(* lemma simple_bool: "P \<or> Q \<Longrightarrow> R"
proof
  assume "P \<or> Q"
  then show "R"
  proof cases   
    assume "P"
    then show "R" sorry
  next
    assume "Q" 
    then show "R" sorry
  qed
qed *)


datatype Color = Red | Green | Blue

lemma color_example: "\<forall>c. c = Red \<or> c = Green \<or> c = Blue"
proof
  fix c
  show "c = Red \<or> c = Green \<or> c = Blue"
  proof (cases c) 
    case Red
    then show ?thesis by simp
  next
    case Green
    then show ?thesis by simp
  next  
    case Blue
    then show ?thesis by simp
  qed
qed


lemma nat_cases: "n = 0 \<or> (\<exists>k. n = Suc k)"
proof (cases n)
  case 0
  then show ?thesis by simp
next
  case (Suc k)
  then show ?thesis by simp
qed


lemma list_cases: "xs = [] \<or> (\<exists>y ys. xs = y # ys)"
proof (cases xs)
  case Nil
  then show ?thesis by simp
next
  case (Cons y ys)
  then show ?thesis by simp
qed

fun not :: "bool \<Rightarrow> bool" where
  "not True = False"
| "not False = True"

lemma not_involutive: "not (not x) = x"
proof (cases x)
  case True
  then show ?thesis by simp
next
  case False
  then show ?thesis by simp
qed

fun even :: "nat \<Rightarrow> bool" where
  "even 0 = True"
| "even (Suc 0) = False"  
| "even (Suc (Suc n)) = even n"

definition odd :: "nat \<Rightarrow> bool" where
  "odd n = (\<not> even n)"

lemma "even n \<or> odd n"
proof (cases n)
  case 0
  then show ?thesis by simp
next
  case (Suc m)
  then show ?thesis 
  proof (cases m)
    case 0
    then show ?thesis by (simp add: odd_def)
  next
    case (Suc k)
    then show ?thesis by (simp add: odd_def)
  qed
qed

lemma even_odd_decomposition: "n = 0 \<or> (\<exists>k. n = Suc k)"
proof (cases n)
  case 0
  then show ?thesis by simp
next
  case (Suc k)
  then show ?thesis by simp
qed

lemma list_induction_case:
  "length xs = length ys \<Longrightarrow> zip xs ys = [] \<or> (\<exists>x y xs' ys'. zip xs ys = (x, y) # zip xs' ys')"
(* proof (cases xs)
  case Nil
  then show ?thesis by simp
next
  case (Cons x xs')
  show ?thesis
  proof (cases ys)
    case Nil
    with Cons show ?thesis by simp
  next
    case (Cons y ys')
    with \<open>xs = x # xs'\<close> show ?thesis      
    by auto
  qed
qed *)
  by (metis list.exhaust zip_eq_ConsE)


lemma option_cases: "opt = None \<or> (\<exists>x. opt = Some x)"
proof (cases opt)
  case None
  then show ?thesis by simp
next
  case (Some x)
  then show ?thesis by simp
qed

lemma simple_rule: "A \<Longrightarrow> A"
  by (rule_tac P="A" in classical) auto





end (*end of theory file*)