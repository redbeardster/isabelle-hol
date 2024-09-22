theory Baby
imports Main

begin

 (* fun conj :: "bool \<Rightarrow> bool \<Rightarrow> bool" where
"conj True True = True" |
"conj _ _ = False"

 fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add 0 n = n" |
"add (Suc m) n = Suc(add m n)"

lemma add_02: "add m 0 = m"
apply(induction m)
apply(auto)
done 

lemma add_03 [simp]: "add 0 m = m"
(* apply(induction m) *)
apply(auto)
done

(* double function *)
(* fun double :: "nat => nat" where 
"double 0 = 0" | 
"double (Suc m) = Suc(m) + Suc(m)"

lemma double_2 [simp]: "double m = add m m"
apply(induction m)
apply (auto)
done *)


(* we can now compute it *)
value "add 5 0"


thm add_02 

(* datatype 'a list = Nil | Cons 'a " 'a list" *)

fun app :: "'a list => 'a list => 'a list" where
"app Nil ys = ys" |
"app (Cons x xs) ys = Cons x (app xs ys)"

fun rev :: "'a list => 'a list" where
"rev Nil = Nil" |
"rev (Cons x xs) = app (rev xs) (Cons x Nil)"


lemma app_Nil2: "app xs Nil = xs"
apply(induction xs)
apply(auto)
done


lemma app_assoc [simp]: "app (app xs ys) zs = app xs (app ys zs)"
apply(induction xs)
apply(auto)
done

fun map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b list" where
"map f Nil = Nil" |
"map f (Cons x xs) = Cons (f x ) (map f xs)"

value "1 + (2::nat)"
value "1 + (2::int)"
value "1 - (2::nat)"
value "1 - (2::int)"


fun count :: "'a list \<Rightarrow> 'a \<Rightarrow> nat" where
  "count [] _ = 0" |
  "count (x#xs) x' = (if x = x' then Suc (count xs x') else count xs x')"

value "count [(1::nat), 1, 1] 1"


theorem "count xs x \<le> length xs"
  apply(induct xs)
   apply auto
  done

fun sum_upto :: "nat \<Rightarrow> nat " where
"sum_upto 0 = 0" | 
"sum_upto n = n + sum_upto (n - 1)"

value "sum_upto 4"

lemma sum_up_to: "sum_upto n = (n * (n+1)) div 2 "
apply(induction n)
apply(auto)
done

thm sum_up_to

(*  tree/mirror *)
datatype 'a tree = Tip | Node "'a tree" 'a " 'a tree"

fun mirror :: "'a tree \<Rightarrow> 'a tree" where
    "mirror Tip = Tip" |
    "mirror (Node l a r ) = Node (mirror r ) a (mirror l)"

lemma "mirror (mirror t) = t"
apply(induction t)
apply(auto)
done

datatype 'a option = None | Some 'a *)

fun lookup :: "('a * 'b) list \<Rightarrow> 'a \<Rightarrow> 'b option" where
"lookup [] x = None" |
"lookup ((a,b) # ps) x = (if a = x then Some b else lookup ps x )"



fun div2 :: "nat \<Rightarrow> nat" where
"div2 0 = 0" |
"div2 (Suc 0) = 0" |
"div2 (Suc(Suc n)) = Suc(div2 n)"

value "div2 2"


lemma "div2 n = n div 2"
apply(induction n rule: div2.induct)
apply(auto)
done


fun intersperse:: "'a => 'a list => 'a list" where
    "intersperse a [] = []" | 
    "intersperse _ [x] = [x]" | 
    "intersperse a (x#xs) = x#a#(intersperse a xs)"
(* it works too: `"intersperse a (Cons x xs) = [x,a]@(intersperse a xs)"` *)


lemma "map f (intersperse a xs) = intersperse (f a) (map f xs)"
apply(induction xs rule: intersperse.induct)
apply(auto)
done


value "intersperse 9 [1::nat,2,3,4,5]"

fun itrev :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"itrev [] ys = ys" |
"itrev (x#xs) ys = itrev xs (x#ys)"

value "itrev [1::nat,2,3,4,5] [5,4,3,2,1]"


lemma "itrev xs ys = rev xs @ ys"
apply(induction xs arbitrary: ys)
apply (auto)
done

datatype 'a optional = Some 'a | None

term "None:: 'a optional"
term "Some :: 'a => 'a optional"

lemma "Some x \<noteq> None" by simp

lemma "\<Sum>{0..n::nat} = (n * (n+1)) div 2"
proof (induction n)
  show "\<Sum>{0..0::nat} = (0* (0+1)) div 2" by simp
next
  fix n assume "\<Sum>{0..n::nat} = n*(n+1) div 2"
  thus "\<Sum>{0..Suc n} = Suc n * (Suc n+1) div 2" by simp
qed


lemma "\<Sum>{0..n::nat} = n*(n+1) div 2" (is "?P n")
proof (induction n)
  show "?P 0" by simp
next
  fix n assume "?P n"
  thus "?P(Suc n)" by simp
qed


fun splice :: \<open>'a list => 'a list => 'a list\<close>
where 
"splice [] [] = []" |
"splice xs [] = xs" |
"splice [] ys = ys" |
"splice (x#xs) (y#ys) = x # y # splice xs ys"

fun sum :: "int list => int" where
  "sum [] = 0" |
  "sum (x#xs) = 1 + sum xs"


 lemma "sum (splice xs ys) = sum xs + sum ys" 
 apply (induction xs ys rule: splice.induct)
 apply (auto)
 done


fun rev :: "'a list => 'a list" 
where 
"rev [] = []" | 
"rev (x#xs) = (rev xs) @ [x]"


fun rev_acc :: "'a list => 'a list => 'a list"  
where 
  "rev_acc [] acc = acc" | 
  "rev_acc (x#xs) acc = rev_acc xs (x # acc)"


(* Isar-style proof *)

lemma "rev xs = rev_acc xs []"
proof (induction xs)
  case Nil 
  then show ?case by simp
next 
  case (Cons a xs)  
  have "rev (a # xs) = (rev xs) @ [a]" by simp
  also have "\<dots> = (rev_acc xs []) @ [a]" using Cons.IH by simp
  then show ?case 
qed


end