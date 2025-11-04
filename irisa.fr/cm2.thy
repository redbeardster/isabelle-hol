theory cm2
imports Main HOL.Rat "~~/src/HOL/Library/Code_Target_Nat"  (* to hide 0, Succ rep. of nats *)
begin


(* Terms and types *)

value "True"
value "1"
value "1::nat"
value "2+5::nat"
value "a+b::nat"
value "[True,False]"
value "x"
value "[x,y,z]"
value "[1,2,3]"
value "[2::nat,6,10]"
value "[(2::nat),6,10]"
value "[x,y,z]"
value "(x,y,z)"
value "(x,x,x)"
value "[(x,y),(y,x)]"
value "[(x)]"

(* Exercise 1 *)
(* append :: 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list *)

value "append [1::nat,2]  (append [3,4] [5,6])"

(* Exercice 2 *)

definition "addNc= (\<lambda>(x::nat,y).x+y)"

value"addNc (1,2)"

definition "add= (\<lambda>x::nat.\<lambda>y. x+y)"

value "add 5 6"

(* Exercise 3 *)

lemma "3 = (Suc (Suc (Suc 0)))"
  apply auto
  done

lemma "[1,1] = (Cons (Suc 0) (Cons (Suc 0) Nil))"
  apply auto
  done

lemma "[1,1] = ((Suc 0)#((Suc 0)#[]))"
  apply auto
  done

value "-56.188::rat"
value "''toto''"

(* Every data has a (hidden) constructor representation *)
value "1::nat"
value "2::nat"


(* Integers are represented by couples of nat (x,y), where the integer 
   value is x-y *)

lemma "(Abs_Integ(1,4) + Abs_Integ(3,0)) = 0"
  sorry  


(* Exercise 4 *)

value "(rev [1::nat,2,3])"

lemma "\<forall>x. (rev [x] = [x])"
  apply auto
  done

lemma "List.member (rev x) y \<longrightarrow> List.member (x) y"
  nitpick
  apply auto
  sorry

(* Example 14 *)

fun c:: "'a => 'a list => bool"
where
"c e []     = False" |
"c e (x#[]) = (if e=x then True else False)"



fun contains:: "'a => 'a list => bool"
where
"contains e []     = False" |
"contains e (x#xs) = (if e=x then True else (contains e xs))"

fun contains2:: "'a => 'a list => bool"
where
"contains2 e []     = False" |
"contains2 e (x#xs) = (e=x \<or> (contains2 e xs))"

(* Example 17 *)
(* A function that is not sufficiently defined, i.e. incomplete or not total *)

fun secondElt:: "'a list \<Rightarrow> 'a"
where
"secondElt (x#(y#ys)) = y"

(* Exercise 6 *)

thm "length_append"

thm "contains.simps"

thm "nth.simps"

find_theorems "rev" "length"

find_theorems "contains"


(* Example 21 *)

lemma "append [1,2] [3,4] = [1,2,3,4]"
  apply (subst append.simps)
  apply (subst append.simps)
  apply (subst append.simps)
  apply auto
  done

(* Exercise 7 *)

(* We can perform rewriting step by step...*)
lemma "contains (2::nat) [1,2,3] = True"
apply (subst contains.simps)
apply (simp del:contains.simps)
apply (subst contains.simps)
apply (simp del:contains.simps)
done

lemma "contains y [x,y,z]"
apply (subst contains.simps)
apply (subst contains.simps)
apply simp
done

lemma "contains y [x,y,z]"
  (* ... or we can print all the rewriting steps using 'simp_trace', but it is hard to read! *)
  using [[simp_trace=true]]
  apply auto
  done

lemma "contains u (append [u] v)"
apply (subst append.simps)
apply (subst contains.simps)
apply simp
done

(* Exercice 8 *)
lemma "contains v (append u [v])"
  apply auto
apply (subst append.simps)
apply (subst contains.simps)
sorry

lemma "(u= [a,b]) \<longrightarrow> contains v (append u [v])"
  apply auto
  done



(* Exercise 9 *)

fun index:: "'a \<Rightarrow> 'a list => nat"
where
"index y (x#xs) = (if x=y then 0 else 1+(index y xs))"

value "index (2::nat) [1,2,3]"
value "index (2::nat) [1,4]"

thm "List.nth.simps"
value "List.nth [10::nat,20,30] 2"

lemma "(List.member l e) \<longrightarrow>   List.nth l (index e l)=e"
  nitpick
  sorry

export_code contains index in Scala



end




