theory cm4
imports Main "~~/src/HOL/Library/Code_Target_Nat"  (* to hide 0, Succ rep. of nats *)
begin

lemma "length la \<le> 1"
  nitpick[card=2,show_all]
  nitpick[card=3,show_all]
  oops

(* Exercise 2.1 *)

lemma "rev l = l"
  nitpick [show_all]
  oops
(* Exercise 2.2 *)

fun nth:: "nat \<Rightarrow> 'a list \<Rightarrow> 'a"
where
"nth 0 (x#_)=x" |
"nth x (y#ys)= (nth (x - 1) ys)"

fun index:: "'a \<Rightarrow> 'a list \<Rightarrow> nat"
where
"index x (y#ys)= (if x=y then 0 else 1+(index x ys))"


value "nth 2 [1::nat, 2, 3, 4]"

value "index 22 [12::nat, 22, 33, 44]"

lemma "nth (index e l) l= e"
  nitpick [card=2,show_all]

lemma nth_index: "List.member l e \<longrightarrow> nth (index e l) l= e"
  nitpick 
  oops

(* Exercise 2.4 *)
lemma append_commut: "([x,y,z] @ [z,y,x]) = ([z,y,x] @ [x,y,z])"
  nitpick [card=10-20]
  oops


fun cutFirst:: "'a list \<Rightarrow> nat \<Rightarrow> 'a list"
where
"cutFirst [] _= []" |
"cutFirst (x#_) (Suc 0)= [x]" |
"cutFirst (x#xs) y = x#(cutFirst xs (y - 1))"

fun cutEnd:: "'a list \<Rightarrow> nat \<Rightarrow> 'a list"
where
"cutEnd [] _ = []" |
"cutEnd (x#xs) (Suc 0)= xs" |
"cutEnd (x#xs) y = (cutEnd xs (y - 1))"

lemma cutEnd_decreasing: "l\<noteq>[] \<Longrightarrow> length(cutEnd l i) < (length l)"
sorry


function slice:: "'a list \<Rightarrow> ('a list) list"
where
"slice l1= 
  (if l1=[] then [] else 
      (let deb=(cutFirst l1 19) in
        let fin=(cutEnd l1 19) in
            (deb#(slice fin))))"
by pat_completeness auto
termination slice
apply (relation "measure (%i. (length i))")
apply auto
by (metis cutEnd_decreasing)

(* Exercise 3 *)
(* Counterexample is of size 20 *)      

lemma length_slice: "length(slice l)<=1"
  quickcheck [tester=narrowing, size=20]
  oops

(* Remark 2: Be careful with size/timeout with quickcheck !!!*)

lemma "rev l = l"
quickcheck [tester=narrowing,timeout=10]     
quickcheck [tester=narrowing,size=1000000,timeout=10]  
oops


lemma "rev [x] = [x]"
  apply auto
  done  

(* fails in finding the counter example: the 10s are spent in building all possible input data of size 1 to 1000000, 
   and NOT in testing the values of size 1, first then generate for size 2, etc... *) 


(* Example 2 *)

lemma "A"
apply (case_tac "C \<or> D")
oops

(* exercice 4 *)
 
lemma "\<forall>x::nat. x<4 \<longrightarrow> x*x < 10"
  nitpick
  apply auto
  apply (case_tac "x=0")
   apply auto
  apply(case_tac "x=1")
   apply auto 
  apply(case_tac "x=2")
   apply auto 
  apply(case_tac "x=3")
   apply auto
done

(* Ou version plus compacte *)
lemma "(x::nat) <4 \<longrightarrow> x*x < 10"
  apply (case_tac "x=0 \<or> x=1 \<or> x=2 \<or> x= 3")
  apply auto
  done


(* Example 3 *)

datatype color= Black | White | Grey 

value "Black"


lemma "P(x::color)"
apply (case_tac "x")
oops
    
  

(* Exercice 5 *)

fun notBlack:: "color \<Rightarrow> bool"
where
"notBlack Black= False" |
"notBlack _ = True"


lemma "notBlack x \<longrightarrow> (x=White \<or> x= Grey)"
  apply auto
  apply (case_tac x)
    apply auto
  done

(* Example 5 *)

fun append :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
"append [] l2 = l2" |
"append (x#xs) l2 = (x#(append xs l2))"


lemma "append l [] = l"
   apply (induct l)
apply auto
done 

(* Example 6 *)


lemma "length (append l1 l2) \<ge> (length l2)"
apply (induct l2) (* Induction sur le deuxième paramètre *)
apply auto (* la preuve va être difficile *)
sorry

(* Induction sur le premier paramètre, la preuve est simple 
  (append est récursive sur le premier paramètre *)
lemma "length (append l1 l2) \<ge> (length l2)"
apply (induct l1)
apply auto
done


(* Exercise 6 *)

datatype 'a binTree= Leaf | Node 'a "'a binTree" "'a binTree"

fun numNodes:: "'a binTree \<Rightarrow> nat"
where
"numNodes Leaf=0" |
"numNodes (Node _ tg td)= 1+(numNodes tg)+(numNodes td)"

definition "tree1= Node (1::nat) (Node 2 Leaf Leaf) (Node 3 Leaf Leaf)"

value "numNodes tree1"

fun contains:: "'a \<Rightarrow> 'a binTree \<Rightarrow> bool"
where
"contains _ Leaf = False" |
"contains x (Node y tg td)= (if x=y then True else ((contains x tg) \<or> (contains x td)))"


lemma "contains x t \<longrightarrow> numNodes t > 0"
  apply (induct t)
   apply auto
  done


fun subTree:: "'a binTree \<Rightarrow> 'a binTree \<Rightarrow> bool"
where
"subTree Leaf Leaf = True" |
"subTree _ Leaf=False" |
"subTree x (Node y tg td)= (if x=(Node y tg td) then True else ((subTree x tg) \<or> (subTree x td)))"

lemma "subTree a b \<longrightarrow> numNodes a \<le> numNodes b "
  apply (induct b)
   apply auto
  using numNodes.simps(1) subTree.elims(2) by blast

value "subTree (Node (1::nat) Leaf Leaf) (Node 2 (Node 1 Leaf Leaf) Leaf)"


(* Exercise 7 *)
fun sumList:: "nat list \<Rightarrow> nat"
where
"sumList []=0" |
"sumList (x#xs)= x+(sumList xs)"

value "sumList [1,2,3,4,5]"

fun sumNat:: "nat \<Rightarrow> nat"
where
"sumNat 0= 0" |
"sumNat i= (i+(sumNat (i - 1)))"

value "sumNat 5"

fun makeList:: "nat \<Rightarrow> nat list"
where
"makeList 0 =[]" |
"makeList i = (i#(makeList (i - 1)))"

value "makeList 30"

lemma length_makeList: "length(makeList i)=i"  
  nitpick
  apply (induct i)
   apply auto
  done

lemma "sumList (makeList n) = sumNat n"
  nitpick
  apply (induct n)
   apply auto
  done

(* Example 7 and 8 *)
lemma ex:"P (x::nat) (y::nat)"
apply (induct x arbitrary: y)
oops

(* Exercice 8 *)

fun leq::"nat => nat => bool"   (infix "=<" 65)
where 
"leq 0 _ = True" |
"leq (Suc _) 0 = False" |
"leq (Suc x) (Suc y) = leq x y"

(* à laisser en exercice *)  
lemma sym: "((x=<y) \<and> (y=< x)) \<longrightarrow> (x=y)"
apply (induct x)  
prefer 2  (* choose the second subgoal as the first *)
(* The induction hypothesis is for a "fixed" y *)
apply (case_tac y)
apply simp   (* This case does not need the induction hypothesis *)
apply simp (* This case need the induction hypothesis, which cannot be used for any other
              value than y= Suc nat. In particular, we cannot use the induction hypothesis 
              for nat ! *)
(* we won't manage to prove it *)
sorry


lemma symb: "((x=<y) \<and> (y=< x)) \<longrightarrow> (x=y)"
apply (induct x arbitrary:y)  
prefer 2 
(* The induction hypothesis is for "any" y *)
apply (case_tac y)
apply auto
apply (case_tac y)
apply auto
done


(* Exercice 9 *)

fun divBy2 :: "nat \<Rightarrow> nat" 
where
"divBy2 0 = 0" |
"divBy2 (Suc 0) = 0" |
"divBy2 (Suc(Suc n)) = Suc(divBy2 n)"

value "divBy2 7"

lemma "divBy2 n = n div 2"
  apply (induct n rule:divBy2.induct)
    apply auto
  done

(* Example 9 *)

lemma "(index (1::nat) [3,4,1,3])=2"
using [[simp_trace=true]]
apply auto
oops

(* Exercise 10 *)
fun nth2:: "nat \<Rightarrow> 'a list \<Rightarrow> 'a"
where
"nth2 0 (x#_)=x" |
"nth2 x (y#ys)= (nth2 (x - 1) ys)"

fun index2:: "'a \<Rightarrow> 'a list \<Rightarrow> nat"
where
"index2 x (y#ys)= (if x=y then 0 else 1+(index2 x ys))"

lemma "(List.member l e) \<longrightarrow> nth2 (index2 e l) l= e"
  apply (induct l)
   apply auto
  using member_rec(2) apply fastforce
  by (simp add: member_rec(1))

(* Exercise 11 *)


fun isSet:: "'a list \<Rightarrow> bool"
where
"isSet []=True" |
"isSet (x#xs)=(if (List.member xs x) then False else (isSet xs))"

value "makeList 6"

lemma memberMakelist: "y > x \<longrightarrow> \<not>(List.member (makeList x) y)"
  apply (induct x)
  apply auto
  apply (simp add: member_rec(2))
  by (simp add: member_rec(1))

lemma "isSet (makeList x)"
  apply (induct x)
   apply auto
  using memberMakelist by blast

(* Example 10 *)

(* Avec un lemme incorrect dont la preuve est terminée par "sorry"... *)
lemma falseLemma: "A"
  sorry

(* ... On peut prouver n'importe quoi *)
lemma "(1::nat)+1=0"
apply (insert falseLemma)
apply auto
done

end