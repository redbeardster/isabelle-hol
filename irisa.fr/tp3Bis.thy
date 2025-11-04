theory tp3Bis
imports Main 
begin

(* Exploitez les générateurs de contre-exemples (nitpick/quickcheck) pour trouver des contre-exemples
  sur les lemmes des exercices 1,2,3 et 4 *)

(* --------- exercice 1 ---------------- *)
(* Avec quickcheck et nitpick *)
lemma exo1: "([x,y,z] @ [z,y,x]) = ([z,y,x] @ [x,y,z])"
oops

(* --------- exercice 2 ---------------- *)
fun contains::"'a => 'a list => bool"
where 
"contains _ [] = False" |
"contains e (x # xs) = (if (x=e) then True else (contains e xs))"

fun oneDelete:: "'a => 'a list => 'a list"
where 
"oneDelete e [] = []" |
"oneDelete e (a#l) = (if e=a then l else a#(oneDelete e l))"

fun isPermut:: "'a list \<Rightarrow> 'a list \<Rightarrow> bool"
where
"isPermut [] [] = True" |
"isPermut (_#_) [] = False" |
"isPermut [] (_#_) = False" |
"isPermut (x#xs) l = (if (contains x l) then (isPermut xs (oneDelete x l)) else False)"

(* Avec quickcheck et nitpick *)
lemma exo2: "\<forall> l1. (((length l1) = (length l2)) \<and> (length l1 >10) \<and> (isPermut l1 l2)) \<longrightarrow> (isPermut (oneDelete x l1) (oneDelete y l2))"
oops

(* --------- exercice 3 ---------------- *)
(* Contrexemples avec quickcheck, nitpick n'y parvient pas dans un temps raisonnable *)
lemma exo3: "((x>4)\<and>(y>30)\<and>(z>12)) \<longrightarrow> (((x::nat)*y)+(y*z) \<noteq> (x*z)+(z*y))"
oops



end