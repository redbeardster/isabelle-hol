theory cm3
imports Main "~~/src/HOL/Library/Code_Target_Nat"  (* to hide 0, Succ rep. of nats *)
begin

(* Objectif exercice 3, voir les let in et case of en application *)

fun contains:: "'a => 'a list => bool"
where
"contains e []     = False" |
"contains e (x#xs) = (if e=x then True else (contains e xs))"


value "contains (1::nat) [2,3,1,4]"

fun even:: "nat \<Rightarrow> bool" and
odd::"nat \<Rightarrow> bool"
where
"even 0=True" |
"even (Suc x)=odd x" |
"odd 0=False" |
"odd (Suc x)= even x"

value "even 10"
value "even 11"
value "odd 11"


(* Example 2 *)

function (sequential) contains2::"'a \<Rightarrow> 'a list \<Rightarrow> bool"
where
"contains2 e []     = False" |
"contains2 e (x#xs) = (if e=x then True else (contains2 e xs))"
apply pat_completeness
apply auto
done
termination contains2
apply (relation "measure (%(x,y). (length y))")
apply auto
done


(* Exercice 1 *)
fun f::"nat \<Rightarrow> nat"
where
"f 0= 6" |
"f x=f (x - 1)" 


fun f2::"int \<Rightarrow> int"
where
"f2 x = (if x<=0 then 0 else f2 (x - 1))"


fun f3::"nat \<Rightarrow> nat \<Rightarrow> nat"
where
"f3 x y= (if x\<ge>10 then 0 else f3 (x + 1) (y + 1))"


function (sequential)f3::"nat \<Rightarrow> nat \<Rightarrow> nat"
where
"f3 x y= (if x\<ge>10 then 0 else f3 (x + 1) (y + 1))"
apply pat_completeness 
apply auto
done
termination f3
apply (relation "measure (\<lambda>(x,y). (10-x))")
apply auto
  done

value "(10::nat) - 20"

  oops
datatype absInt= Mint int | Top


(* Exercice 2 *)

fun sumList::"nat list \<Rightarrow> nat"
  where 
"sumList [] = 0" |
"sumList (x#xs) = ( x + sumList xs)"

value "sumList [1,2,3,4]"

fun sumNat::"nat \<Rightarrow> nat"
  where
 "sumNat 0 = 0"
|"sumNat n = n + (sumNat (n-1))"

value "sumNat 10"

fun makeList::"nat \<Rightarrow> nat list"
  where
"makeList 0 = [0]" |
"makeList x = x#makeList (x-1)"

value "makeList 5"

lemma "sumList (makeList n) = sumNat n"
  nitpick
  apply auto
  sorry

(* Exercise 3 *)

datatype color = Black | White | Grey

fun notBlack::"color \<Rightarrow> bool"
  where
  "notBlack Black = False" |
  "notBlack _ = True"

fun notBlack2::"color \<Rightarrow> bool"
  where
  "notBlack2 x= (case x of Black \<Rightarrow> False | _ \<Rightarrow> True)"

datatype token = TInt int | TString string

value "TInt 13"

fun sumToken::"token \<Rightarrow> token \<Rightarrow> int"
  where
"sumToken (TInt t1) (TInt t2) = t1 + t2" |
"sumToken _ _ = 0"

fun sumToken2::"token \<Rightarrow> token \<Rightarrow> int"
  where
"sumToken2 x y = (case (x,y) of ((TInt t1),(TInt t2)) \<Rightarrow> t1 + t2 | _ \<Rightarrow> 0)"

datatype 'a tree = Feuille | Noeud 'a "'a tree" "'a tree"

fun merge:: "color tree \<Rightarrow> color"
  where
"merge Feuille = Black" |
"merge (Noeud e ag ad) = 
  (let couleurG= (merge ag) in
    (let couleurD= (merge ad) in
       (case (e,couleurG,couleurD) of 
           (Black,Black,Black) \<Rightarrow> Black |
           _ \<Rightarrow> Grey
      )))"

(* 
t1=      Black
         /   \
      White  Black 

t2=      Black
         /   \
      Black  Black 

*)
definition "t1= Noeud Black (Noeud White Feuille Feuille) (Noeud Black Feuille Feuille)"
value "t1"
definition "t2= Noeud Black (Noeud Black Feuille Feuille) (Noeud Black Feuille Feuille)"
value "t2"


value "merge t1"
value "merge t2"


(* Exercice 3 *)

(* Type abbreviations *)
type_synonym name="(string * string)"
type_synonym ('a,'b) pair="('a * 'b)"

(* Don't be surprised the interpret does not display the 
   type abbreviation that you defined :/ *)
value "(''Leonard'',''Michalon'')"
value "(1::nat,''toto'')"

end




