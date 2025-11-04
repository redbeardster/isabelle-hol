theory cm7
imports Main 
begin


(* -------- Model-checking explained in Isabelle/HOL ----------- *)
(* States of the automaton *)
datatype etat= Init | LuA | LuB | Final

(* Letter to type on the digicode *)
datatype lettre= A | B | C | D 

fun transition:: "lettre*etat \<Rightarrow> etat"
where
"transition(A,Init) = LuA" |
"transition(_,Init) = Init" |
"transition(B,LuA) = LuB" |
"transition(A,LuA) = LuA" |
"transition(_,LuA) = Init" |
"transition(C,LuB) = Final" |
"transition(A,LuB) = LuA" |
"transition(_,LuB) = Init" |
"transition(A,Final) = LuA" |
"transition(_,Final) = Init"


fun execution:: "lettre list * etat \<Rightarrow> etat"
where
"execution([],e) = e" |
"execution((x#xs),e) = execution(xs,transition(x,e))"


value "execution([A,B],Init)"
value "execution([A,B,C],Init)"


(* Exercise 1 *)
(* 1) Whatever the state e we start from, after typing  [A,B,C] we reach the Final State *)

lemma zeroLetter: "execution([A,B,C], e) = Final"
apply (case_tac e)
apply auto
done


(* Exercise 2 *)
(* 2) Whatever the state e we start from, the only way to reach the Final State by typing three letters
   is to have typed [A,B,C] *)

theorem zeroLetter2: "execution([x,y,z],e) = Final \<longrightarrow> (x=A \<and> y = B \<and> z=C)"
apply (case_tac x)
apply (case_tac [1-] y)
apply (case_tac [1-] z)
apply (case_tac [1-] e)
apply auto
done


(* 1) can be generalized to any sequence of letters if it ends by [A,B,C] *)

theorem execAppend: "\<forall> e. execution(l1@l2,e)= execution(l2,execution(l1,e))"
apply (induct l1)
apply auto
done

theorem "execution(l@[A,B,C],e)=Final"
by (metis execAppend zeroLetter)


(* 2) can be generalized in the same way *)

theorem "execution(l@[x,y,z],Init)=Final \<longrightarrow> x=A \<and> y=B \<and> z=C"
by (metis (lifting) execAppend zeroLetter2)


(* ----- Static analyzer explained in Isabelle/HOL -------*)

(* Exercice 3 *)

(* We have D=int and we choose the following abstract domain: D# *)

datatype absInt= Neg | Zero | Pos | Undef | Any   

(*       Any
       /  |  \ 
     Neg Zero Pos
       \  |  /
        Undef   *)

(* Concretization function states, for each abstract element, what is the corresponding int set *)
fun concretize:: "absInt \<Rightarrow> int set"
where
"concretize Zero = {0}" |
"concretize Pos  = {x. x>0}" |
"concretize Neg  = {x. x<0}" |
"concretize Any  = {x. True}" |
"concretize Undef = {}"

(* This function cannot be used for programming but only for stating the correctness theorem! *)
(* In particular, value fails on concretize *)
value "concretize Pos"

(* Exercice 3 *)


fun absPlus:: "absInt \<Rightarrow> absInt \<Rightarrow> absInt" (infix "+#" 65)  
where 
"absPlus Undef     _          = Undef"   |
"absPlus _         Undef      = Undef"   |
"absPlus Zero      x          = x"       |
"absPlus x         Zero       = x"       |
"absPlus Pos       Pos        = Pos"     |
"absPlus Neg       Neg        = Neg"     |
"absPlus Neg       Pos        = Any"     |
"absPlus Pos       Neg        = Any"     |
"absPlus Any       _          = Any"     |
"absPlus _         Any        = Any"     


(* Exercice 4 *)


lemma abs_correct: "(x\<in>(concretize abs_x)) \<and> (y \<in> (concretize abs_y)) \<longrightarrow>  (x+y) \<in> (concretize (abs_x +# abs_y))"
  apply (case_tac abs_x)
  apply (case_tac [1-] abs_y)
  apply auto
  done

end