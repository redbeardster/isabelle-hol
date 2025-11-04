theory cm6 
imports Main "~~/src/HOL/Library/Code_Target_Nat"  (* to hide 0, Succ rep. of nats *)
begin


(* Exercise 1 *)

(* Programs are sequences of assignements (x:=y) or reads ( read(x) )
   where x,y are variable names.

   In a program, when executing an assignement x:=y, an exception is
   raised if y is undefined (either by another assignement or by a
   read).

   The objective of the analyzer is to guarantee that the execution of
   a program will be safe, i.e. exception free.

   For instance:

   the program   read(x); y:= x                   is safe 
   the program   read(x); y:= x; z:= u            is not safe 
      (it will raise an exception during execution because u is undefined)

   the program   read(x); y:= x; read(u); z:= u   is safe
   the program   read(u); read(x); y:= x; z:= u   is safe
 *)


(* Statements *)
datatype statement= Read string | Aff string string

(* Programs are statement lists *)
type_synonym program= "statement list"

(* sample programs *)
definition "p1= [(Read ''x''),(Aff ''y'' ''x'')]"
definition "p2= [(Aff ''y'' ''x'')]"
definition "p3= [(Aff ''x'' ''x''),(Read ''x'')]"
definition "p4= [(Read ''x''),(Aff ''y'' ''x''),(Aff ''z'' ''y'')]"
definition "p5= [(Read ''x''),(Aff ''y'' ''x''),(Read ''z''),(Aff ''u'' ''z'')]" 


(* The type of environments (or symbol tables) associating
   values to variable names  *)
type_synonym symTable= "(string * int) list"

(* a sample environment st1= {x\<rightarrow>24, y \<rightarrow> 18} *)
definition "st1= [(''x'',(24::int)),(''y'',18)]"


(* The function returning the value associated to a variable in an environment *)
datatype 'a option= None | Some 'a

fun assoc:: "'a \<Rightarrow> ('a * 'b) list \<Rightarrow> 'b option"
where
"assoc _ []    = None" |
"assoc x ((y,z)#ys)= (if x=y then (Some z) else (assoc x ys))"


value "assoc ''x'' st1"
value "assoc ''y'' st1"
value "assoc ''z'' st1"


(* The type of input channels (values read by the 'read' statements) *)
type_synonym inchan=  "int list"

(* The type of events that may occur while executing a program *)
datatype event= ReadEvent | Assignement string int | Exception


(* Program state is a tuple: (symTable * inchan * event list) *)
type_synonym pgState= "(symTable * inchan * event list)"


(* Interpreter/Evaluator for statements *)
(* In an assignement v1:=v2 if v2 is undefined then we add an "Exception" event in the event list *)

(* Interpreting/Evaluating one instruction Read/Aff *)
fun evalS:: "statement \<Rightarrow> pgState \<Rightarrow> pgState"
where
"evalS (Read v)    (st,(i#inch),evl) = ((v,i)#st,inch,ReadEvent#evl)" | 
"evalS (Read _)    (st,[],evl) = (st,[],evl)" | 
"evalS (Aff v1 v2) (st,inch,evl) = 
  (case (assoc v2 st) of None \<Rightarrow> (st,inch,Exception#evl) |
                         Some(i) \<Rightarrow> ((v1,i)#st,inch,(Assignement v1 i)#evl))"

(* Interpreting/Evaluating complete programs (i.e. lists of instructions) *)
fun evalP:: "program \<Rightarrow> pgState \<Rightarrow> pgState"
where
"evalP [] (st,inch,evl)         = (st,inch,evl)" |
"evalP ((Read _)#_) (st,[],evl) = (st,[],evl)" |
"evalP (s#xs) (st,inch,evl)     = (evalP xs (evalS s (st,inch,evl)))"


(* Recall that:
   p1 is 
          read(x)
          y := x

   "p1= [(Read ''x''),(Aff ''y'' ''x'')]" *)

value "evalP p1 ([],[10],[])"

(* Recall that:
   p2 is
         y:= x

  "p2= [(Aff ''y'' ''x'')]" *)

value "evalP p2 ([],[10],[])"

(* Recall that:
   p3 is 
         x:= x
         read(x)

   "p3= [(Aff ''x'' ''x''),(Read ''x'')]" *)
value "evalP p3 ([],[10],[])"
value "evalP p3 ([],[10],[])"

(* Recall that
   p4 is
         read(x)
         y:= x
         z:= y

   "p4= [(Read ''x''),(Aff ''y'' ''x''),(Aff ''z'' ''y'')]" *)

value "evalP p4 ([],[10],[])"

(* Recall that
   p5 is
         read(x)
         y:= x
         read(z)
         u:= z

   "p5= [(Read ''x''),(Aff ''y'' ''x''),(Read ''z''),(Aff ''u'' ''z'')]" *)

value "evalP p5 ([],[10,11],[])"
value "evalP p5 ([],[10],[])"

(* Exercise 1: We want to define a static analyzer guaranteeing that the execution of the program will be exception-free

   NO INPUT CHANNEL! the san function must give a verdict WHATEVER THE INPUT CHANNEL MAY BE

   fun san:: "program \<Rightarrow> bool"
*)

fun san:: "program \<Rightarrow> string list \<Rightarrow> bool"
  where 
"san [] _  = True" |
"san ((Read x)#r) s = san r (x#s)" |
"san ((Aff x y)#r) s  = ((List.member s y) \<and> (san r (x#s)))"

value "san p1 []"
value "san p2 []"
value "p2"

value "evalP p2 ([],[],[])"
value "san p3"
value "san p4"
value "san p5"

(* Exercise 2: define the BAD predicate 

   fun BAD::"pgState \<Rightarrow> bool"
*)

fun BAD::"pgState \<Rightarrow> bool"
  where 
"BAD (ts,inchan,event) = (List.member event Exception)"

value "BAD (evalP p1 ([],[10],[]))"
value "BAD (evalP p2 ([],[10],[]))"
value "BAD (evalP p3 ([],[10],[]))"

(* Exercise 3: define the correctness lemma for the static analyzer san *)

lemma "san p [] \<longrightarrow> (\<forall> inchan. \<not>BAD (evalP p ([],inchan,[])))"
  nitpick
  sorry


(* Example 1 *)

lemma "((x::nat)+4)*(y+5) >= x*y"
  using [[simp_trace=true,simp_trace_depth_limit=5]] 
  by (simp add: mult_le_mono)
  
  using [[simp_trace=true,simp_trace_depth_limit=5]] 
oops

(* Example 2 *)

fun memb::"'a => 'a list => bool"
where 
"memb _ [] = False" |
"memb e (x # xs) = (if (x=e) then True else (memb e xs))"


fun intersection:: "'a list => 'a list => 'a list"
where
"intersection [] l  = []" |
"intersection (e1#l1) l2 = (if (memb e1 l2) then (e1#(intersection l1 l2)) else (intersection l1 l2))"

theorem interMemb: "((memb e l1) \<and> (memb e l2)) \<longrightarrow> (memb e (intersection l1 l2))"
apply (induct l1)
   apply auto
  done

(* Exercise 4 *)

fun reverse:: "'a list \<Rightarrow> 'a list"
where
"reverse []=[]" |
"reverse (x#xs)= (reverse xs)@[x]"

lemma app_rev:"reverse (l1@l2)=(reverse l2)@(reverse l1)"
apply (induct l1)
apply auto
done

lemma rev_rev:"reverse (reverse l)=l"
apply (induct l)
apply auto
by (metis Cons_eq_appendI app_rev reverse.simps(2) self_append_conv2)


fun fastReverseAux:: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
"fastReverseAux [] y = y" |
"fastReverseAux (x#xs) y= fastReverseAux xs (x#y)"

fun fastReverse:: "'a list \<Rightarrow> 'a list"
where
"fastReverse l= fastReverseAux l []"

value "fastReverse [1::nat,2,3]"


lemma fast1: "\<forall> l2. (fastReverseAux l1 l2) = (reverse l1 @ l2)"
apply (induct l1)
apply auto
done

lemma "fastReverse (l1@l2)= (fastReverse l2)@(fastReverse l1)"
oops

lemma "fastReverse (fastReverse l)=l"
oops


(* Exercise 5 *)
fun power:: "nat \<Rightarrow> nat \<Rightarrow> nat"
where
"power _ 0= 1" |
"power x (Suc 0)= x" |
"power x (Suc y)= x*(power x y)"

value "power 3 2"

lemma powerOne: "power 1 x= 1"
apply (induct x)
apply auto
by (metis Suc_eq_plus1 add_eq_if cm6.power.simps(2) cm6.power.simps(3) nat.exhaust nat_mult_1)

lemma powerSuc: "(power x (Suc y))= x * (power x y)"
apply (induct y)
apply auto
done

lemma powerAdd: "(power x y) * (power x z)= (power x (y + z))"
apply (induct y)
apply auto
by (simp add: powerSuc)

lemma powerMult: "power (x * y) z= (power x z) * (power y z)"
apply (induct z)
apply auto
by (metis mult.assoc mult.commute powerSuc)

lemma powerPower: "(power (power x y) z)=(power x (y * z))"
apply (induct y)
apply auto
apply (metis One_nat_def powerOne)
by (metis powerAdd powerMult powerSuc)

lemma powerDiv2: "(y mod 2=1) --> x*(power (power x (y div 2)) 2) = power x y"
apply (induct y)
apply auto
apply (simp add: powerPower powerSuc)
by (metis One_nat_def add_diff_cancel_left' minus_mod_eq_div_mult plus_1_eq_Suc powerPower powerSuc)


value "(1::nat) mod 2"
value "(1::nat) div 2"
value "(3::nat) mod 2"
value "(3::nat) div 2"

function fastPower:: "nat \<Rightarrow> nat \<Rightarrow> nat"
where
"fastPower _ 0=1" |
"fastPower x (Suc 0)= x" |
"fastPower x (Suc (Suc 0))= x*x" |
"fastPower x (Suc (Suc (Suc y)))= (if ((Suc (Suc (Suc y))) mod 2)=0 
  then (fastPower (fastPower x ((Suc (Suc (Suc y))) div 2)) 2)
  else x*(fastPower (fastPower x ((Suc (Suc (Suc y))) div 2)) 2))"
apply pat_completeness
apply auto
done
termination fastPower
apply (relation "measure (%(x,y). y)")
apply auto
done


value "fastPower 2 10"

(* power 2 5      = 2 * (power 2 4) = 2 * (2 * power 2 3) = etc...  d'où 5 appels récursifs à power *)

(* fastPower 2 5  = 2 * (fastPower (fastPower 2 2) 2) = 2 * (4 * 4) d'où 2 apprels récursifs à fastPower *)



(* Prove the classical properties of exponentiation on fastPower *)

lemma fastPowerPower:"power x y = fastPower x y"
  apply (induct x y rule: fastPower.induct)
     apply auto
  apply (smt (verit, del_insts) cm6.power.simps(2) cm6.power.simps(3) dvd_div_mult_self even_Suc mult.assoc numeral_2_eq_2 odd_Suc_div_two powerMult powerPower)
  by (metis add.commute add_0 div_Suc div_mod_decomp mod_Suc_eq mod_self numeral_2_eq_2 powerPower powerSuc)

lemma fastPowerAdd: "(fastPower x y) * (fastPower x z)= (fastPower x (y + z))"
  using fastPowerPower powerAdd by presburger 

lemma fastPowerMult: "fastPower (x * y) z= (fastPower x z) * (fastPower y z)"
  using fastPowerPower powerMult by force
  

lemma fastPowerPowerFast: "(fastPower (fastPower x y) z)=(fastPower x (y * z))"
  using fastPowerPower powerPower by force
  

(* Exercice 6*)


fun contains::"'a => 'a list => bool"
where 
"contains _ [] = False" |
"contains e (x # xs) = (if (x=e) then True else (contains e xs))"


fun inter:: "'a list => 'a list => 'a list"
where
"inter [] l = l" |
"inter (e1#l1) l2 = (if (contains e1 l2) then e1#(inter l1 l2) else (inter l1 l2))"


lemma interMemb2: "((contains e l1) \<and> (contains e l2)) = (contains e (inter l1 l2))"
  nitpick
  oops

(* Exercice 7 *)

fun nbOccur::"'a \<Rightarrow> 'a list \<Rightarrow> nat"
where
"nbOccur x [] = 0" |
"nbOccur x (y#ys) = (if x=y then 1+(nbOccur x ys) else (nbOccur x ys))"

fun clean::"'a list => 'a list"
where
"clean []= []"|
"clean (e#l)= (if (contains e l) then l else (e#(clean l)))"

lemma clean_prop: "clean [x,y,x]= [y,x]"
oops

(* Exercice 8 *)

fun delete:: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where
"delete _ [] = []" |
"delete x (y#ys) = (if x=y then (delete x ys) else (y#(delete x ys)))"

lemma "contains x l \<longrightarrow> contains y l \<longrightarrow> x\<noteq>y \<longrightarrow> (contains x (delete y l))"
  apply (induct l) 
   apply simp
  apply simp    (* On ne peut pas utiliser notre hypothèse d'induction ... *)
  sorry         (* Car la propriété n'est pas inductive! *)

end
