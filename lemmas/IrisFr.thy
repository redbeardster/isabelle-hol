theory IrisFr
imports Main
begin

(*
 fun member:: "'a \<Rightarrow> 'a list \<Rightarrow> bool" where 
"member x [] = False" |
"member x (y#ys) = (if x = y then True else member x ys)"


(* fun remove:: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "remove x [] = []" 
| "remove x (y#ys) = (if x = y then ys else y#(remove x ys))"

value "remove (1::nat) [1,1,1,1,2,3]" *)

fun remove2:: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "remove2 x [] = []" 
| "remove2 x (y#ys) = (if x = y then remove2 x ys else y#(remove2 x ys))"

value "remove2 (1::nat) [1,1,1,1,2,3]"

thm remove2.induct

 lemma " \<not> (member x (remove2 x l))"
   apply (induct l)
    apply auto
   done

  export_code member remove2 in SML

lemma remove2_member: "\<forall>x l. \<not> (member x (remove2 x l))"
proof (rule allI, rule allI)
  fix x l
  show "\<not> (member x (remove2 x l))"
  proof (induct l)
    case Nil
    show ?case
      by (simp add: member.simps(1) remove2.simps(1))
  next
    case (Cons y ys)
    show ?case
    proof (cases "x = y")
      case True
      (* Если x = y, то remove2 x (y#ys) = remove2 x ys *)
      hence "remove2 x (y#ys) = remove2 x ys"
        by (simp add: remove2.simps(2))
      (* По индукционному предположению \<not> (member x (remove2 x ys)) *)
      with Cons show ?thesis
        by simp
    next
      case False
      (* Если x \<noteq> y, то remove2 x (y#ys) = y # remove2 x ys *)
      hence "remove2 x (y#ys) = y # remove2 x ys"
        by (simp add: remove2.simps(2))
      (* Проверяем, содержится ли x в y # remove2 x ys *)
      show ?thesis
      proof
        assume "member x (remove2 x (y#ys))"
        hence "member x (y # remove2 x ys)"
          using \<open>remove2 x (y#ys) = y # remove2 x ys\<close> by simp
        (* Если member x (y # remove2 x ys), то либо x = y, либо member x (remove2 x ys) *)
        hence "x = y \<or> member x (remove2 x ys)"
        by (simp add: False)
        (* Но x \<noteq> y (по условию False), и по индукционному предположению \<not> (member x (remove2 x ys)) *)
        with False Cons show False
          by simp
      qed
    qed
  qed
qed



lemma "(p1 \<and> p2) \<longrightarrow> p1"
  by auto

lemma "(p1 \<and> p2) \<longrightarrow> p3"
  nitpick
  oops

lemma "(rains \<longrightarrow> umbrella) \<and> \<not> umbrella \<longrightarrow> \<not> rains"
  nitpick
  by auto


lemma "\<forall>x. p(x) \<Longrightarrow> \<exists>x. p(x)"
  by auto

lemma "\<exists>x .p(x) \<Longrightarrow> \<forall> x . p(x)"
  sorry

lemma "\<forall> x. ev(x) \<Longrightarrow> od(s(x))"
  nitpick
  sorry

lemma "\<forall>(x::nat) y . x > y \<Longrightarrow> x +1 > y  +1"
  nitpick
  by auto
  
lemma " (x::nat) > (y::nat) \<Longrightarrow> x +1 > y  +1"
  nitpick
  by auto

lemma "\<forall> m n. (\<not> (m < n) \<and> m < n +1) \<Longrightarrow> m = n"
  nitpick
  by auto

lemma "\<forall> (x::int) . \<exists>y . x + y = 0"
  nitpick
  by arith

lemma "\<forall> y. (\<not>p(f(y))) \<longleftrightarrow> p(f(y))"
  nitpick
  sorry

lemma "\<forall> y . p(f(y)) \<Longrightarrow> p(f(y + 1))"
  nitpick
  by auto

value "append [1::nat] (append [2] [4::nat,5,6])"

definition "add1 = append [1::nat]"
value "add1 [2,3]"

definition "addNc = (\<lambda> (x,y).  x + y)"
value "addNc (1, 2)::nat"


definition "add = (\<lambda>(x::nat) . \<lambda>y. x + y)"
value "add 1 2"

definition "incr = (\<lambda>(x::nat). add 1 x )"

definition "triple = (\<lambda>f x . (f (f (f x))))"
value "triple incr 0"
value "triple add1 [2,3]"

definition "plus3 = triple incr"

value "plus3 10"
value "map incr [1,2,3]"
value "map (\<lambda>(x::nat). x > 4) [0,1,2,3,4,5,6,7]"

value "Cons 0 (Cons(Suc 0) Nil)"
value "Cons (0::nat) ( Nil)"

lemma "3::nat \<equiv> Suc(Suc(Suc 0))"
  by arith

lemma "[1,1,1] \<equiv>   Cons (Suc 0) (Cons (Suc 0) (Cons(Suc 0) Nil))"
  by auto

lemma "hd [1,2] \<equiv> Suc 0"
  by auto

lemma "[1,2] = (Cons x y) \<Longrightarrow> x = 1"
  by auto

value "rev [1::nat,2,3]"

lemma "\<forall> x. rev [x] = [x]"
  by auto

value "map (\<lambda>(x::nat). x * 2 )[1,2,3]"

lemma "\<forall> x y z. append(append x y) z = append x (append y z )"
  by auto

lemma "length (map f l)  = length l"
  by auto

lemma "member (2::nat) [1,2,3] = True"
  apply (subst member.simps)
  apply (simp del: member.simps)
  apply (subst member.simps)
  apply (simp del: member.simps)
  done


fun index :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
"index x []  = 0" |
"index x (y#ys) = (if x = y then 0 else 1 + (index x ys))"

value "index (4::nat) [1,2,3,4,5]"




lemma "List.nth l (index e l) = e "
  nitpick
sorry

lemma "l \<noteq> [] \<longrightarrow> (List.nth l (index e l) = e)"
  nitpick
  sorry


fun nth:: "nat \<Rightarrow> 'a list \<Rightarrow> 'a"
where
"nth 0 (x#_)=x" |
"nth x (y#ys)= (nth (x - 1) ys)"


lemma "List.member l e \<Longrightarrow> nth(index e l ) l = e"
  apply (induct l)
   apply auto
   apply (simp add: member_rec(2))
  apply (simp add: member_rec(1))
  done
  



(* function (sequential) member:: "'a \<Rightarrow> 'a list \<Rightarrow> bool"
  where 
"member e [] = False" |
"member e (x#xs) = (if e = x then True else member e xs)"
     apply pat_completeness
    apply auto
  done

termination member 
  apply (relation "measure (\<lambda>(x,y). (length y))")
   apply auto
  done *)

(* fun f:: "nat \<Rightarrow> nat"
  where 
"f 0 = 0" |
"f x = f (x -1)"
 *)

fun f2 :: "int \<Rightarrow> int"
  where 
"f2 x = (if x <= 0 then 0 else f2 (x -1))"


function (sequential) f3 :: "nat \<Rightarrow> nat \<Rightarrow> nat"
where
"f3 x y = (if x >= 10 then 0 else f3(x+1) (y+1))"
  by pat_completeness auto

termination f3 
  apply (relation "measure (\<lambda>(x,y). 10 -x)")
  by auto



fun sumList:: "nat list \<Rightarrow> nat"
  where 
  "sumList [] = 0" |
  "sumList (x#xs) = x + sumList xs"

value "sumList [1,2,3,4,5]"

fun sumNat :: "nat \<Rightarrow> nat"
  where 
"sumNat 0 = 0" | 
 "sumNat n = n + sumNat (n-1)"

value "sumNat 5"


fun makeList:: "nat \<Rightarrow> nat list"
where
"makeList 0 =[]" |
"makeList i = (i#(makeList (i - 1)))"

value "makeList 10"


lemma "sumList (makeList x ) = sumNat x"
  apply (induct x)
   apply auto
  sorry  



datatype token = MyString string | MyInt int
  
value "MyString ''abc''"
value "MyInt 10"


datatype 'a binTree = Leaf | Node 'a "'a binTree" "'a binTree"

lemma "(x::nat) <4 \<longrightarrow> x*x < 10"
  apply (case_tac "x=0") (* OR: (case_tac "x=0 \<or> x=1 \<or> x= 2 \<or> x=3")*)
  apply auto
  apply (case_tac "x = 1")
  apply auto
  apply (case_tac "x = 2")
   apply auto
  apply (case_tac "x = 3")
   apply auto
  done

datatype color = Black | White | Grey

fun notBlack:: "color \<Rightarrow> bool"
  where 
"notBlack Black = False" | 
"notBlack _ = True"

value "notBlack Black"

lemma "notBlack(c) \<longrightarrow> (c = White \<or> c = Grey)" 
  apply (case_tac "c")
    apply auto
  done

lemma "append l [] = l"
  apply (induct l)
   apply auto
  done

fun append :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
"append [] l2 = l2" |
"append (x#xs) l2 = (x#(append xs l2))"

lemma "length (append l1 l2) \<ge> length (l2)"
  apply (induction l1)
   apply auto
  done

definition "tree1 = Node (1::nat) (Node 2 Leaf Leaf) (Node 3 Leaf Leaf)"

fun numNodes :: "'a binTree \<Rightarrow> nat"
  where
    "numNodes Leaf = 0" |
"numNodes (Node _ tg td) = 1 + (numNodes tg) + (numNodes td)"

value "numNodes tree1"


fun member:: "'a \<Rightarrow> 'a binTree \<Rightarrow> bool"
  where 
"member _ Leaf = False" | 
"member x (Node y tg td) = (if x = y then True else (member x tg ) \<or> (member x td))"

fun subTree :: "'a binTree \<Rightarrow> 'a binTree \<Rightarrow> bool"
  where 
"subTree Leaf Leaf = True" |
"subTree _ Leaf = False" | 
"subTree  x (Node y tg td) = ( if x = (Node y tg td) then True else ( (subTree x tg) \<or> (subTree x td)))"

value "subTree (Node (1::nat) Leaf leaf) (Node 2 (Node 1 Leaf Leaf ) Leaf)"

lemma "member x t \<longrightarrow> numNodes t \<ge> 1"
  apply auto
  apply (induct t)
   apply auto
  done
  
lemma "subTree x y \<Longrightarrow> (numNodes x) \<le> (numNodes y)"
  apply (induction y)
   apply auto
  sorry
  

lemma "(index (1::nat) [3,4,1,3]) = 2"
  apply auto
done


fun isSet :: "'a list \<Rightarrow> bool" 
  where 
"isSet [] = True" |
"isSet (x#xs) = (if (List.member xs x ) then False else (isSet xs))"

value "isSet [1::nat,2,3]"
value "isSet [1::nat,2,2,3]"

value "makeList 3"

lemma makeListSuc : "j > n \<Longrightarrow> \<not> (List.member (makeList n) j)"
  apply (induct n)
   apply auto
   apply (simp add: member_rec(2))
  by (simp add: member_rec(1))

lemma "isSet (makeList n) = True"
  apply (induct n)
   apply auto
  by (simp add: makeListSuc)


(* lemma falseLemma : "A"
  sorry

lemma "(1::nat) + 1 = 0"
  apply (insert falseLemma)
  apply auto
  done
 *)

type_synonym transid = "nat * nat * nat"

datatype message = 
  Pay transid nat
  | Ack transid nat
  | Cancel transid

fun f :: "message \<Rightarrow> nat"
  where 
  "f (Pay _ 0) = 10" |
  "f (Pay _ m) = m"  |
  "f (Ack _ _) = 1"  |
  "f (Cancel _) = 2"

lemma "((f mess) > 0)"
  apply (case_tac mess)
    prefer 2
    apply simp
   prefer 2 
   apply simp
  apply simp
  apply (rename_tac tid montant)
  apply (case_tac montant)
   apply auto
  done
*)

(* lemma sym: "((x=<y) \<and> (y=<x)) \<longrightarrow> (x=y)" *)


fun leq::"nat \<Rightarrow> nat \<Rightarrow> bool"   (infix "=<" 65)
where 
"leq 0 _ = True" |
"leq (Suc _) 0 = False" |
"leq (Suc x) (Suc y) = leq x y"


lemma sym: "((x =< y) \<and> (y =< x ) \<longrightarrow> (x=y))"
  apply (induct x arbitrary: y)
   prefer 2
   apply auto
     apply (case_tac y)
      apply auto
     apply(case_tac y)
   apply auto
  done
  
lemma "((x::nat)+4)*(y+5) \<ge> x *y"
  by (simp add: mult_le_mono)


datatype state = Init| LuA | LuB | Final
datatype letter = A | B | C | D

fun transition:: "letter * state \<Rightarrow> state"
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

fun execution:: "letter list * state \<Rightarrow> state"
where
  "execution([],e) = e" |
  "execution((x#xs),e) = execution(xs,transition(x,e))"

value "execution ([A,B,D], Init)"


lemma zeroLetter: "execution([A,B,C], e) = Final"
  apply (case_tac e )
     apply auto
  done

theorem zeroLetter2: "execution([x,y,z],e) = Final \<longrightarrow> (x=A \<and> y = B \<and> z=C)"
  apply (case_tac x)
 apply (case_tac [1-] y)
apply (case_tac [1-] z)
apply (case_tac [1-] e)
apply auto 
  done

theorem execAppend: "\<forall> e. execution(l1@l2,e)= execution(l2,execution(l1,e))"
apply (induct l1)
apply auto
done


theorem "execution(l@[A,B,C],e)=Final"
  using execAppend zeroLetter by auto


fun count :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" 
  where
"count x [] = 0" | 
"count x (y#ys) = (if x = y then 1 + (count x ys) else count x ys )"

value "count (1::nat) [1,2,3,1,1,1,1]"

lemma "count x xs \<le> length xs"
  apply (induction xs)
   apply auto
  done




end