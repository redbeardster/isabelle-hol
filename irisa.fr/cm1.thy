theory cm1
imports Main 
begin


(* 2) Propositional logic *)

lemma "(p1 \<and> p2) \<longrightarrow> p1"
  apply auto
  done

lemma "(p1 \<and> p2) \<longrightarrow> p3"
  nitpick
  oops

(* Exercise 1 *)

lemma "a \<or> b"
  nitpick
  oops

lemma "(((a \<or> b) \<longrightarrow> \<not>c) \<or> (a \<longrightarrow> b)) \<longrightarrow> a \<longrightarrow> c"
  nitpick
  oops

lemma "(Rains \<longrightarrow> Umbrella \<and> ~Umbrella) \<longrightarrow> ~Rains"
  nitpick
  apply auto
  done

lemma "(A \<longrightarrow> B) = (\<not> A \<or> B)"
  apply auto
  done
  

(* 3) First order logic *)

(* Exercise 2 *)
lemma "\<forall>x. p(x)\<longrightarrow>(\<exists>x. p(x))"
  apply auto
  done

lemma "(\<exists>x. p(x))\<longrightarrow>(\<forall>x. p(x))"
  nitpick
  oops

lemma "\<forall>x. ev (x) \<longrightarrow>  od(s(x))"
  nitpick
  oops

lemma "\<forall>(x::nat) y. x > y \<longrightarrow> (x + 1) > (y + 1)"
  apply auto
  done

lemma "\<forall>(X::int). \<exists>Y.  X + Y = 0"
  apply auto
  sorry

(* Example 24 *)
(* Explain, satisfiable formulas, tautology and contradictions *)

lemma "\<forall>y. p(f(y))"
nitpick (* so what? *) 
oops

lemma "\<not>(\<forall>y. p(f(y)))"
nitpick  (* so what? *) 
oops


lemma "(\<forall>y. p(f(y)) = (\<forall>y. \<not> p(f(y))))"
nitpick (* so what? *) 
oops


lemma "\<not> ( (\<forall>y. p(f(y)) = (\<forall> y. \<not> p(f(y)))) )"
apply auto  (* so what? *)  
done
end


