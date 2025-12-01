theory SomeTypes
  imports Main 

begin

consts MAX_CAPACITY :: nat
axiomatization where MAX_CAPACITY_pos: "MAX_CAPACITY > 0"


record state =
  current_count :: nat

definition new_invariant :: "state \<Rightarrow> bool" where
  "new_invariant s \<equiv> current_count s \<le> MAX_CAPACITY"

 typedef small_nat = "{n::nat. n < 100}"
   using linorder_not_less by fastforce 

datatype Color = Red | Green | Blue

instantiation Color :: linorder
begin
fun less_eq_Color :: "Color \<Rightarrow> Color \<Rightarrow> bool" where
  "less_eq_Color Red _ = True"
| "less_eq_Color Green Green = True"
| "less_eq_Color Green Blue = True"
| "less_eq_Color Blue Blue = True"
| "less_eq_Color _ _ = False"

definition less_Color :: "Color \<Rightarrow> Color \<Rightarrow> bool" where
  "less_Color x y \<longleftrightarrow> x \<le> y \<and> x \<noteq> y"

instance proof
  fix x y z :: Color
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    unfolding less_Color_def by (cases x; cases y) auto
  show "x \<le> x" by (cases x) simp_all
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y" by (cases x; cases y) auto
  show "x \<le> y \<or> y \<le> x" by (cases x; cases y) auto
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z" by (cases x; cases y; cases z) auto
qed
end

axiomatization
  A :: "'a set" and
  B :: "'b set" and
  C :: "'c set" and
  f :: "'d \<Rightarrow> 'c"
where
  A_finite: "finite A" and
  B_infinite: "\<not>finite B" and
  C_definition: "C = {x. \<exists>y. f y = x}"

(* lemma C_is_range: "C = range f"
  using C_definition by blast
 *)


lemma element_in_C: "f x \<in> C"
  using C_definition by auto

lemma finite_A: "finite A"
  by (rule A_finite)

lemma infinite_B: "infinite B" 
  by (simp add: B_infinite)

lemma C_subset_univ: "C \<subseteq> UNIV"
  by simp

(* lemma surjective_iff: "(\<forall>x. x \<in> C) \<longleftrightarrow> surjective f"
(*   unfolding surjective_def *) 
  using C_definition by 
 *)  

(* lemma C_is_range: "C = range f"
  using C_definition by auto *)

definition surjective :: "('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "surjective g \<longleftrightarrow> (\<forall>y. \<exists>x. g x = y)"

(* lemma surjective_iff: "surjective f \<longleftrightarrow> (C = UNIV)"
  unfolding surjective_def using C_definition by force
 *)

(* lemma not_surjective_implies_proper_subset:
  assumes "\<not>surjective f"
  shows "C \<subset> UNIV"
  using assms unfolding surjective_def 
  using C_definition by blast

lemma "\<exists>x. x \<notin> C \<longleftrightarrow> (\<exists>x. \<forall>y. f y \<noteq> x)"
  using C_definition surjective_def  UNIV_eq_I element_in_C psubset_eq by blast
 *)



end