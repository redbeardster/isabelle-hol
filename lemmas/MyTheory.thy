theory MyTheory
imports Main
begin

axiomatization
  A :: "'a set" and
  B :: "'b set" and
  C :: "'c set" and
  f :: "'d \<Rightarrow> 'c"
where
  A_finite: "finite A" and
  B_infinite: "\<not>finite B" and
  C_definition: "C = {x. \<exists>y. f y = x}"

definition surjective :: "('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "surjective g \<longleftrightarrow> (\<forall>y. \<exists>x. g x = y)"

lemma not_surjective_implies_proper_subset:
  assumes "\<not>surjective f"
  shows "C \<subset> UNIV"
proof -
  have "\<exists>y. \<forall>x. f x \<noteq> y"
  proof -
    from assms have "\<not>(\<forall>y. \<exists>x. f x = y)"
      unfolding surjective_def by simp
    thus ?thesis by blast
  qed
  then obtain y where "\<forall>x. f x \<noteq> y"  by blast    
  have "y \<notin> C"
    unfolding C_definition using \<open>\<forall>x. f x \<noteq> y\<close> by auto   
  show ?thesis
    using \<open>y \<notin> C\<close> by auto
qed

end