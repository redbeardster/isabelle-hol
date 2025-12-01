theory CorrectProof
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

lemma "not_surjective_implies_proper_subset":
  assumes "\<not>surjective f"
  shows "C \<subset> UNIV"
  using assms unfolding surjective_def  
  using C_definition by blast

  

(* 
lemma not_surjective_implies_proper_subset_simple:
  assumes "\<not>surjective f"
  shows "C \<subset> UNIV"
proof -
  (* Получаем y такой, что f никогда не принимает значение y*)
  obtain y where "\<forall>x. f x \<noteq> y"
    using assms unfolding surjective_def  using B_infinite finite_code by blast  
  (* Показываем, что этот y не принадлежит C*)
  have "y \<notin> C"
  proof
    assume "y \<in> C"
    then obtain x where "f x = y" 
      unfolding C_definition using C_definition by blast
    with \<open>\<forall>x. f x \<noteq> y\<close> show False
      by sledgehammer
  qed
  
(*  -- Если есть элемент не в C, то C \<noteq> UNIV*)
  show ?thesis
    using \<open>y \<notin> C\<close> by auto
qed
 *)

(* lemma not_surjective_implies_proper_subset_simple:
  assumes "\<not>surjective f"
  shows "C \<subset> UNIV"
  using assms 
  unfolding surjective_def C_definition
proof -
  assume "\<not> (\<forall>y. \<exists>x. f x = y)"
   obtain y where "\<forall>x. f x \<noteq> y"   using B_infinite finite_code by blast
   have "y \<notin> C"    by (smt (verit, ccfv_threshold) C_definition CollectD \<open>\<forall>x. f x \<noteq> y\<close>)
   then
   show ?thesis 
   using B_infinite finite by blast
qed *)

(* lemma not_surjective_implies_proper_subset_simple:
  assumes "\<not>surjective f"
  shows "C \<subset> UNIV"
proof -
  obtain y where "\<forall>x. f x \<noteq> y"
    using assms unfolding surjective_def   using B_infinite finite_code by blast
  have "y \<notin> C"
    using \<open>\<forall>x. f x \<noteq> y\<close> unfolding C_definition  by (smt (verit, best) C_definition mem_Collect_eq)
  show ?thesis
    using \<open>y \<notin> C\<close>  using B_infinite finite by blast
qed *)

(* lemma explicit_version:
  assumes "\<not>surjective f"
  shows "C \<subset> UNIV"
proof -
  (*  Шаг 1: Раскрываем определение сюръективности *)
  from assms have "\<not>(\<forall>y. \<exists>x. f x = y)"
    unfolding surjective_def  using B_infinite finite_code by blast
(*   -- Шаг 2: Преобразуем по закону де Моргана *)
  then obtain y where "\<forall>x. f x \<noteq> y"  using C_definition assms by blast
(*   -- Шаг 3: Показываем, что этот y не в C *)
  have "y \<notin> C"
    unfolding C_definition
    using \<open>\<forall>x. f x \<noteq> y\<close>  using B_infinite finite_code by blast  
(*   -- Шаг 4: Заключаем, что C \<noteq> UNIV *)
  have "C \<noteq> UNIV"
    using \<open>y \<notin> C\<close> using B_infinite finite_code by blast    
(*   -- Шаг 5: А C \<subseteq> UNIV всегда верно *)
  have "C \<subseteq> UNIV" by simp
    
(*   -- Итог: C \<subset> UNIV *)
  show ?thesis
    using \<open>C \<subseteq> UNIV\<close> \<open>C \<noteq> UNIV\<close> by auto
qed *)

(*
lemma explicit_version_clean:
  assumes "\<not>surjective f"
  shows "C \<subset> UNIV"
proof -
  from assms have "\<not>(\<forall>y. \<exists>x. f x = y)"
    unfolding surjective_def by blast  
  then obtain y where "\<forall>x. f x \<noteq> y" by blast    
  have "y \<notin> C"
    unfolding C_definition using \<open>\<forall>x. f x \<noteq> y\<close> by auto    
  have "C \<noteq> UNIV"
    using \<open>y \<notin> C\<close> by auto    
  have "C \<subseteq> UNIV" by simp    
  show ?thesis
    using \<open>C \<subseteq> UNIV\<close> \<open>C \<noteq> UNIV\<close> by simp
qed
 *)

(* lemma explicit_version_clean:
  assumes "\<not>surjective f"
  shows "C \<subset> UNIV"
proof -
  obtain y where hy: "\<forall>x. f x \<noteq> y"
    using assms unfolding surjective_def using C_definition by blast
  have "y \<notin> C" 
    unfolding C_definition using hy using C_definition  by blast
  show ?thesis using \<open>y \<notin> C\<close>  using C_definition by blast
qed *)

(* 
lemma explicit_version_elegant:
  assumes "\<not>surjective f"
  shows "C \<subset> UNIV"
proof -
  obtain y where "\<forall>x. f x \<noteq> y"
    using assms unfolding surjective_def by blast
  have "y \<notin> C" 
    unfolding C_definition using \<open>\<forall>x. f x \<noteq> y\<close> by simp
  show ?thesis using \<open>y \<notin> C\<close> by auto
qed
 *)

(* lemma explicit_version_elegant:
  assumes "\<not>surjective f"
  shows "C \<subset> UNIV"
proof -
  obtain y where "\<forall>x. f x \<noteq> y"
    using assms unfolding surjective_def by blast
  hence "y \<notin> C" 
    unfolding C_definition by auto
  thus ?thesis by auto
qed
 *)



end


