theory Scratch 
  imports Main "HOL-TLA.TLA" 

begin
(* 
fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add 0 n = n" |
"add (Suc m) n = Suc(add m n)"

(*  fun double :: "nat \<Rightarrow> nat" where
"double 0 = 0" |
"double (Suc n) = Suc (Suc (double n))" *)

 lemma nSm_Snm[simp]: "add n (Suc m) = add (Suc n) m"
apply (induction n)
apply (auto)
done 


fun itadd :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"itadd 0 n = n" |
"itadd (Suc m) n = itadd m (Suc n)"

theorem add_itadd: "itadd m n = add m n"
  by (induction m arbitrary: n) auto
 *)



(* typedecl person
typedecl action


consts
  Attempts :: "person => action option stfun"
  Succeeds :: "person => bool stfun"
 *)

consts 
  Trying :: "bool stfun"
  Winning :: "bool stfun"

definition SuccessTheorem :: temporal where
  "SuccessTheorem \<equiv>  leadsto Trying Winning"


(*
consts
  acting    :: "bool stfun"
  succeeding :: "bool stfun" 
  energy    :: "nat stfun"

definition ActionLeadsToSuccess :: temporal where
  "ActionLeadsToSuccess \<equiv>  leadsto acting  succeeding"

definition PersistentActionGuaranteesSuccess :: temporal where
  "PersistentActionGuaranteesSuccess \<equiv> leadsto (Box acting) (Dmd succeeding)"


lemma action_implies_eventual_success:
  "\<turnstile> ActionLeadsToSuccess \<longrightarrow> \<box>(\<box>acting \<leadsto> \<diamond> succeeding)"
  unfolding ActionLeadsToSuccess_def
  proof -
  have "\<turnstile> (Init acting \<longrightarrow> \<diamond>succeeding) \<longrightarrow> Init \<box>acting \<longrightarrow> \<diamond>succeeding"
    using BoxRec Init.Init_simps(1) by fastforce
  then show "\<turnstile> (acting \<leadsto> succeeding) \<longrightarrow> \<box>(\<box>acting \<leadsto> \<diamond> succeeding)"
  by (simp add: STL4 leadsto_def more_temp_simps3(2,3))
  qed


lemma action_implies_eventual_success_simple:
  "\<turnstile> ActionLeadsToSuccess \<longrightarrow> (\<box>acting \<leadsto> \<diamond>succeeding)"
  unfolding ActionLeadsToSuccess_def leadsto_def
  using BoxRec  by (metis ActionLeadsToSuccess_def action_implies_eventual_success leadsto_def more_temp_simps3(2))

(* В TLA используем правильный синтаксис для временных изменений *)
axiomatization where
  energy_depletes: "\<turnstile> energy$ = energy - 1" and  
  success_requires_energy: "\<turnstile> energy > 0 \<longrightarrow> (acting \<longrightarrow> \<diamond>succeeding)" and
  exhaustion: "\<turnstile> energy = 0 \<longrightarrow> \<box>\<not>succeeding" and
  initial_energy: "\<turnstile> energy = 10"  (* Начальная энергия *)


(* Альтернатива: через действия *)
consts
  DepleteEnergy :: action

axiomatization where  
  deplete_axiom: "\<turnstile> DepleteEnergy \<longrightarrow> (energy$ = energy - 1)" and
  default_depletion: "\<turnstile> unchanged energy \<longrightarrow> energy$ = energy - 1"
*)

consts
  acting    :: "bool stfun"
  succeeding :: "bool stfun"
  system_works :: "bool stfun"  (* Система функционирует *)

lemma semantic_difference:
  "\<turnstile> \<box>(\<box>acting \<leadsto> \<diamond>succeeding) \<longrightarrow> (\<box>acting \<leadsto> \<diamond>succeeding)"  
  using reflT by blast

definition EventuallyPermanentFailure :: temporal where
  "EventuallyPermanentFailure \<equiv> Dmd (Box (\<lambda>s. \<not>succeeding s))"

lemma part1_existence:
  "\<turnstile> \<exists>acting succeeding.  acting \<leadsto> succeeding"
  using BoxRec Init.Init_simps  STL4 leadsto_def more_temp_simps3 
proof -
  have "\<turnstile> \<box>\<not> (#False::state \<times> state \<Rightarrow> bool)"
    by simp
  then show ?thesis
    by (metis (no_types) Valid_def inteq_reflection leadsto_false more_temp_simps3(5) temp_simps(2) unl_Rex)
qed

lemma part2_existence:  
  "\<turnstile> \<exists>acting succeeding.  \<diamond>\<box>(\<lambda>s. \<not>succeeding s)"
  using BoxRec Init.Init_simps  STL4 leadsto_def more_temp_simps3  
proof -
  obtain bb :: "(behavior \<Rightarrow> bool) \<Rightarrow> behavior" and bba :: "(behavior \<Rightarrow> bool) \<Rightarrow> behavior" where
    f1: "\<forall>p. (\<turnstile> p) \<or> \<not> p (bb p)"
    by (metis (lifting) intI)
  have "\<exists>p. (\<turnstile> \<lambda>b. \<not> p (b::'b))"
    by blast
  then show ?thesis
    using f1 by (smt (z3) InitDmd STL4E intD more_temp_simps3(2,8) necT unl_Rex)
qed

theorem
fixes x::nat and c n
assumes "x < c" and "n > 0"
shows "n*x < n*c"
  using assms(1,2) by auto


theorem "(x::nat) < 5 \<Longrightarrow> 2*x+3 \<le> 2*5 + 3"
proof -
assume "x < 5"
  then have "2*x \<le> 2*5"  by simp
  then show ?thesis by auto
qed


(* lemma commutativity: "(A \<and> B) \<Longrightarrow> (B \<and> A)"
proof  
  assume "A \<and> B"  
  hence "A" by (rule conjE)   
  from \<open>A \<and> B\<close> have "B" by (rule conjE)
  with \<open>A\<close> show "B \<and> A" by (rule conjI) 
qed
 *)


(*  lemma commutativity_arrow: "(A \<and> B) \<longrightarrow> (B \<and> A)"
proof (rule impI)
  assume "A \<and> B"
  hence "A" by (erule conjE)  
  from \<open>A \<and> B\<close> have "B" by (erule conjE) 
  from \<open>B\<close> \<open>A\<close> show "B \<and> A" by (rule conjI)
qed *)

(*
  this one works
*)
lemma commutativity_arrow: "(A \<and> B) \<longrightarrow> (B \<and> A)"
proof (rule impI)
  assume "A \<and> B"
  have "A" using \<open>A \<and> B\<close> by (rule conjE)
  have "B" using \<open>A \<and> B\<close> by (rule conjE) 
  show "B \<and> A" using \<open>B\<close> \<open>A\<close> by (rule conjI)
qed

(*
  this one works too
*)
(* lemma commutativity_arrow: "(A \<and> B) \<longrightarrow> (B \<and> A)"
proof (rule impI)
  assume "A \<and> B"
  then have "A" proof (rule conjE) qed  \<comment> \<open>Явное применение conjE для A\<close>
  from \<open>A \<and> B\<close> have "B" proof (rule conjE) qed  \<comment> \<open>Явное применение conjE для B\<close>
  show "B \<and> A" using \<open>B\<close> \<open>A\<close> by (rule conjI)
qed
 *)

definition withdrawsum_partial :: "nat \<Rightarrow> nat \<rightharpoonup> nat" where
"withdrawsum_partial a b = 
  (if b \<le> a then Some (a - b) else None)"

value "withdrawsum_partial 10 10"

lemma "A \<subseteq> B \<and> B \<subseteq> C \<Longrightarrow> A \<subseteq> C"
proof  
  assume "A \<subseteq> B \<and> B \<subseteq> C" 
  hence "A \<subseteq> B" and "B \<subseteq> C" by auto 
  fix a
  assume "a \<in> A" 
  with \<open>A \<subseteq> B\<close> \<open>a \<in> A\<close> have "a \<in> B" by blast
  with \<open>B \<subseteq> C \<close> show "a \<in> C" ..
qed 
 
lemma "A \<subseteq> B \<and> B \<subseteq> C \<Longrightarrow> A \<subseteq> C"
proof
  assume prems: "A \<subseteq> B \<and> B \<subseteq> C"
  hence "A \<subseteq> B" and "B \<subseteq> C" by auto
  fix x assume "x \<in> A"
  with \<open>A \<subseteq> B\<close> have "x \<in> B" ..
  with \<open>B \<subseteq> C\<close> show "x \<in> C" ..
qed

lemma "A \<subseteq> B \<and> B \<subseteq> C \<Longrightarrow> A \<subseteq> C"
proof
  assume "A \<subseteq> B \<and> B \<subseteq> C"
  then have "A \<subseteq> B" and "B \<subseteq> C" by auto
  fix x
  assume "x \<in> A"
  with \<open>A \<subseteq> B\<close> have "x \<in> B" by (rule subsetD)
  with \<open>B \<subseteq> C\<close> show "x \<in> C" by (rule subsetD)
qed

lemma "A \<subseteq> B \<and> B \<subseteq> C \<Longrightarrow> A \<subseteq> C"
proof -  
  assume "A \<subseteq> B \<and> B \<subseteq> C"
  hence "A \<subseteq> B" and "B \<subseteq> C" by auto
  show "A \<subseteq> C"  
  proof
    fix a assume "a \<in> A"
    with \<open>A \<subseteq> B\<close> have "a \<in> B" ..
    with \<open>B \<subseteq> C\<close> show "a \<in> C" ..
  qed
qed

lemma "P \<Longrightarrow> P  \<longrightarrow> Q \<Longrightarrow> P \<and> Q"
  by auto


lemma "(\<exists>x . P (f x) \<and> Q x) \<Longrightarrow> \<exists>x . P x"
  apply (erule exE)
  apply (erule conjE)
  apply (rule exI)
  apply assumption
  done

lemma "abs_m_1":
  fixes m::int 
  assumes mn: "abs (m*n) = 1"
  shows "abs m = 1"
  using abs_zmult_eq_1 mn by blast

(*
*)
consts
  is_tungsten :: "'a \<Rightarrow> bool"
  has_high_melting_point :: "'a \<Rightarrow> bool" 
  is_metal :: "'a \<Rightarrow> bool"

(* lemma syllogism_rule:
  assumes "\<exists>x. M x"          
  assumes "\<forall>x. M x \<longrightarrow> P x"  
  assumes "\<forall>x. M x \<longrightarrow> S x"    
  shows "\<exists>x. S x \<and> P x"      
proof -
  from assms(1) obtain m where "M m" by auto
  have "S m" using assms(3) \<open>M m\<close> by blast
  have "P m" using assms(2) \<open>M m\<close> by blast
  show ?thesis using \<open>S m\<close> \<open>P m\<close> by blast
qed
 *)
axiomatization where
  tungsten_exists: "\<exists>x. is_tungsten x"
and  
  premise1: "\<forall>x. is_tungsten x \<longrightarrow> has_high_melting_point x"
and
  premise2: "\<forall>x. is_tungsten x \<longrightarrow> is_metal x"

theorem tungsten_example:
  "\<exists>x. is_metal x \<and> has_high_melting_point x"
  by (meson premise1 premise2 tungsten_exists)


datatype 'a bt = 
  Lf 
  | Br 'a "'a bt" "'a bt" 

fun reflect :: "'a bt \<Rightarrow> 'a bt" where 
"reflect Lf = Lf" 
| "reflect (Br a t1 t2) = Br a (reflect t2) (reflect t1)"


lemma reflect_reflect_ident: "reflect (reflect t) = t"
proof (induction t)
  case Lf
  then show ?case by simp
next
  case (Br x1 t1 t2)
  then show ?case by simp
qed


lemma "P \<or> Q \<Longrightarrow> Q \<or> P"
  apply (erule disjE)
   apply (rule disjI2)
   apply assumption
  apply (rule disjI1)
  apply assumption
  done

lemma "\<exists>x. P \<and> Q(x) \<Longrightarrow> P \<and> (\<exists>x. Q(x))"
  by auto


lemma Least_equality:
  "\<lbrakk>P (k::nat); \<forall> x. P x \<longrightarrow> k \<le> x\<rbrakk> \<Longrightarrow> (LEAST x. P x) = k"
   by (simp add: Least_equality)
  

lemma "(LEAST n::nat. n \<ge> 5) = 5"
  by (simp add: Least_equality)


lemma "(LEAST n::nat. n \<ge> 5) = 5"
proof (rule Least_equality)
  // Подцель 1: P(5), т.е. 5 \<ge> 5
  show "5 \<ge> (5::nat)" by simp
  
  // Подцель 2: \<forall>y. y \<ge> 5 \<rightarrow> 5 \<le> y
  fix y :: nat
  assume "y \<ge> 5"
  show "5 \<le> y" by (simp add: \<open>y \<ge> 5\<close>)
qed








end