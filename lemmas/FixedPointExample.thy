theory FixedPointExample
imports Main
begin

datatype Person = P0 | P1 | P2 | P3

instantiation Person :: enum
begin
definition "enum_Person = [P0, P1, P2, P3]"
definition "enum_all_Person P = (\<forall>x :: Person. P x)"  
definition "enum_ex_Person P = (\<exists>x :: Person. P x)"
instance
  apply standard
  apply (auto simp add: enum_Person_def enum_all_Person_def enum_ex_Person_def)
  apply (case_tac x)
  apply auto
  done
end

type_synonym network = "Person \<Rightarrow> Person set"
type_synonym infected = "Person set"


definition sample_network :: network where
  "sample_network p = (
    case p of
      P0 \<Rightarrow> {P1}
    | P1 \<Rightarrow> {P0, P2}
    | P2 \<Rightarrow> {P1, P3}
    | P3 \<Rightarrow> {P2}
  )"

definition infection_rule :: "network \<Rightarrow> infected \<Rightarrow> infected" where
  "infection_rule net infected = 
    infected \<union> {p. \<exists>q. q \<in> infected \<and> p \<in> net q}"

(* definition infection_step :: "infected \<Rightarrow> infected" where
  "infection_step = infection_rule sample_network"
 *)

definition infection_step :: "infected \<Rightarrow> infected" where
  "infection_step I = 
    I \<union> (\<Union>p \<in> I. sample_network p)"

lemma step_empty: "infection_step {} = {}"
  unfolding infection_step_def infection_rule_def sample_network_def
  by auto

lemma step_P0: "infection_step {P0} = {P0, P1}"
  unfolding infection_step_def infection_rule_def sample_network_def
  by auto

lemma step_P1: "infection_step {P1} = {P0, P1, P2}"  
  unfolding infection_step_def infection_rule_def sample_network_def
  by auto

lemma step_all: "infection_step {P0, P1, P2, P3} = {P0, P1, P2, P3}"
  unfolding infection_step_def infection_rule_def sample_network_def
  by auto

(* lemma all_fixed_points:
  "infection_step I = I \<longleftrightarrow> I \<in> {{}, {P0, P1, P2, P3}}"
  unfolding infection_step_def infection_rule_def sample_network_def
   unfolding infection_step_def sample_network_def
   sorry *)


lemma "lfp infection_step = {}"
  unfolding lfp_def
  by (simp add: cInf_eq_minimum step_empty)


lemma lfp_is_empty: "lfp infection_step = {}"
proof -
have fixed: "infection_step {} = {}"
  by (simp add: step_empty)
have least: "\<And>I. infection_step I = I \<Longrightarrow> {} \<subseteq> I"
  by auto
 show ?thesis
    by (metis fixed least lfp_eqI)
qed

(* lemma gfp_rocks: "gfp infection_step = {P0, P1, P2, P3}"
  unfolding gfp_def infection_step_def infection_rule_def sample_network_def
  by blast *)


(* lemma gfp_rocks: "gfp infection_step = {P0, P1, P2, P3}"
proof -

  have fixed: "infection_step {P0, P1, P2, P3} = {P0, P1, P2, P3}"
    by (auto simp: infection_step_def infection_rule_def sample_network_def
             split: Person.splits)
  
  have greatest: "\<And>I. infection_step I = I \<Longrightarrow> I \<subseteq> {P0, P1, P2, P3}"
    unfolding infection_step_def infection_rule_def sample_network_def
    apply auto
    apply (case_tac x; auto)+
    done
  
  show ?thesis
    by (metis fixed greatest gfp_eqI)
qed *)

(* 
lemma gfp_rocks: "gfp infection_step = {P0, P1, P2, P3}"
proof -
  have fixed: "infection_step {P0, P1, P2, P3} = {P0, P1, P2, P3}"
    by (auto simp: infection_step_def infection_rule_def sample_network_def
             split: Person.splits)
  
  have greatest: "\<And>I. infection_step I = I \<Longrightarrow> I \<subseteq> {P0, P1, P2, P3}"
  proof -
    fix I
    assume "infection_step I = I"
    hence eq: "I \<union> (\<Union>p\<in>I. sample_network p) = I"
      unfolding infection_step_def infection_rule_def by simp
    
    show "I \<subseteq> {P0, P1, P2, P3}"
    proof
      fix x
      assume "x \<in> I"
      show "x \<in> {P0, P1, P2, P3}"
        by (cases x rule: Person.exhaust) simp_all
    qed
  qed
  
  show ?thesis
    by (metis fixed greatest gfp_eqI)
qed *)

lemma gfp_rocks: "gfp infection_step = {P0, P1, P2, P3}"
proof -
  have fixed: "infection_step {P0, P1, P2, P3} = {P0, P1, P2, P3}"
    unfolding infection_step_def infection_rule_def sample_network_def
    by (auto split: Person.splits)
  
  have greatest: "\<And>I. infection_step I = I \<Longrightarrow> I \<subseteq> {P0, P1, P2, P3}"
  proof
    fix I x
    assume "infection_step I = I" and "x \<in> I"
    show "x \<in> {P0, P1, P2, P3}"
      by (cases x rule: Person.exhaust) simp_all
  qed
  
  show ?thesis
    by (metis fixed greatest gfp_eqI)
qed


end

