theory ManualFixedPoint
imports Main
begin

datatype Person = P0 | P1 | P2 | P3

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

definition infection_step :: "infected \<Rightarrow> infected" where
  "infection_step I = 
    I \<union> (\<Union>p \<in> I. sample_network p)"



lemma "infection_step {} = {}"
  by (simp add: infection_step_def)

lemma "infection_step {P0} = {P0, P1}"
  by (auto simp add: infection_step_def sample_network_def)

lemma "infection_step {P1} = {P0, P1, P2}"  
  by (auto simp add: infection_step_def sample_network_def)

lemma "infection_step {P0, P1} = {P0, P1, P2}"
  by (auto simp add: infection_step_def sample_network_def)

lemma "infection_step {P0, P1, P2} = {P0, P1, P2, P3}"
  by (auto simp add: infection_step_def sample_network_def)

lemma "infection_step {P0, P1, P2, P3} = {P0, P1, P2, P3}"
  by (auto simp add: infection_step_def sample_network_def)


theorem fixed_points: 
  "infection_step I = I \<longleftrightarrow> (I = {} \<or> I = {P0, P1, P2, P3})"
  unfolding infection_step_def sample_network_def
  apply auto
  apply (case_tac I; auto)+
  apply (metis Person.exhaust insert_iff)
  apply (case_tac x; auto)+
  done

end