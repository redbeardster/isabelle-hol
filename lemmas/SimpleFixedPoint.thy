theory SimpleFixedPoint
imports Main
begin

definition Person :: "nat set" where
  "Person = {0,1,2,3}"

definition P0 :: nat where "P0 = 0"
definition P1 :: nat where "P1 = 1"  
definition P2 :: nat where "P2 = 2"
definition P3 :: nat where "P3 = 3"

type_synonym network = "nat \<Rightarrow> nat set"
type_synonym infected = "nat set"

definition sample_network :: network where
  "sample_network p = (
    if p = P0 then {P1}
    else if p = P1 then {P0, P2}
    else if p = P2 then {P1, P3}
    else if p = P3 then {P2}
    else {}
  )"

definition infection_step :: "infected \<Rightarrow> infected" where
  "infection_step I = 
    I \<union> (\<Union>p \<in> I. sample_network p)"


value "infection_step {}"
value "infection_step {P0}"
value "infection_step {P0, P1}"

lemma "(\<exists>x y :: 'a::order).  \<not>(x \<le> y) \<and> \<not>(y \<le> x)"


end