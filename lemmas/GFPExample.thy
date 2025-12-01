theory GFPExample
imports Main
begin

context
  fixes system_transitions :: "('state \<times> 'state) set"
begin
datatype state = A | B | C

(* Способ 1: Использовать обычные кортежи *)
inductive_set example_transitions :: "(state \<times> state) set" where
  "(A, B) \<in> example_transitions"
| "(B, C) \<in> example_transitions"
| "(C, A) \<in> example_transitions"


(* Способ 2: С именованными правилами *)
inductive_set example_transitions_named :: "(state \<times> state) set" where
  A_to_B: "(A, B) \<in> example_transitions_named"
| B_to_C: "(B, C) \<in> example_transitions_named"
| C_to_A: "(C, A) \<in> example_transitions_named"


(* Теперь лемма с gfp *)
lemma gfp_property:
  "gfp (\<lambda>X. {s. \<exists>s'. (s, s') \<in> example_transitions \<and> s' \<in> X}) = 
   {s. \<exists>inf_path. inf_path 0 = s \<and> (\<forall>i. (inf_path i, inf_path (i+1)) \<in> example_transitions)}"
  unfolding example_transitions_def
  sorry

end

codatatype 'a stream = SCons (shd: 'a) (stl: "'a stream")

(* Коиндуктивное определение: "все элементы удовлетворяют P" *)
coinductive all_stream :: "('a \<Rightarrow> bool) \<Rightarrow> 'a stream \<Rightarrow> bool" where
  "P (shd s) \<Longrightarrow> all_stream P (stl s) \<Longrightarrow> all_stream P s"

primcorec constant_stream :: "'a \<Rightarrow> 'a stream" where
  "shd (constant_stream x) = x"
| "stl (constant_stream x) = constant_stream x"


lemma "constant_stream 5 = SCons 5 (constant_stream 5)"
  by (simp add: stream.expand)





end