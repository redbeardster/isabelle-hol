theory DAGExample
  imports Main Graph_Theory.Digraph
begin

context fin_digraph
begin

definition "acyclic \<equiv> \<not>(\<exists>c. cycle c)"