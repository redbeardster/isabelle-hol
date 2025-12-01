theory DAGExample
  imports Main 
begin

type_synonym vertex = nat
type_synonym edge = "vertex \<times> vertex"

type_synonym graph = "vertex set \<times> edge set"

definition "dag \<equiv> \<lambda>(V, E). finite V \<and> (\<exists>xs. distinct xs \<and> set xs = V \<and> (\<forall>(u, v)\<in>E. \<exists>i j. i < j \<and> xs ! i = u \<and> xs ! j = v))"



end
