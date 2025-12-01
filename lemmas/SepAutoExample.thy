theory SepAutoExample
  imports Main "HOL-Imperative_HOL.Imperative_HOL"
begin

typedecl node
consts
  val :: "node \<Rightarrow> int"
  next_ :: "node \<Rightarrow> node ptr"

end