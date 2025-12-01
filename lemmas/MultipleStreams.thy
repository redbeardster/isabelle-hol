theory MultipleStreams
imports Main
begin

codatatype 'a stream = SCons (shd: 'a) (stl: "'a stream")

primcorec constant_stream :: "'a \<Rightarrow> 'a stream" where
  "shd (constant_stream x) = x"
| "stl (constant_stream x) = constant_stream x"

primcorec nats_from :: "nat \<Rightarrow> nat stream" where
  "shd (nats_from n) = n"
| "stl (nats_from n) = nats_from (n + 1)"

(* Разные конкретные потоки *)
definition nat_constant :: "nat stream" where
  "nat_constant = constant_stream 100"

definition string_constant :: "string stream" where
  "string_constant = constant_stream ''test''"

definition counting_stream :: "nat stream" where  
  "counting_stream = nats_from 0"


end