theory VerifiedList
imports
  "AutoCorres.AutoCorres"
begin

install_C_file "pool_list.c"
autocorres "pool_list.c"

context pool_list begin
 
term list_length'


(*
lemma list_length_terminates:
  "\<forall>head s. \<exists>result. list_length' head s = result"
  by auto

 lemma list_length_non_negative:
  "\<forall>head s. case list_length' head s of Some r \<Rightarrow> r \<ge> 0 | None \<Rightarrow> True"
  sorry 


lemma list_length_non_negative_simple:
  "\<forall>head s r s'. list_length' head s = Some r \<longrightarrow> r \<ge> 0"
  
   by (metis list_length_non_negative option.case(2)) 


definition valid_node_ptr :: "Node_C ptr \<Rightarrow> lifted_globals \<Rightarrow> bool" where
  "valid_node_ptr p s \<equiv> p = NULL \<or> is_valid_Node_C  s p"

inductive valid_list :: "Node_C ptr \<Rightarrow> lifted_globals \<Rightarrow> bool" where
  valid_list_NULL: "valid_list NULL s"
| valid_list_cons: "\<lbrakk> 
    p \<noteq> NULL;
    is_valid_Node_C s p;
    valid_list (next_C (heap_Node_C s p)) s 
  \<rbrakk> \<Longrightarrow> valid_list p s"
 *)

end (* end of `context pool_list` *)
end
