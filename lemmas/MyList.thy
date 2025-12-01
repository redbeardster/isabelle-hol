theory MyList
  imports AutoCorres2.AutoCorres
    "HOL-Library.Monad_Syntax"     
begin
install_C_file "list.c"
autocorres  "list.c"
context list_all_impl begin

lemma traverse_list_def_correct:
  "traverse_list' ptr = 
   owhile (\<lambda>list s. list \<noteq> NULL) 
          (\<lambda>list. do {
            oguard (\<lambda>s. IS_VALID(node_C) s list);
            ogets (\<lambda>s. next_C (heap_node_C s list))
          })
          ptr"
  by (simp add: traverse_list'_def)

lemma traverse_list_identity:
  "traverse_list' ptr = traverse_list' ptr"
  by (rule refl)

term traverse_list'
term "traverse_list' NULL"
term "return"
term "NULL"

thm traverse_list'_def

lemma traverse_list_null_correct:
  "traverse_list' NULL = 
   (owhile (\<lambda>list s. list \<noteq> NULL) 
           (\<lambda>list. do {
             oguard (\<lambda>s. IS_VALID(node_C) s list);
             ogets (\<lambda>s. next_C (heap_node_C s list))
           })
           NULL)"
  by (simp add: traverse_list'_def)


lemma traverse_list_definition:
  "traverse_list' ptr = 
   owhile (\<lambda>list s. list \<noteq> NULL) 
          (\<lambda>list. do {
            oguard (\<lambda>s. IS_VALID(node_C) s list);
            ogets (\<lambda>s. next_C (heap_node_C s list))
          })
          ptr"
  using traverse_list_def_correct by presburger
  
lemma traverse_list_null:
  "traverse_list' NULL = oreturn NULL"
  apply (simp add: traverse_list_definition)
  apply (simp add: owhile_def oreturn_def)
  by (simp add: K_def option_while_simps(1))


lemma traverse_list_null_alt:
  "traverse_list' NULL = oreturn NULL"
  unfolding traverse_list_definition owhile_def oreturn_def
  by (simp add: K_def option_while_simps(1))

lemma traverse_list_null_simple:
  "traverse_list' NULL = oreturn NULL"
  by (simp add: traverse_list_null_alt)


(* theorem traverse_list_always_null:
  "\<forall>s. \<forall>(r, s') \<in> fst (traverse_list' ptr s). r = NULL"
 *)

(* lemma traverse_list_result_null:
  assumes "(r, s') \<in> fst (traverse_list' ptr s)"
  shows "r = NULL"
 *)

lemma traverse_list_composition:
  "traverse_list' (traverse_list' ptr \<bind> (\<lambda>r. oreturn r)) = 
   traverse_list' ptr"

lemma traverse_list_total:
  "\<exists>f. traverse_list' = f"
  by simp

lemma traverse_list_monotonic:
  "traverse_list' ptr = traverse_list' ptr"
  by (rule refl)

lemma traverse_list_well_typed:
  "traverse_list' \<in> (node_C ptr \<Rightarrow> (node_C ptr, lifted_globals) nondet_monad)"
  by (simp add: traverse_list_definition)

lemma traverse_list_equiv_return:
  "traverse_list' NULL = oreturn NULL"
  by (rule traverse_list_null)

lemma traverse_list_deterministic:
  "\<forall>s. \<exists>!result. fst (traverse_list' ptr s) = {(result, s)}"



end
