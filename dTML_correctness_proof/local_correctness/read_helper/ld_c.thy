(*Rules for identifying the acceptable values to be read by read-only transactions*)
theory ld_c
  imports "../../DTML" 
begin

lemma ld_coh_lt_vrew:
  assumes "(\<tau> \<sigma>) [val   \<leftarrow> a ]\<^sub>t (\<tau> \<sigma>')"
and " \<forall>z. z = syst \<or> ( writeAux \<sigma> z) \<or> ( (coh (\<tau> \<sigma>) z a \<le> vrnew (\<tau> \<sigma>) z) ) "
 and " t \<noteq> syst "
and "total_wfs (\<tau> \<sigma> )"
and "   writeAux \<sigma> t = False "
and " (\<forall>z.   writeAux \<sigma>' z = writeAux \<sigma> z) "
and " a \<noteq> glb"
shows   " \<forall>z. z = syst \<or> ( writeAux \<sigma>' z) \<or> (  (coh (\<tau> \<sigma>') z a \<le> vrnew (\<tau> \<sigma>') z) ) "
 using assms
  apply (simp add:  step_def)
  apply (simp add: load_trans_def  Let_def)
  apply clarify
  apply (case_tac " t= z ")
  apply (subgoal_tac "  coh (\<tau> \<sigma>') t a \<le> vrnew (\<tau> \<sigma>') t" )
   prefer 2
   apply (case_tac "  ind \<noteq> coh (\<tau> \<sigma>) t a ")
  apply (subgoal_tac "  (vrnew (\<tau> \<sigma>') t) = ind")
  prefer 2
     apply ( simp  add: split: if_split_asm)
   apply (subgoal_tac "  (coh (\<tau> \<sigma>') z a ) = ind")
  prefer 2
     apply simp
    apply (metis linorder_le_cases)

   apply (subgoal_tac " vrnew (\<tau> \<sigma>') t = vrnew (\<tau> \<sigma>) t")
    prefer 2
   apply ( simp  add: split: if_split_asm)
   apply simp
  apply blast
  apply blast
  by (metis assms(1) ld_coh_dt_ni ld_vrnew_dt_ni)



lemma ld_coh_lt_vrew_simp:
  assumes "ts [val   \<leftarrow> a ]\<^sub>t ts'"
and " ( (coh ts t a \<le> vrnew ts  t) ) "
and "total_wfs ts"
and " a \<noteq> glb"
shows   "  (  (coh ts' t a \<le> vrnew ts' t) ) "
 using assms
  apply (simp add:  step_def)
  apply (simp add: load_trans_def  Let_def)
  apply clarify
  apply (subgoal_tac "  coh ts' t a \<le> vrnew ts' t" )
   prefer 2
   apply (case_tac "  ind \<noteq> coh ts  t a ")
   apply (subgoal_tac "  (coh ts' t a ) = ind")
  prefer 2
    apply simp
   apply ( simp  add: split: if_split_asm)
  apply ( simp  add: split: if_split_asm)
  by blast





end