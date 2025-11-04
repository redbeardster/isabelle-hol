theory Read_Begin_Global
imports "../../DTML"
begin

(*Begin annotation is stable against the DTML read operation*)
lemma Read_Begin_global:
assumes "thrdsvars"
and "total_wfs (\<tau> \<sigma>)"
and "pm_inv \<sigma> "
and  " \<forall>  t.  (   writer \<sigma> = Some t \<longrightarrow> odd (lastVal glb  (\<tau> \<sigma>)) )"(*persistent invariant*)
and " \<forall>  t. (  (   writer \<sigma>  = Some t    \<longrightarrow> \<lceil>glb\<rceil>\<^sub>t (\<tau> \<sigma>) ))"(*persistent invariant*)
and "glb_monotone_inv (\<tau> \<sigma>) " (*persistent invariant*)
and " (\<forall> b.  mem_tml_prop    glb b (\<tau> \<sigma>)) " (*persistent invariant*)
and " (Read_inv  tb  ((pc \<sigma>) tb)  \<sigma>)  "
and "  Begin_inv  ta  ((pc \<sigma>) ta) \<sigma>  "
and " TML_Read  tb   \<sigma> \<sigma>'"
and "((pc \<sigma>) tb) \<in> {ReadPending, ReadResponding} \<union>  reading \<union> {Aborted} "
and "((pc \<sigma>) ta) \<in> {BeginPending, BeginResponding } \<union> beginning \<union>  {Aborted} "
and " ta \<noteq> syst"
and "tb \<noteq> syst"
and "ta \<noteq> tb"
shows  "  Begin_inv  ta  ((pc \<sigma>') ta) \<sigma>'  " 
  using assms
  apply (unfold thrdsvars_def )
  apply (simp add:TML_Read_def Read_inv_def Begin_inv_def   )
  apply (cases "(pc \<sigma>) ta";simp; cases "(pc \<sigma>) tb" ;simp)
  apply (unfold total_wfs_def)
  apply ( simp add: split: if_split_asm)
  apply (metis assms(2) ld_coh_dt_ni ld_vrnew_dt_ni)
  apply ( simp add: split: if_split_asm)
  apply ( simp add: split: if_split_asm)
  apply (metis assms(2) cas_coh_dt_ni cas_vrnew_dt_ni)
  apply (metis assms(2) cas_coh_dt_ni cas_vrnew_dt_ni)
  apply (metis assms(2) ld_coh_dt_ni ld_vrnew_dt_ni)
  apply ( simp add: split: if_split_asm)
  apply ( simp add: split: if_split_asm)
  apply ( simp add: split: if_split_asm)
  apply ( simp add: split: if_split_asm) 
  apply (smt (verit, best) assms(2) lastVal_ni ld_coh_dt_ni ld_ov_ni ld_vrnew_dt_ni reg_same_ld_dr)
  apply ( simp add: split: if_split_asm)  
  apply ( simp add: split: if_split_asm)  
  apply (intro conjI)
  apply (metis cas_dt_ni reg_same_CAS_dt) apply (elim conjE disjE )
  apply (case_tac "    even (regs (\<tau> \<sigma>) ta DTML.loc)  ")
  apply simp
  apply (elim disjE)
  apply (intro impI)
  apply (subgoal_tac " lastVal glb (\<tau> \<sigma>') =  lastVal glb (\<tau> \<sigma>) ")
  prefer 2
  apply (metis cas_succ_lv_lc lastVal_def numeral_1_eq_Suc_0 numeral_eq_one_iff)
  apply (subgoal_tac " [glb]\<^sub>ta \<tau> \<sigma>' = [glb]\<^sub>ta \<tau> \<sigma>   ")
  prefer 2
  apply (simp add: step_def)
  apply clarify
  apply (subgoal_tac" \<tau> \<sigma>' =
cas_succ_trans tb ind glb (lastVal glb (\<tau> \<sigma>))
(lastVal glb (\<tau> \<sigma>)) c1  nv mnv (\<tau> \<sigma>)")
  prefer 2
  apply (metis cas_fail_reg numeral_1_eq_Suc_0 numeral_eq_one_iff zero_neq_one)
  using  cas_succ_ov_dt_lc 
  apply (metis Un_absorb)
  apply (simp add: total_wfs_def)
  apply (smt (verit, ccfv_SIG) assms(2) cas_le_daddr cas_ov_daddr_ni cas_wfs_preserved emptyE reg_same_CAS_dt subset_singletonD total_wfs_def)
  apply (metis One_nat_def cas_succ_lv_lc lastVal_def reg_same_CAS_dt)
  apply (metis reg_same_CAS_dt)
  apply (metis cas_fail_diff_lv less_irrefl_nat numeral_1_eq_Suc_0 numeral_eq_one_iff zero_neq_one)
  apply (smt (verit, best) One_nat_def assms(2) cas_coh_dt_ni cas_dt_ov_ni cas_fail_lastVal_same cas_le_daddr cas_sv_lc cas_vrnew_dt_ni reg_same_CAS_dt)
  apply (smt (verit, ccfv_SIG) assms(2) lastVal_ni ld_coh_dt_ni ld_ov_ni ld_vrnew_dt_ni reg_same_ld_dt)
  apply (simp add: split if_splits)
  apply (case_tac " regs (\<tau> \<sigma>) tb r3 = regs (\<tau> \<sigma>) tb DTML.loc")
  apply simp
  apply (smt (z3) PC.simps(1644) pc_aux)
  apply (simp add: Ready_total_def read_pre_def)
  apply (simp add: Ready_total_def read_pre_def)
  apply (smt (z3) assms(2) lastVal_ni ld_coh_dt_ni ld_coh_valof_dt_ni ld_le_lim_ni ld_oav_ni ld_ov_ni ld_vrnew_dt_ni reg_same_ld_dr)
  apply ( simp add: split: if_split_asm)  
  apply (simp add: Ready_total_def)
  apply (simp add: Ready_total_def)
  apply ( simp add: split: if_split_asm)  
  apply (subgoal_tac " [glb]\<^sub>ta \<tau> \<sigma>' = [glb]\<^sub>ta \<tau> \<sigma>   ")
  prefer 2
  apply (subgoal_tac " lastVal glb (\<tau> \<sigma>') = lastVal glb (\<tau> \<sigma>) ")
  prefer 2
  apply (metis assms(2) cas_succ_eq cas_succ_lv_lc lastVal_def numeral_1_eq_Suc_0 numeral_eq_one_iff)
  apply (simp add: step_def)
  apply clarify
  apply (subgoal_tac"  \<tau> \<sigma>' =
cas_succ_trans tb ind glb (regs (\<tau> \<sigma>) tb DTML.loc)
(regs (\<tau> \<sigma>) tb DTML.loc) c1  nv mnv (\<tau> \<sigma>)")
  prefer 2
  apply (metis cas_fail_reg numeral_1_eq_Suc_0 numeral_eq_one_iff zero_neq_one)
  apply (subgoal_tac " [glb]\<^sub>ta \<tau> \<sigma>' = [glb]\<^sub>ta \<tau> \<sigma> \<union>   { (regs (\<tau> \<sigma>) tb DTML.loc)} ")
  prefer 2
  apply (metis cas_succ_ov_dt_lc)
  apply (metis cas_fail_reg compval_def insert_absorb insert_is_Un lastVal_def numeral_1_eq_Suc_0 numeral_eq_one_iff sup.commute zero_neq_one)
  apply (subgoal_tac " \<forall> a. [a]\<^sub>ta \<tau> \<sigma>' = [a]\<^sub>ta \<tau> \<sigma>   ")
  prefer 2
  apply (metis cas_dt_ni cas_ov_daddr_ni subsetI subset_antisym)
  apply (simp add:  Ready_total_def read_pre_def)
  apply (case_tac " (odd (regs (\<tau> \<sigma>) ta DTML.loc))")
  apply simp
  apply (metis cas_fail_diff_lv numeral_1_eq_Suc_0 numeral_eq_one_iff zero_neq_one)
  apply (case_tac "  \<not> readAux \<sigma>' ta \<and> \<not> writeAux \<sigma>' ta ")
  apply simp
  apply (metis (no_types, lifting) One_nat_def cas_le_daddr cas_nlv_lc cas_succ_lv_lc lastVal_def reg_same_CAS_dt zero_neq_one)
  apply (smt (z3) assms(2) cas_coh_dt_ni cas_coh_valof_dt_ni cas_le_lim_dt_ni cas_vrnew_dt_ni reg_same_CAS_dt)
  apply (subgoal_tac " \<forall> a. [a]\<^sub>ta \<tau> \<sigma>' = [a]\<^sub>ta \<tau> \<sigma>   ")
  prefer 2
  apply (simp add: step_def)
  apply clarify
  apply (case_tac "  \<tau> \<sigma>' =
  cas_fail_trans tb ind glb (regs (\<tau> \<sigma>) tb DTML.loc)
 (regs (\<tau> \<sigma>) tb DTML.loc) c1 (\<tau> \<sigma>)")
  prefer 2
  apply (metis One_nat_def cas_suc_reg)
  apply (metis cas_fail_ov_ni)
  apply (simp add:  Ready_total_def read_pre_def)
  apply (case_tac " (odd (regs (\<tau> \<sigma>) ta DTML.loc))")
  apply (metis assms(2) cas_fail_oav_ni cas_lc cas_wfs_preserved numeral_1_eq_Suc_0 numeral_eq_one_iff reg_same_CAS_dt singletonD total_wfs_def)
  apply simp
  apply (case_tac "  \<not> readAux \<sigma>' ta \<and> \<not> writeAux \<sigma>' ta ")
  apply simp
  apply (metis One_nat_def assms(2) cas_fail_lastVal_same cas_le_daddr cas_sv_lc reg_same_CAS_dt)
  apply simp
  apply (metis (no_types, opaque_lifting) assms(2) cas_coh_dt_ni cas_coh_valof_dt_ni cas_le_lim_dt_ni cas_vrnew_dt_ni reg_same_CAS_dt)
  apply (simp add:  Ready_total_def read_pre_def)
  apply (smt (z3) assms(2) lastVal_ni ld_coh_dt_ni ld_coh_valof_dt_ni ld_le_lim_ni ld_oav_ni ld_ov_ni ld_vrnew_dt_ni reg_same_ld_dr)
  apply ( simp add: split: if_split_asm)  
  apply (simp add:  Ready_total_def read_pre_def)
  apply (simp add:  Ready_total_def read_pre_def)
  apply (simp add:  Ready_total_def read_pre_def)
  apply ( simp add: split: if_split_asm)  
  apply ( simp add: split: if_split_asm)  
  by ( simp add: split: if_split_asm)  







end






