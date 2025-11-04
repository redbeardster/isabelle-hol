
(*typedecl Val*)

theory Read_Commit_Global
imports "../../DTML"
begin

(*Commit annotation is stable against the DTML read operation*)
lemma Read_Commit_global:
assumes "thrdsvars"
and "total_wfs (\<tau> \<sigma>)"
and "pm_inv \<sigma> " (*persistent invariant*)
and  " \<forall>  t.  (   writer \<sigma> = Some t \<longrightarrow> odd (lastVal glb  (\<tau> \<sigma>)) )"(*persistent invariant*)
and " \<forall>  t. (  (   writer \<sigma>  = Some t    \<longrightarrow> \<lceil>glb\<rceil>\<^sub>t (\<tau> \<sigma>) ))"(*persistent invariant*)
and "glb_monotone_inv (\<tau> \<sigma>) "(*persistent invariant*)
and "(\<forall> a. mem_tml_prop    glb a  (\<tau> \<sigma>)) "(*persistent invariant*)
and "  Read_inv  tb   ((pc \<sigma>) tb)  \<sigma>  "
and "  Commit_inv  ta  ((pc \<sigma>) ta) \<sigma>  "
and " TML_Read  tb   \<sigma> \<sigma>'"
and "((pc \<sigma>) tb) \<in> {ReadPending, ReadResponding  } \<union>  reading \<union> {Aborted} "
and "((pc \<sigma>) ta) \<in> {CommitPending,CommitResponding ,Aborted } \<union> committing" 
and " ta \<noteq> syst"
and "tb \<noteq> syst"
and "ta \<noteq> tb"
shows  "  Commit_inv  ta  ((pc \<sigma>') ta) \<sigma>'  " 
  using assms
  apply (unfold thrdsvars_def  Ready_total_def)
  apply (simp add:TML_Read_def Read_inv_def Commit_inv_def   )
  apply (cases "(pc \<sigma>) tb";simp; cases "(pc \<sigma>) ta" ;simp)
  apply (unfold total_wfs_def  Ready_total_def read_pre_def)
  apply (smt (z3) assms(14) fun_upd_other)
  apply (smt (z3))
  apply metis
  apply (metis (full_types))
  apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc)")
  apply simp
  using  reg_same_st  
  apply (smt (z3) assms(2) lastVal_ni ld_oav_ni ld_ov_ni reg_same_ld_dt)
  apply (case_tac " \<not> readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
  apply simp
  using  reg_same_st   
  apply (smt (z3) assms(2) lastVal_ni ld_ov_ni reg_same_ld_dt)
  apply simp
  using  reg_same_st   
  apply (smt (verit) assms(2) ld_coh_dt_ni ld_coh_valof_dt_ni ld_le_lim_ni ld_vrnew_dt_ni reg_same_ld_dt)
  apply (smt (verit, ccfv_SIG) assms(2) lastVal_ni ld_oav_ni ld_ov_ni reg_same_ld_dt)
  apply (smt (verit, ccfv_SIG) assms(2) lastVal_ni ld_opv_ni ld_ov_ni reg_same_ld_dt)
  apply (metis (no_types, opaque_lifting) assms(2) lastVal_ni ld_ov_ni reg_same_ld_dt)
  apply ( simp add: split: if_split_asm)
  apply ( simp add: split: if_split_asm)
  apply ( simp add: split: if_split_asm)
  apply ( simp add: split: if_split_asm)
  apply ( simp add: split: if_split_asm)
  apply ( simp add: split: if_split_asm)
  apply ( simp add: split: if_split_asm)
  apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc)")
  apply (subgoal_tac "  odd (lastVal glb  (\<tau> \<sigma>)) ")
  prefer 2
  apply presburger
  apply (metis cas_nlv_lc lastVal_def numeral_1_eq_Suc_0 numeral_eq_one_iff zero_neq_one)
  apply (case_tac "  \<not> readAux \<sigma> ta \<and>    \<not> writeAux \<sigma> ta  ")
  apply simp
  apply (subgoal_tac " lastVal glb (\<tau> \<sigma>') = lastVal glb (\<tau> \<sigma>) ")
  prefer 2
  apply (metis assms(2) cas_succ_eq cas_succ_lv_lc lastVal_def numeral_1_eq_Suc_0 numeral_eq_one_iff)
  using  reg_same_CAS_dt 
  apply (smt (z3) assms(2) cas_fail_diff_lv cas_lastVal cas_le_daddr cas_ov_daddr_dt_sx_ni cas_succ_v2_in_x insert_absorb insert_iff insert_not_empty numeral_1_eq_Suc_0 numerals(1) total_wfs_def zero_neq_one)
  apply simp
  apply (intro conjI)
  using  reg_same_CAS_dt 
  apply metis
  apply clarify
  apply (intro conjI)
  apply (metis reg_same_CAS_dt)
  apply (metis cas_coh_dt_ni)
  using cas_coh_dt_ni  reg_same_CAS_dt
  apply (metis assms(2) cas_coh_valof_dt_ni)
  apply (metis assms(15) assms(2) cas_le_lim_dt_ni cas_vrnew_dt_ni)
  apply (metis assms(2) cas_coh_dt_ni cas_vrnew_dt_ni)
  apply (metis reg_same_CAS_dt)
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
  apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc)")
  apply simp
  apply (metis assms(2) cas_fail_oav_ni cas_sv_lc cas_wfs_preserved reg_same_CAS_dt singletonD total_wfs_def)
  apply (case_tac " \<not> readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
  apply (metis One_nat_def assms(2) cas_fail_lastVal_same cas_le_daddr cas_sv_lc reg_same_CAS_dt)
  apply (smt (z3) assms(2) cas_coh_dt_ni cas_coh_valof_dt_ni cas_le_lim_dt_ni cas_vrnew_dt_ni reg_same_CAS_dt)
  apply ( simp add: split: if_split_asm)
  apply (metis Zero_not_Suc cas_fail_diff_lv)
  apply (intro conjI)
  apply (metis reg_same_CAS_dt)
  apply (metis cas_fail_diff_lv cas_fail_lastVal_dt_ni)
  apply (metis One_nat_def assms(2) cas_fail_lastVal_same cas_fail_oav_ni cas_le_daddr cas_sv_lc)
  apply (metis cas_dt_ni reg_same_CAS_dt)
  apply (metis One_nat_def assms(2) cas_fail_lastVal_same cas_sv_lc reg_same_CAS_dt)
  apply ( simp add: split: if_split_asm)
  apply (metis One_nat_def assms(2) cas_succ_eq) 
  apply (intro conjI)
  apply (metis reg_same_CAS_dt)
  apply (metis cas_fail_diff_lv cas_fail_lastVal_dt_ni)
  apply (metis One_nat_def assms(2) cas_fail_lastVal_same cas_fail_opv_ni cas_le_daddr cas_sv_lc)
  apply (metis cas_dt_ni reg_same_CAS_dt)
  apply (metis One_nat_def assms(2) cas_fail_lastVal_same cas_sv_lc reg_same_CAS_dt)
  apply ( simp add: split: if_split_asm)
  apply (metis One_nat_def assms(2) cas_succ_eq)
  apply (intro conjI)
  apply (metis reg_same_CAS_dt)
  apply (metis cas_fail_diff_lv cas_fail_lastVal_dt_ni)
  apply (metis cas_dt_ni reg_same_CAS_dt)
  apply (metis One_nat_def assms(2) cas_fail_lastVal_same cas_sv_lc reg_same_CAS_dt)
  apply ( simp add: split: if_splits)
  apply ( simp add: split: if_split_asm)
  apply ( simp add: split: if_split_asm)
  apply (subgoal_tac " [glb]\<^sub>ta \<tau> \<sigma>' = [glb]\<^sub>ta \<tau> \<sigma>   ")
  prefer 2
  apply (subgoal_tac " lastVal glb (\<tau> \<sigma>') = lastVal glb (\<tau> \<sigma>) ")
  prefer 2
  apply (metis assms(2) lastVal_ni)
  apply (metis ld_ov_ni)
  using  reg_same_ld_dt 
  apply (smt (verit) assms(2) lastVal_ni ld_coh_dt_ni ld_coh_valof_dt_ni ld_le_lim_ni ld_oav_ni ld_ov_ni ld_vrnew_dt_ni)
  using ld_oav_ni ld_ov_ni reg_same_ld_dr
  apply (smt (z3) assms(2) lastVal_ni singleton_insert_inj_eq')
  using  lastVal_ni ld_opv_ni ld_ov_ni reg_same_ld_dr
  apply (smt (z3) assms(2))
  apply (smt (z3) assms(2) lastVal_ni ld_ov_ni reg_same_ld_dt)
  apply (smt (z3) PC.simps(1646) pc_aux)
  apply ( simp add: split: if_split_asm)
  apply (smt (z3) PC.simps(1648) assms(15) pc_aux)
  apply (smt (z3) PC.simps(1649) pc_aux)
  apply ( simp add: split: if_split_asm)
  apply ( simp add: split: if_split_asm)
  by metis+



















end
