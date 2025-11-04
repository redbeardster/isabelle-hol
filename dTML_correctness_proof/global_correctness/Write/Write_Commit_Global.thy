
(*typedecl Val*)

theory Write_Commit_Global
imports "../../DTML"
begin

(*auxiliary lemma*)
lemma upreg_read_pre_ni:
assumes  "read_pre (\<tau> \<sigma>) ta b "
and " \<tau> \<sigma>' = (update_reg tb DTML.loc (lastVal glb (\<tau> \<sigma>)) (\<tau> \<sigma>)) "
and "thrdsvars"
and "total_wfs (\<tau> \<sigma>)"
and " ta \<noteq> syst"
and "tb \<noteq> syst"
and "ta \<noteq> tb"
shows   "read_pre (\<tau> \<sigma>') ta b "
using assms
  apply (unfold total_wfs_def read_pre_def thrdsvars_def)
  apply (intro conjI)
    apply (metis reg_dt_ni)
   apply (metis (mono_tags, lifting) assms(4) reg_coh_ni)
  apply (unfold valOf_def)
  apply (metis (mono_tags, lifting) assms(4) reg_coh_ni reg_dt_ni reg_write__crash reg_write_mem)
  apply (subgoal_tac "vrnew (\<tau> \<sigma>') ta = vrnew (\<tau> \<sigma>) ta ")
  prefer 2
  apply (simp add: update_reg_def)
  using assms(4) reg_coh_lim_dt_ni apply presburger
  apply (subgoal_tac "vrnew (\<tau> \<sigma>') ta = vrnew (\<tau> \<sigma>) ta ")
   prefer 2
   apply (simp add: update_reg_def)
  using assms(4) reg_coh_ni by presburger

(*Commit annotation is stable against the DTML write  operation*)
lemma Write_Commit_global:
assumes "thrdsvars"
and "total_wfs (\<tau> \<sigma>)"
and "pm_inv \<sigma> " (*persistent invariant*)
and "ta \<noteq> tb"
and "  Write_inv  tb  ((pc \<sigma>) tb) \<sigma>  "
and "  Commit_inv  ta   ((pc \<sigma>) ta) \<sigma>  "
and "TML_Write  tb    \<sigma> \<sigma>'"
and  " \<forall>  t.  (   writer \<sigma> = Some t \<longrightarrow> odd (lastVal glb  (\<tau> \<sigma>)) )" (*persistent invariant*)
and "((pc \<sigma>) tb) \<in> {WritePending, WriteResponding} \<union> writing \<union> {Aborted}"
and "((pc \<sigma>) ta) \<in> {CommitPending, CommitResponding, Aborted } \<union> committing"
and " ta \<noteq> syst"
and "tb \<noteq> syst"
and "ta \<noteq> tb"
shows "  Commit_inv  ta   ((pc \<sigma>') ta) \<sigma>' "
using assms
  apply (simp add:TML_Write_def Write_inv_def Commit_inv_def  )
  apply (cases "(pc \<sigma>) ta"; simp; cases "(pc \<sigma>) tb"; simp )
  apply (unfold total_wfs_def Ready_total_def read_pre_def)
  apply ( simp add: split: if_split_asm)
  apply ( simp add: split: if_split_asm)
  apply ( simp add: split: if_split_asm)
  apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc)")
  apply simp
  apply (intro conjI)
  apply (metis reg_same_CAS_dt)
  apply (meson cas_fail_lastVal_dt_ni)
  apply (metis cas_fail_lv_ni lastVal_def reg_same_CAS_dt)
  apply (metis reg_same_CAS_dt)
  apply (metis cas_fail_lv_ni lastVal_def reg_same_CAS_dt)
  apply (meson cas_fail_lastVal_dt_ni)
  apply (metis reg_same_CAS_dt)
  apply (meson cas_fail_lastVal_dt_ni)
  apply (metis assms(2) cas_fail_lastVal_same cas_fail_oav_ni cas_le_daddr)
  apply (metis assms(2) cas_fail_lastVal_same reg_same_CAS_dt)
  apply (case_tac "  readAux \<sigma> ta \<and>  \<not> writeAux \<sigma> ta ")
  apply simp
  apply (smt (verit) assms(2) cas_coh_dt_ni cas_coh_valof_dt_ni cas_le_lim_dt_ni cas_vrnew_dt_ni reg_same_CAS_dt)
  apply simp
  apply (elim disjE)
  apply (metis (no_types, lifting) assms(2) cas_dt_ov_ni cas_fail_oav_ni cas_wfs_preserved reg_same_CAS_dt singletonD total_wfs_def)
  apply (metis assms(2) cas_fail_lastVal_same reg_same_CAS_dt)
  apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc)")
  apply simp
  apply (metis cas_fail_diff_lv neq0_conv)
  apply (case_tac "  readAux \<sigma> ta \<and>  \<not> writeAux \<sigma> ta ")
  apply simp
  apply (smt (z3) assms(2) cas_coh_dt_ni cas_coh_valof_dt_ni cas_le_lim_dt_ni cas_vrnew_dt_ni reg_same_CAS_dt)
  apply (metis Zero_not_Suc cas_lc cas_nlv_lc gr0_implies_Suc lastVal_def le_eq_less_or_eq less_Suc_eq_le reg_same_CAS_dt)
  apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc)")
  apply simp
  apply (case_tac "  readAux \<sigma> ta \<and>  \<not> writeAux \<sigma> ta ")
  apply simp
  using  upreg_read_pre_ni 
  apply (metis (no_types, lifting) assms(2) read_pre_def thrdsvars_def)
  apply simp
  apply (metis reg_dt_ni reg_write_lastVal_ni)
  apply ( simp add: split: if_split_asm)
  apply simp
  using lastVal_ni ld_coh_dt_ni ld_coh_valof_dt_ni ld_le_lim_ni ld_oav_ni ld_ov_ni ld_vrnew_dt_ni reg_same_ld_dt
  apply (smt (verit) assms(2))
  apply (metis fun_upd_other map_upd_eqD1)
  apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc)")
  apply simp
  apply (case_tac "  readAux \<sigma> ta \<and>  \<not> writeAux \<sigma> ta ")
  apply simp
  apply (smt (verit) assms(2) reg_coh_dt_ni reg_same_st st_coh_valof_dt_ni st_le_lim_dt_ni st_vrnew_dt_ni)
  apply simp
  using  reg_coh_dt_ni reg_same_st st_coh_valof_dt_ni st_le_lim_dt_ni st_lv__daddr_ni st_vrnew_dt_ni
  apply (metis assms(2))
  apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc)")
  apply simp
  apply (case_tac "  readAux \<sigma> ta \<and>  \<not> writeAux \<sigma> ta ")
  apply simp
  apply (smt (z3) assms(2) flo_coh_ni flo_coh_valof_dt_ni flo_le_lim_dt_ni flo_vrnew_ni reg_same_flo)
  apply simp
  apply (metis assms(2) flo_lastVal_ni reg_same_flo)
  apply ( simp add: split: if_split_asm)
  apply ( simp add: split: if_split_asm)
  apply (intro conjI)
  apply (metis reg_same_CAS_dt)
  apply (meson cas_fail_lastVal_dt_ni)
  apply (metis assms(2) cas_fail_lastVal_same cas_fail_oav_ni cas_le_daddr)
  apply (metis cas_dt_ov_ni reg_same_CAS_dt)
  apply (metis cas_fail_lv_ni lastVal_def reg_same_CAS_dt)
  apply (metis Zero_not_Suc cas_nlv_lc gr0_implies_Suc lastVal_def)
  apply ( simp add: split: if_split_asm)
  apply ( simp add: split: if_split_asm)
  apply (intro conjI)
  apply (metis reg_same_CAS_dt)
  apply (meson cas_fail_lastVal_dt_ni)
  apply (metis assms(2) cas_fail_lastVal_same cas_fail_opv_ni cas_le_daddr)
  apply (metis cas_dt_ov_ni reg_same_CAS_dt)
  apply (metis cas_fail_lv_ni lastVal_def reg_same_CAS_dt)
  apply (metis Zero_not_Suc cas_nlv_lc gr0_implies_Suc lastVal_def)
  apply ( simp add: split: if_split_asm)
  apply ( simp add: split: if_split_asm)
  apply (metis (no_types, lifting) assms(2) cas_dt_ov_ni cas_fail_lastVal_same cas_le_daddr reg_same_CAS_dt)
  apply (metis cas_fail_diff_lv neq0_conv)
  by ( simp add: split: if_split_asm)+


































































end















