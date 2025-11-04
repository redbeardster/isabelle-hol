theory Write_Begin_Global
imports "../../DTML"
begin

(*Begin annotation is stable against the DTML write operation*)
lemma Write_Begin_global:
assumes "thrdsvars"
and "total_wfs (\<tau> \<sigma>)"
and "pm_inv \<sigma> " (*persistent invariant*)
and "ta \<noteq> tb"
and "  Write_inv  tb  ((pc \<sigma>) tb) \<sigma>  "
and "  Begin_inv  ta   ((pc \<sigma>) ta) \<sigma>  "
and "TML_Write  tb    \<sigma> \<sigma>'"
and "((pc \<sigma>) tb) \<in> {WritePending, WriteResponding } \<union> writing  \<union> {Aborted}"
and "((pc \<sigma>) ta) \<in> {BeginPending, BeginResponding,Aborted } \<union> beginning"
and " ta \<noteq> syst"
and "tb \<noteq> syst"
and "ta \<noteq> tb"
shows "  Begin_inv  ta   ((pc \<sigma>') ta) \<sigma>' "
  using assms
  apply (simp add:TML_Write_def Write_inv_def Begin_inv_def   )
  apply (cases "(pc \<sigma>) tb"; simp; cases "(pc \<sigma>) ta"; simp )
  apply (unfold total_wfs_def Ready_total_def read_pre_def)
  apply ( simp add: split: if_split_asm)
  apply ( simp add: split: if_split_asm)
  apply ( simp add: split: if_split_asm)
  apply ( simp add: split: if_split_asm)
  apply ( simp add: split: if_split_asm)
  apply ( simp add: split: if_split_asm)
  apply ( simp add: split: if_split_asm)
  apply (metis assms(2) cas_coh_dt_ni cas_vrnew_dt_ni)
  apply (metis assms(2) cas_coh_dt_ni cas_vrnew_dt_ni)
  apply ( simp add: split: if_split_asm)
  apply ( simp add: split: if_split_asm)
  apply (smt (verit, best) assms(2) cas_coh_dt_ni cas_dt_ov_ni cas_fail_lastVal_same cas_le_daddr cas_vrnew_dt_ni reg_same_CAS_dt)
  apply (smt (verit, ccfv_SIG) assms(2) cas_coh_dt_ni cas_dt_ni cas_succ_eq cas_succ_lv_lc cas_sv_lc cas_vrnew_dt_ni lastVal_def less_Suc_eq not_gr0 reg_same_CAS_dt)
  apply ( simp add: split: if_split_asm)
  apply (smt (z3) assms(2) cas_coh_dt_ni cas_coh_valof_dt_ni cas_dt_ov_ni cas_fail_lastVal_same cas_fail_oav_ni cas_le_daddr cas_le_lim_dt_ni cas_vrnew_dt_ni reg_same_CAS_dt)
  apply (smt (z3) Suc_lessD Suc_less_eq assms(2) cas_coh_dt_ni cas_coh_valof_dt_ni cas_le_lim_dt_ni cas_succ_eq cas_succ_lv_lc cas_sv_lc cas_vrnew_dt_ni lastVal_def lessI nat_neq_iff reg_same_CAS_dt)
  apply ( simp add: split: if_split_asm)
  using assms(2) reg_coh_ni reg_vrnew_ni apply presburger
  using assms(2) reg_coh_ni reg_dt_ni reg_vrnew_ni reg_write_OV_ni reg_write_lastVal_ni apply presburger
  apply (smt (z3) assms(2) even_Suc fun_upd_other option.inject reg_coh_lim_dt_ni reg_coh_ni reg_dt_ni reg_vrnew_ni reg_write__crash reg_write_lastVal_ni reg_write_mem valOf_def)
  apply ( simp add: split: if_split_asm)
  apply ( simp add: split: if_split_asm)
  apply ( simp add: split: if_split_asm)
  apply ( simp add: split: if_split_asm)
  apply ( simp add: split: if_split_asm)
  apply (metis assms(2) ld_coh_dt_ni ld_vrnew_dt_ni)
  apply (smt (verit, best) assms(2) lastVal_ni ld_coh_dt_ni ld_ov_ni ld_vrnew_dt_ni reg_same_ld_dr)
  apply (smt (z3) assms(2) fun_upd_other lastVal_ni ld_coh_dt_ni ld_coh_valof_dt_ni ld_le_lim_ni ld_vrnew_dt_ni option.inject reg_same_ld_dt)
  apply (metis fun_upd_other option.inject)
  apply (metis assms(2) reg_coh_dt_ni st_vrnew_dt_ni)
  apply (metis assms(2) reg_coh_dt_ni reg_same_st st_lv__daddr_ni st_ov_ni st_vrnew_dt_ni)
  apply (smt (z3) assms(2) fun_upd_other option.inject reg_coh_dt_ni reg_same_st st_coh_valof_dt_ni st_le_lim_dt_ni st_lv__daddr_ni st_vrnew_dt_ni)
  apply (metis assms(2) flo_coh_ni flo_vrnew_ni)
  apply (metis (no_types, lifting) assms(2) flo_lastVal_ni flo_ov_ni reg_same_flo)
  by (smt (z3) assms(2) flo_coh_ni flo_coh_valof_dt_ni flo_lastVal_ni flo_le_lim_dt_ni flo_vrnew_ni fun_upd_other option.inject reg_same_flo)









end

