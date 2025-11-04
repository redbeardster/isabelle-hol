
theory Write_Write_Global
imports "../../DTML"
begin


(*Write annotation is stable against the DTML write  operation*)
lemma Write_Write_global:
assumes "thrdsvars"
and "total_wfs (\<tau> \<sigma>)"
and "pm_inv \<sigma> " (*persistent invariant*)
and "ta \<noteq> tb"
and "  Write_inv  tb  ((pc \<sigma>) tb) \<sigma>  "
and "   Write_inv  ta  ((pc \<sigma>) ta) \<sigma>  "
and "TML_Write  tb   \<sigma> \<sigma>'"
and "((pc \<sigma>) tb) \<in> {WritePending, WriteResponding} \<union> writing \<union> {Aborted}"
and "((pc \<sigma>) ta) \<in> {WritePending, WriteResponding} \<union> writing \<union> {Aborted} "
and " ta \<noteq> syst"
and "tb \<noteq> syst"
and "ta \<noteq> tb"
and  " \<forall>  t.  (   writer \<sigma> = Some t \<longrightarrow> odd (lastVal glb  (\<tau> \<sigma>)) )" (*persistent invariant*)
and " \<forall>  t. (  (   writer \<sigma>  = Some t    \<longrightarrow> \<lceil>glb\<rceil>\<^sub>t (\<tau> \<sigma>) ))" (*persistent invariant*)
shows "  Write_inv  ta  ((pc \<sigma>') ta) \<sigma>'  "
  using assms
  apply (simp add:TML_Write_def Write_inv_def  )
  apply (cases "(pc \<sigma>) tb"; simp; cases "(pc \<sigma>) ta"; simp )
  apply (unfold total_wfs_def Ready_total_def read_pre_def)
  apply (smt (verit) fun_upd_other)
  apply (smt (verit) fun_upd_other)
  apply (smt (verit) fun_upd_other)
  apply (smt (verit) fun_upd_other)
  apply (smt (verit) fun_upd_other)
  apply (smt (verit) fun_upd_other)
  apply (smt (verit) fun_upd_other)
  apply (smt (verit) fun_upd_other)
  apply (smt (verit) fun_upd_other)
  apply (smt (verit) fun_upd_other)
  apply ( simp add: split: if_split_asm)
  apply ( simp add: split: if_split_asm)
  apply ( simp add: split: if_split_asm)
  apply ( simp add: split: if_split_asm)
  apply ( simp add: split: if_split_asm)
  apply ( simp add: split: if_split_asm)
  apply ( simp add: split: if_split_asm)
  apply ( simp add: split: if_split_asm)
  apply ( simp add: split: if_split_asm)
  apply ( simp add: split: if_split_asm)
  apply ( simp add: split: if_split_asm)
  apply ( simp add: split: if_split_asm)
  apply (subgoal_tac "  (\<forall>l. [l]\<^sub>ta \<tau> \<sigma>' =  [l]\<^sub>ta \<tau> \<sigma>   )  ")
  prefer 2
  using cas_dt_ov_ni apply presburger
  apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc) ")
  apply (metis assms(2) cas_fail_oav_ni cas_wfs_preserved reg_same_CAS_dt singletonD total_wfs_def)
  apply (case_tac "    \<not> readAux \<sigma> ta \<and>  \<not> writeAux \<sigma> ta ")
  apply (metis assms(2) cas_fail_lastVal_same cas_le_daddr reg_same_CAS_dt)
  apply (metis (no_types, lifting) assms(2) cas_coh_dt_ni cas_coh_valof_dt_ni cas_le_lim_dt_ni cas_vrnew_dt_ni reg_same_CAS_dt)
  apply (smt (z3) Suc_lessD Suc_less_eq assms(2) cas_coh_dt_ni cas_coh_valof_dt_ni cas_lc cas_le_lim_dt_ni cas_succ_eq cas_vrnew_dt_ni lastVal_def lessI reg_same_CAS_dt zero_less_iff_neq_zero)
  apply ( simp add: split: if_split_asm)
  apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc) ")
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
  apply (metis cas_fail_lv_ni lastVal_def reg_same_CAS_dt)

  apply (case_tac "    \<not> readAux \<sigma> ta \<and>  \<not> writeAux \<sigma> ta ")
  apply (smt (verit) assms(2) cas_dt_ov_ni cas_fail_lastVal_same cas_le_daddr reg_same_CAS_dt)
  apply simp
  apply (metis (no_types, lifting) assms(2) cas_coh_dt_ni cas_coh_valof_dt_ni cas_le_lim_dt_ni cas_vrnew_dt_ni reg_same_CAS_dt)
  apply (smt (verit) assms(2) cas_coh_dt_ni cas_coh_valof_dt_ni cas_fail_diff_lv cas_lc cas_le_lim_dt_ni cas_vrnew_dt_ni lastVal_def less_Suc_eq neq0_conv reg_same_CAS_dt)
  apply ( simp add: split: if_split_asm)
  apply (smt (verit, best) assms(2) cas_dt_ov_ni cas_fail_lastVal_same cas_fail_oav_ni cas_le_daddr reg_same_CAS_dt)
  apply (smt (verit, best) assms(2) cas_dt_ov_ni cas_fail_lastVal_same cas_fail_oav_ni cas_le_daddr reg_same_CAS_dt)
  apply ( simp add: split: if_split_asm)
  apply (metis (no_types, lifting) assms(2) cas_dt_ov_ni cas_fail_lastVal_same cas_fail_oav_ni cas_le_daddr reg_same_CAS_dt)
  apply (metis cas_fail_diff_lv not_gr0)
  apply ( simp add: split: if_split_asm)
  apply (metis (no_types, lifting) assms(2) cas_dt_ov_ni cas_fail_lastVal_same cas_fail_oav_ni cas_le_daddr reg_same_CAS_dt)
  apply (metis cas_fail_diff_lv not_gr0)
  apply ( simp add: split: if_splits)
  apply (smt (verit, best) assms(2) cas_dt_ov_ni cas_fail_lastVal_same cas_fail_oav_ni cas_le_daddr reg_same_CAS_dt)
  apply (metis cas_fail_diff_lv not_gr0)
  apply ( simp add: split: if_splits)
  apply (smt (verit, ccfv_SIG) assms(2) cas_dt_ov_ni cas_fail_lastVal_same cas_fail_oav_ni cas_le_daddr reg_same_CAS_dt)
  apply (metis cas_fail_diff_lv not_gr0)
  apply ( simp add: split: if_splits)
  apply (metis assms(2) cas_dt_ov_ni cas_fail_oav_ni cas_wfs_preserved reg_same_CAS_dt singletonD total_wfs_def)
  apply (metis cas_fail_diff_lv not_gr0)
  apply ( simp add: split: if_splits)
  apply (metis assms(2) cas_dt_ov_ni cas_fail_oav_ni cas_wfs_preserved reg_same_CAS_dt singletonD total_wfs_def)
  apply (metis cas_fail_diff_lv not_gr0)
  apply ( simp add: split: if_splits)
  apply (subgoal_tac "  (\<forall>l. [l]\<^sub>ta \<tau> \<sigma>' =  [l]\<^sub>ta \<tau> \<sigma>   )  ")
  prefer 2
  using cas_dt_ov_ni apply presburger
  apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc) ")
  apply (metis assms(2) cas_fail_oav_ni cas_wfs_preserved reg_same_CAS_dt singletonD total_wfs_def)
  apply (case_tac "    \<not> readAux \<sigma> ta \<and>  \<not> writeAux \<sigma> ta ")
  apply (metis assms(2) cas_fail_lastVal_same cas_le_daddr reg_same_CAS_dt)
  apply (metis (no_types, lifting) assms(2) cas_coh_dt_ni cas_coh_valof_dt_ni cas_le_lim_dt_ni cas_vrnew_dt_ni reg_same_CAS_dt)
  apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc) ")
  apply (metis cas_fail_diff_lv gr_implies_not_zero)
  apply (case_tac "    \<not> readAux \<sigma> ta \<and>  \<not> writeAux \<sigma> ta ")
  apply (metis bot_nat_0.not_eq_extremum cas_fail_diff_lv cas_lc lastVal_def less_Suc_eq reg_same_CAS_dt)
  apply (metis (no_types, lifting) assms(2) cas_coh_dt_ni cas_coh_valof_dt_ni cas_le_lim_dt_ni cas_vrnew_dt_ni reg_same_CAS_dt)
  apply ( simp add: split: if_splits)
  apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc) ")
  apply (metis option.inject)
  apply (case_tac "    \<not> readAux \<sigma> ta \<and>  \<not> writeAux \<sigma> ta ")
  apply (metis fun_upd_other reg_dt_ni reg_write_lastVal_ni)
  apply (metis (no_types, lifting) assms(2) fun_upd_other reg_coh_lim_dt_ni reg_coh_ni reg_dt_ni reg_vrnew_ni reg_write__crash reg_write_mem valOf_def)
    (*  using reg_dt_ni apply presburger*)
  apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc) ")
  apply (metis option.inject)
  apply (case_tac "    \<not> readAux \<sigma> ta \<and>  \<not> writeAux \<sigma> ta ")
  apply (metis fun_upd_other reg_dt_ni reg_write_lastVal_ni)
  apply (metis (no_types, lifting) assms(2) fun_upd_other reg_coh_lim_dt_ni reg_coh_ni reg_dt_ni reg_vrnew_ni reg_write__crash reg_write_mem valOf_def)
  using reg_dt_ni apply presburger
  apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc) ")
  apply (metis option.inject)
  apply (case_tac "    \<not> readAux \<sigma> ta \<and>  \<not> writeAux \<sigma> ta ")
  apply (metis fun_upd_other reg_dt_ni reg_write_lastVal_ni)
  apply (metis (no_types, lifting) assms(2) fun_upd_other reg_coh_lim_dt_ni reg_coh_ni reg_dt_ni reg_vrnew_ni reg_write__crash reg_write_mem valOf_def)
  apply ( simp add: split: if_splits)
  apply ( simp add: split: if_splits)
  apply ( simp add: split: if_splits)
  apply ( simp add: split: if_splits)
  apply ( simp add: split: if_splits)
  apply (smt (z3) assms(2) fun_upd_other lastVal_ni ld_coh_dt_ni ld_coh_valof_dt_ni ld_le_lim_ni ld_vrnew_dt_ni option.inject reg_same_ld_dt)
  apply (smt (z3) assms(2) fun_upd_other lastVal_ni ld_coh_dt_ni ld_coh_valof_dt_ni ld_le_lim_ni ld_vrnew_dt_ni option.inject reg_same_ld_dt)
  apply (metis reg_same_ld_dt)
  apply (smt (z3) assms(2) fun_upd_other lastVal_ni ld_coh_dt_ni ld_coh_valof_dt_ni ld_le_lim_ni ld_vrnew_dt_ni option.inject reg_same_ld_dt)
  apply (metis fun_upd_other option.inject)
  apply (metis fun_upd_other option.inject)
  apply (smt (z3) assms(2) fun_upd_other option.inject reg_coh_dt_ni reg_same_st st_coh_valof_dt_ni st_le_lim_dt_ni st_lv__daddr_ni st_vrnew_dt_ni)
  apply (smt (z3) assms(2) fun_upd_other option.inject reg_coh_dt_ni reg_same_st st_coh_valof_dt_ni st_le_lim_dt_ni st_lv__daddr_ni st_vrnew_dt_ni)
  apply (smt (z3) assms(2) fun_upd_other option.inject reg_coh_dt_ni reg_same_st st_coh_valof_dt_ni st_le_lim_dt_ni st_lv__daddr_ni st_vrnew_dt_ni)
  apply (metis reg_same_st)
  apply (smt (z3) assms(2) fun_upd_other option.inject reg_coh_dt_ni reg_same_st st_coh_valof_dt_ni st_le_lim_dt_ni st_lv__daddr_ni st_vrnew_dt_ni)
  apply (smt (z3) assms(2) flo_coh_ni flo_coh_valof_dt_ni flo_lastVal_ni flo_le_lim_dt_ni flo_vrnew_ni fun_upd_other option.inject reg_same_flo)
  apply (smt (z3) assms(2) flo_coh_ni flo_coh_valof_dt_ni flo_lastVal_ni flo_le_lim_dt_ni flo_vrnew_ni fun_upd_other option.inject reg_same_flo)
  apply (metis reg_same_flo)
  by (smt (z3) assms(2) flo_coh_ni flo_coh_valof_dt_ni flo_lastVal_ni flo_le_lim_dt_ni flo_vrnew_ni fun_upd_other option.inject reg_same_flo)


end
