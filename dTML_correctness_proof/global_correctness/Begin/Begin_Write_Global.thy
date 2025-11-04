
(*typedecl Val*)

theory Begin_Write_Global
  imports "../../DTML"
begin


(*Write annotation is stable against the DTML begin operation*)
lemma Begin_Write_global:
assumes "thrdsvars"
and "total_wfs (\<tau> \<sigma>)"
and "  Begin_inv  tb  ((pc \<sigma>) tb) \<sigma>  "
and "  Write_inv  ta  ((pc \<sigma>) ta) \<sigma>  "
and "TML_Begin tb  \<sigma> \<sigma>'"
and "((pc \<sigma>) tb) \<in> {BeginPending,BeginResponding,Aborted} \<union>  beginning "
and "((pc \<sigma>) ta) \<in> {WritePending,WriteResponding } \<union> writing \<union> {Aborted }"
and " ta \<noteq> syst"
and "tb \<noteq> syst"
and "ta \<noteq> tb"
shows  "  Write_inv  ta  ((pc \<sigma>') ta) \<sigma>'  "
  using assms
  apply (simp add:TML_Begin_def Begin_inv_def Write_inv_def   )
  apply (cases "(pc \<sigma>) ta"; simp; cases "(pc \<sigma>) tb"; simp )
  apply (unfold Ready_total_def total_wfs_def)
  apply (metis reg_same_ld_dr)
  apply (smt (z3) assms(2) fun_upd_other lastVal_ni ld_coh_dt_ni ld_crash ld_le_lim_ni ld_oav_ni ld_ov_ni ld_step_mem ld_vrnew_dt_ni read_pre_def reg_same_ld_dr valOf_def)
  apply (simp split:if_splits )
  apply (metis reg_same_ld_dr)
  apply (simp split:if_splits )
  apply (case_tac " \<not> readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta  ")
  apply simp
  apply (metis assms(2) lastVal_ni ld_ov_ni reg_same_ld_dr)
  apply (case_tac "  readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta  ")
  apply (simp add: read_pre_def  )
  apply (smt (z3) assms(2) ld_coh_dt_ni ld_coh_valof_dt_ni ld_le_lim_ni ld_vrnew_dt_ni reg_same_ld_dr)
  apply (smt (z3) assms(2) lastVal_ni ld_oav_ni ld_ov_ni reg_same_ld_dr)
  apply (simp split:if_splits )
  apply (metis reg_same_ld_dr)
  apply (simp split:if_splits )
  apply (smt (verit) assms(2) lastVal_ni ld_oav_ni ld_ov_ni reg_same_ld_dr)
  apply (simp split:if_splits )
  apply (smt (verit) Ready_total_def Write_inv_def assms(4) pc_aux)
  apply (smt (z3) assms(2) lastVal_ni ld_oav_ni ld_ov_ni reg_same_ld_dr)
  apply (simp add: Ready_total_def read_pre_def)
  apply (simp split:if_splits )
  apply metis
  apply (smt (z3) assms(2) lastVal_ni ld_oav_ni ld_ov_ni reg_same_ld_dr)
  apply (simp split:if_splits )
  apply (metis (no_types, lifting) assms(2) lastVal_ni ld_oav_ni ld_ov_ni reg_same_ld_dr)
  apply (simp split:if_splits )
  apply metis
  apply metis
  apply (smt (z3) assms(2) lastVal_ni ld_oav_ni ld_ov_ni reg_same_ld_dr)
  apply (simp split:if_splits )
  apply (smt (verit) assms(2) lastVal_ni ld_oav_ni ld_ov_ni reg_same_ld_dr)
  apply (simp split:if_splits )
  apply metis
  apply metis
  apply (metis (no_types, lifting) assms(2) lastVal_ni ld_oav_ni ld_ov_ni reg_same_ld_dr)
  apply (simp split:if_splits )
  apply (smt (verit) assms(2) lastVal_ni ld_oav_ni ld_ov_ni reg_same_ld_dr)
  apply (simp split:if_splits )
  apply metis
  apply metis
  apply metis
  apply (smt (verit, ccfv_SIG) assms(2) lastVal_ni ld_oav_ni ld_ov_ni reg_same_ld_dr)
  apply (simp split:if_splits )
  apply metis
  apply metis
  apply metis
  apply (simp add: read_pre_def)
  apply (case_tac " \<not> readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta  ")
  apply simp
  apply (metis assms(2) lastVal_ni ld_ov_ni reg_same_ld_dr)
  apply (case_tac "  readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta  ")
  apply (simp add: read_pre_def  )
  apply (smt (z3) assms(2) ld_coh_dt_ni ld_coh_valof_dt_ni ld_le_lim_ni ld_vrnew_dt_ni reg_same_ld_dr)
  apply (smt (z3) assms(2) lastVal_ni ld_oav_ni ld_ov_ni reg_same_ld_dr)
  apply (simp split:if_splits )
  by(simp split:if_splits )





















end

