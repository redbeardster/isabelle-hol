theory Begin_Commit_Global
  imports "../../DTML"
begin



(*Commit annotation is stable against the DTML Begin operation*)
lemma Begin_Commit_global:
  assumes "thrdsvars"
    and "total_wfs (\<tau> \<sigma>)"
    and "  Begin_inv  tb  ((pc \<sigma>) tb) \<sigma>  "
    and "  Commit_inv  ta   ((pc \<sigma>) ta) \<sigma>  "
    and "TML_Begin tb  \<sigma> \<sigma>'"
    and "((pc \<sigma>) tb) \<in> {BeginPending,BeginResponding, Aborted} \<union>  beginning "
    and "((pc \<sigma>) ta) \<in> {CommitPending,CommitResponding ,Aborted } \<union> committing"
    and " ta \<noteq> syst"
    and "tb \<noteq> syst"
    and "ta \<noteq> tb"
  shows "  Commit_inv  ta   ((pc \<sigma>') ta) \<sigma>' "
  using assms
  apply (simp add:TML_Begin_def Begin_inv_def Commit_inv_def total_wfs_def  )
  apply (simp split:if_splits )
   apply (cases "(pc \<sigma>) ta"; simp; cases "(pc \<sigma>) tb"; simp )
  apply (simp add: Ready_total_def)
  apply (simp add: Ready_total_def read_pre_def)
  apply (case_tac " \<not> readAux \<sigma> ta \<and> \<not> writeAux \<sigma> ta  ")
  apply simp 
  apply (smt (z3) assms(10) assms(2) lastVal_ni ld_ov_ni reg_same_ld_dr)
  apply (case_tac "  readAux \<sigma> ta \<and> \<not> writeAux \<sigma> ta  ")
  apply simp 
  apply (smt (z3) assms(10) assms(2) ld_coh_dt_ni ld_coh_valof_dt_ni ld_le_lim_ni ld_vrnew_dt_ni reg_same_ld_dr)
  apply (case_tac "    writeAux \<sigma> ta  ")
  apply simp 
  apply (smt (z3) assms(2) lastVal_ni ld_oav_ni ld_ov_ni reg_same_ld_dr)
  apply force
  apply (simp add: Ready_total_def)
  apply metis
  apply (smt (z3) assms(2) lastVal_ni ld_oav_ni ld_ov_ni reg_same_ld_dr)
  apply (metis (no_types, opaque_lifting) assms(2) lastVal_ni ld_oav_ni ld_wfs_preserved reg_same_ld_dr total_wfs_def)
  apply metis
  apply metis
  apply metis
  apply (intro conjI)
  apply (metis reg_same_ld_dr)
  apply (metis assms(2) lastVal_ni ld_ov_ni)
  apply (metis assms(2) lastVal_ni ld_opv_ni)
  apply (metis ld_ov_ni reg_same_ld_dr)
  apply (metis assms(2) lastVal_ni reg_same_ld_dr)
  apply metis
  apply metis
  apply metis
  apply metis
  apply (metis (no_types, lifting) assms(2) lastVal_ni ld_ov_ni reg_same_ld_dr)
  apply (metis reg_same_ld_dr)
  apply (metis assms(2) lastVal_ni ld_ov_ni)
  apply (metis ld_ov_ni reg_same_ld_dr)
  apply (cases "(pc \<sigma>) tb"; simp; cases "(pc \<sigma>) ta"; simp )
  apply (simp add: Ready_total_def)
  apply metis
  apply metis
  apply (smt (z3) assms(2) lastVal_ni ld_oav_ni ld_ov_ni reg_same_ld_dr)
  apply (simp add: Ready_total_def read_pre_def)
  apply (case_tac " \<not> readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
  apply simp
  apply (metis (no_types, opaque_lifting) assms(2) lastVal_ni ld_ov_ni reg_same_ld_dr)
  apply (case_tac " readAux \<sigma> ta \<and>  \<not> writeAux \<sigma> ta ")
  apply simp
  apply (smt (z3) assms(2) ld_coh_dt_ni ld_coh_valof_dt_ni ld_le_lim_ni ld_vrnew_dt_ni reg_same_ld_dr)
  apply simp
  apply (smt (z3) assms(2) lastVal_ni ld_oav_ni ld_ov_ni reg_same_ld_dr)
  apply (smt (z3) assms(2) lastVal_ni ld_oav_ni ld_ov_ni reg_same_ld_dr)
  apply (smt (z3) assms(2) lastVal_ni ld_opv_ni ld_ov_ni reg_same_ld_dr)
  apply (metis (no_types, opaque_lifting) assms(2) lastVal_ni ld_ov_ni reg_same_ld_dr)
  apply (simp add: Ready_total_def read_pre_def)
  apply metis
  apply metis
  apply metis
  apply (simp add: Ready_total_def read_pre_def)
  by metis+




end












