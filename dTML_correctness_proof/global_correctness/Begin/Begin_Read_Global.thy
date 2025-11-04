
(*typedecl Val*)

theory Begin_Read_Global
imports "../../DTML"
begin

(*Read annotation is stable against the DTML Begin operation*)
lemma Begin_Read_global:
assumes "thrdsvars"
and "total_wfs (\<tau> \<sigma>)"

and "  Begin_inv  tb  ((pc \<sigma>) tb) \<sigma>  "
and "  Read_inv  ta   ((pc \<sigma>) ta)  \<sigma>   "
and "TML_Begin tb  \<sigma> \<sigma>'"
and "((pc \<sigma>) tb) \<in> {BeginPending,BeginResponding,Aborted} \<union>  beginning "
and "((pc \<sigma>) ta) \<in> {ReadPending,ReadResponding,Aborted } \<union> reading"
and " ta \<noteq> syst"
and "tb \<noteq> syst"
and "ta \<noteq> tb"
shows "  Read_inv  ta   ((pc \<sigma>') ta)  \<sigma>'  "
  using assms
  apply (simp add:TML_Begin_def Begin_inv_def Read_inv_def total_wfs_def  )
  apply (simp split:if_splits )
   apply (cases "(pc \<sigma>) ta"; simp; cases "(pc \<sigma>) tb"; simp )
               apply (unfold  Ready_total_def )
               apply (elim disjE conjE)
                      apply (simp add: Ready_total_def  read_pre_def)
  apply (simp add: Ready_total_def  )
  apply (case_tac "  \<not> readAux \<sigma>' ta \<and>  \<not> writeAux \<sigma>' ta  ")
  apply simp
  apply (metis (no_types, lifting) assms(2) lastVal_ni ld_ov_ni reg_same_ld_dr)
    (*****************here**********************)
  apply (smt (z3) assms(2) lastVal_ni ld_coh_dt_ni ld_coh_valof_dt_ni ld_le_lim_ni ld_oav_ni ld_ov_ni ld_vrnew_dt_ni read_pre_def reg_same_ld_dr)
  apply (simp add: Ready_total_def read_pre_def)
  apply (case_tac "  \<not> readAux \<sigma>' ta \<and>  \<not> writeAux \<sigma>' ta  ")
  apply simp
  using assms(2) lastVal_ni reg_same_ld_dr apply force
  apply simp
  apply (metis assms(2) lastVal_ni ld_ov_ni reg_same_ld_dr)
  apply (metis assms(2) lastVal_ni reg_same_ld_dr)
  apply (simp add: read_pre_def)
  apply (smt (z3) assms(2) lastVal_ni ld_coh_dt_ni ld_coh_valof_dt_ni ld_le_lim_ni ld_le_lim_valof_dt_ni ld_ov_ni ld_vrnew_dt_ni reg_same_ld_dr)
  apply (simp add: read_pre_def)
  apply (smt (z3) assms(2) lastVal_ni ld_coh_dt_ni ld_coh_valof_dt_ni ld_le_lim_ni ld_le_lim_valof_dt_ni ld_ov_ni ld_vrnew_dt_ni reg_same_ld_dr)
  apply (simp add: read_pre_def)
  apply (smt (z3) assms(2) lastVal_ni ld_coh_dt_ni ld_coh_valof_dt_ni ld_le_lim_ni ld_ov_ni ld_vrnew_dt_ni reg_same_ld_dr)
  apply metis
  apply (simp add: read_pre_def)
  apply (smt (z3) assms(2) lastVal_ni ld_coh_dt_ni ld_coh_valof_dt_ni ld_le_lim_ni ld_oav_ni ld_ov_ni ld_vrnew_dt_ni reg_same_ld_dr)
  apply (simp add: read_pre_def)
  apply (smt (z3) assms(2) lastVal_ni ld_coh_dt_ni ld_coh_valof_dt_ni ld_le_lim_ni ld_le_lim_valof_dt_ni ld_oav_ni ld_ov_ni ld_vrnew_dt_ni read_pre_def reg_same_ld_dr)
  apply (simp add: read_pre_def)
  apply (smt (z3) assms(2) lastVal_ni ld_coh_dt_ni ld_coh_valof_dt_ni ld_le_lim_ni ld_le_lim_valof_dt_ni ld_oav_ni ld_ov_ni ld_vrnew_dt_ni read_pre_def reg_same_ld_dr)
  using assms(2) lastVal_ni reg_same_ld_dr apply force
  apply (simp add: read_pre_def)
  apply (smt (z3) assms(2) lastVal_ni ld_coh_dt_ni ld_coh_valof_dt_ni ld_le_lim_ni ld_le_lim_valof_dt_ni ld_oav_ni ld_ov_ni ld_vrnew_dt_ni read_pre_def reg_same_ld_dr)
  apply (smt (z3) assms(2) lastVal_ni ld_coh_dt_ni ld_coh_valof_dt_ni ld_le_lim_ni ld_le_lim_valof_dt_ni ld_oav_ni ld_ov_ni ld_vrnew_dt_ni read_pre_def reg_same_ld_dr)
  apply (simp add: read_pre_def)
  apply (smt (z3) assms(2) lastVal_ni ld_coh_dt_ni ld_coh_valof_dt_ni ld_le_lim_ni ld_le_lim_valof_dt_ni ld_oav_ni ld_ov_ni ld_vrnew_dt_ni read_pre_def reg_same_ld_dr)
  apply (simp add: read_pre_def)
  apply (smt (z3) assms(2) lastVal_ni ld_coh_dt_ni ld_coh_valof_dt_ni ld_le_lim_ni ld_le_lim_valof_dt_ni ld_oav_ni ld_ov_ni ld_vrnew_dt_ni read_pre_def reg_same_ld_dr)
  apply (metis fun_upd_other)
  apply (simp add: read_pre_def)
  apply (smt (z3) assms(2) lastVal_ni ld_coh_dt_ni ld_coh_valof_dt_ni ld_le_lim_ni ld_le_lim_valof_dt_ni ld_oav_ni ld_ov_ni ld_vrnew_dt_ni read_pre_def reg_same_ld_dr)
  apply (simp add: read_pre_def)
  apply (cases "(pc \<sigma>) tb"; simp; cases "(pc \<sigma>) ta"; simp )
  apply (simp add: read_pre_def)
  apply (smt (z3) assms(2) lastVal_ni ld_coh_dt_ni ld_coh_valof_dt_ni ld_le_lim_ni ld_oav_ni ld_ov_ni ld_vrnew_dt_ni reg_same_ld_dr)
  apply (simp add: read_pre_def)
  apply (smt (z3) assms(2) lastVal_ni ld_coh_dt_ni ld_coh_valof_dt_ni ld_le_coh_ni ld_le_lim_valof_dt_ni ld_oav_ni ld_ov_ni ld_vrnew_dt_ni reg_same_ld_dr)
  apply (simp add: read_pre_def)
  apply (smt (z3) assms(2) lastVal_ni ld_coh_dt_ni ld_coh_valof_dt_ni ld_le_coh_ni ld_le_lim_valof_dt_ni ld_oav_ni ld_ov_ni ld_vrnew_dt_ni reg_same_ld_dr)
  apply (smt (z3) assms(2) lastVal_ni ld_coh_dt_ni ld_coh_valof_dt_ni ld_le_coh_ni ld_le_lim_valof_dt_ni ld_oav_ni ld_ov_ni ld_vrnew_dt_ni reg_same_ld_dr)
  apply (simp add: read_pre_def)
  apply (smt (z3) assms(2) lastVal_ni ld_coh_dt_ni ld_coh_valof_dt_ni ld_le_coh_ni ld_le_lim_valof_dt_ni ld_oav_ni ld_ov_ni ld_vrnew_dt_ni reg_same_ld_dr)
  apply (simp add: read_pre_def)
  apply (smt (z3) assms(2) lastVal_ni ld_coh_dt_ni ld_coh_valof_dt_ni ld_le_coh_ni ld_le_lim_valof_dt_ni ld_oav_ni ld_ov_ni ld_vrnew_dt_ni reg_same_ld_dr)
  apply (simp add: read_pre_def)
  apply (smt (z3) assms(2) lastVal_ni ld_coh_dt_ni ld_coh_valof_dt_ni ld_le_coh_ni ld_le_lim_valof_dt_ni ld_oav_ni ld_ov_ni ld_vrnew_dt_ni reg_same_ld_dr)
  apply meson
  apply meson
  by meson


end












