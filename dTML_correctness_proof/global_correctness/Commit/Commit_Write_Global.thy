theory Commit_Write_Global
imports "../../DTML"
begin


(*Write annotation is stable against the DTML commit operation*)
lemma Commit_Write_global:
assumes "thrdsvars"
and "total_wfs (\<tau> \<sigma>)"
and "pm_inv \<sigma> "
and "ta \<noteq> tb"
and "  Write_inv  ta  ((pc \<sigma>) ta) \<sigma>  "
and "  Commit_inv  tb   ((pc \<sigma>) tb) \<sigma>  "
and "TML_Commit tb  \<sigma> \<sigma>'"
and "((pc \<sigma>) tb) \<in> {CommitPending,CommitResponding,Aborted} \<union> committing"
and "((pc \<sigma>) ta) \<in> {WritePending,WriteResponding } \<union> writing \<union>{Aborted}"
and   " \<forall>  t.  ( writer \<sigma> = Some t \<longrightarrow> odd (lastVal glb  (\<tau> \<sigma>)) )"  (*persistent invariant*)
and " ta \<noteq> syst"
and "tb \<noteq> syst"
and "ta \<noteq> tb"
shows " Write_inv  ta ((pc \<sigma>') ta) \<sigma>' "
  using assms
  apply (simp add:TML_Commit_def Write_inv_def Commit_inv_def TML_Write_def  )
  apply (simp split:if_splits )
   apply (cases "(pc \<sigma>) ta"; simp; cases "(pc \<sigma>) tb"; simp )
  apply (simp add: Ready_total_def read_pre_def)
  apply (case_tac " odd (regs (\<tau> \<sigma>) ta DTML.loc)")
  apply simp 
  apply (case_tac "      \<not> readAux \<sigma>' ta \<and>  \<not> writeAux \<sigma>' ta ")
  apply (metis lastVal_def reg_same_sfence sf_nlv_ni total_wfs_def)
  apply (smt (z3) reg_same_sfence sf_coh_ni sf_coh_valof_dt_ni sf_le_lim_ni sf_vrnew_dt_ni)
  apply (simp add: Ready_total_def read_pre_def)
  apply (case_tac " odd (regs (\<tau> \<sigma>) ta DTML.loc)")
  apply simp 
  apply (case_tac "      \<not> readAux \<sigma>' ta \<and>  \<not> writeAux \<sigma>' ta ")
  apply (metis lastVal_def reg_same_sfence sf_nlv_ni total_wfs_def)
  apply (smt (z3) reg_same_sfence sf_coh_ni sf_coh_valof_dt_ni sf_le_lim_ni sf_vrnew_dt_ni)
  apply (simp add: Ready_total_def read_pre_def)
  apply (smt (verit, best) less_Suc_eq reg_coh_dt_ni reg_same_st st_coh_valof_dt_ni st_lastVal_lc st_le_lim_dt_ni st_vrnew_dt_ni total_wfs_def)
  apply (simp add: Ready_total_def read_pre_def)
  apply (case_tac " odd (regs (\<tau> \<sigma>) ta DTML.loc)")
  apply simp 
  apply (case_tac "      \<not> readAux \<sigma> ta \<and>  \<not> writeAux \<sigma> ta ")
  apply simp
  apply (elim disjE conjE)
  apply metis
  apply (smt (verit, best) less_Suc_eq reg_coh_dt_ni reg_same_st st_coh_valof_dt_ni st_lastVal_lc st_le_lim_dt_ni st_vrnew_dt_ni total_wfs_def)
  apply (smt (verit, best) less_Suc_eq reg_coh_dt_ni reg_same_st st_coh_valof_dt_ni st_lastVal_lc st_le_lim_dt_ni st_vrnew_dt_ni total_wfs_def)
  apply (simp add: Ready_total_def read_pre_def)
  apply metis
  apply (simp add: Ready_total_def read_pre_def)
  apply (case_tac " odd (regs (\<tau> \<sigma>) ta DTML.loc)")
  apply simp 
  apply (case_tac "      \<not> readAux \<sigma>' ta \<and>  \<not> writeAux \<sigma>' ta ")
  apply (metis lastVal_def reg_same_sfence sf_nlv_ni total_wfs_def)
  apply (smt (z3) reg_same_sfence sf_coh_ni sf_coh_valof_dt_ni sf_le_lim_ni sf_vrnew_dt_ni)
  apply (simp add: Ready_total_def read_pre_def)
  apply (case_tac " odd (regs (\<tau> \<sigma>) ta DTML.loc)")
  apply force
  apply (case_tac "      \<not> readAux \<sigma>' ta \<and>  \<not> writeAux \<sigma>' ta ")
  apply (metis lastVal_def reg_same_sfence sf_nlv_ni total_wfs_def)
  apply (smt (z3) reg_same_sfence sf_coh_ni sf_coh_valof_dt_ni sf_le_lim_ni sf_vrnew_dt_ni)
  apply (simp add: Ready_total_def read_pre_def)
  apply (case_tac " odd (regs (\<tau> \<sigma>) ta DTML.loc)")
  apply force
  apply (case_tac "      \<not> readAux \<sigma> ta \<and>  \<not> writeAux \<sigma> ta ")
  apply simp
  apply (elim disjE conjE)
  apply metis
  apply (subgoal_tac " even (regs (\<tau> \<sigma>') ta DTML.loc) \<and> regs (\<tau> \<sigma>') ta DTML.loc < lastVal glb (\<tau> \<sigma>') ")
  prefer 2
  apply (intro conjI)
  apply (metis reg_same_st)
  apply (unfold total_wfs_def)
  apply (metis less_SucI reg_same_st st_lastVal_lc)
  apply meson
  apply (case_tac " odd (regs (\<tau> \<sigma>) ta DTML.loc)")
  apply simp 
  apply (case_tac " \<not> readAux \<sigma>' ta \<and>  \<not> writeAux \<sigma>' ta ")
  apply presburger
  apply simp
  apply (intro conjI)
  using  reg_same_st
  apply metis
  using  reg_same_st
  apply (smt (z3) assms(2) reg_coh_dt_ni st_coh_valof_dt_ni st_le_lim_dt_ni st_vrnew_dt_ni)
  using  reg_same_st 
  apply metis
  apply (metis reg_same_sfence)
  using  reg_same_st  
  apply metis
  apply (simp add: Ready_total_def read_pre_def)
  using  reg_same_st 
  apply metis
  apply (simp add: Ready_total_def read_pre_def)
  using  reg_same_st 
  apply (case_tac " odd (regs (\<tau> \<sigma>) ta DTML.loc)")
  apply force
  apply (case_tac "      \<not> readAux \<sigma> ta \<and>  \<not> writeAux \<sigma> ta ")
  apply simp
  apply (metis lastVal_def reg_same_sfence sf_nlv_ni)
  apply (smt (z3) assms(2) assms(4) reg_same_sfence sf_coh_ni sf_coh_valof_dt_ni sf_le_lim_ni sf_vrnew_dt_ni)
  apply (simp add: Ready_total_def read_pre_def)
  apply force
  apply (simp add: Ready_total_def read_pre_def)
  using  reg_same_st  
  apply (smt (z3) assms(2) less_SucI reg_coh_dt_ni st_coh_valof_dt_ni st_lastVal_lc st_le_lim_dt_ni st_vrnew_dt_ni)
  apply (cases "(pc \<sigma>) ta"; simp; cases "(pc \<sigma>) tb"; simp )
  apply (simp add: Ready_total_def read_pre_def)
  apply (simp add: Ready_total_def read_pre_def)
  by (simp add: Ready_total_def read_pre_def)



end
