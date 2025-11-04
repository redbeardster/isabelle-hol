theory Commit_Commit_Global
imports "../../DTML"
begin

(*Commit annotation is stable against the DTML commit operation*)
lemma Commit_Commit_global:
assumes "thrdsvars"
and "total_wfs (\<tau> \<sigma>)"
and "pm_inv \<sigma> " (*persistent invariant*)
and "ta \<noteq> tb"
and "  Commit_inv  ta   ((pc \<sigma>) ta) \<sigma>   "
and "  Commit_inv  tb   ((pc \<sigma>) tb) \<sigma>  "
and "TML_Commit tb  \<sigma> \<sigma>'"
and "((pc \<sigma>) tb) \<in> {CommitPending,CommitResponding,Aborted} \<union> committing"
and "((pc \<sigma>) ta) \<in> {CommitPending,CommitResponding,Aborted} \<union>  committing"
and " ta \<noteq> syst"
and "tb \<noteq> syst"
and "ta \<noteq> tb"
shows "  Commit_inv  ta   ((pc \<sigma>') ta) \<sigma>'  "
  using assms
  apply (simp add:TML_Commit_def Commit_inv_def total_wfs_def  )
  apply (cases "(pc \<sigma>) ta"; simp; cases "(pc \<sigma>) tb"; simp )
  apply ( simp add: split: if_split_asm)
  apply (simp add: Ready_total_def read_pre_def)
  apply (case_tac " (odd (regs (\<tau> \<sigma>) ta DTML.loc)) ")
  apply simp
  apply (simp add: total_wfs_def)
  apply (smt (z3) assms(2) lastVal_def reg_same_sfence sf_coh_ni sf_coh_valof_dt_ni sf_le_lim_ni sf_nlv_ni sf_vrnew_dt_ni)
  apply (simp add: Ready_total_def read_pre_def)
  apply (simp add: Ready_total_def read_pre_def)
  apply (case_tac " \<not> readAux \<sigma> ta \<and> \<not> writeAux \<sigma> ta  ")
  apply simp
  apply (metis assms(2) lev_in_ov reg_same_sfence sf_ov_ni singletonD total_wfs_def)
  apply (case_tac "  readAux \<sigma> ta \<and> \<not> writeAux \<sigma> ta  ")
  apply simp
  apply (smt (z3) assms(2) reg_same_sfence sf_coh_ni sf_coh_valof_dt_ni sf_le_lim_ni sf_vrnew_dt_ni)
  apply (case_tac "   writeAux \<sigma> ta  ")
  apply simp
  apply (smt (z3) assms(4) lastVal_def reg_same_sfence sf_nlv_ni sf_oav_ni sf_ov_ni)
  apply (simp add: Ready_total_def read_pre_def)
  apply (smt (z3) PC.simps(1088) Ready_total_def pc_aux read_pre_def)
  apply (simp add: Ready_total_def read_pre_def)
  apply (smt (z3) assms(2) less_SucI reg_coh_dt_ni reg_same_st st_coh_valof_dt_ni st_lastVal_lc st_le_lim_dt_ni st_vrnew_dt_ni)
  apply (smt (z3) PC.simps(1647) pc_aux)
  apply metis
  apply metis
  apply (smt (z3) PC.simps(1648) pc_aux)
  apply metis
  apply metis
  apply (simp add: split if_splits)
  apply (smt (z3) PC.simps(1649) fun_upd_other)
  apply (smt (verit) PC.simps(1649) fun_upd_other)
  apply metis
  apply (simp add: split if_splits)
  apply (cases" pc \<sigma>' ta"; simp)
  apply (metis PC.distinct(387) fun_upd_def)
  apply (metis PC.distinct(455) fun_upd_def)
  apply (metis PC.distinct(521) fun_upd_def)
  apply (metis PC.distinct(585) fun_upd_other)
  apply (simp add: split if_splits)
  apply (cases" pc \<sigma>' ta"; simp)
  apply (metis PC.distinct(449) fun_upd_def)
  apply (metis PC.distinct(517) fun_upd_def)
  apply (metis PC.distinct(583) fun_upd_other)
  by (metis PC.distinct(647) fun_upd_other)










end
