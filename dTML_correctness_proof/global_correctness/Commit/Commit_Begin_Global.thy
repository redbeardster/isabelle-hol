theory Commit_Begin_Global
imports "../../DTML"
begin


(*Begin annotation is stable against the DTML commit operation*)
lemma Commit_Begin_global:
assumes "thrdsvars"
and "total_wfs (\<tau> \<sigma>)"
and "pm_inv \<sigma> " (*persistent invariant*)
and "ta \<noteq> tb"
and "  Begin_inv  ta  ((pc \<sigma>) ta) \<sigma>  "
and "  Commit_inv  tb   ((pc \<sigma>) tb) \<sigma>  "
and "TML_Commit tb  \<sigma> \<sigma>'"
and "((pc \<sigma>) tb) \<in> {CommitPending,CommitResponding,Aborted} \<union> committing" 
and "((pc \<sigma>) ta) \<in> {BeginPending,BeginResponding,Aborted } \<union> beginning"
and " ta \<noteq> syst"
and "tb \<noteq> syst"
and "ta \<noteq> tb"
shows " Begin_inv  ta  ((pc \<sigma>') ta) \<sigma>' "
  using assms
  apply (simp add:TML_Commit_def Begin_inv_def Commit_inv_def TML_Write_def  )
  apply (simp split:if_splits )
   apply (cases "(pc \<sigma>) ta"; simp; cases "(pc \<sigma>) tb"; simp )
  using total_wfs_def
  apply (metis sf_coh_ni sf_vrnew_dt_ni)
  apply (metis reg_coh_dt_ni st_vrnew_dt_ni)
  apply (unfold total_wfs_def)
  apply (smt (z3) assms(2) lev_in_ov reg_same_sfence sf_coh_ni sf_ov_ni sf_vrnew_dt_ni singletonD)
  apply (elim disjE conjE)
  apply (intro conjI)
  apply (subgoal_tac " regs (\<tau> \<sigma>) ta DTML.loc = regs (\<tau> \<sigma>') ta DTML.loc ")
  prefer 2
  apply (metis reg_same_st)
  apply (subgoal_tac " [glb]\<^sub>ta \<tau> \<sigma>' = [glb]\<^sub>ta \<tau> \<sigma> \<union> {Suc (lastVal glb (\<tau> \<sigma>))}")
  prefer 2
  apply (metis st_ov_dt_lc)
  apply (metis UnI1)
  apply (metis less_SucI reg_same_st st_lastVal_lc)
  apply(simp add: Ready_total_def read_pre_def )
  apply (case_tac " odd (regs (\<tau> \<sigma>) ta DTML.loc)")
  apply simp
  apply (case_tac "    \<not> readAux \<sigma> ta \<and> \<not> writeAux \<sigma> ta ")
  apply simp
  apply (metis (no_types, lifting) assms(2) lev_in_ov reg_same_sfence sf_ov_ni singletonD total_wfs_def)
  apply simp
  apply(simp add: Ready_total_def read_pre_def )
  apply (case_tac " odd (regs (\<tau> \<sigma>) ta DTML.loc)")
  apply simp
  apply (case_tac "    \<not> readAux \<sigma> ta \<and> \<not> writeAux \<sigma> ta ")
  apply simp
  apply (metis (no_types, lifting) assms(2) lev_in_ov reg_same_sfence sf_ov_ni singletonD total_wfs_def)
  apply simp
  apply (smt (z3) assms(2) reg_same_sfence sf_coh_ni sf_coh_valof_dt_ni sf_le_lim_ni sf_vrnew_dt_ni)
  apply(simp add: Ready_total_def read_pre_def )
  apply (smt (z3) assms(2) less_SucI reg_coh_dt_ni reg_same_st st_coh_valof_dt_ni st_lastVal_lc st_le_lim_dt_ni st_vrnew_dt_ni)
  apply(simp add: Ready_total_def read_pre_def )
  apply (smt (z3) assms(2) less_SucI reg_coh_dt_ni reg_same_st st_coh_valof_dt_ni st_lastVal_lc st_le_lim_dt_ni st_vrnew_dt_ni)
  apply (cases "(pc \<sigma>) ta"; simp; cases "(pc \<sigma>) tb"; simp )
  by(simp add: Ready_total_def read_pre_def )





end
