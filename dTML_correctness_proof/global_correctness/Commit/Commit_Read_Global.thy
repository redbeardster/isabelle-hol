theory Commit_Read_Global
imports "../../DTML"
begin

(*auxiliary lemma*)
lemma sf_read_pre_ni:
assumes  "read_pre (\<tau> \<sigma>) ta z "
and " (\<tau> \<sigma>) [sfence ]\<^sub>tb (\<tau> \<sigma>')" 
and "thrdsvars"
and "total_wfs (\<tau> \<sigma>)"
and " ta \<noteq> syst"
and "tb \<noteq> syst"
and "ta \<noteq> tb"
shows   "read_pre (\<tau> \<sigma>') ta z "
  using assms
  apply (unfold read_pre_def total_wfs_def thrdsvars_def)
  by (metis (no_types, opaque_lifting) assms(4) reg_same_sfence sf_coh_ni sf_coh_valof_dt_ni sf_le_lim_ni sf_vrnew_dt_ni)

(*auxiliary lemma*)
lemma wr_glb_read_pre_ni:
assumes  "read_pre (\<tau> \<sigma>) ta b "
and "  (\<tau> \<sigma>) [glb := Suc (lastVal glb (\<tau> \<sigma>))]\<^sub>tb (\<tau> \<sigma>')" 
and "thrdsvars"
and "total_wfs (\<tau> \<sigma>)"
and " ta \<noteq> syst"
and "tb \<noteq> syst"
and "ta \<noteq> tb"
shows   "read_pre (\<tau> \<sigma>') ta b "
 using assms
  apply (unfold read_pre_def total_wfs_def thrdsvars_def)
  by (metis (no_types, lifting) assms(4) reg_coh_dt_ni reg_same_st st_coh_valof_dt_ni st_le_lim_dt_ni st_vrnew_dt_ni)


(*auxiliary lemma*)
lemma loc_notin_glb:
assumes " regs (\<tau> \<sigma>) ta DTML.loc \<notin> [glb]\<^sub>ta \<tau> \<sigma>"
and "total_wfs (\<tau> \<sigma>) "
and "thrdsvars"
and "  regs (\<tau> \<sigma>) ta loc \<le> lastVal glb  (\<tau> \<sigma>)"
and "(\<tau> \<sigma>) [glb := Suc (lastVal glb (\<tau> \<sigma>))]\<^sub>tb (\<tau> \<sigma>')"
and " ta \<noteq> syst"
and "tb \<noteq> syst"
and "ta \<noteq> tb"
shows " regs (\<tau> \<sigma>') ta DTML.loc \<notin> [glb]\<^sub>ta \<tau> \<sigma>'"
  using assms
  apply (unfold total_wfs_def thrdsvars_def)
  apply (subgoal_tac  " [glb]\<^sub>ta (\<tau> \<sigma>') = [glb]\<^sub>ta (\<tau> \<sigma>)  \<union> {Suc (lastVal glb (\<tau> \<sigma>))}")
   prefer 2
  using  st_ov_dt_lc apply meson
  by (simp add: reg_same_st)

(*Read annotation is stable against the DTML commit operation*)
lemma Commit_Read_global:
assumes "thrdsvars"
and "total_wfs (\<tau> \<sigma>)"
and "pm_inv \<sigma> "
and "  Read_inv  ta   ((pc \<sigma>) ta)  \<sigma>   "
and "  Commit_inv  tb   ((pc \<sigma>) tb) \<sigma>  "
and "TML_Commit tb  \<sigma> \<sigma>'"
and "glb_monotone_inv (\<tau> \<sigma>) " (*persistent invariant*)
and "((pc \<sigma>) tb) \<in> {CommitPending,CommitResponding ,Aborted} \<union> committing"
and "((pc \<sigma>) ta) \<in> {ReadPending,ReadResponding } \<union> reading \<union> {Aborted}"
and  " pc \<sigma>  syst  = RecIdle \<longrightarrow> (\<forall>t.  (t \<noteq> syst  \<and> ((pc \<sigma>) t \<notin> {PC.NotStarted,PC.Aborted, PC.Committed,PC.Begin2,PC.BeginPending, PC.CommitResponding   }) \<longrightarrow>   regs (\<tau> \<sigma>) t loc \<le> lastVal glb  (\<tau> \<sigma>) ))"  (*persistent invariant*)
and " ta \<noteq> syst"
and "tb \<noteq> syst"
and "ta \<noteq> tb"
shows "  Read_inv  ta   ((pc \<sigma>') ta)  \<sigma>' "
  using assms
  apply (simp add:TML_Commit_def Read_inv_def Commit_inv_def  )
  apply (cases "(pc \<sigma>) ta"; simp; cases "(pc \<sigma>) tb"; simp )
  apply (unfold total_wfs_def)
  apply ( simp add: split: if_split_asm)
  apply (simp add: Ready_total_def read_pre_def ) 
  apply blast
  apply (simp add: Ready_total_def read_pre_def ) 
  apply (simp add: Ready_total_def read_pre_def ) 
  apply (case_tac "  \<not> readAux \<sigma> ta \<and>  \<not> writeAux \<sigma> ta ")
  apply simp
  apply (metis (no_types, lifting) assms(2) lev_in_ov reg_same_sfence sf_ov_ni singletonD total_wfs_def)
  apply (case_tac "  readAux \<sigma> ta \<and>  \<not> writeAux \<sigma> ta ")
  apply simp
  apply (smt (z3) assms(2) reg_same_sfence sf_coh_ni sf_coh_valof_dt_ni sf_le_lim_ni sf_vrnew_dt_ni)
  apply simp
  apply (case_tac "  writeAux \<sigma> ta ")
  apply simp
  apply presburger
  apply (simp add: Ready_total_def read_pre_def ) 
  apply force
  apply (simp add: Ready_total_def  ) 
  apply (case_tac "  \<not> readAux \<sigma> ta \<and>  \<not> writeAux \<sigma> ta ")
  apply simp
  apply (metis less_Suc_eq reg_same_st st_lastVal_lc)
  apply (case_tac "  readAux \<sigma> ta \<and>  \<not> writeAux \<sigma> ta ")
  apply simp
  apply (metis assms(1) assms(2) reg_same_st wr_glb_read_pre_ni)
  apply presburger
  apply ( simp add: split: if_split_asm)
  apply (simp add: Ready_total_def  ) 
  apply meson
  apply (simp add: Ready_total_def  ) 
  apply (simp add: Ready_total_def  ) 
  apply (subgoal_tac "\<forall>a. [a]\<^sup>A\<^sub>ta  \<tau> \<sigma>' = [a]\<^sup>A\<^sub>ta  \<tau> \<sigma> ")
  prefer 2
  apply (metis sf_oav_ni)
  apply (subgoal_tac " \<forall>l. [l]\<^sub>ta \<tau> \<sigma> =  [l]\<^sub>ta \<tau> \<sigma>'")
  prefer 2
  apply (metis sf_ov_ni)
  apply (case_tac " (odd (regs (\<tau> \<sigma>') ta DTML.loc))")
  apply simp
  apply (smt (verit, best) lastVal_def reg_same_sfence sf_nlv_ni)
  apply (case_tac "  \<not> readAux \<sigma>' ta \<and>  \<not> writeAux \<sigma>' ta ")
  apply simp
  apply (metis lastVal_def reg_same_sfence sf_nlv_ni)
  apply simp
  apply (metis assms(1) assms(2) reg_same_sfence sf_read_pre_ni)
  apply (simp add: Ready_total_def read_pre_def ) 
  apply force
  apply (simp add: Ready_total_def read_pre_def ) 
  apply (smt (verit, best) assms(2) less_Suc_eq reg_coh_dt_ni reg_same_st st_coh_valof_dt_ni st_lastVal_lc st_le_lim_dt_ni st_vrnew_dt_ni)
  apply ( simp add: split: if_split_asm)
  apply (simp add: Ready_total_def read_pre_def ) 
  apply (elim disjE conjE)
  apply (metis option.inject)
  apply metis
  apply (metis lastVal_def reg_same_sfence sf_nlv_ni)
  apply (smt (z3) assms(2) reg_same_sfence sf_coh_ni sf_coh_valof_dt_ni sf_le_lim_ni sf_vrnew_dt_ni sfence_crash step_mem_sfence valOf_def)
  apply (metis reg_same_sfence sf_ov_ni)
  apply metis
  apply (case_tac "  \<not> readAux \<sigma>' ta \<and>  \<not> writeAux \<sigma>' ta ")
  apply simp
  apply (metis PC.distinct(103) PC.distinct(179) PC.distinct(25) PC.distinct(655) PC.distinct(715) PC.distinct(937) Suc_le_mono less_eq_Suc_le reg_same_st st_lastVal_lc)
  apply (case_tac "  readAux \<sigma> ta \<and>  \<not> writeAux \<sigma> ta ")
  apply simp
  apply (elim disjE conjE)
  apply (subgoal_tac " even (regs (\<tau> \<sigma>') ta DTML.loc) \<and>
(\<forall>a. a \<noteq> glb \<longrightarrow> read_pre (\<tau> \<sigma>') ta a) \<and>
regs (\<tau> \<sigma>') ta DTML.loc \<in> [glb]\<^sub>ta \<tau> \<sigma>' \<and>
regs (\<tau> \<sigma>') ta DTML.val = valOf (last_entry_lim (\<tau> \<sigma>') (inLoc \<sigma> ta) (coh (\<tau> \<sigma>') ta glb)) (inLoc \<sigma> ta) (\<tau> \<sigma>') ")
  prefer 2
  apply (intro conjI)
  apply (metis reg_same_st)
  apply (meson assms(1) assms(2) wr_glb_read_pre_ni)
  apply (smt (z3) Set.set_insert assms(13) insert_subset reg_same_st st_sset_lc)
  apply (metis assms(2) reg_same_st st_le_coh_valof_dt_ni)
  apply force
  apply (metis PC.distinct(103) PC.distinct(179) PC.distinct(25) PC.distinct(655) PC.distinct(715) PC.distinct(937) assms(2) loc_notin_glb reg_same_st thrdsvars_def)
  apply (simp add: Ready_total_def read_pre_def )
  apply (metis PC.distinct(15) PC.distinct(357) PC.distinct(503) PC.distinct(77) assms(2) less_Suc_eq loc_notin_glb reg_same_st st_lastVal_lc st_le_coh_valof_dt_ni thrdsvars_def wr_glb_read_pre_ni)
  apply ( simp add: split: if_split_asm)
  apply (metis lastVal_def reg_same_sfence sf_nlv_ni)
  apply (metis less_Suc_eq reg_same_st st_lastVal_lc)
  apply ( simp add: split: if_split_asm)
  apply (elim disjE conjE)
  apply (metis option.inject)
  apply (smt (verit, ccfv_SIG) assms(2) reg_same_sfence sf_coh_ni sf_le_lim_ni sf_read_pre_ni sfence_crash step_mem_sfence thrdsvars_def valOf_def)
  apply (metis reg_same_sfence sf_ov_ni)
  apply meson
  apply (elim disjE conjE)
  apply (metis (no_types, opaque_lifting) PC.distinct(19) PC.distinct(361) PC.distinct(593) PC.distinct(81) assms(2) loc_notin_glb reg_same_st st_le_coh_valof_dt_ni thrdsvars_def wr_glb_read_pre_ni)
  apply (metis PC.distinct(1039) PC.distinct(107) PC.distinct(183) PC.distinct(29) PC.distinct(659) PC.distinct(719) assms(1) assms(2) loc_notin_glb reg_same_st)
  apply ( simp add: split: if_split_asm)
  apply (smt (z3) assms(2) option.inject reg_same_sfence sf_coh_ni sf_le_lim_ni sf_read_pre_ni sfence_crash step_mem_sfence thrdsvars_def valOf_def)
  apply meson
  apply (metis assms(2) reg_same_st st_le_coh_valof_dt_ni thrdsvars_def wr_glb_read_pre_ni)
  apply ( simp add: split: if_split_asm)
  apply (smt (z3) Ready_total_def assms(2) fun_upd_other lastVal_def option.inject reg_same_sfence sf_nlv_ni sf_read_pre_ni thrdsvars_def)
  apply (simp add: Ready_total_def read_pre_def ) 
  apply (simp add: Ready_total_def read_pre_def )
  apply (case_tac "  \<not> readAux \<sigma>' ta \<and>  \<not> writeAux \<sigma>' ta ")
  apply simp
  apply (case_tac "  readAux \<sigma> ta \<and>  \<not> writeAux \<sigma> ta ")
  apply presburger
  apply (metis (no_types, lifting) assms(2) lev_in_ov reg_same_sfence sf_ov_ni singletonD total_wfs_def)
  apply simp
  apply (case_tac "  writeAux \<sigma> ta ")
  apply simp
  apply (smt (z3) assms(2) reg_same_sfence sf_coh_ni sf_coh_valof_dt_ni sf_le_lim_ni sf_vrnew_dt_ni)
  apply (simp add: Ready_total_def read_pre_def )
  apply (smt (verit, best) assms(2) less_Suc_eq reg_coh_dt_ni reg_same_st st_coh_valof_dt_ni st_lastVal_lc st_le_lim_dt_ni st_vrnew_dt_ni)
  apply (simp add: Ready_total_def read_pre_def ) 
  apply (smt (verit, best) assms(2) less_Suc_eq reg_coh_dt_ni reg_same_st st_coh_valof_dt_ni st_lastVal_lc st_le_lim_dt_ni st_vrnew_dt_ni)
  apply (simp add: Ready_total_def read_pre_def ) 
  by( simp add: split: if_split_asm)














end
    