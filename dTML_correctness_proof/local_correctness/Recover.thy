(*Showing local correctness of the DTML Recover annotation*)
theory Recover 
imports "../DTML" 
begin

(*DTML Recover annotation is locally correct*)
lemma Recover_local:
assumes "thrdsvars"
and "total_wfs (\<tau> \<sigma>)"
and "  Recover_inv  syst ((pc \<sigma>) syst) \<sigma>  "
and "TML_Recover  syst \<sigma> \<sigma>'"
shows " Recover_inv  syst ((pc \<sigma>') syst) \<sigma>'" 
using assms
  apply (simp add:TML_Recover_def Recover_inv_def get_key_def total_wfs_def )
  apply (cases "pc \<sigma> syst";  simp )
  apply (intro conjI)
  using reg_write_OV_ni reg_write_lastVal_ni apply presburger
  using get_key_in_dom  
  apply (metis reg_write_lc)
  using reg_write_mem apply presburger
  apply (subgoal_tac " Msg.loc (memory (\<tau> \<sigma>') ! (length(memory(\<tau> \<sigma>) ))) \<noteq> glb")
  prefer 2
  apply (metis st_loc)
  apply (subgoal_tac "length(memory(\<tau> \<sigma>') ) = length(memory(\<tau> \<sigma>) ) +1 ")
  prefer 2
  apply (metis st_mem_length)
  apply (subgoal_tac " \<forall>i. 0 \<le> i \<and> i < length (memory (\<tau> \<sigma>)) \<longrightarrow> memory (\<tau> \<sigma>) ! i = memory (\<tau> \<sigma>') ! i")
  prefer 2
  apply (meson mem_l_step)
  apply (intro conjI)
  apply (metis assms(2) st_lastVal_lc st_lv__daddr_ni st_ov_lc st_ov_ni)
  apply (metis (mono_tags, opaque_lifting) Suc_eq_plus1 less_irrefl_nat less_trans_Suc linorder_neqE_nat zero_le)
  apply (metis reg_same_st)
  apply (subgoal_tac " memory (\<tau> \<sigma>) = memory (\<tau> \<sigma>') ")
  prefer 2
  apply (simp add: step_def)
  apply (intro conjI)
  apply (smt (verit, ccfv_threshold) assms(2) flo_lastVal_ni flo_ov_ni)
  apply (subgoal_tac  " lastVal  (regs (\<tau> \<sigma>) syst c2) (\<tau> \<sigma>) = lastVal  (regs (\<tau> \<sigma>') syst c2) (\<tau> \<sigma>') "  )
  prefer 2
  apply (metis assms(2) flo_lastVal_ni reg_same_flo)
  apply (metis assms(2) empty_iff flo_oav_ov_rel_s reg_same_flo total_wfs_def)
  apply metis
  apply (metis reg_same_flo)
  apply (subgoal_tac  " lastVal  (regs (\<tau> \<sigma>) syst c2) (\<tau> \<sigma>) = lastVal  (regs (\<tau> \<sigma>') syst c2) (\<tau> \<sigma>') "  )
  prefer 2
  apply (metis lastVal_def reg_same_sfence sf_nlv_ni)
  apply (intro conjI)
  apply (metis assms(2) sf_ov_ni sf_wfs_preserved singletonD total_wfs_def)
  apply (metis assms(2) empty_iff opv_oav_sf_s reg_same_sfence total_wfs_def)
  apply (metis step_mem_sfence)
  apply (metis reg_same_sfence)
  apply (intro conjI)
  apply clarify
  apply (subgoal_tac "lastVal a (\<tau> \<sigma>') = lastVal a (\<tau> \<sigma>)")
  prefer 2
  using assms(2) lastVal_ni apply presburger
  apply (metis assms(2) insert_absorb ld_ov_sub lev_in_ov subset_singletonD total_wfs_def)
  apply (metis ld_step_mem)
  apply (subgoal_tac " regs (\<tau> \<sigma>') syst c1  \<in>[glb]\<^sub>syst (\<tau> \<sigma>) ")
  prefer 2
  using ld_ov_lc apply presburger
  apply (subgoal_tac " [glb]\<^sub>syst (\<tau> \<sigma>) = { survived_val (\<tau> \<sigma>) glb} ")
  prefer 2
  apply (subgoal_tac  "OTS (\<tau> \<sigma>)   syst  glb  = {0}")
  prefer 2
  apply (subgoal_tac "  (\<forall>i. 0 < i \<and> i < length (memory (\<tau> \<sigma>)) \<longrightarrow> i \<notin> OTS (\<tau> \<sigma>)   syst  glb) ")
  prefer 2
  apply (metis comploc_ots loc_eq_comploc)
  apply (subgoal_tac " OTS (\<tau> \<sigma>)   syst  glb \<noteq> {} ")
  prefer 2
  apply (metis empty_iff)
  apply (unfold OTS_def OTSF_def)
  apply (smt (z3) Collect_cong empty_def le_eq_less_or_eq mem_Collect_eq singleton_conv2)
  apply (simp add: mapval_def)
  apply (metis OTSF_def OTS_def singletonD singleton_conv2 survived_val_preserved_load)
  apply  ( simp add: split: if_split_asm)
  apply (case_tac "  log \<sigma> = Map.empty" )
  apply simp
  by simp



end









