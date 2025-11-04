(*Showing local correctness of the DTML Commit annotation*)
theory Commit
  imports "../DTML" 
begin

(*DTML Commit annotation is locally correct*)
lemma Commit_local:
assumes "thrdsvars"
and "total_wfs (\<tau> \<sigma>)"
and "  Commit_inv  t   ((pc \<sigma>) t) \<sigma>  "
and "TML_Commit  t   \<sigma> \<sigma>'"
and " t \<noteq> syst"
shows " Commit_inv  t   ((pc \<sigma>') t) \<sigma>'" 
  using assms
  apply (simp add:TML_Commit_def Commit_inv_def )
  apply (cases "pc \<sigma> t";  simp add: total_wfs_def )
  apply(simp add:  split: if_split_asm)
  apply (smt (z3) Ready_total_def singletonI)
  apply (intro conjI)
  apply (metis reg_same_sfence)
  apply (metis lastVal_def sf_nlv_ni sf_ov_ni)
  apply (metis emptyE insertE lev_in_opv opv_oav_sf subset_singleton_iff)
  apply (metis reg_same_sfence sf_ov_ni)
  apply (metis lastVal_def reg_same_sfence sf_nlv_ni)
  by metis


end

