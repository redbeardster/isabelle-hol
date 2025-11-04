
(*typedecl Val*)

theory Begin_Begin_Global
imports "../../DTML"
begin


(*Begin annotation is stable against the DTML Begin operation*)
lemma Begin_Begin_global:
  assumes "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
  and "  Begin_inv  tb  ((pc \<sigma>) tb) \<sigma>  "
  and "  Begin_inv  ta  ((pc \<sigma>) ta) \<sigma>   "
   and "TML_Begin tb  \<sigma> \<sigma>'"
 and "((pc \<sigma>) tb) \<in> {BeginPending,BeginResponding,  Aborted} \<union>  beginning "
  and "((pc \<sigma>) ta) \<in> {BeginPending,BeginResponding,  Aborted}  \<union> beginning"
and " ta \<noteq> syst"
and "tb \<noteq> syst"
and "ta \<noteq> tb"
shows "  Begin_inv  ta  ((pc \<sigma>') ta) \<sigma>'  "
  using assms
  apply (simp add:TML_Begin_def Begin_inv_def  total_wfs_def  )
   apply (cases "(pc \<sigma>) ta"; simp; cases "(pc \<sigma>) tb"; simp )
           
  apply (metis assms(2) ld_coh_dt_ni ld_vrnew_dt_ni)
 apply(simp add:  split: if_split_asm)
        apply(simp add:  split: if_split_asm)
       apply (smt (z3) assms(2) lastVal_ni ld_ov_ni reg_same_ld_dr)
  apply (smt (z3) PC.simps(1644) pc_aux)

  apply (simp add: Ready_total_def)
    apply (simp add: Ready_total_def read_pre_def)

  apply (smt (z3) assms(2) lastVal_ni ld_coh_dt_ni ld_coh_valof_dt_ni ld_le_lim_ni ld_oav_ni ld_ov_ni ld_vrnew_dt_ni reg_same_ld_dr)
        apply(simp add:  split: if_split_asm)
    apply (simp add: Ready_total_def read_pre_def)
    apply (simp add: Ready_total_def read_pre_def)
  by(simp add:  split: if_split_asm)



end












