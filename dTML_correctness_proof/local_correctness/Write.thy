(*Showing local correctness of the DTML Write annotation*)
theory Write
imports "../DTML" 
begin

(*DTML Write annotation is locally correct*)
lemma Write_local:
assumes "thrdsvars"
and "total_wfs (\<tau> \<sigma>)"
and "  Write_inv  t  ((pc \<sigma>) t) \<sigma>  "
and "TML_Write  t   \<sigma> \<sigma>'"
and " syst \<noteq> t"
and " ( (writer \<sigma> = None \<and>  ((pc \<sigma>) syst) = RecIdle)   \<longrightarrow> ( \<forall> a. a \<in>  dom (log \<sigma>) \<longrightarrow> [a]\<^sup>A\<^sub>t (\<tau> \<sigma>) =  {lastVal a  (\<tau> \<sigma>)}) )  " (*need to prove *)
and   " \<forall>  t.  ( writer \<sigma> = Some t \<longrightarrow> odd (lastVal glb  (\<tau> \<sigma>)) )"
and "  (\<forall>a. a \<in> dom (log \<sigma>) \<longrightarrow> a \<noteq> glb) "
shows "Write_inv t  ((pc \<sigma>') t) \<sigma>'" 
  using assms
  apply (simp add:TML_Write_def Write_inv_def  )
  apply (cases "pc \<sigma> t";  simp;  cases "pc \<sigma>' t";  simp  )
  using total_wfs_def lastVal_def 
  apply (elim conjE)
  apply ( simp  add: split: if_split_asm)
  apply (simp add: Ready_total_def)
  apply (elim conjE)
  apply ( simp  add: split: if_split_asm)
  apply (simp add: Ready_total_def)
  apply ( simp  add: split: if_split_asm)
  apply ( simp  add: split: if_split_asm)
  apply (smt (z3) Ready_total_def)
  apply ( simp  add: split: if_split_asm)
  apply ( simp  add: split: if_split_asm)
  apply (simp add: Ready_total_def)
  apply ( simp  add: split: if_split_asm)
  apply ( simp  add: split: if_split_asm)
  apply ( simp  add: split: if_split_asm)
  apply ( simp  add: split: if_split_asm)
  apply ( simp  add: split: if_split_asm)
  apply ( simp  add: split: if_split_asm)
  apply (subgoal_tac "writer \<sigma> = None ")
  prefer 2
  apply (unfold total_wfs_def)
  apply ( simp  add: split: if_split_asm)
  apply ( simp  add: split: if_split_asm)
  apply ( simp  add: split: if_split_asm)
  apply ( simp  add: split: if_split_asm)
  using total_wfs_def 
  apply (intro conjI) 
  apply (metis reg_same_CAS_dr)
  apply (metis assms(2) cas_lastVal less_numeral_extra(3))
  apply (metis cas_sv_lc less_numeral_extra(3) numeral_1_eq_Suc_0 numerals(1))
  apply (metis cas_lc gr0_conv_Suc lastVal_def nat.distinct(1) reg_same_CAS_dr)
  apply (subgoal_tac "  (\<forall>a. a \<in> dom (log \<sigma>) \<longrightarrow> [a]\<^sup>A\<^sub>t  \<tau> \<sigma> = {lastVal a (\<tau> \<sigma>)})  ")
  prefer 2
  apply (metis cas_nlv_lc gr0_conv_Suc lastVal_def nat.distinct(1) not_None_eq)
  using cas_le_daddr cas_oav_daddr_ni apply presburger
  apply ( simp  add: split: if_split_asm)
  apply ( simp  add: split: if_split_asm)
  apply ( simp  add: split: if_split_asm)
  apply ( simp  add: split: if_split_asm)
  apply ( simp  add: split: if_split_asm)
  apply ( simp  add: split: if_split_asm)
  apply (metis reg_OAV_ni reg_write_OV_ni reg_write_lastVal_ni reg_write_lc)
  apply ( simp  add: split: if_split_asm)
  apply ( simp  add: split: if_split_asm)
  apply ( simp  add: split: if_split_asm)
  apply ( simp  add: split: if_split_asm)
  apply ( simp  add: split: if_split_asm)
  apply ( simp  add: split: if_split_asm)
  apply ( simp  add: split: if_split_asm)
  apply ( simp  add: split: if_split_asm)
  apply ( simp  add: split: if_split_asm)
  apply ( simp  add: split: if_split_asm)
  apply (intro conjI)
  apply (metis reg_same_ld_dt)
  apply (smt (z3) assms(2) insert_absorb lastVal_ni ld_ov_sub lev_in_ov subset_singletonD)
  apply (metis assms(2) lastVal_ni reg_same_ld_dt)
  apply (metis assms(2) lastVal_ni ld_ov_lc singletonD)
  apply (metis assms(2) lastVal_ni ld_oav_ni)
  apply (metis assms(2) lastVal_ni ld_oav_ni)
  apply (intro conjI)
  apply (metis reg_same_st)
  apply (metis assms(2) st_lastVal_lc st_lv__daddr_ni st_ov_lc st_ov_ni)
  apply (metis assms(2) reg_same_st st_lv__daddr_ni)
  apply (metis assms(2) st_lv__daddr_ni st_oav_daddr_ni)
  apply (simp add: Ready_total_def)
  apply (intro conjI)
  apply (metis reg_same_flo)
  apply (metis assms(2) flo_lastVal_ni flo_ov_ni)
  apply (metis assms(2) flo_lastVal_ni reg_same_flo)
  apply (metis reg_same_flo)
  apply (metis assms(2) flo_lastVal_ni reg_same_flo)
  apply (metis assms(2) flo_lastVal_ni flo_ov_ni)
  apply (metis reg_same_flo)
  apply (metis assms(2) flo_lastVal_ni flo_ov_ni)
  apply clarify
  apply (case_tac " a = inLoc \<sigma> t")
  apply (subgoal_tac "lastVal a (\<tau> \<sigma>')  = lastVal a (\<tau> \<sigma>)  ")
  prefer 2
  apply (metis assms(2) flo_lastVal_ni)
  using flo_oav_ov_rel_s[where  t =t]  
  apply (metis assms(2) empty_iff total_wfs_def)
  apply (metis assms(2) domIff flo_lastVal_ni flo_oav_daddr_ni option.distinct(1))
  by (metis assms(2) flo_lastVal_ni reg_same_flo)







end









