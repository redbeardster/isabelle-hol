
(*typedecl Val*)

theory Write_Read_Global
imports "../../DTML"
begin


 (*auxiliary lemma*)
lemma cas_read_pre_ni:
assumes  "read_pre (\<tau> \<sigma>) ta b "
and " \<tau> \<sigma> [CAS glb regs (\<tau> \<sigma>) tb DTML.loc Suc (regs (\<tau> \<sigma>) tb DTML.loc) c1]\<^sub>tb \<tau> \<sigma>' "
and "thrdsvars"
and "total_wfs (\<tau> \<sigma>)"
and " ta \<noteq> syst"
and "tb \<noteq> syst"
and "ta \<noteq> tb"
shows   "read_pre (\<tau> \<sigma>') ta b "
  using assms
  apply (unfold total_wfs_def read_pre_def)
  apply (subgoal_tac " ta \<noteq> tb ")
   prefer 2
  using thrdsvars_def apply linarith
  apply (subgoal_tac " (regs (\<tau> \<sigma>) ta DTML.loc) = (regs (\<tau> \<sigma>') ta DTML.loc)")
   prefer 2
  using reg_same_CAS_dt
   apply presburger
  apply (subgoal_tac "  valOf ( last_entry_lim (\<tau> \<sigma>') b (coh (\<tau> \<sigma>') ta  glb)) b (\<tau> \<sigma>) = valOf(  last_entry_lim (\<tau> \<sigma>) b (coh (\<tau> \<sigma>) ta glb)) b (\<tau> \<sigma>) ")
   prefer 2
  using assms(4) cas_le_lim_dt_ni apply presburger
  apply (intro conjI)  
      apply metis
  using cas_coh_dt_ni apply presburger
  using assms(4) cas_coh_valof_dt_ni apply presburger
   apply (metis assms(4) cas_le_lim_dt_ni cas_vrnew_dt_ni)
  by(metis assms(4) cas_coh_dt_ni cas_vrnew_dt_ni)

(*\<tau> \<sigma> [a := v]\<^sub>tb \<tau> \<sigma>*) (*auxiliary lemma*)
lemma write_v_read_pre_ni:
assumes  "read_pre (\<tau> \<sigma>) ta b "
and "( \<tau> \<sigma>) [a := v]\<^sub>tb (\<tau> \<sigma>') "
and "thrdsvars"
and "total_wfs (\<tau> \<sigma>)"
and " ta \<noteq> syst"
and "tb \<noteq> syst"
and "ta \<noteq> tb"
shows   "read_pre (\<tau> \<sigma>') ta b "
  using assms
  apply (unfold total_wfs_def read_pre_def thrdsvars_def)
  apply (subgoal_tac " vrnew (\<tau> \<sigma>') ta = vrnew (\<tau> \<sigma>) ta")
   prefer 2
   apply (simp add: step_def)
   apply (simp add: store_trans_def)
  apply (intro conjI)
      apply (metis reg_same_st)
     apply (metis assms(4) reg_coh_dt_ni)
    apply (metis assms(4) reg_same_st st_coh_valof_dt_ni)
   apply (metis assms(4) st_le_lim_dt_ni)
  by (metis assms(4) reg_coh_dt_ni)


(* \<tau> \<sigma> [r3 \<leftarrow> a]\<^sub>tb \<tau> \<sigma>' *) (*auxiliary lemma*)
lemma read_read_pre_ni:
assumes  "read_pre (\<tau> \<sigma>) ta b "
and "(\<tau> \<sigma>) [r3 \<leftarrow> a]\<^sub>tb (\<tau> \<sigma>') "
and "thrdsvars"
and "total_wfs (\<tau> \<sigma>)"
and " ta \<noteq> syst"
and "tb \<noteq> syst"
and "ta \<noteq> tb"
shows   "read_pre (\<tau> \<sigma>') ta b "
  using assms
  apply (simp add: total_wfs_def read_pre_def thrdsvars_def)
  apply (intro conjI)
  using reg_same_ld_dt apply presburger
     apply (metis assms(4) ld_coh_dt_ni)
    apply (metis assms(4) ld_coh_valof_dt_ni reg_same_ld_dt)
   apply (metis assms(2) assms(4) ld_le_coh_ni ld_vrnew_dt_ni)
  by (metis assms(4) ld_coh_dt_ni ld_vrnew_dt_ni)

(*auxiliary lemma*)
lemma upreg_read_pre_ni:
assumes  "read_pre (\<tau> \<sigma>) ta b "
and " \<tau> \<sigma>' = (update_reg tb DTML.loc (lastVal glb (\<tau> \<sigma>)) (\<tau> \<sigma>)) "
and "thrdsvars"
and "total_wfs (\<tau> \<sigma>)"
and " ta \<noteq> syst"
and "tb \<noteq> syst"
and "ta \<noteq> tb"
shows   "read_pre (\<tau> \<sigma>') ta b "
  using assms
  apply (unfold total_wfs_def read_pre_def thrdsvars_def)
  apply (intro conjI)
      apply (metis reg_dt_ni)
     apply (metis (mono_tags, lifting) assms(4) reg_coh_ni)
    apply (unfold valOf_def)
    apply (metis (mono_tags, lifting) assms(4) reg_coh_ni reg_dt_ni reg_write__crash reg_write_mem)
   apply (subgoal_tac "vrnew (\<tau> \<sigma>') ta = vrnew (\<tau> \<sigma>) ta ")
    prefer 2
    apply (simp add: update_reg_def)
  using assms(4) reg_coh_lim_dt_ni apply presburger
  apply (subgoal_tac "vrnew (\<tau> \<sigma>') ta = vrnew (\<tau> \<sigma>) ta ")
   prefer 2
   apply (simp add: update_reg_def)
  using assms(4) reg_coh_ni by presburger

(*\<tau> \<sigma> [flush\<^sub>o a]\<^sub>tb \<tau> \<sigma>'*)  (*auxiliary lemma*)
lemma flo_read_pre_ni:
assumes  "read_pre (\<tau> \<sigma>) ta b "
and " (\<tau> \<sigma>) [flush\<^sub>o a]\<^sub>tb (\<tau> \<sigma>')"
and "thrdsvars"
and "total_wfs (\<tau> \<sigma>)"
and " ta \<noteq> syst"
and "tb \<noteq> syst"
and "ta \<noteq> tb"
shows   "read_pre (\<tau> \<sigma>') ta b "
  using assms
  apply (unfold total_wfs_def read_pre_def thrdsvars_def)
  apply (subgoal_tac "vrnew (\<tau> \<sigma>') ta = vrnew (\<tau> \<sigma>) ta ")
   prefer 2
   apply (simp add: step_def flush_opt_trans_def)
  by (metis (no_types, lifting) assms(4) flo_coh_ni flo_coh_valof_dt_ni flo_le_lim_dt_ni reg_same_flo)


(*Read annotation is stable against the DTML write  operation*)
lemma Write_Read_global:
assumes "thrdsvars"
and "total_wfs (\<tau> \<sigma>)"
and "pm_inv \<sigma> "
and  " \<forall>  t.  (   writer \<sigma> = Some t \<longrightarrow> odd (lastVal glb  (\<tau> \<sigma>)) )" (*persistent invariant*)
and " \<forall>  t. (  (   writer \<sigma>  = Some t    \<longrightarrow> \<lceil>glb\<rceil>\<^sub>t (\<tau> \<sigma>) ))" (*persistent invariant*)
and "glb_monotone_inv (\<tau> \<sigma>) " (*persistent invariant*)
and " (\<forall> a \<noteq> glb. mem_tml_prop    glb a  (\<tau> \<sigma>) )" (*persistent invariant*)
and "mem_tml_prop3  (\<tau> \<sigma>)" (*persistent invariant*)
and "  Write_inv  tb  ((pc \<sigma>) tb) \<sigma>  "
and "  Read_inv  ta   ((pc \<sigma>) ta)  \<sigma>  "
and "TML_Write  tb    \<sigma> \<sigma>'"
and "((pc \<sigma>) tb) \<in> {WritePending, WriteResponding} \<union> writing \<union> {Aborted}"
and "((pc \<sigma>) ta) \<in> {ReadPending, ReadResponding } \<union> reading \<union> {Aborted}" 
and " ta \<noteq> syst"
and "tb \<noteq> syst"
and "ta \<noteq> tb"
shows "  Read_inv  ta   ((pc \<sigma>') ta)  \<sigma>'  "
  using assms
  apply (simp add:TML_Write_def Write_inv_def Read_inv_def thrdsvars_def )
  apply (cases "(pc \<sigma>) tb"; simp; cases "(pc \<sigma>) ta"; simp )
  apply (unfold total_wfs_def  Ready_total_def)
  apply ( simp add: split: if_split_asm)
  apply ( simp add: split: if_split_asm)
  apply ( simp add: split: if_split_asm)
  apply ( simp add: split: if_split_asm)
  apply ( simp add: split: if_split_asm)
  apply ( simp add: split: if_split_asm)
  apply ( simp add: split: if_split_asm)
  apply ( simp add: split: if_split_asm)
  apply ( simp add: split: if_split_asm)
  apply ( simp add: split: if_split_asm)
  apply ( simp add: split: if_split_asm)
  apply ( simp add: split: if_split_asm)
  apply ( simp add: split: if_split_asm)
  apply ( simp add: split: if_split_asm)
  apply ( simp add: split: if_split_asm)
  apply ( simp add: split: if_split_asm)
  apply (case_tac "   odd (regs (\<tau> \<sigma>) ta DTML.loc)")
  apply simp
  apply (intro conjI)
  apply (metis reg_same_CAS_dt)
  apply (meson cas_fail_lastVal_dt_ni)
  apply (metis assms(2) cas_fail_lastVal_same reg_same_CAS_dt)
  apply (metis reg_same_CAS_dt)
  apply (metis assms(2) cas_fail_lastVal_same reg_same_CAS_dt)
  apply (meson cas_fail_lastVal_dt_ni)
  apply (metis reg_same_CAS_dt)
  apply (meson cas_fail_lastVal_dt_ni)
  apply (metis assms(2) cas_fail_lastVal_same cas_fail_oav_ni cas_le_daddr)
  apply (metis assms(2) cas_fail_lastVal_same reg_same_CAS_dt)
  apply (case_tac " \<not> readAux \<sigma>' ta \<and>  \<not> writeAux \<sigma>' ta ")
  apply simp
  apply (elim disjE)
  apply (subgoal_tac "      regs (\<tau> \<sigma>') ta DTML.loc = lastVal glb (\<tau> \<sigma>') \<or>
regs (\<tau> \<sigma>') ta DTML.loc < lastVal glb (\<tau> \<sigma>') ")
  prefer 2
  apply (metis assms(2) cas_fail_lastVal_same reg_same_CAS_dt)
  apply (subgoal_tac " \<forall> l. [l]\<^sub>ta  (\<tau> \<sigma>') = [l]\<^sub>ta  (\<tau> \<sigma>) ")
  prefer 2
  apply (metis (no_types, lifting) cas_dt_ni cas_fail_lastVal_dt_ni singletonD)
  apply (metis cas_le_daddr reg_same_CAS_dt)
  apply (metis assms(2) cas_fail_lastVal_same reg_same_CAS_dt)
  apply (metis assms(1) assms(2) cas_read_pre_ni reg_same_CAS_dt)
  apply (metis (no_types, lifting) Suc_lessD Suc_mono assms(1) assms(2) cas_lc cas_read_pre_ni cas_succ_eq lastVal_def lessI not_gr0 reg_same_CAS_dt)
  apply ( simp add: split: if_split_asm)
  apply (case_tac "   odd (regs (\<tau> \<sigma>) ta DTML.loc)")
  apply simp
  apply (intro conjI)
  apply (metis reg_same_CAS_dt)
  apply (meson cas_fail_lastVal_dt_ni)
  apply (metis assms(2) cas_fail_lastVal_same reg_same_CAS_dt)
  apply (meson cas_fail_lastVal_dt_ni)
  apply (metis cas_le_daddr reg_same_CAS_dt)
  apply (metis cas_fail_lv_ni lastVal_def reg_same_CAS_dt)
  apply (meson cas_fail_lastVal_dt_ni)
  apply (metis reg_same_CAS_dt)
  apply (meson cas_fail_lastVal_dt_ni)
  apply (metis assms(2) cas_fail_lastVal_same cas_fail_oav_ni cas_le_daddr)
  apply (smt (z3) assms(1) assms(2) cas_fail_lastVal_same cas_le_daddr cas_le_lim_valof_dt_ni cas_nov_lc cas_read_pre_ni even_Suc reg_same_CAS_dt)
  apply (case_tac "   odd (regs (\<tau> \<sigma>) ta DTML.loc)")
  apply simp
  apply simp
  apply (case_tac " \<not> readAux \<sigma>' ta \<and>  \<not> writeAux \<sigma>' ta ")
  apply (elim disjE)
  apply simp
  apply (subgoal_tac " regs (\<tau> \<sigma>') ta DTML.loc = lastVal glb (\<tau> \<sigma>') \<and> (\<forall>l. [l]\<^sub>ta \<tau> \<sigma>' = {lastVal l (\<tau> \<sigma>')}) ")
  prefer 2
  apply (intro conjI)
  apply (metis assms(2) cas_fail_lastVal_same reg_same_CAS_dt)
  apply (metis cas_fail_lastVal_dt_ni)
  apply (metis assms(2) cas_fail_lastVal_same)
  apply simp
  apply (subgoal_tac " \<forall> l. [l]\<^sub>ta  (\<tau> \<sigma>') = [l]\<^sub>ta  (\<tau> \<sigma>) ")
  prefer 2
  apply (metis cas_dt_ov_ni)
  using  reg_same_CAS_dt
  apply (metis assms(2) cas_fail_lastVal_same)
  apply simp
  apply (smt (z3) assms(1) assms(2) cas_fail_diff_lv cas_le_lim_valof_dt_ni cas_nov_lc cas_read_pre_ni cas_succ_lv_lc cas_sv_lc even_Suc lastVal_def less_Suc_eq neq0_conv reg_same_CAS_dt)
  apply (case_tac "   odd (regs (\<tau> \<sigma>) ta DTML.loc)")
  apply simp
  apply (metis cas_fail_diff_lv gr_implies_not_zero)
  apply (case_tac " \<not> readAux \<sigma>' ta \<and>  \<not> writeAux \<sigma>' ta ")
  apply simp
  apply (intro conjI)
  apply (metis assms(2) cas_fail_lastVal_same reg_same_CAS_dt)
  apply (metis cas_fail_diff_lv cas_lc lastVal_def less_Suc_eq neq0_conv reg_same_CAS_dt)
  apply (smt (verit) cas_lc cas_nlv_lc dual_order.asym lastVal_def less_Suc_eq reg_same_CAS_dt)
  apply (metis assms(1) assms(2) cas_read_pre_ni reg_same_CAS_dt)
  apply ( simp add: split: if_split_asm)
  apply (case_tac "   odd (regs (\<tau> \<sigma>) ta DTML.loc)")
  apply simp
  apply (intro conjI)
  apply (metis reg_same_CAS_dt)
  apply (metis cas_fail_lv_ni lastVal_def reg_same_CAS_dt)
  apply (meson cas_fail_lastVal_dt_ni)
  apply (metis cas_le_daddr reg_same_CAS_dt)
  apply (metis assms(2) cas_fail_lastVal_same cas_fail_oav_ni cas_le_daddr)
  apply simp
  apply (case_tac " \<not> readAux \<sigma>' ta \<and>  \<not> writeAux \<sigma>' ta ")
  apply simp
  apply (metis assms(2) cas_fail_lastVal_same cas_le_daddr reg_same_CAS_dt)
  apply simp
  apply (elim disjE)
  apply simp+
  apply (smt (z3) assms(1) assms(2) cas_fail_diff_lv cas_le_lim_valof_dt_ni cas_nov_lc cas_read_pre_ni cas_succ_lv_lc cas_sv_lc even_Suc lastVal_def less_Suc_eq neq0_conv reg_same_CAS_dt)
  apply (smt (z3) assms(1) assms(2) cas_fail_diff_lv cas_le_lim_valof_dt_ni cas_nov_lc cas_read_pre_ni cas_succ_lv_lc cas_sv_lc even_Suc lastVal_def less_Suc_eq neq0_conv reg_same_CAS_dt)
  apply (smt (z3) assms(1) assms(2) cas_fail_diff_lv cas_le_lim_valof_dt_ni cas_nov_lc cas_read_pre_ni cas_succ_lv_lc cas_sv_lc even_Suc lastVal_def less_Suc_eq neq0_conv reg_same_CAS_dt)
  apply (smt (z3) assms(1) assms(2) cas_fail_diff_lv cas_le_lim_valof_dt_ni cas_nov_lc cas_read_pre_ni cas_succ_lv_lc cas_sv_lc even_Suc lastVal_def less_Suc_eq neq0_conv reg_same_CAS_dt)
  apply (smt (z3) assms(1) assms(2) cas_fail_diff_lv cas_le_lim_valof_dt_ni cas_nov_lc cas_read_pre_ni cas_succ_lv_lc cas_sv_lc even_Suc lastVal_def less_Suc_eq neq0_conv reg_same_CAS_dt)
  apply (smt (z3) assms(1) assms(2) cas_fail_diff_lv cas_le_lim_valof_dt_ni cas_nov_lc cas_read_pre_ni cas_succ_lv_lc cas_sv_lc even_Suc lastVal_def less_Suc_eq neq0_conv reg_same_CAS_dt)
  apply ( simp add: split: if_split_asm)
  apply (case_tac "   odd (regs (\<tau> \<sigma>) ta DTML.loc)")
  apply simp         
  apply (case_tac " \<not> readAux \<sigma>' ta \<and>  \<not> writeAux \<sigma>' ta ")
  apply (metis assms(2) cas_fail_lastVal_same cas_le_daddr reg_same_CAS_dt)
  apply (smt (z3) assms(1) assms(2) cas_fail_diff_lv cas_le_lim_valof_dt_ni cas_nov_lc cas_read_pre_ni cas_succ_lv_lc cas_sv_lc even_Suc lastVal_def less_Suc_eq neq0_conv reg_same_CAS_dt)
  apply (smt (z3) assms(1) assms(2) cas_fail_diff_lv cas_le_lim_valof_dt_ni cas_nov_lc cas_read_pre_ni cas_succ_lv_lc cas_sv_lc even_Suc lastVal_def less_Suc_eq neq0_conv reg_same_CAS_dt)
  apply ( simp add: split: if_split_asm)
  apply (case_tac "   odd (regs (\<tau> \<sigma>) ta DTML.loc)")
  apply simp
  apply (intro conjI)
  apply (metis reg_same_CAS_dt)
  apply (metis cas_fail_lv_ni lastVal_def reg_same_CAS_dt)
  apply (meson cas_fail_lastVal_dt_ni)
  apply (metis cas_le_daddr reg_same_CAS_dt)
  apply (metis assms(2) cas_fail_lastVal_same cas_fail_oav_ni cas_le_daddr)
  apply (case_tac " \<not> readAux \<sigma>' ta \<and>  \<not> writeAux \<sigma>' ta ")
  apply (metis assms(2) cas_fail_lastVal_same cas_le_daddr reg_same_CAS_dt)
  apply (smt (z3) assms(1) assms(2) cas_fail_diff_lv cas_le_lim_valof_dt_ni cas_nov_lc cas_read_pre_ni cas_succ_lv_lc cas_sv_lc even_Suc lastVal_def less_Suc_eq neq0_conv reg_same_CAS_dt)
  apply (smt (z3) assms(1) assms(2) cas_fail_diff_lv cas_le_lim_valof_dt_ni cas_nov_lc cas_read_pre_ni cas_succ_lv_lc cas_sv_lc even_Suc lastVal_def less_Suc_eq neq0_conv reg_same_CAS_dt)
  apply ( simp add: split: if_split_asm)
  apply (case_tac "   odd (regs (\<tau> \<sigma>) ta DTML.loc)")
  apply simp
  apply (intro conjI)
  apply (metis reg_same_CAS_dt)
  apply (metis assms(2) cas_fail_lastVal_same reg_same_CAS_dt)
  apply (metis cas_le_daddr reg_same_CAS_dt)
  apply (meson cas_fail_lastVal_dt_ni)
  apply (metis reg_same_CAS_dt)
  apply (metis assms(2) cas_fail_lastVal_same cas_fail_oav_ni cas_le_daddr)
  apply (metis assms(1) assms(2) cas_le_lim_valof_dt_ni cas_read_pre_ni reg_same_CAS_dt)
  apply (metis (no_types, lifting) assms(1) assms(2) cas_le_lim_valof_dt_ni cas_read_pre_ni cas_succ_eq cas_sv_lc not_gr0 reg_same_CAS_dt)
  apply ( simp add: split: if_split_asm)
  apply (case_tac "   odd (regs (\<tau> \<sigma>) ta DTML.loc)")
  apply simp
  apply (intro conjI)
  apply (metis reg_same_CAS_dt)
  apply (meson cas_fail_lastVal_dt_ni)
  apply (metis assms(2) cas_fail_lastVal_same reg_same_CAS_dt)
  apply (metis reg_same_CAS_dt)
  apply (metis assms(2) cas_fail_lastVal_same reg_same_CAS_dt)
  apply (meson cas_fail_lastVal_dt_ni)
  apply (metis reg_same_CAS_dt)
  apply (meson cas_fail_lastVal_dt_ni)
  apply (metis assms(2) cas_fail_lastVal_same cas_fail_oav_ni cas_le_daddr)
  apply (metis assms(2) cas_fail_lastVal_same reg_same_CAS_dt)
  apply (case_tac " \<not> readAux \<sigma>' ta \<and>  \<not> writeAux \<sigma>' ta ")
  apply simp
  apply (metis (no_types, lifting) assms(2) cas_dt_ov_ni cas_fail_lastVal_same cas_le_daddr reg_same_CAS_dt)
  apply (metis assms(1) assms(2) cas_read_pre_ni reg_same_CAS_dt)
  apply (metis assms(1) assms(2) cas_read_pre_ni cas_succ_eq cas_succ_lv_lc cas_sv_lc lastVal_def less_Suc_eq not_gr0 reg_same_CAS_dt)
  apply ( simp add: split: if_split_asm)
  apply (metis assms(1) assms(2) fun_upd_other option.inject reg_dt_ni reg_write_lastVal_ni upreg_read_pre_ni)
    (***********************)
  apply (case_tac "   odd (regs (\<tau> \<sigma>) ta DTML.loc)")
  apply simp
  apply simp
  apply (metis assms(1) assms(2) reg_dt_ni reg_write_lastVal_ni upreg_read_pre_ni)
  apply (case_tac "   odd (regs (\<tau> \<sigma>) ta DTML.loc)")
  apply simp
  apply (case_tac " \<not> readAux \<sigma>' ta \<and>  \<not> writeAux \<sigma>' ta ")
  apply simp
  using reg_dt_ni reg_write_lastVal_ni apply presburger
  apply (case_tac "  readAux \<sigma>' ta \<and>  \<not> writeAux \<sigma>' ta ")
  apply simp
  apply (subgoal_tac " memory (\<tau> \<sigma>)  = memory (\<tau> \<sigma>') ")
  prefer 2
  using reg_write_mem apply presburger
  using lastVal_def 
  apply (metis assms(1) assms(2) option.inject reg_coh_lim_dt_ni reg_dt_ni reg_write_OV_ni reg_write__crash reg_write_lastVal_ni upreg_read_pre_ni valOf_def)
  using lastVal_def 
  apply (metis assms(1) assms(2) option.inject reg_coh_lim_dt_ni reg_dt_ni reg_write_OV_ni reg_write__crash reg_write_lastVal_ni upreg_read_pre_ni valOf_def)
  using lastVal_def
  using reg_dt_ni reg_write_lastVal_ni apply presburger
  using lastVal_def 
  apply (metis assms(1) assms(2) option.inject reg_coh_lim_dt_ni reg_dt_ni reg_write_OV_ni reg_write__crash reg_write_mem upreg_read_pre_ni valOf_def)
  using lastVal_def
  apply (metis assms(1) assms(2) option.inject reg_coh_lim_dt_ni reg_dt_ni reg_write__crash reg_write_mem upreg_read_pre_ni valOf_def)
  using lastVal_def 
  apply (metis assms(1) assms(2) fun_upd_other option.inject reg_dt_ni reg_write_lastVal_ni upreg_read_pre_ni)
  apply ( simp add: split: if_split_asm)
  apply ( simp add: split: if_split_asm)
  apply ( simp add: split: if_split_asm)
  apply ( simp add: split: if_split_asm)
  apply ( simp add: split: if_split_asm)
  apply ( simp add: split: if_split_asm)
  apply ( simp add: split: if_split_asm)
  apply ( simp add: split: if_split_asm)
(*******************************)
  apply (metis assms(1) assms(2) fun_upd_apply lastVal_ni option.inject read_read_pre_ni reg_same_ld_dt)
  apply (metis assms(1) assms(2) fun_upd_apply lastVal_ni option.inject read_read_pre_ni reg_same_ld_dt)
  apply (smt (z3) assms(1) assms(2) lastVal_ni ld_le_lim_valof_dt_ni ld_ov_ni option.inject read_read_pre_ni reg_same_ld_dt)
  apply (metis assms(2) lastVal_ni reg_same_ld_dt)
  apply (metis (no_types, lifting) assms(1) assms(2) ld_le_lim_valof_dt_ni ld_ov_ni option.inject read_read_pre_ni reg_same_ld_dr)
  apply (metis (no_types, lifting) assms(1) assms(2) ld_le_lim_valof_dt_ni option.inject read_read_pre_ni reg_same_ld_dr)
  apply (metis assms(1) assms(2) fun_upd_apply lastVal_ni option.inject read_read_pre_ni reg_same_ld_dr)
  apply (metis fun_upd_other option.inject)
  apply (metis fun_upd_def map_upd_Some_unfold)
  apply (metis option.inject)
  apply (metis option.inject)
  apply (metis option.inject)
  apply (metis fun_upd_other option.inject)
    (****************)
  apply (metis assms(1) assms(2) fun_upd_apply option.inject reg_same_st st_lv__daddr_ni write_v_read_pre_ni)
  apply (metis assms(1) assms(2) fun_upd_apply option.inject reg_same_st st_lv__daddr_ni write_v_read_pre_ni)
  apply (smt (z3) assms(1) assms(2) option.inject reg_same_st st_le_coh_valof_dt_ni st_lv__daddr_ni st_ov_ni write_v_read_pre_ni)
  apply (metis assms(2) reg_same_st st_lv__daddr_ni)
  apply (metis assms(1) assms(2) option.inject reg_same_st st_le_coh_valof_dt_ni st_ov_ni write_v_read_pre_ni)
  apply (metis assms(1) assms(2) option.inject reg_same_st st_le_coh_valof_dt_ni write_v_read_pre_ni)
  apply (metis assms(1) assms(2) fun_upd_apply option.inject reg_same_st st_lv__daddr_ni write_v_read_pre_ni)
    (**************)
  apply (metis assms(1) assms(2) flo_lastVal_ni flo_read_pre_ni fun_upd_apply option.inject reg_same_flo)
  apply (metis assms(1) assms(2) flo_lastVal_ni flo_read_pre_ni fun_upd_apply option.inject reg_same_flo)
  apply (smt (z3) assms(1) assms(2) flo_lastVal_ni flo_le_coh_valof_dt_ni flo_ov_ni flo_read_pre_ni option.inject reg_same_flo)
  apply (metis assms(2) flo_lastVal_ni reg_same_flo)
  apply (metis assms(1) assms(2) flo_le_coh_valof_dt_ni flo_ov_ni flo_read_pre_ni option.inject reg_same_flo)
  apply (metis assms(1) assms(2) flo_le_coh_valof_dt_ni flo_read_pre_ni option.inject reg_same_flo)
  by (metis assms(1) assms(2) flo_lastVal_ni flo_read_pre_ni fun_upd_other option.inject reg_same_flo)





























































































































end

