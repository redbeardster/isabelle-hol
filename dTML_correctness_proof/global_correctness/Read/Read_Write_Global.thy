theory Read_Write_Global
imports "../../DTML"
begin


(*Write annotation is stable against the DTML read operation*)
lemma Read_Write_global:
assumes "thrdsvars"
and "total_wfs (\<tau> \<sigma>)"
and "pm_inv \<sigma> "
and  " \<forall>  t.  (   writer \<sigma> = Some t \<longrightarrow> odd (lastVal glb  (\<tau> \<sigma>)) )" (*persistent invariant*)
and " \<forall>  t. (  (   writer \<sigma>  = Some t    \<longrightarrow> \<lceil>glb\<rceil>\<^sub>t (\<tau> \<sigma>) ))"  (*persistent invariant*)
and "glb_monotone_inv (\<tau> \<sigma>) "  (*persistent invariant*)
and "(\<forall> a \<noteq> glb. mem_tml_prop    glb a  (\<tau> \<sigma>)) " (*persistent invariant*)
and "  Read_inv  tb   ((pc \<sigma>) tb)  \<sigma>  "
and "  Write_inv  ta  ((pc \<sigma>) ta) \<sigma>  "
and " TML_Read  tb   \<sigma> \<sigma>'"
and "((pc \<sigma>) tb) \<in> {ReadPending, ReadResponding } \<union>  reading \<union> {Aborted} "
and "((pc \<sigma>) ta) \<in> {WritePending, WriteResponding  } \<union> writing \<union> {Aborted}" 
and " ta \<noteq> syst"
and "tb \<noteq> syst"
and "ta \<noteq> tb"
shows  "  Write_inv  ta   ((pc \<sigma>') ta) \<sigma>'  " 
  using assms
  apply (unfold thrdsvars_def )
  apply (simp add:TML_Read_def Read_inv_def Write_inv_def   )
  apply (cases "(pc \<sigma>) ta";simp; cases "(pc \<sigma>) tb" ;simp)
                      apply (unfold total_wfs_def Ready_total_def read_pre_def )
                      apply (smt (z3) fun_upd_other)
                      apply (subgoal_tac " \<forall>a .   [a]\<^sub>ta \<tau> \<sigma> =  [a]\<^sub>ta  \<tau> \<sigma>' ")
                      prefer 2
                      apply (metis ld_ov_ni)
                      apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc) ")
                      apply simp
  using  reg_same_ld_dt
                      apply (smt (z3) assms(2) lastVal_ni ld_oav_ni)
                      apply simp
  using  reg_same_ld_dt
                      apply (smt (verit) assms(2) lastVal_ni ld_coh_dt_ni ld_coh_valof_dt_ni ld_le_lim_ni ld_vrnew_dt_ni)
  using  reg_same_ld_dt 
                      apply (smt (z3) PC.simps(1659) pc_aux)
                      apply ( simp add: split: if_split_asm)
                      apply (subgoal_tac " \<forall>a .   [a]\<^sub>ta \<tau> \<sigma> =  [a]\<^sub>ta  \<tau> \<sigma>' ")
                      prefer 2
  using assms(2) cas_ov_daddr_dt_sx_ni apply presburger
                      apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc) ")
                      apply simp
                      apply (metis One_nat_def assms(2) cas_succ_eq)
                      apply (case_tac "    \<not> readAux \<sigma> ta \<and>  \<not> writeAux \<sigma> ta ")
                      apply simp
                      apply (metis (no_types, lifting) One_nat_def assms(2) cas_le_daddr cas_succ_eq cas_succ_lv_lc lastVal_def reg_same_CAS_dt)
                      apply (smt (z3) assms(2) cas_coh_dt_ni cas_coh_valof_dt_ni cas_le_lim_dt_ni cas_vrnew_dt_ni reg_same_CAS_dt)
                      apply (subgoal_tac " \<forall>a .   [a]\<^sub>ta \<tau> \<sigma> =  [a]\<^sub>ta  \<tau> \<sigma>' ")
                      prefer 2
  using assms(2) cas_ov_daddr_dt_sx_ni apply presburger
                      apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc) ")
                      apply simp
                      apply (metis assms(2) cas_fail_oav_ni cas_sv_lc cas_wfs_preserved reg_same_CAS_dt singletonD total_wfs_def)
                      apply (case_tac "    \<not> readAux \<sigma> ta \<and>  \<not> writeAux \<sigma> ta ")
                      apply (metis One_nat_def assms(2) cas_fail_lastVal_same cas_lc cas_le_daddr reg_same_CAS_dt)
                      apply simp
                      apply (metis (no_types, opaque_lifting) assms(2) cas_coh_dt_ni cas_coh_valof_dt_ni cas_le_lim_dt_ni cas_vrnew_dt_ni reg_same_CAS_dt)
                      apply (subgoal_tac " \<forall>a .   [a]\<^sub>ta \<tau> \<sigma> =  [a]\<^sub>ta  \<tau> \<sigma>' ")
                      prefer 2
                      apply (metis ld_ov_ni)
                      apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc) ")
                      apply (smt (z3) assms(2) fun_upd_other lastVal_ni ld_oav_ni reg_same_ld_dr)
                      apply (case_tac "    \<not> readAux \<sigma> ta \<and>  \<not> writeAux \<sigma> ta ")
                      apply (metis (no_types, opaque_lifting) assms(2) fun_upd_other lastVal_ni reg_same_ld_dt)
                      apply (smt (z3) assms(2) fun_upd_other ld_coh_dt_ni ld_coh_valof_dt_ni ld_le_lim_ni ld_vrnew_dt_ni reg_same_ld_dr)
                      apply (simp add: split if_splits)
                      apply (case_tac " regs (\<tau> \<sigma>) tb r3 =
regs (\<tau> \<sigma>) tb DTML.loc")
                      apply simp
                      apply simp
                      apply (smt (z3) fun_upd_other)
                      apply simp
  using  reg_same_ld_dt
                      apply (smt (verit) assms(2) lastVal_ni ld_coh_dt_ni ld_coh_valof_dt_ni ld_le_lim_ni ld_oav_ni ld_ov_ni ld_vrnew_dt_ni)
  using  reg_same_ld_dt 
                      apply ( simp add: split: if_split_asm)
  apply ( simp add: split: if_split_asm)
  apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc) ")
  apply (metis cas_nlv_lc lastVal_def numeral_1_eq_Suc_0 numeral_eq_one_iff zero_neq_one)
  apply (case_tac "    \<not> readAux \<sigma> ta \<and>  \<not> writeAux \<sigma> ta ")
  apply simp
  apply (subgoal_tac "even (regs (\<tau> \<sigma>') ta DTML.loc)")
  prefer 2
  apply (metis reg_same_CAS_dt)
  apply simp
  apply (elim disjE)
  apply (smt (z3) assms(2) cas_le_daddr cas_ov_daddr_dt_sx_ni cas_succ_lv_lc lastVal_def numeral_1_eq_Suc_0 numerals(1) reg_same_CAS_dt)
  apply (metis cas_lc lastVal_def numeral_1_eq_Suc_0 one_eq_numeral_iff reg_same_CAS_dt zero_neq_one)
  apply (metis cas_fail_diff_lv less_irrefl_nat n_not_Suc_n)
  apply (metis Zero_not_Suc cas_fail_diff_lv less_irrefl_nat)
  apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc) ")
  apply (smt (z3) assms(2) fun_upd_other lastVal_ni ld_oav_ni reg_same_ld_dr)
  apply (case_tac "    \<not> readAux \<sigma> ta \<and>  \<not> writeAux \<sigma> ta ")
  apply (metis (no_types, opaque_lifting) assms(2) fun_upd_other lastVal_ni reg_same_ld_dt)
  apply simp
  apply (intro conjI)
  apply (metis reg_same_CAS_dt)
  apply (smt (z3) One_nat_def assms(2) cas_coh_dt_ni cas_coh_valof_dt_ni cas_fail_diff_lv cas_lc cas_le_daddr cas_le_lim_dt_ni cas_ov_daddr_dt_sx_ni cas_vrnew_dt_ni lastVal_def reg_same_CAS_dt zero_neq_one)
  apply (metis reg_same_CAS_dt)
  apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc) ")
  apply simp
  apply (intro conjI)
  apply (metis reg_same_CAS_dt)
  apply (metis cas_fail_diff_lv cas_fail_lastVal_dt_ni)
  apply (metis cas_fail_lv_ni lastVal_def reg_same_CAS_dt)
  apply (metis reg_same_CAS_dt)
  apply (metis cas_fail_lv_ni lastVal_def reg_same_CAS_dt)
  apply (metis cas_fail_diff_lv cas_fail_lastVal_dt_ni)
  apply (metis reg_same_CAS_dt)
  apply (metis cas_fail_diff_lv cas_fail_lastVal_dt_ni)
  apply (metis assms(2) cas_fail_diff_lv cas_fail_lastVal_same cas_fail_oav_ni cas_le_daddr)
  apply (metis cas_fail_lv_ni lastVal_def reg_same_CAS_dt)
  apply (case_tac "    \<not> readAux \<sigma> ta \<and>  \<not> writeAux \<sigma> ta ")
  apply simp
  apply (elim disjE)
  apply (subgoal_tac " (\<forall>l. [l]\<^sub>ta \<tau> \<sigma>' = {lastVal l (\<tau> \<sigma>')}) ")
  prefer 2
  apply (metis (no_types, lifting) assms(2) cas_ov_daddr_dt_sx_ni lev_in_ov singleton_iff total_wfs_def)
  apply (metis cas_possible_lv_lc lastVal_def reg_same_CAS_dt)
  apply (metis cas_possible_lv_lc lastVal_def reg_same_CAS_dt)
  apply (subgoal_tac " (\<forall>l. [l]\<^sub>ta \<tau> \<sigma>' = {lastVal l (\<tau> \<sigma>')}) ")
  prefer 2
  apply (metis (no_types, lifting) assms(2) cas_ov_daddr_dt_sx_ni lev_in_ov singleton_iff total_wfs_def)
  apply (metis cas_fail_lv_ni lastVal_def less_irrefl_nat reg_same_CAS_dt)
  apply (metis cas_fail_lv_ni lastVal_def less_irrefl_nat reg_same_CAS_dt)
  apply (case_tac "    \<not> readAux \<sigma> ta \<and>  \<not> writeAux \<sigma> ta ")
  apply simp
  apply (case_tac "     readAux \<sigma> ta \<and>  \<not> writeAux \<sigma> ta ")
  apply simp
  apply (intro conjI)
  apply (metis reg_same_CAS_dt)
  apply (smt (z3) One_nat_def assms(2) cas_coh_dt_ni cas_coh_valof_dt_ni cas_fail_diff_lv cas_lc cas_le_daddr cas_le_lim_dt_ni cas_ov_daddr_dt_sx_ni cas_vrnew_dt_ni lastVal_def reg_same_CAS_dt zero_neq_one)
  apply (metis reg_same_CAS_dt)
  apply presburger
  apply simp
  using  reg_same_ld_dr
  apply (smt (verit) assms(2) lastVal_ni ld_coh_dt_ni ld_coh_valof_dt_ni ld_le_lim_ni ld_oav_ni ld_ov_ni ld_vrnew_dt_ni)
  using  reg_same_ld_dr 
  apply (smt (z3) PC.simps(1660) assms(14) pc_aux)
  using  inloc_aux
  apply (metis fun_upd_other)
  apply (metis reg_same_ld_dt)
  apply (subgoal_tac " \<forall>a .   [a]\<^sub>ta \<tau> \<sigma> =  [a]\<^sub>ta  \<tau> \<sigma>' ")
  prefer 2
  apply (meson ld_ov_ni)
  apply (metis (no_types, opaque_lifting) assms(2) lastVal_ni ld_oav_ni reg_same_ld_dt)
  apply ( simp add: split: if_split_asm)
  apply (smt (z3) assms(2) lastVal_ni ld_oav_ni ld_ov_ni reg_same_ld_dr)
  apply ( simp add: split: if_split_asm)
  apply ( simp add: split: if_splits)
  apply (metis One_nat_def assms(2) cas_succ_eq)
  apply (smt (z3) assms(2) cas_dt_ov_ni cas_fail_lastVal_same cas_fail_oav_ni cas_le_daddr cas_succ_eq cas_sv_lc reg_same_CAS_dt)
  apply (smt (z3) assms(2) lastVal_ni ld_oav_ni ld_ov_ni reg_same_ld_dr)
  apply ( simp add: split: if_splits)
  apply ( simp add: split: if_splits)
  apply ( simp add: split: if_splits)
  apply (metis reg_same_CAS_dt)
  apply (metis reg_same_CAS_dt)
  apply (metis reg_same_ld_dt)
  apply ( simp add: split: if_splits)
  using  inloc_aux 
  apply (metis update_def)
  apply (intro conjI)
  apply (metis reg_same_ld_dt)
  apply (metis assms(2) lastVal_ni ld_ov_ni)
  apply (metis reg_same_ld_dt)
  apply (metis assms(2) lastVal_ni reg_same_ld_dt)
  apply (metis assms(2) lastVal_ni ld_oav_ni)
  apply ( simp add: split: if_splits)
  apply ( simp add: split: if_splits)
  apply (metis Zero_not_Suc cas_fail_diff_lv)
  apply (subgoal_tac " \<forall>a .   [a]\<^sub>ta \<tau> \<sigma> =  [a]\<^sub>ta  \<tau> \<sigma>' ")
  prefer 2
  apply (metis assms(2) cas_ov_daddr_dt_sx_ni)
  apply (smt (z3) assms(2) cas_fail_diff_lv cas_fail_lastVal_same cas_fail_oav_ni cas_le_daddr reg_same_CAS_dt)
  apply (smt (z3) assms(2) lastVal_ni ld_oav_ni ld_ov_ni reg_same_ld_dt)
  apply ( simp add: split: if_splits)
  apply ( simp add: split: if_splits)
  apply (smt (z3) assms(2) lastVal_ni ld_oav_ni ld_ov_ni reg_same_ld_dt)
  apply (smt (z3) PC.simps(1663) assms(14) pc_aux)
  apply ( simp add: split: if_splits)
  apply (metis One_nat_def assms(2) cas_succ_eq)
  apply (metis One_nat_def assms(2) cas_fail_lastVal_same cas_fail_oav_ni cas_lc cas_ov_daddr_dt_sx_ni cas_wfs_preserved insertE insert_absorb insert_not_empty reg_same_CAS_dt total_wfs_def)
  apply (smt (verit, best) assms(2) lastVal_ni ld_oav_ni ld_ov_ni reg_same_ld_dt)
  apply ( simp add: split: if_splits)
  apply (metis fun_upd_other)
  apply (smt (z3) assms(2) fun_upd_other lastVal_ni ld_coh_dt_ni ld_coh_valof_dt_ni ld_le_lim_ni ld_oav_ni ld_ov_ni ld_vrnew_dt_ni reg_same_ld_dt)
  apply ( simp add: split: if_splits)
  apply ( simp add: split: if_splits)
  apply (smt (z3) One_nat_def assms(2) cas_coh_dt_ni cas_coh_valof_dt_ni cas_fail_diff_lv cas_lc cas_le_daddr cas_le_lim_dt_ni cas_ov_daddr_dt_sx_ni cas_vrnew_dt_ni lastVal_def reg_same_CAS_dt zero_neq_one)
  apply (subgoal_tac " \<forall>a .   [a]\<^sub>ta \<tau> \<sigma> =  [a]\<^sub>ta  \<tau> \<sigma>' ")
  prefer 2
  apply (metis assms(2) cas_ov_daddr_dt_sx_ni)
  apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc) ")
  apply simp
  apply (metis assms(2) cas_fail_oav_ni cas_sv_lc cas_wfs_preserved reg_same_CAS_dt singletonD total_wfs_def)
  apply (case_tac "    \<not> readAux \<sigma> ta \<and>  \<not> writeAux \<sigma> ta ")
  apply (metis One_nat_def assms(2) cas_fail_lastVal_same cas_lc cas_le_daddr reg_same_CAS_dt)
  apply simp
  apply (smt (z3) assms(2) lastVal_ni ld_oav_ni ld_ov_ni reg_same_ld_dt)
  apply (smt (z3) PC.simps(1664) pc_aux)
  apply (metis fun_upd_apply)
  apply (smt (z3) assms(2) lastVal_ni ld_oav_ni ld_ov_ni reg_same_ld_dr)
  apply (smt (z3) PC.simps(1665) pc_aux)
  apply ( simp add: split: if_splits)
  apply (metis cas_nlv_lc lastVal_def numeral_1_eq_Suc_0 one_eq_numeral_iff zero_neq_one)
  apply (intro conjI)
  apply (metis reg_same_CAS_dt)
  apply (metis assms(15) cas_fail_diff_lv cas_fail_lastVal_dt_ni)
  apply (metis cas_fail_lv_ni lastVal_def reg_same_CAS_dt)
  apply (metis cas_le_daddr reg_same_CAS_dt)
  apply (metis (no_types, opaque_lifting) assms(2) cas_fail_diff_lv cas_fail_lastVal_same cas_fail_oav_ni cas_le_daddr)
  apply (smt (z3) assms(2) lastVal_ni ld_oav_ni ld_ov_ni reg_same_ld_dr)
  apply ( simp add: split: if_splits)
  apply (metis fun_upd_apply)
  apply (smt (z3) assms(2) lastVal_ni ld_oav_ni ld_ov_ni reg_same_ld_dt)
  apply (case_tac "  even (regs (\<tau> \<sigma>) tb DTML.loc) \<and> \<not> readAux \<sigma> tb")
  apply simp
  apply simp
  apply ( simp add: split: if_splits)
  apply (metis Zero_not_Suc cas_fail_diff_lv)
  apply (intro conjI)
  apply (metis reg_same_CAS_dt)
  apply (metis cas_fail_diff_lv cas_fail_lastVal_dt_ni)
  apply (metis cas_fail_lv_ni lastVal_def reg_same_CAS_dt)
  apply (metis assms(2) cas_fail_diff_lv cas_fail_lastVal_same cas_fail_oav_ni cas_le_daddr)
  apply (smt (z3) assms(2) lastVal_ni ld_oav_ni ld_ov_ni reg_same_ld_dt)
  apply ( simp add: split: if_splits)
  apply (metis fun_upd_other)
  using  reg_same_ld_dt  
  apply (smt (z3) assms(2) lastVal_ni ld_oav_ni ld_ov_ni)
  apply ( simp add: split: if_splits)
  apply ( simp add: split: if_splits)
  apply (metis Zero_not_Suc cas_fail_diff_lv)
  apply (intro conjI)
  apply (metis reg_same_CAS_dt)
  apply (metis cas_fail_diff_lv cas_fail_lastVal_dt_ni)
  apply (metis cas_fail_lv_ni lastVal_def reg_same_CAS_dt)
  apply (metis (no_types, opaque_lifting) assms(2) cas_fail_diff_lv cas_fail_lastVal_same cas_fail_oav_ni cas_le_daddr numeral_2_eq_2)
  apply (smt (z3) assms(2) lastVal_ni ld_oav_ni ld_ov_ni reg_same_ld_dt)
  apply ( simp add: split: if_splits)
  apply ( simp add: split: if_splits)
  apply simp
  using  reg_same_ld_dt  
  apply (smt (verit) assms(2) lastVal_ni ld_coh_dt_ni ld_coh_valof_dt_ni ld_le_lim_ni ld_oav_ni ld_ov_ni ld_vrnew_dt_ni)


  apply ( simp add: split: if_splits)
  apply ( simp add: split: if_splits)

  apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc) ")
  apply simp
  apply (intro conjI)
  apply (metis reg_same_CAS_dt)
  apply (metis cas_fail_diff_lv cas_fail_lastVal_dt_ni)
  apply (metis cas_fail_lv_ni lastVal_def reg_same_CAS_dt)
  apply (metis reg_same_CAS_dt)
  apply (metis cas_fail_lv_ni lastVal_def reg_same_CAS_dt)
  apply (metis cas_fail_diff_lv cas_fail_lastVal_dt_ni)
  apply (metis reg_same_CAS_dt)
  apply (metis cas_fail_diff_lv cas_fail_lastVal_dt_ni)
  apply (metis assms(2) cas_fail_diff_lv cas_fail_lastVal_same cas_fail_oav_ni cas_le_daddr)
  apply (metis cas_fail_lv_ni lastVal_def reg_same_CAS_dt)
  apply (case_tac "    \<not> readAux \<sigma> ta \<and>  \<not> writeAux \<sigma> ta ")
  apply simp
  apply (elim disjE)
  apply (subgoal_tac " (\<forall>l. [l]\<^sub>ta \<tau> \<sigma>' = {lastVal l (\<tau> \<sigma>')}) ")
  prefer 2
  apply (metis (no_types, lifting) assms(2) cas_ov_daddr_dt_sx_ni lev_in_ov singleton_iff total_wfs_def)
  apply (metis cas_possible_lv_lc lastVal_def reg_same_CAS_dt)
  apply (metis cas_possible_lv_lc lastVal_def reg_same_CAS_dt)
  apply (metis Zero_not_Suc cas_fail_diff_lv less_irrefl_nat)
  apply (metis Zero_not_Suc cas_fail_diff_lv less_irrefl_nat)
  apply simp
  apply (metis (no_types, opaque_lifting) assms(2) cas_coh_dt_ni cas_coh_valof_dt_ni cas_le_lim_dt_ni cas_vrnew_dt_ni reg_same_CAS_dt)

  apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc) ")
  apply simp
  apply (intro conjI)
  apply (metis reg_same_CAS_dt)
  apply (metis cas_fail_diff_lv cas_fail_lastVal_dt_ni)
  apply (metis cas_fail_lv_ni lastVal_def reg_same_CAS_dt)
  apply (metis reg_same_CAS_dt)
  apply (metis cas_fail_lv_ni lastVal_def reg_same_CAS_dt)
  apply (metis cas_fail_diff_lv cas_fail_lastVal_dt_ni)
  apply (metis reg_same_CAS_dt)
  apply (metis cas_fail_diff_lv cas_fail_lastVal_dt_ni)
  apply (metis assms(2) cas_fail_diff_lv cas_fail_lastVal_same cas_fail_oav_ni cas_le_daddr)
  apply (metis cas_fail_lv_ni lastVal_def reg_same_CAS_dt)
  apply (case_tac "    \<not> readAux \<sigma> ta \<and>  \<not> writeAux \<sigma> ta ")
  apply simp
  apply (elim disjE)
  apply (subgoal_tac " (\<forall>l. [l]\<^sub>ta \<tau> \<sigma>' = {lastVal l (\<tau> \<sigma>')}) ")
  prefer 2
  apply (metis (no_types, lifting) assms(2) cas_ov_daddr_dt_sx_ni lev_in_ov singleton_iff total_wfs_def)
  apply (metis cas_possible_lv_lc lastVal_def reg_same_CAS_dt)
  apply (metis cas_possible_lv_lc lastVal_def reg_same_CAS_dt)
  apply (subgoal_tac " \<forall> l.  lastVal l (\<tau> \<sigma>') = lastVal l (\<tau> \<sigma>) ")
  prefer 2
  apply (metis cas_fail_lv_ni cas_le_daddr lastVal_def less_irrefl_nat)
  apply (metis assms(2) cas_ov_daddr_dt_sx_ni reg_same_CAS_dt)
  apply (metis cas_fail_lv_ni lastVal_def less_irrefl_nat reg_same_CAS_dt)
  apply simp
  apply (metis (no_types, opaque_lifting) assms(2) cas_coh_dt_ni cas_coh_valof_dt_ni cas_le_lim_dt_ni cas_vrnew_dt_ni reg_same_CAS_dt)
  apply simp
  using  reg_same_ld_dr
  apply (smt (verit) assms(2) lastVal_ni ld_coh_dt_ni ld_coh_valof_dt_ni ld_le_lim_ni ld_oav_ni ld_ov_ni ld_vrnew_dt_ni)

  apply ( simp add: split: if_splits)
  apply ( simp add: split: if_splits)
  apply ( simp add: split: if_splits)
  by ( simp add: split: if_splits)















end
