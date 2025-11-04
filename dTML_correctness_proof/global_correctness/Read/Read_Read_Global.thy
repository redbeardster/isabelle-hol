
(*typedecl Val*)

theory Read_Read_Global
imports "../../DTML"
begin

(*auxiliary lemma*)
lemma cas_read_pre_ni:
assumes  "read_pre (\<tau> \<sigma>) ta b "
and "\<tau> \<sigma> [CAS glb regs (\<tau> \<sigma>) tb DTML.loc regs (\<tau> \<sigma>) tb DTML.loc c1]\<^sub>tb \<tau> \<sigma>'"
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
by (metis assms(4) cas_coh_dt_ni cas_coh_valof_dt_ni cas_le_lim_dt_ni cas_vrnew_dt_ni)


(*auxiliary lemma*)
lemma read_read_pre_ni:
assumes  "read_pre (\<tau> \<sigma>) ta g "
and "( \<tau> \<sigma>) [f \<leftarrow> v]\<^sub>tb ( \<tau> \<sigma>')"
and "thrdsvars"
and "total_wfs (\<tau> \<sigma>)"
and " ta \<noteq> syst"
and "tb \<noteq> syst"
and "ta \<noteq> tb"
shows   "read_pre (\<tau> \<sigma>') ta g "
  using assms
  apply (subgoal_tac " ta \<noteq> tb ")
   prefer 2
  using thrdsvars_def apply linarith
  apply (unfold total_wfs_def read_pre_def)
  apply (intro conjI)
      apply (metis reg_same_ld_dr)
  using assms(4) ld_coh_dt_ni apply presburger
    apply (subgoal_tac " regs (\<tau> \<sigma>) ta DTML.loc = regs (\<tau> \<sigma>') ta DTML.loc")
     prefer 2
  using reg_same_ld_dr apply presburger
    apply (subgoal_tac " (coh (\<tau> \<sigma>') ta glb) = (coh (\<tau> \<sigma>) ta glb)")
     prefer 2
  using assms(4) ld_coh_dt_ni apply presburger
    apply (simp add: valOf_def)
    apply (metis ld_step_mem survived_val_preserved_load)
   apply (metis assms(4) ld_le_coh_ni ld_vrnew_dt_ni)
  by (metis assms(4) ld_coh_dt_ni ld_vrnew_dt_ni)

(*auxiliary lemma*)
lemma read_cas_lv_ni:
assumes "(\<forall>l. [l]\<^sub>ta \<tau> \<sigma> = {lastVal l (\<tau> \<sigma>)})"
and " \<tau> \<sigma> [CAS glb regs (\<tau> \<sigma>) tb DTML.loc regs (\<tau> \<sigma>) tb DTML.loc c1]\<^sub>tb \<tau> \<sigma>' "
and "regs (\<tau> \<sigma>') tb  c1 = 1"
and "thrdsvars"
and "total_wfs (\<tau> \<sigma>)"
and " ta \<noteq> syst"
and "tb \<noteq> syst"
and "ta \<noteq> tb"
shows "\<forall>l. [l]\<^sub>ta \<tau> \<sigma>' = {lastVal l (\<tau> \<sigma>')}"
  using assms
  apply (unfold  total_wfs_def)
  apply clarify
  apply (case_tac " l \<noteq> glb ")
   apply (smt (verit, ccfv_SIG) cas_le_daddr cas_ov_daddr_ni_s ex_in_conv)
  apply (subgoal_tac " lastVal l (\<tau> \<sigma>) = regs (\<tau> \<sigma>) tb DTML.loc ")
   prefer 2
   apply(simp add: step_def)
   apply clarify
   apply (subgoal_tac " \<tau> \<sigma>' = cas_succ_trans tb ind glb (regs (\<tau> \<sigma>) tb DTML.loc) (regs (\<tau> \<sigma>) tb DTML.loc) c1  nv mnv (\<tau> \<sigma>)")
    prefer 2
    apply (metis Zero_neq_Suc cas_fail_reg)
   apply (metis Zero_neq_Suc assms(2) cas_fail_diff_lv)
  apply (subgoal_tac " lastVal l (\<tau> \<sigma>') = regs (\<tau> \<sigma>) tb DTML.loc ")
   prefer 2
   apply(simp add: step_def)
   apply clarify
   apply (subgoal_tac " \<tau> \<sigma>' = cas_succ_trans tb ind glb (regs (\<tau> \<sigma>) tb DTML.loc) (regs (\<tau> \<sigma>) tb DTML.loc) c1  nv mnv (\<tau> \<sigma>)")
    prefer 2
    apply (metis Zero_neq_Suc cas_fail_reg)
   apply (metis assms(2) assms(3) cas_succ_lv_lc lastVal_def)
  apply (subgoal_tac " lastVal l (\<tau> \<sigma>')  \<in>  [l]\<^sub>ta  (\<tau> \<sigma>')")
   prefer 2
  using lev_in_ov apply blast
  by (smt (z3) Set.set_insert cas_nov_lc lev_in_ov singleton_insert_inj_eq subset_iff subset_insertI)


(*Read annotation is stable against the DTML read operation*)
lemma Read_Read_global:
assumes "thrdsvars"
and "total_wfs (\<tau> \<sigma>)"
and "pm_inv \<sigma> "
and  " \<forall>  t.  (   writer \<sigma> = Some t \<longrightarrow> odd (lastVal glb  (\<tau> \<sigma>)) )"  (*persistent invariant*)
and " \<forall>  t. (  (   writer \<sigma>  = Some t    \<longrightarrow> \<lceil>glb\<rceil>\<^sub>t (\<tau> \<sigma>) ))" (*persistent invariant*)
and "glb_monotone_inv (\<tau> \<sigma>) " (*persistent invariant*)
and " (\<forall> a \<noteq> glb. (mem_tml_prop    glb a  (\<tau> \<sigma>))) "
and "  Read_inv  tb   ((pc \<sigma>) tb)  \<sigma>  "
and "  Read_inv  ta   ((pc \<sigma>) ta)  \<sigma>  "
and " TML_Read  tb   \<sigma> \<sigma>'"
and "((pc \<sigma>) tb) \<in> {ReadPending, ReadResponding } \<union>  reading\<union> {Aborted} "
and "((pc \<sigma>) ta) \<in> {ReadPending, ReadResponding  } \<union>  reading \<union> {Aborted}" 
and " mem_tml_prop3   (\<tau> \<sigma>) "
and " ta \<noteq> syst"
and "tb \<noteq> syst"
and "ta \<noteq> tb"
shows  "  Read_inv  ta  ((pc \<sigma>') ta)  \<sigma>'  "
  using assms
  apply (unfold thrdsvars_def )
  apply (simp add:TML_Read_def Read_inv_def  )
  apply (cases "(pc \<sigma>) ta";simp; cases "(pc \<sigma>) tb" ;simp)
  apply (unfold total_wfs_def Ready_total_def)
  apply simp
  apply ( simp add: split: if_split_asm)
  apply (smt (z3) assms(1) assms(2) lastVal_ni ld_oav_ni ld_ov_ni read_read_pre_ni reg_same_ld_dr)
  apply ( simp add: split: if_split_asm)
  apply ( simp add: split: if_split_asm)
  apply (subgoal_tac " [glb]\<^sub>ta \<tau> \<sigma>' = [glb]\<^sub>ta \<tau> \<sigma>   ")
  prefer 2
  apply (subgoal_tac " lastVal glb (\<tau> \<sigma>') = lastVal glb (\<tau> \<sigma>) ")
  prefer 2
  apply (metis assms(2) cas_succ_eq cas_succ_lv_lc lastVal_def numeral_1_eq_Suc_0 numeral_eq_one_iff)
  apply (simp add: step_def)
  apply clarify
  apply (subgoal_tac"  \<tau> \<sigma>' =
cas_succ_trans tb ind glb (regs (\<tau> \<sigma>) tb DTML.loc)
(regs (\<tau> \<sigma>) tb DTML.loc) c1  nv mnv (\<tau> \<sigma>)")
  prefer 2
  apply (metis cas_fail_reg numeral_1_eq_Suc_0 numeral_eq_one_iff zero_neq_one)
  apply (subgoal_tac " [glb]\<^sub>ta \<tau> \<sigma>' = [glb]\<^sub>ta \<tau> \<sigma> \<union>   { (regs (\<tau> \<sigma>) tb DTML.loc)} ")
  prefer 2
  apply (metis cas_succ_ov_dt_lc)
  apply (metis cas_fail_reg compval_def insert_absorb insert_is_Un lastVal_def numeral_1_eq_Suc_0 numeral_eq_one_iff sup.commute zero_neq_one)
  apply (subgoal_tac " \<forall> a. [a]\<^sub>ta \<tau> \<sigma>' = [a]\<^sub>ta \<tau> \<sigma>   ")
  prefer 2
  apply (metis cas_dt_ni cas_ov_daddr_ni subsetI subset_antisym)
  apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc)")
  apply simp
  apply (metis One_nat_def assms(2) cas_succ_eq)
  apply (case_tac " \<not> readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
  apply simp
  apply (metis (no_types, lifting) One_nat_def cas_le_daddr cas_nlv_lc cas_succ_lv_lc lastVal_def reg_same_CAS_dt zero_neq_one)
  apply simp
  apply (metis assms(2) cas_read_pre_ni reg_same_CAS_dt thrdsvars_def)
  apply (subgoal_tac " \<forall> a. [a]\<^sub>ta \<tau> \<sigma>' = [a]\<^sub>ta \<tau> \<sigma>   ")
  prefer 2
  apply (simp add: step_def)
  apply clarify
  apply (case_tac "  \<tau> \<sigma>' =
cas_fail_trans tb ind glb (regs (\<tau> \<sigma>) tb DTML.loc)
(regs (\<tau> \<sigma>) tb DTML.loc) c1 (\<tau> \<sigma>)")
  prefer 2
  apply (metis One_nat_def cas_suc_reg)
  apply (metis cas_fail_ov_ni)
  apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc)")
  apply simp
  apply (metis assms(2) cas_fail_oav_ni cas_sv_lc cas_wfs_preserved reg_same_CAS_dt singletonD total_wfs_def)
  apply (case_tac " \<not> readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
  apply (metis One_nat_def assms(2) cas_fail_lastVal_same cas_le_daddr cas_sv_lc reg_same_CAS_dt)
  apply (metis assms(2) cas_read_pre_ni reg_same_CAS_dt thrdsvars_def)
  apply (smt (z3) assms(1) assms(2) fun_upd_other lastVal_ni ld_oav_ni ld_ov_ni read_read_pre_ni reg_same_ld_dt)
  apply ( simp add: split: if_split_asm) 
  apply (smt (z3) fun_upd_other)
  apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc)")
  apply simp
  apply (smt (z3) assms(2) lastVal_ni ld_oav_ni ld_ov_ni reg_same_ld_dt)
  apply (case_tac " \<not> readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
  apply simp
  apply (metis assms(2) lastVal_ni ld_ov_ni reg_same_ld_dt)
  apply simp
  apply (metis assms(1) assms(2) read_read_pre_ni reg_same_ld_dr)
  apply simp
  apply ( simp add: split: if_split_asm) 
  apply ( simp add: split: if_split_asm) 
  apply (elim conjE disjE)
  apply metis
  apply (metis One_nat_def cas_le_daddr cas_succ_lv_lc lastVal_def reg_same_CAS_dt)
  apply (metis One_nat_def cas_succ_lv_lc lastVal_def reg_same_CAS_dt)
  apply (metis assms(1) assms(2) cas_le_lim_valof_dt_ni cas_read_pre_ni reg_same_CAS_dt)
  apply (metis cas_nov_lc reg_same_CAS_dt)
  apply (metis One_nat_def assms(2) cas_succ_eq)
  apply (metis One_nat_def assms(2) cas_succ_eq less_irrefl_nat)
  apply (metis One_nat_def assms(2) cas_succ_eq less_irrefl_nat)
  apply (metis One_nat_def assms(2) cas_succ_eq less_irrefl_nat)
  apply (metis One_nat_def assms(2) cas_succ_eq less_irrefl_nat)
  apply meson
  apply meson
  apply meson
  apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc)")
  apply (smt (z3) assms(2) lastVal_ni ld_oav_ni ld_ov_ni reg_same_ld_dt)
  apply (case_tac " \<not> readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
  apply simp
  apply (smt (z3) assms(2) cas_le_daddr cas_ov_daddr_dt_sx_ni cas_succ_lv_lc lastVal_def numeral_1_eq_Suc_0 numerals(1) reg_same_CAS_dt)
  apply metis
  apply (metis cas_lc lastVal_def numeral_1_eq_Suc_0 one_eq_numeral_iff reg_same_CAS_dt zero_neq_one)
  apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc)")
  apply meson
  apply (case_tac " \<not> readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
  apply simp
  apply (case_tac "  readAux \<sigma> ta \<and>   \<not>writeAux \<sigma> ta ")
  apply simp
  apply (metis assms(1) assms(2) cas_read_pre_ni reg_same_CAS_dt)
  apply presburger
  apply (metis Zero_not_Suc cas_fail_diff_lv)
  apply fastforce
  apply meson
  apply meson
  apply force
  apply meson
  apply meson
  apply meson
  apply meson
  apply meson
  apply fastforce
  apply meson
  apply meson
  apply (metis cas_fail_diff_lv less_irrefl_nat numeral_1_eq_Suc_0 one_eq_numeral_iff zero_neq_one)
  apply (metis cas_fail_diff_lv less_irrefl_nat n_not_Suc_n)
  apply (metis cas_fail_diff_lv less_irrefl_nat n_not_Suc_n)
  apply (elim  disjE)
  apply metis
  apply (metis One_nat_def assms(2) cas_fail_lastVal_same cas_lc cas_le_daddr reg_same_CAS_dt)
  apply (metis One_nat_def assms(2) cas_fail_lastVal_same cas_lc reg_same_CAS_dt)
  apply (metis assms(1) assms(2) cas_le_lim_valof_dt_ni cas_read_pre_ni reg_same_CAS_dt)
  apply (metis cas_nov_lc reg_same_CAS_dt)
  apply (subgoal_tac "  odd (regs (\<tau> \<sigma>') ta DTML.loc) \<and>
regs (\<tau> \<sigma>') ta DTML.loc = lastVal glb (\<tau> \<sigma>') \<and>
(\<forall>l. [l]\<^sub>ta \<tau> \<sigma>' = {lastVal l (\<tau> \<sigma>')}) \<and>
regs (\<tau> \<sigma>') ta DTML.val = lastVal (inLoc \<sigma> ta) (\<tau> \<sigma>')  \<and> (\<forall>a. a \<in> dom (log \<sigma>) \<longrightarrow> [a]\<^sup>A\<^sub>ta  \<tau> \<sigma>' = {lastVal a (\<tau> \<sigma>')}) ")
  prefer 2
  apply (intro conjI)
  apply (metis reg_same_CAS_dt)
  apply (metis assms(2) cas_fail_diff_lv cas_fail_lastVal_same reg_same_CAS_dt)
  apply (metis cas_fail_diff_lv cas_fail_lastVal_dt_ni)
  apply (metis cas_le_daddr reg_same_CAS_dt)
  apply (metis One_nat_def assms(2) cas_fail_lastVal_same cas_fail_oav_ni cas_le_daddr cas_sv_lc)
  apply force
  apply (metis assms(2) cas_fail_diff_lv cas_fail_lastVal_same cas_le_daddr less_irrefl_nat reg_same_CAS_dt)
  apply (metis One_nat_def assms(2) cas_fail_lastVal_same cas_sv_lc reg_same_CAS_dt)
  apply (metis assms(1) assms(2) cas_le_lim_valof_dt_ni cas_read_pre_ni reg_same_CAS_dt)
  apply (metis (mono_tags, lifting) cas_fail_nov_ni cas_nov_lc lastVal_def reg_same_CAS_dt)
  apply (smt (z3) assms(1) assms(2) lastVal_ni ld_le_lim_valof_dt_ni ld_oav_ni ld_ov_ni read_read_pre_ni reg_same_ld_dt)
  apply ( simp add: split: if_split_asm) 
  apply (smt (z3) fun_upd_other)
  apply (subgoal_tac " \<forall> l.  lastVal l (\<tau> \<sigma>') =  lastVal l (\<tau> \<sigma>) ")
  prefer 2
  apply (metis cas_le_daddr cas_possible_lv_lc lastVal_def)
  apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc)")
  apply meson
  apply (case_tac " \<not> readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
  apply simp
  apply (metis assms(2) cas_ov_daddr_dt_sx_ni reg_same_CAS_dt)
  apply (smt (z3) cas_fail_lastVal_dt_ni cas_sv_lc numeral_1_eq_Suc_0 numerals(1) reg_same_CAS_dt)
  apply (smt (z3) assms(2) cas_fail_lastVal_dt_ni cas_fail_lastVal_same cas_sv_lc numeral_1_eq_Suc_0 numerals(1) reg_same_CAS_dt)
  apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc)")
  apply meson
  apply (case_tac " \<not> readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
  apply meson
  apply (case_tac " readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
  apply simp
  apply (intro conjI)
  apply (metis reg_same_CAS_dt)
  apply (metis assms(1) assms(2) cas_read_pre_ni)
  apply (metis reg_same_CAS_dt)
  apply presburger
  apply (subgoal_tac " \<forall> l.  lastVal l (\<tau> \<sigma>') =  lastVal l (\<tau> \<sigma>) ")
  prefer 2
  apply (metis cas_fail_lv_ni cas_le_daddr lastVal_def)
  apply (case_tac " readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
  apply presburger
  apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc)")
  apply simp
  apply (smt (z3) cas_dt_ov_ni cas_fail_diff_lv cas_fail_oav_ni reg_same_CAS_dt)
  apply force
  apply meson
  apply meson
  apply force
  apply meson
  apply meson
  apply meson
  apply meson
  apply fastforce
  apply meson
  apply meson
  apply meson
  apply meson
  apply (subgoal_tac " \<forall> l.  lastVal l (\<tau> \<sigma>') =  lastVal l (\<tau> \<sigma>) ")
  prefer 2
  apply (metis cas_fail_lv_ni cas_le_daddr lastVal_def less_irrefl_nat)
  apply (metis assms(2) cas_ov_daddr_dt_sx_ni reg_same_CAS_dt)
  apply (metis cas_fail_lv_ni lastVal_def less_irrefl_nat reg_same_CAS_dt)
  apply (subgoal_tac " \<forall> l.  lastVal l (\<tau> \<sigma>') =  lastVal l (\<tau> \<sigma>) ")
  prefer 2
  apply (metis cas_fail_lv_ni cas_le_daddr lastVal_def less_irrefl_nat)
  apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc)")
  apply meson
  apply (case_tac " \<not> readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
  apply meson
  apply (case_tac " readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
  apply simp
  apply (intro conjI)
  apply (metis reg_same_CAS_dt)
  apply (metis assms(1) assms(2) cas_read_pre_ni)
  apply (metis reg_same_CAS_dt)

(********HERE*****************************)
  apply ( simp add: split: if_split_asm) 
  apply (case_tac "  (odd (regs (\<tau> \<sigma>) ta DTML.loc))")
  apply simp
  apply (intro conjI)
  apply (metis reg_same_ld_dr)
  apply (smt (z3) assms(2) lastVal_ni ld_ov_ni)
  apply (metis assms(2) lastVal_ni reg_same_ld_dt)
  apply (metis assms(2) lastVal_ni reg_same_ld_dr)
  apply (smt (z3) assms(16) assms(2) lastVal_ni reg_same_ld_dr)
  apply (smt (z3) assms(2) lastVal_ni ld_ov_ni)
  apply (metis (no_types, opaque_lifting) reg_same_ld_dt)
  apply (smt (z3) assms(2) lastVal_ni ld_ov_ni)
  apply (smt (z3) assms(2) lastVal_ni ld_oav_ni)
  apply (metis assms(2) lastVal_ni reg_same_ld_dt)
  apply simp
  apply (smt (verit) assms(1) assms(2) lastVal_ni ld_ov_ni read_read_pre_ni reg_same_ld_dt)
  apply ( simp add: split: if_split_asm) 
  apply (smt (z3) fun_upd_other)
  apply (smt (verit) assms(1) assms(2) lastVal_ni ld_le_lim_valof_dt_ni ld_oav_ni ld_ov_ni read_read_pre_ni reg_same_ld_dr)
  apply ( simp add: split: if_split_asm) 
  apply ( simp add: split: if_split_asm) 
  apply (case_tac "  (odd (regs (\<tau> \<sigma>) ta DTML.loc))")
  apply simp
  apply (metis cas_fail_diff_lv n_not_Suc_n)
  apply simp
  apply (case_tac "   readAux \<sigma> ta \<and>  \<not> writeAux \<sigma> ta ")
  apply simp
  apply (smt (z3) assms(1) assms(2) cas_fail_diff_lv cas_le_lim_valof_dt_ni cas_nov_lc cas_read_pre_ni numeral_1_eq_Suc_0 reg_same_CAS_dt zero_neq_numeral)
  apply (subgoal_tac " \<forall> l.  lastVal l (\<tau> \<sigma>') =  lastVal l (\<tau> \<sigma>) ")
  prefer 2
  apply (metis cas_le_daddr cas_nlv_lc cas_succ_lv_lc lastVal_def numeral_1_eq_Suc_0 numerals(1) zero_neq_one)
  apply (smt (z3) cas_le_daddr cas_nlv_lc cas_succ_lv_lc lastVal_def numeral_1_eq_Suc_0 numerals(1) reg_same_CAS_dt zero_neq_one)
  apply (case_tac "  (odd (regs (\<tau> \<sigma>) ta DTML.loc))")
  apply simp
  apply (intro conjI)
  apply (metis reg_same_CAS_dt)
  apply (metis cas_fail_lv_ni lastVal_def reg_same_CAS_dt)
  apply (metis cas_fail_diff_lv cas_fail_lastVal_dt_ni)
  apply (metis cas_le_daddr reg_same_CAS_dt)
  apply (metis assms(2) cas_fail_diff_lv cas_fail_lastVal_same cas_fail_oav_ni cas_le_daddr)
  apply (case_tac "   readAux \<sigma> ta \<and>  \<not> writeAux \<sigma> ta ")
  apply simp
  apply (elim disjE)
  apply (metis assms(1) assms(2) cas_le_lim_valof_dt_ni cas_read_pre_ni reg_same_CAS_dt)
  apply (metis cas_nov_lc reg_same_CAS_dt)
  apply (metis assms(1) assms(2) cas_le_lim_valof_dt_ni cas_read_pre_ni reg_same_CAS_dt)
  apply (metis (mono_tags, lifting) cas_fail_nov_ni cas_nov_lc lastVal_def reg_same_CAS_dt)
  apply (smt (z3) assms(2) cas_fail_lastVal_same cas_le_daddr cas_sv_lc numeral_1_eq_Suc_0 numerals(1) reg_same_CAS_dt)
  apply (smt (z3) assms(1) assms(2) lastVal_ni ld_le_lim_valof_dt_ni ld_oav_ni ld_ov_ni read_read_pre_ni reg_same_ld_dt)
  apply ( simp add: split: if_split_asm) 
  apply (smt (z3) fun_upd_other)
  apply ( simp add: split: if_split_asm) 
  apply (smt (z3) assms(1) assms(2) lastVal_ni ld_le_lim_valof_dt_ni ld_oav_ni ld_ov_ni read_read_pre_ni reg_same_ld_dr)
  apply ( simp add: split: if_split_asm) 
  apply ( simp add: split: if_split_asm) 
  apply (elim disjE) 
  apply (smt (z3) cas_le_daddr cas_succ_lv_lc lastVal_def numeral_1_eq_Suc_0 numerals(1) reg_same_CAS_dt)
  apply (metis (no_types, lifting) cas_succ_lv_lc lastVal_def numeral_1_eq_Suc_0 numerals(1) reg_same_CAS_dt)
  apply (metis assms(2) cas_succ_eq less_not_refl2 numeral_1_eq_Suc_0 numerals(1))
  apply (metis assms(2) cas_succ_eq less_irrefl_nat numeral_1_eq_Suc_0 numerals(1))
  apply (smt (z3) assms(2) cas_fail_lastVal_same cas_le_daddr cas_sv_lc numeral_1_eq_Suc_0 numerals(1) reg_same_CAS_dt)
  apply (smt (z3) assms(2) lastVal_ni reg_same_ld_dr)
  apply (smt (z3) PC.simps(1655) pc_aux)
  apply (smt (z3) fun_upd_other)
  apply (subgoal_tac " \<forall> l.  lastVal l (\<tau> \<sigma>') =  lastVal l (\<tau> \<sigma>) ")
  prefer 2
  apply (smt (z3) assms(2) lastVal_ni)
  apply (case_tac "  (odd (regs (\<tau> \<sigma>) ta DTML.loc))")
  apply simp
  apply (metis ld_oav_ni ld_ov_ni reg_same_ld_dr)
  apply simp
  apply (case_tac "   readAux \<sigma> ta \<and>  \<not> writeAux \<sigma> ta ")
  apply simp
  apply (smt (z3) assms(1) assms(2) ld_le_lim_valof_dt_ni ld_ov_ni read_read_pre_ni reg_same_ld_dr)
  apply (smt (z3) assms(1) assms(2) fun_upd_other lastVal_ni ld_oav_ni ld_ov_ni read_read_pre_ni reg_same_ld_dt)
  apply ( simp add: split: if_split_asm)
  apply ( simp add: split: if_split_asm) 
  apply (case_tac "  (odd (regs (\<tau> \<sigma>) ta DTML.loc))")
  apply simp
  apply (metis One_nat_def assms(2) cas_succ_eq)
  apply simp
  apply (case_tac "   readAux \<sigma> ta \<and>  \<not> writeAux \<sigma> ta ")
  apply simp
  using  cas_read_pre_ni reg_same_CAS_dt 
  apply (metis (no_types, lifting) assms(1) assms(16) assms(2) cas_le_lim_valof_dt_ni cas_ov_daddr_dt_sx_ni)
  apply (metis assms(1) assms(2) cas_read_pre_ni reg_same_CAS_dt)
  apply (case_tac "  (odd (regs (\<tau> \<sigma>) ta DTML.loc))")
  apply simp
  apply (intro conjI)
  apply (metis reg_same_CAS_dt)
  apply (metis cas_fail_lv_ni lastVal_def reg_same_CAS_dt)
  apply (metis cas_fail_diff_lv cas_fail_lastVal_dt_ni)
  apply (metis cas_le_daddr reg_same_CAS_dt)
  apply (metis assms(2) cas_fail_diff_lv cas_fail_lastVal_same cas_fail_oav_ni cas_le_daddr)
  apply simp
  apply (case_tac "   readAux \<sigma> ta \<and>  \<not> writeAux \<sigma> ta ")
  apply simp
  using  cas_read_pre_ni reg_same_CAS_dt 
  apply (metis (no_types, lifting) assms(1) assms(16) assms(2) cas_le_lim_valof_dt_ni cas_ov_daddr_dt_sx_ni)
  apply presburger
  apply (case_tac "  (odd (regs (\<tau> \<sigma>) ta DTML.loc))")
  apply simp
  apply (smt (z3) assms(2) lastVal_ni ld_oav_ni ld_ov_ni reg_same_ld_dt)
  apply simp
  apply (case_tac "   readAux \<sigma> ta \<and>  \<not> writeAux \<sigma> ta ")
  apply simp
  apply (smt (z3) assms(1) assms(2) ld_le_lim_valof_dt_ni ld_ov_ni read_read_pre_ni reg_same_ld_dr)
  apply metis
  apply ( simp add: split: if_split_asm) 
  apply (smt (z3) fun_upd_other)
  apply (case_tac "   readAux \<sigma> ta \<and>  \<not> writeAux \<sigma> ta ")
  apply simp
  using  cas_read_pre_ni reg_same_CAS_dt 
  apply (smt (z3) assms(2) ld_le_lim_valof_dt_ni read_read_pre_ni reg_same_ld_dr reg_same_ld_dt thrdsvars_def)
  apply (case_tac "  (odd (regs (\<tau> \<sigma>) ta DTML.loc))")
  apply simp
  apply (smt (z3) assms(2) lastVal_ni ld_oav_ni ld_ov_ni reg_same_ld_dr)
  apply simp
  apply (case_tac "   readAux \<sigma> ta \<and>  \<not> writeAux \<sigma> ta ")
  apply simp
  apply (smt (z3) assms(1) assms(2) ld_le_lim_valof_dt_ni ld_ov_ni read_read_pre_ni reg_same_ld_dr)
  apply ( simp add: split: if_split_asm) 
  apply ( simp add: split: if_split_asm) 
  apply (case_tac "  (odd (regs (\<tau> \<sigma>) ta DTML.loc))")
  apply simp
  apply (metis cas_fail_diff_lv n_not_Suc_n)
  apply simp
  apply (case_tac "   readAux \<sigma> ta \<and>  \<not> writeAux \<sigma> ta ")
  apply simp
  apply (elim disjE)
  apply (subgoal_tac "    even (regs (\<tau> \<sigma>') ta DTML.loc) \<and>
writer \<sigma>' \<noteq> Some ta \<and>
(\<forall>a. a \<noteq> glb \<longrightarrow> read_pre (\<tau> \<sigma>') ta a) \<and>
regs (\<tau> \<sigma>') ta DTML.loc = regs (\<tau> \<sigma>') ta r3 \<and>
regs (\<tau> \<sigma>') ta DTML.val = valOf (last_entry_lim (\<tau> \<sigma>') (inLoc \<sigma> ta) (coh (\<tau> \<sigma>') ta glb)) (inLoc \<sigma> ta) (\<tau> \<sigma>') \<and> pc \<sigma> syst = RecIdle ")
  prefer 2
  apply (intro conjI)
  apply (metis reg_same_CAS_dt)
  apply blast
  apply (metis assms(1) assms(2) cas_read_pre_ni)
  apply (metis reg_same_CAS_dt)
  apply (metis assms(2) cas_le_lim_valof_dt_ni reg_same_CAS_dt)
  apply blast
  apply blast
  apply (metis reg_same_CAS_dt)
  apply (metis cas_nlv_lc lastVal_def less_irrefl_nat numeral_1_eq_Suc_0 one_eq_numeral_iff zero_neq_one)
  apply (metis cas_fail_diff_lv less_irrefl_nat numeral_1_eq_Suc_0 one_eq_numeral_iff zero_neq_one)
  apply presburger
  apply (case_tac "  (odd (regs (\<tau> \<sigma>) ta DTML.loc))")
  apply simp
  apply (subgoal_tac "(\<forall>l. [l]\<^sub>ta \<tau> \<sigma>' = {lastVal l (\<tau> \<sigma>')}) ")
  prefer 2
  apply (metis cas_fail_diff_lv cas_fail_lastVal_dt_ni)
  apply (smt (z3) assms(2) cas_fail_diff_lv cas_fail_lastVal_same cas_fail_oav_ni cas_le_daddr reg_same_CAS_dt)
  apply simp
  apply (case_tac "   readAux \<sigma> ta \<and>  \<not> writeAux \<sigma> ta ")
  apply simp
  apply (elim disjE)
  apply (subgoal_tac "    even (regs (\<tau> \<sigma>') ta DTML.loc) \<and>
writer \<sigma>' \<noteq> Some ta \<and>
(\<forall>a. a \<noteq> glb \<longrightarrow> read_pre (\<tau> \<sigma>') ta a) \<and>
regs (\<tau> \<sigma>') ta DTML.loc = regs (\<tau> \<sigma>') ta r3 \<and> regs (\<tau> \<sigma>') ta DTML.val = valOf (last_entry_lim (\<tau> \<sigma>') (inLoc \<sigma> ta) (coh (\<tau> \<sigma>') ta glb)) (inLoc \<sigma> ta) (\<tau> \<sigma>') \<and> pc \<sigma> syst = RecIdle ")
  prefer 2
  apply (intro conjI)
  apply (metis reg_same_CAS_dt)
  apply blast
  apply (metis assms(1) assms(2) cas_read_pre_ni)
  apply (metis reg_same_CAS_dt)
  apply (metis assms(2) cas_le_lim_valof_dt_ni reg_same_CAS_dt)
  apply blast
  apply blast
  apply (metis reg_same_CAS_dt)
  apply simp
  apply (subgoal_tac " even (regs (\<tau> \<sigma>') ta DTML.loc) \<and>
(\<forall>a. a \<noteq> glb \<longrightarrow> read_pre (\<tau> \<sigma>') ta a) \<and>
regs (\<tau> \<sigma>') ta DTML.loc = regs (\<tau> \<sigma>') ta r3 \<and> regs (\<tau> \<sigma>') ta DTML.val = valOf (last_entry_lim (\<tau> \<sigma>') (inLoc \<sigma> ta) (coh (\<tau> \<sigma>') ta glb)) (inLoc \<sigma> ta) (\<tau> \<sigma>')")
  prefer 2
  apply (intro conjI)
  apply (metis reg_same_CAS_dt)
  apply (metis assms(1) assms(14) assms(15) assms(2) cas_read_pre_ni)
  apply (metis reg_same_CAS_dt)
  apply (subgoal_tac "  regs (\<tau> \<sigma>') ta DTML.val =  regs (\<tau> \<sigma>) ta DTML.val ")
  prefer 2
  using reg_same_CAS_dt apply presburger
  using  cas_le_lim_valof_dt_ni 
  apply (metis assms(2))
  apply blast
  apply (metis reg_same_CAS_dt)
  apply presburger
  apply (smt (verit) assms(1) assms(2) lastVal_ni ld_le_lim_valof_dt_ni ld_oav_ni ld_ov_ni read_read_pre_ni reg_same_ld_dr)
  apply ( simp add: split: if_split_asm) 
  apply (smt (verit) fun_upd_other)
  apply (case_tac "  (odd (regs (\<tau> \<sigma>) ta DTML.loc))")
  apply simp
  apply (smt (z3) assms(2) lastVal_ni ld_oav_ni ld_ov_ni reg_same_ld_dt)
  apply simp
  apply (case_tac "   readAux \<sigma> ta \<and>  \<not> writeAux \<sigma> ta ")
  apply simp
  apply (smt (z3) assms(1) assms(2) ld_le_lim_valof_dt_ni ld_ov_ni read_read_pre_ni reg_same_ld_dr)
  apply (smt (z3) assms(2) lastVal_ni ld_ov_ni reg_same_ld_dt)
  apply ( simp add: split: if_split_asm) 
  apply ( simp add: split: if_split_asm) 
  apply (case_tac "  (odd (regs (\<tau> \<sigma>) ta DTML.loc))")
  apply simp
  apply (smt (z3) cas_fail_diff_lv numeral_1_eq_Suc_0 numerals(1) zero_neq_one)
  apply simp
  apply (case_tac "   readAux \<sigma> ta \<and>  \<not> writeAux \<sigma> ta ")
  apply simp
  apply (intro conjI)
  apply (metis reg_same_CAS_dt)
  apply (metis assms(1) assms(2) cas_read_pre_ni)
  apply (metis reg_same_CAS_dt)
  apply (subgoal_tac " \<forall> l.  lastVal l (\<tau> \<sigma>') =  lastVal l (\<tau> \<sigma>) ")
  prefer 2
  apply (metis cas_le_daddr cas_nlv_lc cas_succ_lv_lc lastVal_def numeral_1_eq_Suc_0 numerals(1) zero_neq_one)
  apply (metis assms(2) cas_ov_daddr_dt_sx_ni reg_same_CAS_dt)
  apply (case_tac "  (odd (regs (\<tau> \<sigma>) ta DTML.loc))")
  apply simp
  apply (intro conjI)
  apply (metis reg_same_CAS_dt)
  apply (metis (no_types, opaque_lifting) cas_fail_diff_lv cas_fail_lastVal_dt_ni)
  apply (metis (no_types, lifting) assms(2) cas_fail_diff_lv cas_fail_lastVal_same reg_same_CAS_dt)
  apply (smt (z3) reg_same_CAS_dt)
  apply (smt (z3) assms(2) cas_fail_diff_lv cas_fail_lastVal_same reg_same_CAS_dt)
  apply (metis (no_types, lifting) cas_fail_diff_lv cas_fail_lastVal_dt_ni)
  apply (metis reg_same_CAS_dt)
  apply (metis cas_fail_diff_lv cas_fail_lastVal_dt_ni)
  apply (metis assms(2) cas_fail_diff_lv cas_fail_lastVal_same cas_fail_oav_ni cas_le_daddr)
  apply (metis cas_fail_lv_ni lastVal_def reg_same_CAS_dt)
  apply (case_tac "   readAux \<sigma> ta \<and>  \<not> writeAux \<sigma> ta ")
  apply simp
  apply (intro conjI)
  apply (metis reg_same_CAS_dt)
  apply (metis assms(1) assms(2) cas_read_pre_ni)
  apply (metis reg_same_CAS_dt)
  apply (subgoal_tac " \<forall> l.  lastVal l (\<tau> \<sigma>') =  lastVal l (\<tau> \<sigma>) ")
  prefer 2
  apply (metis assms(2) cas_fail_lastVal_same cas_le_daddr cas_sv_lc numeral_1_eq_Suc_0 numerals(1))
  apply (metis assms(2) cas_ov_daddr_dt_sx_ni reg_same_CAS_dt)
  apply (case_tac "  (odd (regs (\<tau> \<sigma>) ta DTML.loc))")
  apply simp
  apply (smt (z3) assms(2) lastVal_ni ld_oav_ni ld_ov_ni reg_same_ld_dt)
  apply simp
  apply (case_tac "readAux \<sigma> ta \<and>  \<not> writeAux \<sigma> ta ")
  apply simp
  apply (smt (z3) assms(1) assms(2) ld_le_lim_valof_dt_ni ld_ov_ni read_read_pre_ni reg_same_ld_dr)
  apply (smt (z3) assms(2) lastVal_ni ld_ov_ni reg_same_ld_dr)
  apply ( simp add: split: if_split_asm) 
  apply ( simp add: split: if_split_asm) 
  apply ( simp add: split: if_split_asm) 
  by ( simp add: split: if_split_asm) 








end












