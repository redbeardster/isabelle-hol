(*Showing local correctness of the DTML Read annotation*)
theory Read
imports "../DTML"  "read_helper/Read_Rules"
begin

(*auxiliary lemma*)
lemma  OTS_sub_p:
assumes " (\<forall>i. i \<in> OTS (\<tau> \<sigma>) t glb \<longrightarrow> i = coh (\<tau> \<sigma>) t glb \<or> valOf i glb (\<tau> \<sigma>) \<noteq> regs (\<tau> \<sigma>) t DTML.loc) "
and "total_wfs (\<tau> \<sigma>)"
and" \<phi> \<subseteq> OTS (\<tau> \<sigma>) t glb  "
and " (\<forall>i.  i \<in> \<phi> \<longrightarrow> i \<ge> l)"
and " coh (\<tau> \<sigma>) t glb < l "
shows "(\<forall>i. i \<in> \<phi> \<longrightarrow>  valOf i glb (\<tau> \<sigma>) \<noteq> regs (\<tau> \<sigma>) t DTML.loc) "
  using assms
  using leD by blast

(*auxiliary lemma*)
lemma  OTS_not_coh:
assumes " (\<forall>i. i \<in> OTS (\<tau> \<sigma>) t glb \<longrightarrow> i = coh (\<tau> \<sigma>) t glb \<or> valOf i glb (\<tau> \<sigma>) \<noteq> regs (\<tau> \<sigma>) t DTML.loc) "
and "total_wfs (\<tau> \<sigma>)"
and "thrdsvars"
and"   (\<tau> \<sigma>) [r3   \<leftarrow>   glb ]\<^sub>t (\<tau> \<sigma>')"
and "coh (\<tau> \<sigma>') t glb \<noteq> coh (\<tau> \<sigma>) t glb "
shows " (\<forall>i. i \<in> OTS (\<tau> \<sigma>') t glb \<longrightarrow>  valOf i glb (\<tau> \<sigma>') \<noteq> regs (\<tau> \<sigma>') t DTML.loc) "
  using assms
  apply (subgoal_tac " \<forall>i. i \<in> OTS (\<tau> \<sigma>') t glb \<longrightarrow> i \<ge> coh (\<tau> \<sigma>') t glb  ")
   prefer 2
   apply (simp add: step_def)
   apply (simp add: load_trans_def)
   apply (simp add:OTS_def)
   apply (simp add:OTSF_def)
  apply (subgoal_tac " coh (\<tau> \<sigma>') t glb  \<ge> coh (\<tau> \<sigma>) t glb  ")
   prefer 2
   apply (simp add: step_def)
   apply (simp add: load_trans_def Let_def)
   apply (simp add:OTS_def)
   apply (simp add:OTSF_def)
  using assms(4) coh_ld_st_sadrr total_wfs_def apply blast
  apply (subgoal_tac " coh (\<tau> \<sigma>') t glb  > coh (\<tau> \<sigma>) t glb  ")
   prefer 2
   apply linarith
  apply (subgoal_tac "  OTS (\<tau> \<sigma>') t glb  \<subseteq>  OTS (\<tau> \<sigma>) t glb  ")
   prefer 2
   apply (unfold total_wfs_def)
   apply (meson ld_ots_sub)
  apply (subgoal_tac " regs (\<tau> \<sigma>') t DTML.loc = regs (\<tau> \<sigma>) t DTML.loc ")
   prefer 2
   apply (simp add: step_def)
   apply (meson assms(4) reg_same_ld_dt)
  by (metis assms(1) in_mono ld_crash ld_step_mem le_antisym valOf_def)

(*auxiliary lemma*)
lemma lem_same:
assumes  "thrdsvars"
and " a \<noteq> glb "
and "total_wfs ts "
and  " mem_tml_prop3  ts "
and " last_entry_lim ts a (coh ts  t glb) \<le> vrnew ts t "
and "  (coh ts  t glb) > 0 "
and "  ts  [r3 \<leftarrow> glb]\<^sub>t ts' "
and "   valOf (coh (ts) t glb) glb (ts) = regs (ts) t DTML.loc" 
and " regs (ts') t r3 = regs (ts) t DTML.loc "
and "(coh ts  t glb)  \<noteq> (coh ts'  t glb)"
shows " last_entry_lim ts' a (coh ts'  t glb) =last_entry_lim ts a (coh ts  t glb)"
  using assms
  apply (unfold total_wfs_def)
  apply (subgoal_tac " comploc (memory ts ! coh ts t glb) glb = glb ")
   prefer 2
   apply blast
  apply (subgoal_tac "   Msg.loc((memory ts)!(coh ts  t glb)) = glb ")
   prefer 2
  using  loc_eq_comploc
   apply (metis (no_types, lifting) add_lessD1 aux coh_lc coh_ld_st_sadrr ld_step_mem le_iff_add)
  apply (subgoal_tac " comploc (memory ts' ! coh ts' t glb) glb = glb ")
   prefer 2
  using coh_loc_rel_preserved apply blast
  apply (subgoal_tac "   Msg.loc((memory ts')!(coh ts'  t glb)) = glb ")
   prefer 2
  using  loc_eq_comploc 
   apply (metis aux coh_lc coh_ld_st_sadrr less_Suc_eq_le mem_structured_preserved neq0_conv not_less_eq)
  apply (subgoal_tac "    compval ts ((memory ts)!(coh ts  t glb)) glb = compval ts' ((memory ts')!(coh ts'  t glb)) glb ")
   prefer 2
   apply (metis reg_coh_lc valOf_def)
  apply (unfold mem_tml_prop3_def)
  apply (subgoal_tac " memory ts = memory ts' ")
   prefer 2
   apply (metis ld_step_mem)
  apply (simp(no_asm) add: last_entry_lim_def)
  apply (subgoal_tac "last_entry_set_lim ts' a (coh ts t glb) = 
last_entry_set_lim ts' a (coh ts' t glb) ")
   apply (unfold  last_entry_set_lim_def)
   apply metis
  by (smt (verit, best) Collect_cong aux coh_lc coh_ld_st_sadrr i_noteqo_loc ld_crash le_neq_implies_less le_trans less_imp_le_nat linorder_neqE_nat)




(*auxiliary lemma*)
lemma lem_lt_vrew:
assumes  "thrdsvars"
and " a \<noteq> glb "
and "total_wfs ts "
and  " mem_tml_prop3  ts "
and " last_entry_lim ts a (coh ts  t glb) \<le> vrnew ts t "
and "  (coh ts  t glb) > 0 "
and "  ts  [r3 \<leftarrow> glb]\<^sub>t ts' "
and "   valOf (coh (ts) t glb) glb (ts) = regs (ts) t DTML.loc" 
and " regs (ts') t r3 = regs (ts) t DTML.loc "
and "(coh ts  t glb)  \<noteq> (coh ts'  t glb)"
shows " last_entry_lim ts' a (coh ts'  t glb) \<le> vrnew ts' t"
  using assms
  apply (unfold total_wfs_def)
  apply (subgoal_tac "  last_entry_lim ts' a (coh ts t glb) =
last_entry_lim ts' a (coh ts' t glb) ")
   prefer 2
  using assms(3) ld_le_lim_ni lem_same apply presburger
  by (metis Load_Rules.vrnew_ld_st_sadrr assms(3) assms(4) assms(5) assms(7) coh_loc_rel_def ld_le_lim_ni le_trans)



(*DTML Read annotation is locally correct*)
lemma Read_local:
assumes "thrdsvars"
and "total_wfs (\<tau> \<sigma>)"
and "Read_inv t  ((pc \<sigma>) t) \<sigma>" 
and "TML_Read  t   \<sigma> \<sigma>'"
and " (\<forall> a.  mem_tml_prop   glb  a (\<tau> \<sigma>)) " (*persistent invariant*)
and " \<forall>  t. (  (   writer \<sigma>  = Some t    \<longrightarrow> \<lceil>glb\<rceil>\<^sub>t (\<tau> \<sigma>) ))"  (*persistent invariant*)
and " glb_monotone_inv  (\<tau> \<sigma>) " (*persistent invariant*)
and " \<forall>t a. t = syst \<or>    writer \<sigma> = Some t \<or>  pc \<sigma> t = Committed \<or>  pc \<sigma> t = CommitResponding  \<or> ( ( coh (\<tau> \<sigma>) t a) \<le> vrnew (\<tau> \<sigma>) t) " (*persistent invariant*)
and " t \<noteq> syst "
and "  mem_tml_prop3  (\<tau> \<sigma>) " (*persistent invariant*)
and " t \<noteq> syst"
and   " \<forall>  t.  ( writer \<sigma> = Some t \<longrightarrow> odd (lastVal glb  (\<tau> \<sigma>)) )" (*persistent invariant*)
and   " \<forall>  a.  (a \<in> dom( log \<sigma>)  \<longrightarrow> a \<noteq> glb )" (*persistent invariant*)
shows "Read_inv t  ((pc \<sigma>') t) \<sigma>'" 
  using assms
  apply (simp add:TML_Read_def Read_inv_def  total_wfs_def )
  apply (cases "pc \<sigma> t";  simp)
  apply (unfold Ready_total_def)
  apply (simp add: Ready_total_def)
  apply (metis fun_upd_apply)
  apply (case_tac "odd (regs (\<tau> \<sigma>') t DTML.loc)")
  apply (subgoal_tac "
odd (regs (\<tau> \<sigma>') t DTML.loc) \<and>
regs (\<tau> \<sigma>') t DTML.loc = lastVal glb (\<tau> \<sigma>') \<and>
(\<forall>l. [l]\<^sub>t \<tau> \<sigma>' = {lastVal l (\<tau> \<sigma>')}) \<and>
writer \<sigma>' = Some t \<and>
writeAux \<sigma> t \<and>
regs (\<tau> \<sigma>') t DTML.val = lastVal (inLoc \<sigma> t) (\<tau> \<sigma>') \<and>
pc \<sigma> syst = RecIdle \<and> (\<forall>a. a \<in> dom (log \<sigma>) \<longrightarrow> [a]\<^sup>A\<^sub>t  \<tau> \<sigma>' = {lastVal a (\<tau> \<sigma>')}) ")
  prefer 2
  apply (intro conjI)
  apply meson
  apply (metis assms(2) lastVal_ni reg_same_ld_dt)
  apply (subgoal_tac "  \<forall>l. [l]\<^sub>t \<tau> \<sigma> = {lastVal l (\<tau> \<sigma>)} ")
  prefer 2
  apply (metis reg_same_ld_dt)
  apply (simp add: total_wfs_def)
  apply (subgoal_tac "  \<forall>l. lastVal l (\<tau> \<sigma>') =   lastVal l (\<tau> \<sigma>) ")
  prefer 2
  apply (metis assms(2) lastVal_ni)
  apply (metis OV_notempty_preserved ex_in_conv ld_ov_sub subset_singleton_iff)
  apply (smt (z3) Ready_total_def reg_same_ld_dt)
  apply (smt (z3) Ready_total_def reg_same_ld_dt)
  apply (smt (z3) Ready_total_def assms(2) lastVal_ni ld_ov_lc reg_same_ld_dt singletonD)
  using Ready_total_def apply blast
  apply (smt (z3) Ready_total_def assms(2) lastVal_ni ld_oav_ni reg_same_ld_dt)
  apply blast
  apply (case_tac "  even (regs (\<tau> \<sigma>) t DTML.loc) \<and> \<not> readAux \<sigma> t " )
  apply (metis assms(2) lastVal_ni ld_ov_lc reg_same_ld_dt singletonD)
  apply (case_tac "  even (regs (\<tau> \<sigma>) t DTML.loc) \<and>  readAux \<sigma> t " )
  apply clarify
  apply (intro conjI)
  apply blast
  apply metis
  apply clarify
  apply (simp add:  read_pre_def)
  apply (intro conjI)
  apply (metis coh_ld_st_dadrr)
  apply (unfold valOf_def)
  apply (metis coh_ld_st_dadrr ld_crash ld_step_mem reg_same_ld_dt)
  apply (metis (no_types, lifting) Load_Rules.vrnew_ld_st_sadrr assms(2) coh_ld_st_dadrr ld_le_lim_ni le_trans)
  using ld_coh_lt_vrew_simp assms(2)
  apply (metis Load_Rules.vrnew_ld_st_sadrr coh_ld_st_dadrr le_trans)
  apply (metis assms(2) ld_coh_lt_vrew_simp)
  apply (smt (z3) assms(1) assms(2) ld_coh_noteq_last_entry_lim_fin read_pre_def reg_coh_lc valOf_def)
  apply blast       
  apply (metis reg_same_ld_dt)
  apply( simp add: split: if_split_asm)
  apply fastforce
  apply (case_tac " regs (\<tau> \<sigma>') t c1 = Suc 0 ")
  apply simp
  apply (subgoal_tac " even (regs (\<tau> \<sigma>') t DTML.loc) \<and>
\<not> writeAux \<sigma>' t \<and>
even (regs (\<tau> \<sigma>') t DTML.loc) \<and>
0 < coh (\<tau> \<sigma>') t glb \<and>
valOf (coh (\<tau> \<sigma>') t glb) glb (\<tau> \<sigma>') = regs (\<tau> \<sigma>') t DTML.loc \<and>
last_entry_lim (\<tau> \<sigma>') a (coh (\<tau> \<sigma>') t glb) \<le> vrnew (\<tau> \<sigma>') t \<and>
valOf (coh (\<tau> \<sigma>') t glb) glb (\<tau> \<sigma>') = regs (\<tau> \<sigma>') t DTML.loc")
  prefer 2
  apply (intro conjI)
  apply (metis reg_same_CAS_dr)
  apply meson
  apply (metis reg_same_CAS_dr)
  apply (metis assms(2) cas_succ_gr_z numeral_1_eq_Suc_0 numerals(1))
  apply (metis assms(2) cas_succ_valoflex_eq_v2 numeral_1_eq_Suc_0 numerals(1) reg_same_CAS_dr)
  apply (metis assms(2) cas_succ_lastentry_gr_vrnew numeral_1_eq_Suc_0 numerals(1))
  apply (metis assms(2) cas_succ_valoflex_eq_v2 numeral_1_eq_Suc_0 numerals(1) reg_same_CAS_dr)
  apply (simp add:  Ready_total_def read_pre_def)
  apply (metis One_nat_def assms(2) cas_fail_diff_lv cas_succ_lastentry_gr_vrnew cas_succ_v2_in_x cas_succ_valoflex_eq_v2 cas_succ_vnrew_eq_length numerals(1) zero_neq_one)
  apply (case_tac " regs (\<tau> \<sigma>') t c1 \<noteq> 1")
  apply simp
  apply (metis One_nat_def)
  apply (elim disjE conjE)
  apply clarify
  apply (subgoal_tac" odd (regs (\<tau> \<sigma>') t DTML.loc) \<and>
regs (\<tau> \<sigma>') t DTML.loc = lastVal glb (\<tau> \<sigma>') \<and>
writer \<sigma>' = Some t \<and>
writeAux \<sigma>' t \<and>
regs (\<tau> \<sigma>') t DTML.val = lastVal (inLoc \<sigma> t) (\<tau> \<sigma>') \<and>
(\<forall>l. [l]\<^sub>t \<tau> \<sigma>' = {lastVal l (\<tau> \<sigma>')}) \<and>
regs (\<tau> \<sigma>') t DTML.loc = regs (\<tau> \<sigma>') t r3 \<and>
pc \<sigma> syst = RecIdle \<and>
(\<forall>a. a \<in> dom (log \<sigma>) \<longrightarrow> [a]\<^sup>A\<^sub>t  \<tau> \<sigma>' = {lastVal a (\<tau> \<sigma>')})   ")
  prefer 2
  apply (intro conjI)
  apply (metis reg_same_ld_dt)
  apply (metis assms(2) lastVal_ni reg_same_ld_dt)
  apply blast
  apply blast
  apply (metis assms(2) lastVal_ni reg_same_ld_dt)
  apply (subgoal_tac "\<forall>l. [l]\<^sub>t \<tau> \<sigma>' \<noteq> {} ")
  prefer 2
  apply (metis OV_notempty_preserved assms(2) empty_iff total_wfs_def)
  apply (smt (verit) assms(2) lastVal_ni ld_ov_sub subset_singletonD)
  apply (metis ld_ov_lc reg_same_ld_dt singleton_iff)
  apply blast
  apply (metis assms(2) lastVal_ni ld_oav_ni)
  apply blast
  apply (case_tac " regs (\<tau> \<sigma>') t DTML.loc = regs (\<tau> \<sigma>') t r3 ")
  apply (subgoal_tac "(\<forall>a \<noteq> glb. read_pre (\<tau> \<sigma>') t (a ))")
  prefer 2
  apply clarify
  apply (simp add: read_pre_def)
  apply (intro conjI)
  apply (metis reg_same_ld_dt)
  apply (metis bot_nat_0.not_eq_extremum coh_ld_st_sadrr le_zero_eq read_pre_def)
  apply (metis reg_coh_lc valOf_def)
  apply (smt (z3) Load_Rules.vrnew_ld_st_sadrr assms(1) assms(10) assms(2) ld_le_lim_ni le_trans lem_lt_vrew reg_same_ld_dt)
  apply (metis Load_Rules.vrnew_ld_st_sadrr coh_ld_st_dadrr le_trans)
  apply (simp add: read_pre_def)
  apply (smt (z3) assms(1) assms(10) assms(2) cas_fail_crash ld_le_lim_ni ld_step_mem lem_same reg_same_ld_dt)
  apply (metis reg_same_ld_dt)
  apply (metis ld_ov_lc reg_same_ld_dt)
  apply( simp add: split: if_split_asm)
  apply (simp add: Ready_total_def read_pre_def)
  by metis








end

