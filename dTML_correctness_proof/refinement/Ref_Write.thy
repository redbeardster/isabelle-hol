(*Showing that the simulation relation holds for the DTML Write operation*)
theory Ref_Write
imports "../Refinement"
begin

(*auxiliary lemma*)
lemma   tr_rel_write7_self:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "tmemory as \<noteq> [] "
and "TML_Write ta  cs  cs'"
and "((pc cs) ta)  = PC.Write7"
and " Write_inv  ta  ((pc cs) ta) cs " 
and"   tr_rel   cs as ta"
and " ta \<noteq> syst"
shows " tr_rel cs' (TMWrite_trans ta  ((inLoc cs) ta)  ((inVal cs) ta) as) ta"
  using assms
  apply (simp add:TML_Write_def tr_rel_def  total_wfs_def Write_inv_def TMWrite_trans_def  tmstep_def  split: if_splits )
  apply (unfold validity_prop_def  in_flight_def)
  apply (cases "pc cs ta";  simp)
  by (metis reg_same_st)


(*auxiliary lemma*)
lemma   tr_rel_write7_stable:
assumes  "thrdsvars"
and   "\<forall>t.  tms_inv as  t "
and "total_wfs (\<tau> cs) "
and "TML_Write ta  cs  cs'"
and "((pc cs) ta)  = PC.Write7"
and " Write_inv  ta  ((pc cs) ta) cs " 
and"   tr_rel   cs as t"
and " t \<noteq>  ta"
and " ta \<noteq> syst"
shows "  tr_rel cs' (TMWrite_trans ta  ((inLoc cs) ta)  ((inVal cs) ta)  as) t"
  using assms
  apply (simp add:TML_Write_def tr_rel_def tms_inv_def  total_wfs_def Write_inv_def TMWrite_trans_def  tmstep_def  split: if_splits )
  apply (unfold validity_prop_def  in_flight_def)
  apply (cases "pc cs t";  simp)
  apply (metis  reg_same_st )
  apply (metis  reg_same_st )
  apply (metis  reg_same_st)
  apply (metis reg_same_st)
  apply (metis assms(3) reg_same_st st_lv__daddr_ni)
  apply (metis assms(3) reg_same_st st_lv__daddr_ni)
  apply (metis reg_same_st)
  apply (metis (no_types, lifting) assms(3) reg_same_st st_lv__daddr_ni)
  apply (metis (no_types, lifting) assms(3) reg_same_st st_lv__daddr_ni)
  apply (metis assms(3) reg_same_st st_lv__daddr_ni)
  apply (metis (no_types, lifting) assms(3) reg_same_st st_lv__daddr_ni)
  apply (metis assms(3) st_lv__daddr_ni)
  apply (metis reg_same_st)
  apply (metis reg_same_st)
  apply (metis assms(3) reg_same_st st_lv__daddr_ni)
  apply (metis assms(3) reg_same_st st_lv__daddr_ni)
  apply (metis assms(3) reg_same_st st_lv__daddr_ni)
  apply (metis assms(3) st_lv__daddr_ni)
  apply (metis reg_same_st)
  apply (metis reg_same_st)
  apply (metis reg_same_st)
  apply (metis reg_same_st)
  apply (metis reg_same_st)
  apply (metis reg_same_st)
  apply (metis assms(3) reg_same_st st_lv__daddr_ni)
  by (metis assms(3) reg_same_st st_lv__daddr_ni)


(*auxiliary lemma*)
lemma st_compval_daddr_ni2:
assumes " step t ( Store x v) ts ts'"
and " total_wfs ts"
and "x \<noteq> y"
shows "(\<forall> n . (0 < n \<and> n < length(memory ts' ) \<and> comploc ((memory (ts'))!n) y = y   ) \<longrightarrow> compval ( ts') (memory ( ts') ! n) y  =   compval ( ts) (memory ( ts) ! n) y   ) "
  using assms
  using st_compval_daddr_ni by blast




(*the simulation relation holds from Write7 to Write8  (non stuttering step) *)
lemma   f_sim_write_write7_lp:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "TML_Write ta  cs  cs'"
and " Write_inv  ta  ((pc cs) ta) cs " 
and "((pc cs) ta)  = PC.Write7"
and " pc cs  syst  = RecIdle \<longrightarrow> even (recoveredGlb cs ) "
and   " \<forall>  t.  (  writer cs = Some t \<longrightarrow> odd (lastVal glb  (\<tau> cs)) )"
and" f_sim  cs as "
and "tmemory as \<noteq> [] "
and   "\<forall>t.  tms_inv as  t "
and "    (\<forall> n. (0 \<le> n \<and> n  < length (memory (\<tau> cs))  \<and> comploc ((memory (\<tau> cs))!n) glb= glb) \<longrightarrow>  (valOf n glb  (\<tau> cs)) \<le> lastVal glb  (\<tau> cs) ) "
and "  (  \<forall> i   .  ( ( 0 <  i \<and>  i < length(memory (\<tau> cs)) \<and>  comploc (memory (\<tau> cs)!i) glb = glb ) \<longrightarrow> compval (\<tau> cs) (memory (\<tau> cs) ! i) glb  \<ge>   recoveredGlb cs  ) )"
and "  (  compval (\<tau> cs) (memory (\<tau> cs) ! 0) glb = survived_val (\<tau> cs) glb  \<and> (pc cs syst = RecIdle  \<longrightarrow>survived_val (\<tau> cs) glb   \<le>   recoveredGlb cs  )) "
and " ta \<noteq> syst"
shows "\<exists> as'. tmstep ta ( TMWrite   ((inLoc cs) ta)  ((inVal cs) ta)) as  as'   \<and> f_sim  cs' as'  "
  using assms
  apply (subgoal_tac " tpc as ta = TPC.WritePending")
  prefer 2
  apply (simp add: f_sim_def)
  apply (subgoal_tac "  tr_rel cs as ta ")
  prefer 2
  apply presburger
  apply (simp add: tr_rel_def)
  apply (simp add: Write_inv_def  TML_Write_def f_sim_def total_wfs_def f_sim_def tmstep_def  )
  apply (intro conjI allI)
  prefer 9
  apply (metis assms(1) assms(2) assms(3) assms(4) tr_rel_write7_self tr_rel_write7_stable)
  apply (simp add: global_rel_def )
  apply (intro impI conjI)
  apply (simp add: logical_glb_def write_count_def TMWrite_trans_def)
  apply (metis assms(2) lev_in_ov singletonD st_ov_ni total_wfs_def)
  apply (intro allI impI)
  apply (simp add: writes_def  apply_partial_def maxIndex_def TMWrite_trans_def)
  apply (intro conjI impI)
  apply (meson st_lastVal_lc)
  apply (metis st_lastVal_lc)
  apply (metis assms(2) st_lv__daddr_ni)
  apply (intro allI impI conjI)
  apply (simp add: maxIndex_def TMWrite_trans_def)
  apply (metis assms(2) domIff lev_in_ov singletonD st_ov_ni total_wfs_def)
  apply (simp add: maxIndex_def TMWrite_trans_def)
  apply (metis option.distinct(1))
  apply (simp add: TMWrite_trans_def)
  apply (simp add:  no_read_rdSet_empty_def TMWrite_trans_def)
  apply (simp add: no_write_wrSet_empty_def TMWrite_trans_def)
  apply(simp add:  write_wrSet_notEmpty_def)
  apply (unfold  TMWrite_trans_def updateSet_def)
  apply(simp add: split: if_splits)
  apply (simp add: read_rdSet_notEmpty_def   TMWrite_trans_def)
    (*new down*)
  apply (simp add:  loc_in_wrSet_def TMWrite_trans_def )
  apply (metis assms(2) st_lastVal_lc st_lv__daddr_ni)
  apply (simp add:   even_loc_wrSet_empty_def TMWrite_trans_def )
  apply (metis reg_same_st)
  apply (simp add:odd_loc_wrSet_notEmpty_def  TMWrite_trans_def )
  apply (metis reg_same_st)
    (*new up*)
    (***************************)
  apply (unfold read_prop_def)
  apply (subgoal_tac "  write_count (logical_glb cs') =  write_count (logical_glb cs) ")
  prefer 2
  apply (simp add: write_count_def  logical_glb_def)
  apply (metis assms(2) st_lv__daddr_ni)
  apply (subgoal_tac " \<forall> n . (0 \<le> n \<and> n  < length (memory (\<tau> cs'))  \<and> comploc ((memory (\<tau> cs'))!n) glb= glb ) \<longrightarrow>  comploc ((memory (\<tau> cs))!n) glb= glb ")
  prefer 2
  apply (metis assms(2) less_imp_le_nat st_comploc_daddr_ni)
  apply clarify
  apply (subgoal_tac "\<forall>n. ( 0 \<le> n \<and> n  < length (memory (\<tau> cs'))  \<and> comploc ((memory (\<tau> cs'))!n) glb= glb ) \<longrightarrow> n < length (memory (\<tau> cs))   ")
  prefer 2
  apply (metis (mono_tags, opaque_lifting) Nat.add_0_right add_Suc_right assms(6) i_noteqo_loc leD length_greater_0_conv less_eq_Suc_le linorder_neqE_nat mem_structured_def mem_structured_preserved numeral_1_eq_Suc_0 numerals(1) st_lastEntry_lc st_loc st_mem_length)

  apply (subgoal_tac "  valOf (last_entry_lim  ( \<tau> cs') l n) l ( \<tau> cs')  =    valOf (last_entry_lim  (\<tau> cs) l n) l  (\<tau> cs)   ")
  prefer 2
  apply (metis assms(2) nat_less_le st_lelim_daddr_ni)
  apply (simp(no_asm) add: split if_splits )
  apply (intro conjI)
  prefer 2
  apply blast
  by (metis less_imp_le_nat st_valOf_nle_ni)


(*********************************************)
(*auxiliary lemma*)
lemma mem_write2_ni[simp] : 
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "TML_Write ta  cs  cs'"
and " Write_inv  ta  ((pc cs) ta) cs " 
and "((pc cs) ta)  = PC.Write2"
and "((pc cs') ta)  = PC.Aborted"
shows "tmemory (TMWrite_trans ta  ((inLoc cs) ta)  ((inVal cs) ta) as) = tmemory as"
  using assms
  by (simp add: TMWrite_trans_def)



(*auxiliary lemma*)
lemma  write_count_write2_write_1[simp] : 
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "TML_Write ta cs  cs'"
and " Write_inv  ta  ((pc cs) ta) cs " 
and "((pc cs) ta)  = PC.Write2"
and "((pc cs') ta)  = PC.Write3"
and"pc cs  syst  = RecIdle "
and " pc cs  syst  = RecIdle \<longrightarrow> even (recoveredGlb cs ) "
and   " \<forall>  t.  (  writer cs = Some t \<longrightarrow> odd (lastVal glb  (\<tau> cs)) )"
and " ta \<noteq> syst"
and "pc cs  syst  = RecIdle  \<longrightarrow> ( lastVal glb (\<tau> cs)  \<ge>recoveredGlb cs ) "
shows "write_count (logical_glb cs') = write_count (logical_glb cs) "
  using assms
  apply (simp add: TML_Write_def Write_inv_def total_wfs_def  split: if_splits)
  apply (subgoal_tac " writer cs = None  ")
  prefer 2
  apply (metis Zero_not_Suc assms(9) cas_nlv_lc gr0_implies_Suc lastVal_def not_Some_eq)
  apply (subgoal_tac " logical_glb cs = (lastVal glb (\<tau> cs) - recoveredGlb cs) ")
  prefer 2
  apply (simp add: logical_glb_def)
  apply (subgoal_tac " lastVal glb (\<tau> cs)  = regs (\<tau> cs) ta DTML.loc")
  prefer 2
  using cas_fail_diff_lv gr_implies_not_zero apply blast
  apply (subgoal_tac " logical_glb cs' = (lastVal glb (\<tau> cs') - recoveredGlb cs') ")
  prefer 2
  apply (simp add: logical_glb_def)
  apply (subgoal_tac " regs (\<tau> cs') ta DTML.loc + 1 =lastVal glb (\<tau> cs') ")
  prefer 2
  using  reg_same_CAS_dr  lastVal_def  cas_lc 
  apply (metis Suc_eq_plus1 less_numeral_extra(3))
  apply (simp add: write_count_def)
  apply (subgoal_tac " (regs (\<tau> cs') ta DTML.loc)  = (regs (\<tau> cs) ta DTML.loc)  ")
  prefer 2
  using reg_same_CAS_dr apply presburger
  by (metis Suc_diff_le dvd_diff_nat even_Suc_div_two)


(*auxiliary lemma*)
lemma  write_count_write2_write_2[simp] : 
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "TML_Write ta  cs  cs'"
and " Write_inv  ta  ((pc cs) ta) cs " 
and "((pc cs) ta)  = PC.Write2"
and "((pc cs') ta)  = PC.Write3"
and"pc cs  syst  = RecIdle "
and " pc cs  syst  = RecIdle \<longrightarrow> even (recoveredGlb cs ) "
and   " \<forall>  t.  (  writer cs = Some t \<longrightarrow> odd (lastVal glb  (\<tau> cs)) )"
and "pc cs  syst  = RecIdle  \<longrightarrow> ( lastVal glb (\<tau> cs)  \<ge>recoveredGlb cs ) "
and " ta \<noteq> syst"
shows "write_count (logical_glb cs') = write_count ((regs (\<tau> cs') ta DTML.loc - recoveredGlb cs')) "
  using assms
  apply (simp add: TML_Write_def Write_inv_def total_wfs_def  split: if_splits)
  apply (subgoal_tac " lastVal glb (\<tau> cs)  = regs (\<tau> cs) ta DTML.loc")
  prefer 2
  using cas_fail_diff_lv gr_implies_not_zero apply blast
  apply (subgoal_tac " logical_glb cs' = (lastVal glb (\<tau> cs') - recoveredGlb cs') ")
  prefer 2
  apply (simp add: logical_glb_def)
  apply (subgoal_tac " regs (\<tau> cs') ta DTML.loc + 1 =lastVal glb (\<tau> cs') ")
  prefer 2
  using  reg_same_CAS_dr  lastVal_def  cas_lc 
  apply (metis Suc_eq_plus1 less_numeral_extra(3))
  apply (simp add: write_count_def)
  apply (subgoal_tac "odd ( Suc (regs (\<tau> cs') ta DTML.loc))")
  prefer 2
  apply (metis even_Suc reg_same_CAS_dr)
  apply (subgoal_tac "even( recoveredGlb cs')" )
  prefer 2
  using thrdsvars_def  
  apply meson
  by (metis Suc_diff_le diff_is_0_eq' dvd_diff_nat even_Suc even_Suc_div_two nat_le_linear not_less_eq_eq)

(*auxiliary lemma*)
lemma writes_write2_ni[simp] : 
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "TML_Write ta  cs  cs'"
and " Write_inv  ta  ((pc cs) ta) cs " 
and "((pc cs) ta)  = PC.Write2"
and "((pc cs') ta)  = PC.Aborted"
shows " (writes cs'  ( TMAbort_trans  ta  as)  ) =  (writes cs as) "
  using assms
  apply (simp add: TML_Write_def writes_def TMAbort_trans_def  Write_inv_def)
  apply(case_tac "writer cs' ")
  apply (smt (verit, ccfv_threshold) option.discI option.simps(4))
  by(simp add: split: if_splits)


(*auxiliary lemma*)
lemma   tr_rel_write2_write3_self:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "TML_Write ta  cs  cs'"
and "((pc cs) ta)  = PC.Write2"
and "((pc cs') ta)  = PC.Write3"
and " Write_inv  ta  ((pc cs) ta) cs " 
and"   tr_rel   cs as ta"
and " ta \<noteq> syst"
and " f_sim  cs  as"
and   "\<forall>t.  tms_inv as  t "
and"pc cs  syst  = RecIdle "
and " pc cs  syst  = RecIdle \<longrightarrow> even (recoveredGlb cs ) "
and   " \<forall>  t.  (  writer cs = Some t \<longrightarrow> odd (lastVal glb  (\<tau> cs)) )"
and "pc cs  syst  = RecIdle  \<longrightarrow> ( lastVal glb (\<tau> cs)  \<ge>recoveredGlb cs ) "
shows "   tr_rel   cs' as ta  "
  using assms
  apply (simp add:TML_Write_def tr_rel_def  tms_inv_def  in_flight_def validity_prop_def total_wfs_def Write_inv_def  split: if_splits )
  apply (cases "pc cs ta";  simp)
  apply (intro conjI)
  apply (smt (z3) cas_fail_diff_lv less_numeral_extra(3) reg_same_CAS_dr)
  apply (metis cas_fail_diff_lv less_numeral_extra(3) reg_same_CAS_dr)
  by (metis cas_fail_diff_lv less_numeral_extra(3) )


(*auxiliary lemma*)
lemma    tr_rel_write2_write3_stable:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "TML_Write ta  cs  cs'"
and "((pc cs) ta)  = PC.Write2"
and "((pc cs') ta)  = PC.Write3"
and " Write_inv  ta  ((pc cs) ta) cs " 
and " t \<noteq> ta "
and"   tr_rel   cs as t"
and " f_sim  cs  as"
and   "\<forall>t.  tms_inv as  t "
and"pc cs  syst  = RecIdle "
and " pc cs  syst  = RecIdle \<longrightarrow> even (recoveredGlb cs ) "
and   " \<forall>  t.  (  writer cs = Some t \<longrightarrow> odd (lastVal glb  (\<tau> cs)) )"
and  " pc cs syst  = RecIdle \<longrightarrow> (\<forall>t.  ( t \<noteq> syst  \<and> ((pc cs) t \<notin> {PC.NotStarted,PC.BeginPending, PC.Committed,PC.Begin2 ,PC.Aborted  }) \<longrightarrow>   regs (\<tau> cs) t loc \<le> lastVal glb  (\<tau> cs) ))"
and "pc cs  syst  = RecIdle  \<longrightarrow> ( lastVal glb (\<tau> cs)  \<ge>recoveredGlb cs ) " 
and " ta \<noteq> syst"
shows "   tr_rel   cs' as t  "
  using assms
  apply (simp add:TML_Write_def tr_rel_def in_flight_def validity_prop_def total_wfs_def Write_inv_def  split: if_splits )
  apply (cases "pc cs t";  simp)
  apply (unfold in_flight_def validity_prop_def)
  apply (metis reg_same_CAS_dt)
  apply (metis reg_same_CAS_dt)
  apply (metis reg_same_CAS_dt)
  apply (metis reg_same_CAS_dt)
  apply (intro conjI )
  apply (subgoal_tac "regs (\<tau> cs') t DTML.loc = regs (\<tau> cs) t DTML.loc ")
  prefer 2
  using reg_same_CAS_dt apply presburger
  apply (metis Suc_eq_plus1 cas_lc dvd_add_right_iff lastVal_def odd_one zero_less_iff_neq_zero)
  apply (metis reg_same_CAS_dt)
  apply (metis reg_same_CAS_dt)
  apply (metis Suc_eq_plus1 cas_lc dvd_add_right_iff lastVal_def odd_one reg_same_CAS_dt zero_less_iff_neq_zero)
  apply (metis reg_same_CAS_dt)
  apply (metis reg_same_CAS_dt)
  apply (metis Suc_eq_plus1 cas_lc dvd_add_right_iff lastVal_def odd_one reg_same_CAS_dt zero_less_iff_neq_zero)
  apply (metis Suc_eq_plus1 cas_lc dvd_add_right_iff lastVal_def odd_one reg_same_CAS_dt zero_less_iff_neq_zero)
  apply (metis Suc_eq_plus1 cas_lc dvd_add_right_iff lastVal_def odd_one reg_same_CAS_dt zero_less_iff_neq_zero)
  apply (metis Zero_not_Suc cas_lc even_Suc lastVal_def less_imp_Suc_add)
  apply (metis reg_same_CAS_dt)
  apply (metis reg_same_CAS_dt)
  apply (metis Suc_eq_plus1 cas_lc dvd_add_right_iff lastVal_def odd_one reg_same_CAS_dt zero_less_iff_neq_zero)
  apply (metis Suc_eq_plus1 cas_lc dvd_add_right_iff lastVal_def odd_one reg_same_CAS_dt zero_less_iff_neq_zero)
  by (metis Suc_eq_plus1 cas_lc dvd_add_right_iff lastVal_def odd_one reg_same_CAS_dt zero_less_iff_neq_zero)+


(*auxiliary lemma*)
lemma    tr_rel_write2_write3_global:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "TML_Write ta  cs  cs'"
and "((pc cs) ta)  = PC.Write2"
and "((pc cs') ta)  = PC.Write3"
and " Write_inv  ta  ((pc cs) ta) cs " 
and"  \<forall> t. tr_rel   cs as t"
and " f_sim  cs  as"
and   "\<forall>t.  tms_inv as  t "
and"pc cs  syst  = RecIdle "
and " pc cs  syst  = RecIdle \<longrightarrow> even (recoveredGlb cs ) "
and   " \<forall>  t.  (  writer cs = Some t \<longrightarrow> odd (lastVal glb  (\<tau> cs)) )"
and  " pc cs  syst  = RecIdle \<longrightarrow> (\<forall>t.  (t \<noteq> syst  \<and> ((pc cs) t \<notin> {PC.NotStarted,PC.BeginPending,PC.Committed,PC.Begin2  ,PC.Aborted   }) \<longrightarrow>   regs (\<tau> cs) t loc \<le> lastVal glb  (\<tau> cs) ))"
and "pc cs  syst  = RecIdle  \<longrightarrow> ( lastVal glb (\<tau> cs)  \<ge>recoveredGlb cs ) " 
and " ta \<noteq> syst"
shows " \<forall>t.  tr_rel   cs' as t  "
  using assms
  apply clarify
  apply (case_tac " ta = t")
  using  tr_rel_write2_write3_self[where cs= cs and as= as and cs' = cs' ]
  apply blast
  using assms  tr_rel_write2_write3_stable[where cs= cs and as= as and cs' = cs' ]
  by presburger


(*auxiliary lemma*)
lemma   global_rel_write_write2_write3_stuttering:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "TML_Write ta  cs  cs'"
and "((pc cs) ta)  = PC.Write2"
and "((pc cs') ta)  = PC.Write3"
and " Write_inv  ta  ((pc cs) ta) cs " 
and " f_sim  cs  as"
and   "\<forall>t.  tms_inv as  t "
and"pc cs  syst  = RecIdle "
and " pc cs  syst  = RecIdle \<longrightarrow> even (recoveredGlb cs ) "
and   " \<forall>  t.  (  writer cs = Some t \<longrightarrow> odd (lastVal glb  (\<tau> cs)) )"
and  " pc cs  syst  = RecIdle \<longrightarrow> (\<forall>t.  (t \<noteq> syst  \<and> ((pc cs) t \<notin> {PC.NotStarted ,PC.BeginPending, PC.Committed,PC.Begin2  ,PC.Aborted   }) \<longrightarrow>   regs (\<tau> cs) t loc \<le> lastVal glb  (\<tau> cs) ))"
and "pc cs  syst  = RecIdle  \<longrightarrow> ( lastVal glb (\<tau> cs)  \<ge>recoveredGlb cs ) " 
and " ta \<noteq> syst"
shows " global_rel  cs' as  "
  using assms
  apply (simp add: Write_inv_def tmstep_def TML_Write_def split:if_splits)
  apply (simp add:  f_sim_def)
  apply (simp add: global_rel_def)
  apply (intro conjI impI)
  apply (subgoal_tac " write_count (logical_glb cs')   = write_count (logical_glb cs)  ")
  prefer 2
  apply (subgoal_tac " even ( lastVal glb (\<tau> cs) )")
  prefer 2
  using total_wfs_def
  apply (metis cas_fail_diff_lv not_gr_zero)
  apply (simp add: step_def)
  apply clarify
  apply (subgoal_tac "    \<tau> cs' =
cas_succ_trans ta ind glb (regs (\<tau> cs) ta DTML.loc)
(Suc (regs (\<tau> cs) ta DTML.loc)) c1  nv mnv (\<tau> cs)")
  prefer 2
  using total_wfs_def  
  using cas_fail_reg neq0_conv apply blast
  apply (subgoal_tac " odd ( lastVal glb (\<tau> cs') )")
  prefer 2
  using total_wfs_def 
  apply (metis cas_suc_compval cas_suc_mem_l cas_succ_lastentry even_Suc lastVal_def)
  apply (subgoal_tac " lastVal glb (\<tau> cs') = ( lastVal glb (\<tau> cs) +1 ) ")
  prefer 2
  using total_wfs_def  apply (simp(no_asm) add:  cas_succ_trans_def)
  apply (metis cas_fail_reg cas_suc_compval cas_suc_mem_l cas_succ_lastentry compval_def lastVal_def not_gr_zero)
  apply (subgoal_tac "  write_count( logical_glb cs) = write_count( logical_glb cs')   ")
  prefer 2
  apply (simp add: logical_glb_def write_count_def)
  apply (metis Suc_diff_le dvd_diff_nat even_Suc_div_two)
  apply metis
  apply presburger
  apply (subgoal_tac " writes cs as = Map.empty")
  prefer 2
  apply (simp add: writes_def)
  apply (subgoal_tac " writer cs = None ")
  prefer 2
  apply (subgoal_tac "even (lastVal glb  (\<tau> cs))  ")
  prefer 2
  apply (simp add: total_wfs_def  )
  apply (metis cas_fail_diff_lv gr_implies_not_zero)
  apply (meson option.exhaust)
  apply (metis option.case_eq_if)
  apply (simp add: writes_def)
  apply (subgoal_tac "wrSet as ta = Map.empty ")
  prefer 2
  apply (simp add: tr_rel_def)
  apply (subgoal_tac " even (regs (\<tau> cs) ta DTML.loc)")  
  prefer 2
  apply blast
  apply (subgoal_tac "   regs (\<tau> cs) ta DTML.loc = lastVal glb (\<tau> cs)")
  prefer 2
  apply (simp add: total_wfs_def)
  apply (metis cas_fail_diff_lv gr_implies_not_zero)
  apply (smt (z3) PC.simps(1661))

  apply clarify
  apply (subgoal_tac " lastVal l (\<tau> cs') =  lastVal l (\<tau> cs) ")
  prefer 2
  apply (simp add: total_wfs_def)
  apply (metis (no_types, lifting) cas_le_daddr)
  apply (metis apply_partial_def)
  apply (intro allI conjI impI)
  apply (subgoal_tac " writes cs as = Map.empty")
  prefer 2
  apply (simp add: writes_def)
  apply (subgoal_tac " writer cs = None ")
  prefer 2
  apply (subgoal_tac "even (lastVal glb  (\<tau> cs))  ")
  prefer 2
  apply (simp add: total_wfs_def  )
  apply (metis cas_fail_diff_lv gr_implies_not_zero)
  apply (meson option.exhaust)
  apply (metis option.case_eq_if)
  apply (simp add: writes_def)
  apply (subgoal_tac " lastVal l (\<tau> cs') =  lastVal l (\<tau> cs) ")
  prefer 2
  apply (simp add: total_wfs_def)
  apply (metis (no_types, lifting) cas_le_daddr)
  apply presburger
  by (metis option.discI)





(*the simulation relation holds from Write2 to Write3  (stuttering step) *)
lemma   f_sim_write_write2_write3_stuttering:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "TML_Write ta  cs  cs'"
and "((pc cs) ta)  = PC.Write2"
and "((pc cs') ta)  = PC.Write3"
and " Write_inv  ta  ((pc cs) ta) cs " 
and " f_sim  cs  as"
and   "\<forall>t.  tms_inv as  t "
and"pc cs  syst  = RecIdle "
and " pc cs  syst  = RecIdle \<longrightarrow> even (recoveredGlb cs ) "
and   " \<forall>  t.  (  writer cs = Some t \<longrightarrow> odd (lastVal glb  (\<tau> cs)) )"
and  " pc cs  syst  = RecIdle \<longrightarrow> (\<forall>t.  (t \<noteq> syst  \<and> ((pc cs) t \<notin> {PC.NotStarted ,PC.BeginPending, PC.Committed,PC.Begin2 ,PC.Aborted    }) \<longrightarrow>   regs (\<tau> cs) t loc \<le> lastVal glb  (\<tau> cs) ))"
and "pc cs  syst  = RecIdle  \<longrightarrow> ( lastVal glb (\<tau> cs)  \<ge>recoveredGlb cs ) " 
and " ta \<noteq> syst"
shows " f_sim  cs' as  "
  using assms
  apply (subgoal_tac " \<forall> t.  tr_rel cs' as t ")
  prefer 2
  apply (subgoal_tac "  \<forall> t.  tr_rel cs as t  ")
  prefer 2
  apply (simp add: f_sim_def)
  using  tr_rel_write2_write3_global[where cs= cs and as= as and cs' = cs' ]
  apply blast
  apply (simp add: Write_inv_def tmstep_def TML_Write_def split:if_splits)
  apply (simp add:  f_sim_def)
  apply (intro conjI)
  using global_rel_write_write2_write3_stuttering [where cs = cs  and as = as and cs' = cs']
  using assms(1) assms(12) assms(3) assms(5) assms(6) assms(7) apply presburger
  apply (intro conjI allI)
  apply (simp add:no_read_rdSet_empty_def)
  apply(simp add:no_write_wrSet_empty_def)
  apply (simp add: write_wrSet_notEmpty_def)
  apply (simp add: read_rdSet_notEmpty_def)
    (*new down*)
  apply (simp add:  loc_in_wrSet_def TMWrite_trans_def )
  using  even_loc_wrSet_empty_def
  apply (metis PC.distinct(1259) PC.distinct(39) PC.distinct(729) domD emptyE insertE option.discI tNotCrashed_def)
  apply (simp add:  even_loc_wrSet_empty_def)
  apply (smt (z3) reg_same_CAS_dt)
  apply (simp add:odd_loc_wrSet_notEmpty_def  TMWrite_trans_def )
  apply (smt (verit) reg_same_CAS_dt) 

  apply (unfold read_prop_def total_wfs_def)

  apply (subgoal_tac " regs (\<tau> cs') ta c1 = 1")
  prefer 2
  apply (metis Nat.lessE Zero_not_Suc cas_lc)

  apply (subgoal_tac " length (memory (\<tau> cs') ) = length (memory (\<tau> cs)) + 1 ")
  prefer 2
  using mem_length_cas_succ_step 
  apply metis
  apply (subgoal_tac " \<forall>i. 0 \<le> i \<and> i < length (memory (\<tau> cs) ) \<longrightarrow> (memory (\<tau> cs'))!i = (memory (\<tau> cs))!i ")
  prefer 2
  apply (metis mem_l_cas_succ_step)
  apply (intro allI  impI)
  apply (case_tac "  n < length (memory (\<tau> cs)) ")
  apply (metis cas_succ_lelim_nle_ni cas_succ_valOf_nle_ni le0)
  apply (case_tac "  n = length (memory (\<tau> cs)) ")
  apply (subgoal_tac " valOf   (last_entry_lim (\<tau> cs') l (length (memory (\<tau> cs))) ) l (\<tau> cs')    =  lastVal l (\<tau> cs')")
  prefer 2
  apply (metis cas_succ_lv_lim_eq_lv_val)
    (*  apply (simp add: global_rel_def)*)
    (* apply (simp add: logical_glb_def )*)
  apply (subgoal_tac " writer cs = None ")
  prefer 2
  apply (metis One_nat_def cas_fail_diff_lv option.collapse zero_neq_one)


  apply (subgoal_tac "  (valOf (length (memory (\<tau> cs))) glb (\<tau> cs')   = lastVal glb (\<tau> cs') ) ")
  prefer 2
  apply (subgoal_tac " regs (\<tau> cs') ta DTML.loc + 1 =lastVal glb (\<tau> cs') ")
  prefer 2
  using  reg_same_CAS_dr  lastVal_def  cas_lc 
  apply (metis One_nat_def Suc_eq_plus1 cas_succ_lv_lc)
  apply (simp add: valOf_def lastVal_def)
  apply (subgoal_tac "  last_entry (\<tau> cs') glb =  length (memory (\<tau> cs)) ")
  prefer 2
  apply (simp add: step_def)
  apply (metis One_nat_def cas_fail_reg cas_suc_mem_l cas_succ_lastentry zero_neq_one)
  apply presburger

  apply (subgoal_tac "  write_count (logical_glb cs') =  write_count (logical_glb cs) ")
  prefer 2
  apply (metis assms(1) assms(11) assms(13) assms(2) assms(3) assms(4) assms(5) assms(6) assms(9) write_count_write2_write_1)
    (*  apply (unfold logical_glb_def)*)

  apply (subgoal_tac " logical_glb cs' = (lastVal glb (\<tau> cs') - recoveredGlb cs') ")
  prefer 2
  apply (simp add: logical_glb_def)

  apply (subgoal_tac "   write_count
(valOf (length (memory (\<tau> cs))) glb (\<tau> cs') - recoveredGlb cs') = write_count(  logical_glb cs') ")
  prefer 2
  apply presburger
  apply (subgoal_tac " global_rel cs'  as")
  prefer 2
  using global_rel_write_write2_write3_stuttering [where cs = cs  and as = as and cs' = cs']
  apply (metis assms(1) assms(12) assms(2) assms(3) assms(5) assms(6) assms(7))
  apply (simp add: global_rel_def)
  apply (subgoal_tac " writes cs' as = writes cs as ")
  prefer 2
  apply (simp add: writes_def)
  apply (simp add: tr_rel_def)
  apply (smt (z3) One_nat_def PC.simps(1661) assms(2) cas_succ_eq)

  apply (subgoal_tac " (writes cs' as) = Map.empty " )
  prefer 2
  apply (simp add: writes_def)
  apply (unfold  maxIndex_def)
  apply (simp add: apply_partial_def)
  apply (metis option.distinct(1) option.simps(4))
  by (metis Suc_diff_1 diff_add_inverse2 less_SucE trans_less_add2)

(*******************************************************)



(*auxiliary lemma*)
lemma   tr_rel_write2_abort_self:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "TML_Write ta  cs  cs'"
and "((pc cs) ta)  = PC.Write2"
and "((pc cs') ta)  = PC.Aborted"
and " Write_inv  ta  ((pc cs) ta) cs " 
and"   tr_rel   cs as ta"
shows "  tr_rel cs'  ( TMAbort_trans  ta  as)  ta"
  using assms
  by  (simp add:TML_Write_def tr_rel_def TMAbort_trans_def   split: if_splits )


(*auxiliary lemma*)
lemma    tr_rel_write2_abort_stable:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "TML_Write ta  cs  cs'"
and "((pc cs) ta)  = PC.Write2"
and "((pc cs') ta)  = PC.Aborted"
and " Write_inv  ta  ((pc cs) ta) cs " 
and " t \<noteq> ta "
and"   tr_rel   cs as t"
and " ta \<noteq> syst"
shows "  tr_rel cs'  ( TMAbort_trans  ta  as)  t"
  using assms
  apply (simp add:TML_Write_def TMAbort_trans_def  tr_rel_def in_flight_def validity_prop_def total_wfs_def Write_inv_def  split: if_splits )
  apply (unfold  in_flight_def validity_prop_def) 
  apply (cases "pc cs t";  simp)
  apply (metis  reg_same_CAS_dt)
  apply (metis  reg_same_CAS_dt)
  apply (metis  reg_same_CAS_dt)
  apply (metis reg_same_CAS_dt)
  apply (smt (verit) assms(2) cas_fail_lastVal_same reg_same_CAS_dt)
  apply (smt (verit) assms(2) cas_fail_lastVal_same reg_same_CAS_dt)
  apply (metis reg_same_CAS_dt)
  apply (smt (z3) assms(2) cas_fail_lastVal_same reg_same_CAS_dt)
  apply (smt (z3) assms(2) cas_fail_lastVal_same reg_same_CAS_dt)
  apply (metis (no_types, lifting) assms(2) cas_fail_lastVal_same reg_same_CAS_dt)
  apply (smt (verit) assms(2) cas_fail_lastVal_same reg_same_CAS_dt)
  apply (metis assms(2) cas_fail_lastVal_same reg_same_CAS_dt)
  apply (metis cas_possible_lv_lc even_Suc lastVal_def reg_same_CAS_dt)
  apply (metis reg_same_CAS_dt)
  apply (metis assms(2) cas_fail_lastVal_same reg_same_CAS_dt)
  apply (smt (verit) assms(2) assms(7) cas_fail_lastVal_same reg_same_CAS_dt)
  apply (smt (verit) assms(2) cas_fail_lastVal_same reg_same_CAS_dt)
  apply (smt (verit) assms(2) cas_fail_lastVal_same reg_same_CAS_dt)
  apply (metis reg_same_CAS_dt)
  apply (metis reg_same_CAS_dt)
  apply (metis reg_same_CAS_dt )
  apply (metis reg_same_CAS_dt )
  apply (metis reg_same_CAS_dt)
  apply (metis reg_same_CAS_dt)
  apply (smt (verit) assms(2) cas_fail_lastVal_same reg_same_CAS_dt)
  by (smt (verit) assms(2) cas_fail_lastVal_same reg_same_CAS_dt)




(*the simulation relation holds from Write2 to Aborted (non stuttering step) *)
lemma   f_sim_write_write2_abort_lp:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "TML_Write ta  cs  cs'"
and " Write_inv  ta  ((pc cs) ta) cs " 
and "((pc cs) ta)  = PC.Write2"
and "((pc cs') ta)  = PC.Aborted"
and" f_sim  cs as "
and " ta \<noteq> syst"
shows "  \<exists> as'. tmstep ta  TMAbort  as  as'  \<and> f_sim  cs' as' "
  using assms
  apply (simp add: Write_inv_def  tmstep_def  tmstep_def TML_Write_def TMAbort_trans_def split:if_splits)
  apply (simp add:  f_sim_def)
  apply (subgoal_tac "  tpc as ta = TPC.WritePending ")
  prefer 2
  apply (simp add: tr_rel_def)
  apply (smt (z3) PC.simps(1661))
  apply (intro conjI)
  apply (simp add: global_rel_def)
  apply (intro conjI impI)
  apply (subgoal_tac " logical_glb cs' = logical_glb cs ")
  prefer 2
  apply (simp add: logical_glb_def)
  apply (subgoal_tac " lastVal glb (\<tau> cs') = lastVal glb (\<tau> cs) ")
  prefer 2
  apply (metis cas_fail_lastVal_same)
  apply (subgoal_tac " recoveredGlb cs' = recoveredGlb cs ")
  prefer 2
  apply presburger
  apply (cases "writer cs'")
  apply (smt (z3) PC.distinct(271) PC.distinct(305) assms(6) fun_upd_other option.case_eq_if)
  apply (simp add: split if_splits)
  apply presburger
  apply clarify
  apply (subgoal_tac " lastVal l (\<tau> cs') = lastVal l (\<tau> cs) ")
  prefer 2
  using total_wfs_def
  apply (metis cas_fail_lastVal_same cas_le_daddr)
  apply (subgoal_tac "  (writes cs'  ( TMAbort_trans  ta  as)  ) =  (writes cs as)  ")
  prefer 2
  apply (meson assms(1) assms(3) assms(4) assms(6) writes_write2_ni)
  apply (simp add: TMAbort_trans_def maxIndex_def  apply_partial_def)
  apply (simp add: TMAbort_trans_def maxIndex_def  apply_partial_def)
  apply (intro conjI allI)
  using total_wfs_def cas_fail_lastVal_same cas_le_daddr  apply metis
  using total_wfs_def cas_fail_lastVal_same cas_le_daddr apply metis
  apply (intro allI conjI)
  apply (simp add: no_read_rdSet_empty_def )
  apply (simp add:  no_write_wrSet_empty_def)
  apply (simp add: write_wrSet_notEmpty_def)
  apply (simp add: read_rdSet_notEmpty_def)
    (*new down*)
  apply (simp add:  loc_in_wrSet_def  )
  apply (unfold total_wfs_def)
  apply (metis assms(2) cas_fail_lastVal_same cas_le_daddr)
  apply (simp add:  even_loc_wrSet_empty_def)
  apply (metis reg_same_CAS_dt)
  apply (simp add:odd_loc_wrSet_notEmpty_def  TMWrite_trans_def )
  apply (smt (verit) reg_same_CAS_dt)
    (*new up*)
  apply (case_tac " ta = t ")
  apply simp
  apply (subgoal_tac " as\<lparr>tpc := (tpc as)(t := TPC.Aborted)\<rparr> = TMAbort_trans  ta  as ")
  prefer 2
  apply (simp add:  TMAbort_trans_def) 
  using assms(1) assms(2) assms(3) assms(4) assms(6) tr_rel_write2_abort_self apply presburger

  apply (subgoal_tac " as\<lparr>tpc := (tpc as)(ta := TPC.Aborted)\<rparr> = TMAbort_trans  ta  as ")
  prefer 2
  apply (simp add:  TMAbort_trans_def)
  using assms(1) assms(2) assms(3) assms(4) assms(6) tr_rel_write2_abort_stable apply presburger
  apply (unfold read_prop_def)
  apply clarify
  apply (subgoal_tac "    valOf (last_entry_lim (\<tau> cs') l n) l (\<tau> cs') =    valOf (last_entry_lim (\<tau> cs) l n) l (\<tau> cs) ")
  prefer 2
  using cas_succ_lelim_daddr_ni 
  apply (metis nat_less_le)
  apply (subgoal_tac  " memory (\<tau> cs) = memory (\<tau> cs') ")
  prefer 2
  using cas_fail_mem_same   apply meson
  apply (subgoal_tac " valOf n glb (\<tau> cs')  = valOf n glb (\<tau> cs)  ")
  prefer 2
  apply (simp(no_asm) add: valOf_def)
  apply (metis survived_val_preserved_cas)
  apply (simp add: write_count_def)
  using TPC.distinct(15) apply presburger
  using TPC.distinct(53) apply presburger
  using TPC.distinct(35) apply presburger
  using TPC.distinct(125) apply presburger
  using TPC.distinct(69) by presburger


(******************************************************)


(*auxiliary lemma*)
lemma   tr_rel_write3_self:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "TML_Write ta  cs  cs'"
and "((pc cs) ta)  = PC.Write3"
and "((pc cs') ta)  = PC.Write4"
and " Write_inv  ta  ((pc cs) ta) cs " 
and"   tr_rel   cs as ta"
and"pc cs  syst  = RecIdle "
and " pc cs  syst  = RecIdle \<longrightarrow> even (recoveredGlb cs ) "
and "pc cs  syst  = RecIdle  \<longrightarrow> ( lastVal glb (\<tau> cs)  \<ge>recoveredGlb cs ) " 
shows "   tr_rel   cs' as ta  "
  using assms
  apply(simp add:TML_Write_def tr_rel_def  in_flight_def validity_prop_def total_wfs_def Write_inv_def  split: if_splits )
  apply (intro conjI)

  apply (subgoal_tac "  write_count (regs (\<tau> cs') ta DTML.loc - recoveredGlb cs') =  write_count (regs (\<tau> cs) ta DTML.loc - recoveredGlb cs') ")
  prefer 2
  apply (subgoal_tac " regs (\<tau> cs') ta DTML.loc  = regs (\<tau> cs) ta DTML.loc +1 ")
  prefer 2
  apply (metis Suc_eq_plus1 reg_write_lc)
  apply (subgoal_tac " even(  regs (\<tau> cs) ta DTML.loc )")
  prefer 2
  apply blast
  apply (unfold  write_count_def)
  apply (metis Nat.add_diff_assoc2 dvd_diff_nat even_Suc even_succ_div_two le_SucE)
  apply presburger
  by (metis Suc_diff_le dvd_diff_nat even_Suc even_Suc_div_two le_Suc_eq reg_write_lc)


(*auxiliary lemma*)
lemma   tr_rel_write3_stable:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "TML_Write ta  cs  cs'"
and "((pc cs) ta)  = PC.Write3"
and "((pc cs') ta)  = PC.Write4"
and " Write_inv  ta  ((pc cs) ta) cs " 
and "t \<noteq> ta"
and"   tr_rel   cs as t"
and " ta \<noteq> syst"
shows "   tr_rel   cs' as t  "
  using assms
  apply(simp add:TML_Write_def tr_rel_def  in_flight_def validity_prop_def total_wfs_def Write_inv_def  split: if_splits )
  apply (cases  "pc cs t"; simp )
  apply (unfold  in_flight_def validity_prop_def)
  apply (metis assms(7) reg_dt_ni )
  apply (metis reg_dt_ni )
  apply (metis reg_dt_ni )
  apply (metis reg_dt_ni)
  by (metis reg_dt_ni reg_write_lastVal_ni)+


(*the simulation relation holds from Write3 to Write4  (stuttering step) *)
lemma   f_sim_write_write3:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "TML_Write ta cs  cs'"
and " Write_inv  ta  ((pc cs) ta) cs " 
and "((pc cs) ta)  = PC.Write3"
and " a \<noteq> glb"
and" f_sim  cs as "
and"pc cs  syst  = RecIdle "
and " pc cs  syst  = RecIdle \<longrightarrow> even (recoveredGlb cs ) "
and "pc cs  syst  = RecIdle  \<longrightarrow> ( lastVal glb (\<tau> cs)  \<ge>recoveredGlb cs ) " 
and " ta \<noteq> syst"
shows " f_sim  cs' as  "
  using assms
  apply (simp add: Write_inv_def tmstep_def TML_Write_def f_sim_def total_wfs_def)
  apply (intro conjI)
  apply (simp add: global_rel_def)
  apply (intro impI conjI)
  apply (simp add:  write_count_def logical_glb_def)
  using reg_write_lastVal_ni apply presburger
  apply (intro allI impI)
  apply (simp add: writes_def)
  using reg_write_lastVal_ni apply presburger
  using reg_write_lastVal_ni apply presburger
  apply (intro conjI allI)
  apply (simp add: no_read_rdSet_empty_def )
  apply (simp add:  no_write_wrSet_empty_def)
  apply (simp add:  write_wrSet_notEmpty_def)
  apply (simp add: read_rdSet_notEmpty_def)
  apply (simp add:  loc_in_wrSet_def  )
  apply (metis reg_write_lastVal_ni)
  apply (simp add:  even_loc_wrSet_empty_def)
  using reg_dt_ni apply presburger
  apply (simp add:odd_loc_wrSet_notEmpty_def  TMWrite_trans_def )
  using reg_dt_ni apply presburger
  apply (metis assms(1) assms(2) assms(3) assms(4) fun_upd_same tr_rel_write3_self tr_rel_write3_stable)
  apply (unfold read_prop_def)
  using less_or_eq_imp_le reg_write_mem upreg_lelim_nle_ni upreg_valOf_nle_ni by presburger


(****************************************************)

(*auxiliary lemma*)
lemma   tr_rel_write4_self:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "TML_Write ta  cs  cs'"
and "((pc cs) ta)  = PC.Write4"
and " Write_inv  ta  ((pc cs) ta) cs " 
and"   tr_rel   cs as ta"
shows "   tr_rel   cs' as ta  "
  using assms
  by(simp add:TML_Write_def tr_rel_def  in_flight_def validity_prop_def total_wfs_def Write_inv_def  split: if_splits )


(*auxiliary lemma*)
lemma   tr_rel_write4_stable:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "TML_Write ta  cs  cs'"
and "((pc cs) ta)  = PC.Write4"
and " Write_inv  ta  ((pc cs) ta) cs " 
and"   tr_rel   cs as t"
and " t \<noteq> ta "
and " ta \<noteq> syst"
shows "   tr_rel   cs' as t "
  using assms
  apply(simp add:TML_Write_def tr_rel_def  in_flight_def validity_prop_def total_wfs_def Write_inv_def  split: if_splits )
  apply (unfold  in_flight_def validity_prop_def)
  apply (cases "pc cs t"; simp)
  by  metis


(*the simulation relation holds from Write4 to Write5  (stuttering step) *)
lemma   f_sim_write_write4:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "TML_Write ta  cs  cs'"
and " Write_inv  ta ((pc cs) ta) cs " 
and "((pc cs) ta)  = PC.Write4"
and " a \<noteq> glb"
and " pc cs  syst  = RecIdle \<longrightarrow> even (recoveredGlb cs ) "
and   " \<forall>  t.  (  writer cs = Some t \<longrightarrow> odd (lastVal glb  (\<tau> cs)) )"
and "pc cs  syst  = RecIdle  \<longrightarrow> ( lastVal glb (\<tau> cs)  \<ge>recoveredGlb cs ) "
and " ta \<noteq> syst"
and" f_sim  cs as "
shows " f_sim  cs' as  "
  using assms
  apply (simp add: Write_inv_def tmstep_def TML_Write_def f_sim_def total_wfs_def  split: if_splits)
  apply (intro conjI)
  apply (simp add: global_rel_def)
  apply (intro conjI impI)
  apply (simp add: logical_glb_def write_count_def)
  apply (simp add: writes_def)
  apply (intro conjI allI)
  apply (simp add: no_read_rdSet_empty_def)
  apply (simp add: no_write_wrSet_empty_def)
  apply (simp add: write_wrSet_notEmpty_def)
  apply (simp add: read_rdSet_notEmpty_def)
  apply (simp add:  loc_in_wrSet_def  )
  apply (simp add:  even_loc_wrSet_empty_def)
  apply (simp add:odd_loc_wrSet_notEmpty_def  TMWrite_trans_def )
  apply (metis assms(1) assms(2) assms(3) assms(4) tr_rel_write4_self tr_rel_write4_stable)
  apply (unfold read_prop_def)
  apply metis
  apply (intro conjI allI)
  apply (simp add: global_rel_def)
  apply (intro conjI impI)
  apply (simp add: logical_glb_def write_count_def)
  apply (simp add: writes_def)
  apply (simp add: no_read_rdSet_empty_def)
  apply (simp add: no_write_wrSet_empty_def)
  apply (simp add:  write_wrSet_notEmpty_def)
  apply (simp add: read_rdSet_notEmpty_def)
  apply (simp add:  loc_in_wrSet_def  )
  apply (simp add:  even_loc_wrSet_empty_def)
  apply (simp add:odd_loc_wrSet_notEmpty_def  TMWrite_trans_def )
  apply (metis assms(1) assms(2) assms(3) assms(4) tr_rel_write4_self tr_rel_write4_stable)
  by metis



(*********************************************)


(*auxiliary lemma*)
lemma   tr_rel_write5_self:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "TML_Write ta  cs  cs'"
and "((pc cs) ta)  = PC.Write5"
and " Write_inv  ta  ((pc cs) ta) cs " 
and"   tr_rel   cs as ta"
shows "   tr_rel   cs' as ta  "
  using assms
  apply(simp add:TML_Write_def tr_rel_def  in_flight_def validity_prop_def total_wfs_def Write_inv_def  split: if_splits )
  using reg_same_ld_dt 
  by metis


(*auxiliary lemma*)
lemma   tr_rel_write5_stable:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "TML_Write ta  cs  cs'"
and "((pc cs) ta)  = PC.Write5"
and " Write_inv  ta  ((pc cs) ta) cs " 
and"   tr_rel   cs as t"
and " t \<noteq> ta "
and " ta \<noteq> syst"
shows "   tr_rel   cs' as t "
  using assms
  apply(simp add:TML_Write_def tr_rel_def  in_flight_def validity_prop_def total_wfs_def Write_inv_def   )
  apply (unfold  in_flight_def validity_prop_def)
  apply (cases "pc cs t"; simp)
  apply (metis assms(2) lastVal_ni reg_same_ld_dr)
  apply (metis  reg_same_ld_dt)
  apply (metis  reg_same_ld_dt)
  apply (metis  reg_same_ld_dt)
  apply (metis assms(2) lastVal_ni reg_same_ld_dt)
  apply (metis assms(2) lastVal_ni reg_same_ld_dt)
  apply (metis reg_same_ld_dt)
  apply (metis  reg_same_ld_dt)
  apply (metis (no_types, lifting) assms(2) lastVal_ni reg_same_ld_dt)
  apply (smt (z3) assms(2) assms(7) lastVal_ni reg_same_ld_dr)
  apply (smt (verit, ccfv_SIG) assms(2) lastVal_ni reg_same_ld_dt)
  apply (metis assms(2) lastVal_ni reg_same_ld_dt)
  apply (metis reg_same_ld_dt)
  apply (metis reg_same_ld_dt)
  apply (smt (z3) assms(2) lastVal_ni reg_same_ld_dt)
  apply (metis assms(2) lastVal_ni reg_same_ld_dt)
  apply (metis assms(2) lastVal_ni reg_same_ld_dt)
  apply (metis assms(2) lastVal_ni)
  apply (metis reg_same_ld_dt)
  apply (metis reg_same_ld_dt)
  apply (metis reg_same_ld_dt)
  apply (metis reg_same_ld_dt)
  apply (metis reg_same_ld_dt)
  apply (metis reg_same_ld_dt)
  by (metis assms(2) lastVal_ni reg_same_ld_dt)+


(*the simulation relation holds from Write5 to Write6  (stuttering step) *)
lemma   f_sim_write_write5:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "TML_Write ta  cs  cs'"
and " Write_inv  ta  ((pc cs) ta) cs " 
and "((pc cs) ta)  = PC.Write5"
and " a \<noteq> glb"
and " pc cs  syst  = RecIdle \<longrightarrow> even (recoveredGlb cs ) "
and   " \<forall>  t.  (  writer cs = Some t \<longrightarrow> odd (lastVal glb  (\<tau> cs)) )"
and "pc cs  syst  = RecIdle  \<longrightarrow> ( lastVal glb (\<tau> cs)  \<ge>recoveredGlb cs ) "
and" f_sim  cs as "
and " ta \<noteq> syst"
shows " f_sim  cs' as  "
  using assms
  apply (simp add: Write_inv_def  TML_Write_def f_sim_def total_wfs_def )
  apply (intro conjI)
  apply (simp add: global_rel_def)
  apply (intro impI allI conjI impI)
  prefer 3
  apply (simp add: writes_def)    
  apply (simp add: write_count_def logical_glb_def)
  apply (metis assms(2) lastVal_ni)
  apply (simp add: write_count_def logical_glb_def)
  apply (metis assms(2) lastVal_ni)
  apply (simp add: writes_def)
  apply (metis assms(2) lastVal_ni)
  apply (metis (no_types, opaque_lifting) assms(2) lastVal_ni)
  apply (intro allI conjI)
  apply (simp add: no_read_rdSet_empty_def)
  apply (simp add: no_write_wrSet_empty_def)
  apply (simp add: write_wrSet_notEmpty_def )
  apply (simp add: read_rdSet_notEmpty_def)
  apply (simp add:  loc_in_wrSet_def  )
  apply (metis assms(2) lastVal_ni)
  apply (simp add:  even_loc_wrSet_empty_def)
  apply (metis (no_types, lifting) reg_same_ld_dt)
  apply (simp add:odd_loc_wrSet_notEmpty_def  TMWrite_trans_def )
  apply (smt (verit) reg_same_ld_dt)
  apply (metis assms(1) assms(2) assms(3) assms(4) tr_rel_write5_self tr_rel_write5_stable)
  apply (unfold read_prop_def)
  by (metis ld_lelim_nle_ni ld_step_mem ld_valOf_nle_ni less_or_eq_imp_le)



(************************)

(*auxiliary lemma*)
lemma   tr_rel_write6_self:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "TML_Write ta  cs  cs'"
and "((pc cs) ta)  = PC.Write6"
and " Write_inv  ta  ((pc cs) ta) cs " 
and"   tr_rel   cs as ta"
shows "  tr_rel   cs' as ta"
  using assms
  by(simp add:TML_Write_def tr_rel_def  in_flight_def validity_prop_def total_wfs_def Write_inv_def  split: if_splits )


(*auxiliary lemma*)
lemma   tr_rel_write6_stable:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "TML_Write ta  cs  cs'"
and "((pc cs) ta)  = PC.Write6"
and " Write_inv  ta  ((pc cs) ta) cs " 
and"   tr_rel   cs as t"
and " t \<noteq> ta "
shows "   tr_rel   cs' as t "
  using assms
  apply(simp add:TML_Write_def tr_rel_def  in_flight_def validity_prop_def total_wfs_def Write_inv_def   )
  apply (unfold  in_flight_def validity_prop_def)
  by presburger


(*the simulation relation holds from Write6 to Write7  (stuttering step) *)
lemma   f_sim_write_write6:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "TML_Write ta  cs  cs'"
and " Write_inv  ta  ((pc cs) ta) cs " 
and "((pc cs) ta)  = PC.Write6"
and " a \<noteq> glb"
and " pc cs  syst  = RecIdle \<longrightarrow> even (recoveredGlb cs ) "
and   " \<forall>  t.  (  writer cs = Some t \<longrightarrow> odd (lastVal glb  (\<tau> cs)) )"
and "pc cs  syst  = RecIdle  \<longrightarrow> ( lastVal glb (\<tau> cs)  \<ge>recoveredGlb cs ) "
and" f_sim  cs as "
and " ta \<noteq> syst"
shows " f_sim  cs' as  "
  using assms
  apply (simp add: Write_inv_def  TML_Write_def f_sim_def total_wfs_def )
  apply (intro conjI)
  apply (simp add: global_rel_def)
  apply (intro impI allI conjI impI)
  apply (simp add: logical_glb_def)
  apply (simp add: writes_def)
  apply (metis option.distinct(1))
  apply blast
  apply (intro allI conjI)
  apply (simp add: no_read_rdSet_empty_def)
  apply (simp add: no_write_wrSet_empty_def)
  apply (simp add:  write_wrSet_notEmpty_def)
  apply (simp add: read_rdSet_notEmpty_def)
  apply (simp add:  loc_in_wrSet_def  )
  apply (simp add:  even_loc_wrSet_empty_def)
  apply (simp add:odd_loc_wrSet_notEmpty_def  TMWrite_trans_def )
  apply (metis assms(1) assms(2) assms(3) assms(4) tr_rel_write6_self tr_rel_write6_stable)
  apply (unfold read_prop_def) 
  by presburger

(**************************************************)

(*auxiliary lemma*)
lemma   tr_rel_write8_self:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "TML_Write ta  cs  cs'"
and "((pc cs) ta)  = PC.Write8"
and " Write_inv  ta  ((pc cs) ta) cs " 
and"   tr_rel   cs as ta"
shows "  tr_rel   cs' as ta"
  using assms
  apply(simp add:TML_Write_def tr_rel_def  in_flight_def validity_prop_def total_wfs_def Write_inv_def  split: if_splits )
  by (metis reg_same_flo)


(*auxiliary lemma*)
lemma   tr_rel_write8_stable:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "TML_Write ta  cs  cs'"
and "((pc cs) ta)  = PC.Write8"
and " Write_inv  ta  ((pc cs) ta) cs " 
and"   tr_rel   cs as t"
and " t \<noteq> ta "
and " ta \<noteq> syst"
shows "   tr_rel   cs' as t "
  using assms
  apply(simp add:TML_Write_def tr_rel_def  in_flight_def validity_prop_def total_wfs_def Write_inv_def   )
  apply (unfold  in_flight_def validity_prop_def)
  apply (cases " pc cs t"; simp)
  apply (metis reg_same_flo)
  apply (metis  reg_same_flo)
  apply (metis  reg_same_flo)
  apply (metis reg_same_flo)     
  apply (metis assms(2) flo_lastVal_ni reg_same_flo)
  apply (smt (z3) assms(2) flo_lastVal_ni reg_same_flo)
  apply (metis reg_same_flo)
  apply (metis reg_same_flo)
  apply (metis assms(2) flo_lastVal_ni reg_same_flo)
  apply (metis assms(2) flo_lastVal_ni reg_same_flo)
  apply (smt (z3) assms(2) flo_lastVal_ni reg_same_flo)
  apply (metis assms(2) flo_lastVal_ni)
  apply (metis reg_same_flo)
  apply (metis reg_same_flo)
  apply (metis (no_types, opaque_lifting) assms(2) flo_lastVal_ni reg_same_flo)
  by (metis assms(2) flo_lastVal_ni reg_same_flo)+



(*the simulation relation holds from Write8 to WriteResponding  (stuttering step) *)
lemma   f_sim_write_write8:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "TML_Write ta  cs  cs'"
and " Write_inv  ta  ((pc cs) ta) cs " 
and "((pc cs) ta)  = PC.Write8"
and " a \<noteq> glb"
and " pc cs  syst  = RecIdle \<longrightarrow> even (recoveredGlb cs ) "
and   " \<forall>  t.  (  writer cs = Some t \<longrightarrow> odd (lastVal glb  (\<tau> cs)) )"
and "pc cs  syst  = RecIdle  \<longrightarrow> ( lastVal glb (\<tau> cs)  \<ge>recoveredGlb cs ) "
and" f_sim  cs as "
and " ta \<noteq> syst"
shows " f_sim  cs' as  "
  using assms
  apply (simp add: Write_inv_def  TML_Write_def f_sim_def total_wfs_def )
  apply (intro conjI)
  apply (simp add: global_rel_def)
  apply (intro impI allI conjI impI)
  apply (simp add: logical_glb_def write_count_def)
  apply (metis assms(2) flo_lastVal_ni)
  apply (simp add: maxIndex_def writes_def)
  apply (metis assms(2) flo_lastVal_ni)
  apply (metis assms(2) flo_lastVal_ni)
  apply (metis option.distinct(1))
  apply (intro allI conjI)
  apply (simp add:  no_read_rdSet_empty_def)
  apply (simp add:  no_write_wrSet_empty_def)
  apply (simp add:  write_wrSet_notEmpty_def)
  apply (simp add: read_rdSet_notEmpty_def)
  apply (simp add:  loc_in_wrSet_def  )
  apply (metis assms(2) flo_lastVal_ni)
  apply (simp add:  even_loc_wrSet_empty_def)
  apply (metis reg_same_flo)
  apply (simp add:odd_loc_wrSet_notEmpty_def  TMWrite_trans_def )
  apply (metis reg_same_flo)
  apply (metis assms(1) assms(2) assms(3) assms(4) tr_rel_write8_self tr_rel_write8_stable)
  apply (unfold read_prop_def)
  apply (subgoal_tac " memory (\<tau> cs ) = memory (\<tau> cs' ) ")
  prefer 2
  apply (simp add: step_def)
  by (metis flo_lelim_nle_ni flo_valOf_nle_ni less_or_eq_imp_le)


(******************************************)

(*auxiliary lemma*)
lemma   tr_rel_write_write1_self:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "TML_Write ta  cs  cs'"
and "((pc cs) ta)  = PC.Write1"
and " Write_inv  ta  ((pc cs) ta) cs " 
and   "\<forall>t.  tms_inv as  t "
and "  pc cs syst = RecIdle "
and"   tr_rel   cs as ta"
and" f_sim  cs as "
and " ta \<noteq> syst"
shows "  tr_rel   cs' as ta"
  using assms
  apply(simp add: tms_inv_def TML_Write_def tr_rel_def  in_flight_def validity_prop_def total_wfs_def Write_inv_def  split: if_splits )
  apply (intro conjI impI)
  apply (simp add: f_sim_def)
  apply simp
  apply (simp add: f_sim_def)
  apply (simp add: no_write_wrSet_empty_def)
  apply (unfold  Ready_total_def)
  apply (metis PC.distinct(1219) PC.distinct(37) PC.distinct(727))
  apply (simp add: f_sim_def)
  apply (simp add: no_write_wrSet_empty_def)
  by (metis (no_types, lifting))




(*auxiliary lemma*)
lemma   tr_rel_write_write1_stable:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "TML_Write ta cs  cs'"
and "((pc cs) ta)  = PC.Write1"
and " Write_inv  ta  ((pc cs) ta) cs " 
and"   tr_rel   cs as t"
and " t \<noteq> ta "
and " ta \<noteq> syst"
shows "   tr_rel   cs' as t "
  using assms
  apply(simp add:TML_Write_def tr_rel_def  in_flight_def validity_prop_def total_wfs_def Write_inv_def  split: if_splits  )
  apply (unfold  in_flight_def validity_prop_def)
  apply (cases "  pc cs t"; simp)
  apply metis
  apply blast
  apply blast
  apply meson
  apply meson
  apply (cases "  pc cs t"; simp)
  apply metis
  apply meson
  apply force
  apply fastforce
  by meson


(*auxiliary lemma*)
lemma write_pc_write1_logical_glb_ni:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "TML_Write ta  cs  cs'"
and " Write_inv  ta  ((pc cs) ta) cs " 
and "((pc cs) ta)  = PC.Write1"
and "pc cs  syst  = RecIdle  \<longrightarrow> ( lastVal glb (\<tau> cs)  \<ge>recoveredGlb cs ) "
shows " logical_glb cs'  = logical_glb cs  "
  using assms
  apply (simp add: Write_inv_def  TML_Write_def f_sim_def total_wfs_def split: if_splits )
  apply (simp add: logical_glb_def)
  apply (cases "writer cs'")
  apply (metis option.simps(4))
  apply (smt (verit) PC.distinct(605) PC.distinct(607) fun_upd_other fun_upd_same option.simps(5))
  apply (simp add: logical_glb_def)
  apply (cases "writer cs'")
  apply (metis option.simps(4))
  by (smt (verit) PC.distinct(605) PC.distinct(611) fun_upd_other fun_upd_same option.simps(5))


(*************************************)

(*auxiliary lemma*)
lemma write_pc_write1_writes_ni:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "TML_Write ta  cs  cs'"
and " Write_inv  ta ((pc cs) ta) cs " 
and "((pc cs) ta)  = PC.Write1"
shows " writes cs' as   = writes cs as  "
  using assms
  apply (simp add: Write_inv_def  TML_Write_def f_sim_def total_wfs_def split: if_splits )
  apply (simp add: writes_def)
  apply (cases "writer cs'")
  apply (metis option.simps(4))
  apply (smt (z3) Ready_total_def fun_upd_other option.simps(5))
  apply (simp add: writes_def)
  apply (cases "writer cs'")
  apply (metis option.simps(4))
  by (smt (z3) PC.distinct(605) PC.distinct(611) Ready_total_def fun_upd_same option.simps(5))

(*the simulation relation holds from Write1 to Write2  (stuttering step) *)
lemma   f_sim_write_write1:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "TML_Write ta  cs  cs'"
and " Write_inv  ta  ((pc cs) ta) cs " 
and "((pc cs) ta)  = PC.Write1"
and " pc cs  syst  = RecIdle \<longrightarrow> even (recoveredGlb cs ) "
and   " \<forall>  t.  (  writer cs = Some t \<longrightarrow> odd (lastVal glb  (\<tau> cs)) )"
and "pc cs  syst  = RecIdle  \<longrightarrow> ( lastVal glb (\<tau> cs)  \<ge>recoveredGlb cs ) "
and" f_sim  cs as "
and   "\<forall>t.  tms_inv as  t "
and " pc cs syst = RecIdle "
and " ta \<noteq> syst"
shows " f_sim  cs' as  "
  using assms
  apply (simp add: Write_inv_def  TML_Write_def f_sim_def total_wfs_def split: if_splits )
  apply (intro conjI)
  apply (simp add: global_rel_def)
  apply (intro impI allI conjI impI)
  apply (elim conjE )
  apply (simp add: write_count_def)
  apply (subgoal_tac " logical_glb cs'  = logical_glb cs  ")
  prefer 2
  using  write_pc_write1_logical_glb_ni [where cs = cs and ta = ta and cs' = cs']
  using assms(1) assms(2) assms(3) assms(4) assms(8) apply fastforce
  apply presburger
  apply (simp add:  maxIndex_def  apply_partial_def)
  apply (metis assms(1) assms(2) assms(3) assms(4) write_pc_write1_writes_ni)
  apply (intro conjI allI)
  apply (simp add: no_read_rdSet_empty_def)
  apply (simp add: no_write_wrSet_empty_def)
  apply (simp add:  write_wrSet_notEmpty_def)
  apply (simp add:   read_rdSet_notEmpty_def)
  apply (simp add:loc_in_wrSet_def)
  apply (simp add: even_loc_wrSet_empty_def)
  apply (simp add:odd_loc_wrSet_notEmpty_def  TMWrite_trans_def )
  apply (metis assms(1) assms(12) assms(2) assms(3) assms(4) f_sim_def tr_rel_write_write1_self tr_rel_write_write1_stable)
  apply (unfold read_prop_def)
  apply metis
  apply (intro conjI)
  apply (simp add: global_rel_def)
  apply (intro impI allI conjI impI)
  apply (elim conjE )
  apply (simp add: write_count_def  )
  apply (metis \<open>\<lbrakk>thrdsvars; total_wfs (\<tau> cs); TML_Write ta cs cs'; Write_inv ta (pc cs ta) cs; pc cs ta = Write1; pc cs syst = RecIdle \<longrightarrow> recoveredGlb cs \<le> lastVal glb (\<tau> cs)\<rbrakk> \<Longrightarrow> logical_glb cs' = logical_glb cs\<close> assms(1) assms(2) assms(3) assms(4))
  apply (metis assms(1) assms(2) assms(3) assms(4) write_pc_write1_writes_ni)
  apply (intro conjI allI)
  apply (simp add: no_read_rdSet_empty_def)
  apply (simp add: no_write_wrSet_empty_def)
  apply (simp add:  write_wrSet_notEmpty_def)
  apply (simp add:   read_rdSet_notEmpty_def)
  apply (simp add:loc_in_wrSet_def)
  apply (simp add: even_loc_wrSet_empty_def)
  apply (simp add:odd_loc_wrSet_notEmpty_def  TMWrite_trans_def )
  apply (metis assms(1) assms(12) assms(2) assms(3) assms(4) assms(9) f_sim_def tr_rel_write_write1_self tr_rel_write_write1_stable)
  by metis


(******************************************************************************************)


(*auxiliary lemma*)
lemma   tr_rel_write_WritePending_self:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "TML_Write ta  cs  cs'"
and "((pc cs) ta)  = PC.WritePending"
and " Write_inv  ta  ((pc cs) ta) cs " 
and   "\<forall>t.  tms_inv as  t "
and "  pc cs syst = RecIdle "
and"   tr_rel   cs as ta"
and" f_sim  cs as "
and " ta \<noteq> syst"
shows "  tr_rel   cs' as ta"
  using assms
  by(simp add: tms_inv_def TML_Write_def tr_rel_def  in_flight_def validity_prop_def total_wfs_def Write_inv_def  split: if_splits )


(*auxiliary lemma*)
lemma   tr_rel_write_WritePending_stable:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "TML_Write ta cs  cs'"
and "((pc cs) ta)  = PC.WritePending"
and " Write_inv  ta  ((pc cs) ta) cs " 
and"   tr_rel   cs as t"
and " t \<noteq> ta "
and " ta \<noteq> syst"
shows "   tr_rel   cs' as t "
  using assms
  apply(simp add:TML_Write_def tr_rel_def  in_flight_def validity_prop_def total_wfs_def Write_inv_def  split: if_splits  )
  apply (unfold  in_flight_def validity_prop_def)
  apply (cases "  pc cs t"; simp)
  apply metis
  apply blast
  apply blast
  apply meson
  by meson




(*the simulation relation holds from WritePending to Write1 (stuttering step) *)
lemma   f_sim_write_WritePending:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "TML_Write ta  cs  cs'"
and " Write_inv  ta  ((pc cs) ta) cs " 
and "((pc cs) ta)  = PC.WritePending"
and " pc cs  syst  = RecIdle \<longrightarrow> even (recoveredGlb cs ) "
and   " \<forall>  t.  (  writer cs = Some t \<longrightarrow> odd (lastVal glb  (\<tau> cs)) )"
and "pc cs  syst  = RecIdle  \<longrightarrow> ( lastVal glb (\<tau> cs)  \<ge>recoveredGlb cs ) "
and" f_sim  cs as "
and   "\<forall>t.  tms_inv as  t "
and " pc cs syst = RecIdle "
and " ta \<noteq> syst"
shows " f_sim  cs' as  "
  using assms
  apply (simp add: Write_inv_def  TML_Write_def f_sim_def total_wfs_def split: if_splits )
  apply (intro conjI)
  apply (simp add: global_rel_def)
  apply (intro impI allI conjI impI)
  apply (simp add:  write_count_def logical_glb_def)
  apply (cases " writer cs' ")
  apply (metis option.case_eq_if)
  apply simp
  apply (smt (verit) PC.distinct(603) Suc_eq_plus1)
  apply (simp add: maxIndex_def writes_def)
  apply (cases " writer cs' ")
  apply (metis option.case_eq_if)
  apply simp
  apply (intro conjI allI)
  apply (simp add: no_read_rdSet_empty_def)
  apply (simp add: no_write_wrSet_empty_def)
  apply (simp add:  write_wrSet_notEmpty_def)
  apply (simp add:   read_rdSet_notEmpty_def)
  apply (simp add:loc_in_wrSet_def)
  apply (simp add: even_loc_wrSet_empty_def)
  apply (simp add:odd_loc_wrSet_notEmpty_def  TMWrite_trans_def )
  apply (metis assms(1) assms(2) assms(3) assms(4) f_sim_def tr_rel_write_WritePending_self tr_rel_write_WritePending_stable)
  apply (unfold  read_prop_def)
  by metis

(*******************************************)

(*auxiliary lemma*)
lemma   tr_rel_Write_self_lp:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "  TML_Write_invocation   ta cs  cs'  "
and "((pc cs) ta)  = PC.Ready"
and "  Write_invocation_inv   ta  ((pc cs) ta) cs " 
and " f_sim cs as "
and"   tr_rel   cs as ta"
and " ta \<noteq> syst"
shows "  tr_rel cs' (TMWrite_inv_trans  ta  as) ta "
  using assms
  by (simp add: TML_Write_invocation_def tr_rel_def Write_invocation_inv_def TMWrite_inv_trans_def  validity_prop_def  split: if_splits )

(*auxiliary lemma*)
lemma   tr_rel_Write_stable_lp:
assumes  "thrdsvars"
and   "\<forall>t.  tms_inv as  t "
and "total_wfs (\<tau> cs) "
and "((pc cs) ta)  = PC.Ready"
and "  Write_invocation_inv   ta  ((pc cs) ta) cs " 
and "  TML_Write_invocation   ta cs  cs'  "
and " f_sim cs as "
and"   tr_rel   cs as t"
and " t \<noteq> ta "
and " ta \<noteq> syst"
shows "  tr_rel cs' (TMWrite_inv_trans  ta  as) t "
  using assms
  apply (simp add: TML_Write_invocation_def tr_rel_def  Write_invocation_inv_def  TMWrite_inv_trans_def split: if_splits )
  apply (unfold validity_prop_def  in_flight_def total_wfs_def  )
  apply (cases "pc cs t";  simp)
  apply metis
  apply metis
  apply (metis PC.distinct(1489) fun_upd_def)
  apply (metis PC.distinct(1491) fun_upd_def)
  by (metis PC.distinct(1493) fun_upd_def)


(*auxiliary lemma*)
lemma write_ready_logical_glb_ni:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and " TML_Write_invocation  ta   cs cs'"
and "((pc cs) ta)  = PC.Ready"
shows " logical_glb cs = logical_glb cs' "
  using assms
  apply (unfold total_wfs_def)
  apply (simp add: TML_Write_invocation_def logical_glb_def)
  apply (cases "pc cs ta";  simp)
  apply (subgoal_tac "  lastVal glb (\<tau> cs) =  lastVal glb (\<tau> cs') ")
  prefer 2
  apply metis
  apply (subgoal_tac "  recoveredGlb cs' =  recoveredGlb cs ")
  prefer 2
  apply presburger
  apply (cases " writer cs" )
  apply simp
  apply (simp add:  split if_splits )
  by (smt (z3) PC.distinct(603) PC.distinct(645) fun_upd_def option.simps(5))


(*auxiliary lemma*)
lemma write_ready_writes_ni:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and " TML_Write_invocation  ta   cs cs'"
and "((pc cs) ta)  = PC.Ready"
shows " writes cs as = writes  cs'  (TMWrite_inv_trans  ta  as) "
  using assms
  apply (unfold total_wfs_def)
  apply (simp add: TML_Write_invocation_def TMWrite_inv_trans_def logical_glb_def writes_def)
  apply (cases "pc cs ta";  simp)
  apply (cases " writer cs" )
  apply simp
  apply (intro conjI impI)
  apply (cases " writer cs'" )
  apply simp+
  apply (cases " writer cs'" )
  by simp+

(*the simulation relation holds for inv(write) (non stuttering step) *)
lemma   f_sim_write_inv_ready_lp:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "  TML_Write_invocation   ta cs  cs'  "
and "((pc cs) ta)  = PC.Ready"
and " Write_invocation_inv ta  ((pc cs) ta) cs " 
and " f_sim  cs  as"
and   "\<forall>t.  tms_inv as  t "
and"pc cs  syst  = RecIdle "
and " ta \<noteq> syst"
shows "  \<exists> as'. tmstep ta  TMWriteInv  as  as'  \<and> f_sim  cs' as' "
  using assms
  apply (unfold total_wfs_def)
  apply (simp add: TML_Write_invocation_def Write_invocation_inv_def tmstep_def  f_sim_def)
  apply (subgoal_tac " memory ( \<tau>  cs) = memory( \<tau> cs' )")
  prefer 2
  apply presburger
  apply (cases "pc cs ta";  simp)
  apply (intro conjI)
  apply (simp add: global_rel_def)
  apply (intro conjI)
  apply (simp add: TMWrite_inv_trans_def  write_count_def) 
  apply (metis assms(1) assms(2) assms(3) write_ready_logical_glb_ni)
  apply (simp add: maxIndex_def  TMWrite_inv_trans_def  ) 
  using TMWrite_inv_trans_def assms(1) assms(2) assms(3) write_ready_writes_ni apply presburger
  apply (simp add: maxIndex_def  TMWrite_inv_trans_def apply_partial_def ) 
  apply (simp add: maxIndex_def  TMWrite_inv_trans_def apply_partial_def ) 
  apply (simp add:  TMWrite_inv_trans_def )
  apply (simp add: no_read_rdSet_empty_def  no_write_wrSet_empty_def write_wrSet_notEmpty_def  read_rdSet_notEmpty_def loc_in_wrSet_def even_loc_wrSet_empty_def  odd_loc_wrSet_notEmpty_def )
  apply (subgoal_tac " tpc as ta = TPC.Ready")
  prefer 2
  apply (simp add: tr_rel_def)
  apply (smt (z3) PC.simps(1680))
  apply simp
  apply (intro conjI allI impI)
  apply (metis TMWrite_inv_trans_def assms(1) assms(2) assms(3) assms(5) assms(6) tr_rel_Write_self_lp)
  using tr_rel_Write_stable_lp [where as=as and cs=cs  and cs'=cs' and ta = ta] 
  apply (metis TMWrite_inv_trans_def assms(1) assms(2) assms(3) assms(5) assms(6))
  apply (simp add:   TMWrite_inv_trans_def)
  apply (unfold  read_prop_def)
  apply (subgoal_tac " tpc as ta = TPC.Ready")
  prefer 2
  apply (simp add: tr_rel_def)
  apply (smt (z3) PC.simps(1680))
  by simp


(********************************************)


(*auxiliary lemma*)
lemma   tr_rel_WriteResponding_self_lp:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "  TML_Write_response  ta cs  cs'  "
and "((pc cs) ta)  = PC.WriteResponding"
and "  Write_Response_inv   ta  ((pc cs) ta) cs " 
and " f_sim cs as "
and"   tr_rel   cs as ta"
and " ta \<noteq> syst"
shows "  tr_rel cs' ( TMWrite_resp_trans  ta  as) ta "
using assms
by (simp add: TML_Write_response_def tr_rel_def Write_Response_inv_def TMWrite_resp_trans_def  validity_prop_def  split: if_splits )


(*auxiliary lemma*)
lemma   tr_rel_WriteResponding_stable_lp:
assumes  "thrdsvars"
and   "\<forall>t.  tms_inv as  t "
and "total_wfs (\<tau> cs) "
and "((pc cs) ta)  =PC.WriteResponding"
and "  Write_Response_inv   ta  ((pc cs) ta) cs " 
and "   TML_Write_response   ta cs  cs'  "
and " f_sim cs as "
and"   tr_rel   cs as t"
and " t \<noteq> ta "
and " ta \<noteq> syst"
shows "  tr_rel cs' ( TMWrite_resp_trans  ta  as) t "
  using assms
  apply (simp add: TML_Write_response_def tr_rel_def  Write_Response_inv_def  TMWrite_resp_trans_def split: if_splits )
  apply (unfold validity_prop_def  in_flight_def total_wfs_def  )
  apply (cases "pc cs t";  simp)
  apply metis
  apply metis
  apply (metis PC.distinct(1489) fun_upd_def)
  apply (metis PC.distinct(1491) fun_upd_def)
  by (metis PC.distinct(1493) fun_upd_def)



(*auxiliary lemma*)
lemma read_writeResponding_logical_glb_ni:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and " TML_Write_response  ta   cs cs'"
and "((pc cs) ta)  = PC.WriteResponding"
shows " logical_glb cs = logical_glb cs' "
  using assms
  apply (unfold total_wfs_def)
  apply (simp add: TML_Write_response_def logical_glb_def)
  apply (cases "pc cs ta";  simp)
  apply (subgoal_tac "  lastVal glb (\<tau> cs) =  lastVal glb (\<tau> cs') ")
  prefer 2
  apply metis
  apply (subgoal_tac "  recoveredGlb cs' =  recoveredGlb cs ")
  prefer 2
  apply presburger
  apply (cases " writer cs" )
  apply simp
  apply (simp add:  split if_splits )
  by (smt (verit) PC.distinct(621) PC.distinct(645) fun_upd_other fun_upd_same option.simps(5))




(*auxiliary lemma*)
lemma read_writeResponding_writes_ni:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and " TML_Write_response  ta   cs cs'"
and "((pc cs) ta)  =  PC.WriteResponding"
shows " writes cs as = writes  cs'  (TMWrite_resp_trans  ta  as) "
using assms
apply (unfold total_wfs_def)
apply (simp add: TML_Write_response_def TMWrite_resp_trans_def logical_glb_def writes_def)
apply (cases "pc cs ta";  simp)
apply (cases " writer cs" )
apply simp
apply (intro conjI impI)
apply (cases " writer cs'" )
apply simp+
apply (cases " writer cs'" )
by simp+


(*the simulation relation holds from res(Write) (non stuttering step) *)
lemma   f_sim_write_inv_WriteResponding_lp:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "  TML_Write_response   ta cs  cs'  "
and "((pc cs) ta)  =  PC.WriteResponding"
and " Write_Response_inv ta  ((pc cs) ta) cs " 
and " f_sim  cs  as"
and   "\<forall>t.  tms_inv as  t "
and"pc cs  syst  = RecIdle "
and " ta \<noteq> syst"
shows "  \<exists> as'. tmstep ta  TMWriteResp  as  as'  \<and> f_sim  cs' as'  "
  using assms
  apply (unfold total_wfs_def)
  apply (simp add: TML_Write_response_def tmstep_def  Write_Response_inv_def  f_sim_def)
  apply (subgoal_tac " memory ( \<tau>  cs) = memory( \<tau> cs' )")
  prefer 2
  apply presburger
  apply (cases "pc cs ta";  simp)
  apply (intro conjI)
  apply (simp add: global_rel_def)
  apply (intro conjI)
  apply (simp add: TMWrite_resp_trans_def  write_count_def) 
  apply (metis assms(1) assms(2) assms(3)  read_writeResponding_logical_glb_ni)
  apply (simp add: maxIndex_def  TMWrite_resp_trans_def  ) 
  using  read_writeResponding_writes_ni TMWrite_resp_trans_def 
  using assms(1) assms(2) assms(3) apply presburger
  apply (simp add: maxIndex_def  TMWrite_resp_trans_def apply_partial_def ) 
  apply (simp add: maxIndex_def  TMWrite_resp_trans_def apply_partial_def ) 
  apply (simp add:  TMWrite_resp_trans_def )
  apply (simp add: no_read_rdSet_empty_def  no_write_wrSet_empty_def write_wrSet_notEmpty_def  odd_loc_wrSet_notEmpty_def read_rdSet_notEmpty_def loc_in_wrSet_def even_loc_wrSet_empty_def )
  apply (subgoal_tac " tpc as ta = TPC.WriteResponding")
  prefer 2
  apply (simp add: tr_rel_def)
  apply (smt (z3) PC.simps(1668))
  apply simp
  apply (intro conjI allI impI)
  apply (metis TMWrite_resp_trans_def assms(1) assms(2) assms(3) assms(5) assms(6) tr_rel_WriteResponding_self_lp)
  apply (metis TMWrite_resp_trans_def assms(1) assms(2) assms(3) assms(5) assms(6) tr_rel_WriteResponding_stable_lp)
  apply (simp add:   TMWrite_resp_trans_def)
  apply (unfold  read_prop_def)
  apply (subgoal_tac " tpc as ta = TPC.WriteResponding")
  prefer 2
  apply (simp add: tr_rel_def)
  apply (smt (z3) PC.simps(1668))
  by simp
(*******************************************)




end
