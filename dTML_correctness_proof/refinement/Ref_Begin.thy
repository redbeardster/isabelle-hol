(*Showing that the simulation relation holds for the DTML Begin operation*)

theory Ref_Begin
imports "../Refinement"
begin

(**********inv(Begin operation)**********)

(*auxiliary lemma*)
lemma   tr_rel_notStarted_self_lp:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "  TML_Begin_invocation   ta cs  cs'  "
and "((pc cs) ta)  = PC.NotStarted"
and "  Begin_invocation_inv   ta  ((pc cs) ta) cs " 
and " f_sim cs as "
and"   tr_rel   cs as ta"
and " ta \<noteq> syst"
shows "  tr_rel cs' (TMBegin_inv_trans  ta  as) ta "
  using assms
  by (simp add: TML_Begin_invocation_def tr_rel_def Begin_invocation_inv_def TMBegin_inv_trans_def  validity_prop_def  split: if_splits )

(*auxiliary lemma*)
lemma   tr_rel_notStarted_stable_lp:
assumes  "thrdsvars"
and   "\<forall>t.  tms_inv as  t "
and "total_wfs (\<tau> cs) "
and "((pc cs) ta)  = PC.NotStarted"
and "  Begin_invocation_inv   ta  ((pc cs) ta) cs " 
and "  TML_Begin_invocation   ta cs  cs'  "
and " f_sim cs as "
and"   tr_rel   cs as t"
and " t \<noteq> ta "
and " ta \<noteq> syst"
shows "  tr_rel cs' (TMBegin_inv_trans  ta  as) t "
  using assms
  apply (simp add: TML_Begin_invocation_def tr_rel_def  Begin_invocation_inv_def  TMBegin_inv_trans_def split: if_splits )
  apply (unfold validity_prop_def  in_flight_def total_wfs_def  )
  apply (cases "pc cs t";  simp)
  apply metis
  apply metis
  apply (metis PC.distinct(1489) fun_upd_def)
  apply (metis PC.distinct(1491) fun_upd_def)
  by (metis PC.distinct(1493) fun_upd_def)


(*auxiliary lemma*)
lemma begin_notStarted_logical_glb_ni:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and " TML_Begin_invocation  ta   cs cs'"
and "((pc cs) ta)  = PC.NotStarted"
shows " logical_glb cs = logical_glb cs' "
  using assms
  apply (unfold total_wfs_def)
  apply (simp add: TML_Begin_invocation_def logical_glb_def)
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
  by (smt (verit) PC.distinct(15) PC.distinct(93) fun_upd_other fun_upd_same option.simps(5))


(*auxiliary lemma*)
lemma begin_notStarted_writes_ni:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and " TML_Begin_invocation  ta   cs cs'"
and "((pc cs) ta)  = PC.NotStarted"
shows " writes cs as = writes  cs'  (TMBegin_inv_trans  ta  as) "
  using assms
  apply (unfold total_wfs_def)
  apply (simp add: TML_Begin_invocation_def TMBegin_inv_trans_def logical_glb_def writes_def)
  apply (cases "pc cs ta";  simp)
  apply (cases " writer cs" )
  apply simp
  apply (intro conjI impI)
  apply (cases " writer cs'" )
  apply simp+
  apply (cases " writer cs'" )
  by simp+


(*the simulation relation holds for inv(Begin)  (non  stuttering step) *)
lemma   f_sim_notStarted_beginPending_lp:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "  TML_Begin_invocation   ta cs  cs'  "
and "((pc cs) ta)  = PC.NotStarted"
and " Begin_invocation_inv ta  ((pc cs) ta) cs " 
and " f_sim  cs  as"
and   "\<forall>t.  tms_inv as  t "
and " ta \<noteq> syst"
shows " \<exists> as'. tmstep ta  TMBeginInv  as  as'  \<and> f_sim  cs' as'  "
  using assms
  apply (unfold total_wfs_def)
  apply (simp add: TML_Begin_invocation_def   Begin_invocation_inv_def tmstep_def  f_sim_def)
  apply (subgoal_tac " memory ( \<tau>  cs) = memory( \<tau> cs' )")
  prefer 2
  apply presburger
  apply (cases "pc cs ta";  simp)
  apply (intro conjI )
  apply (simp add: global_rel_def)
  apply (intro conjI impI)
  apply (simp add: TMBegin_inv_trans_def  write_count_def) 
  apply (metis assms(1) assms(2) assms(3) begin_notStarted_logical_glb_ni)
  apply (simp add: maxIndex_def  TMBegin_inv_trans_def  ) 
  using TMBegin_inv_trans_def assms(2) assms(3) begin_notStarted_writes_ni thrdsvars_def apply presburger
  apply (simp add: maxIndex_def  TMBegin_inv_trans_def apply_partial_def ) 
  apply (simp add: maxIndex_def  TMBegin_inv_trans_def apply_partial_def ) 
  apply (simp add:  TMBegin_inv_trans_def )
  apply (simp add: no_read_rdSet_empty_def  no_write_wrSet_empty_def write_wrSet_notEmpty_def  read_rdSet_notEmpty_def loc_in_wrSet_def even_loc_wrSet_empty_def )
  apply (subgoal_tac " tpc as ta = TPC.NotStarted")
  prefer 2
  apply (simp add: tr_rel_def)
  apply (meson global_rel_def)
  apply simp
  apply (intro conjI allI impI)
  apply (simp add: tr_rel_def)
  apply (unfold  tms_inv_def)
  apply (smt (z3) TPC.simps(133))
  apply (smt (z3) TPC.simps(133))
  apply (smt (z3) TPC.simps(133))
  apply (simp add:  odd_loc_wrSet_notEmpty_def)
  apply (metis TMBegin_inv_trans_def assms(1) assms(2) assms(3) assms(5) assms(6) tr_rel_notStarted_self_lp)
  apply (simp add:  odd_loc_wrSet_notEmpty_def)
  using tr_rel_notStarted_stable_lp [where as=as and cs=cs  and cs'=cs' and ta = ta] 
  apply (metis TMBegin_inv_trans_def assms(1) assms(2) assms(3) assms(5) assms(6) assms(7))
  apply (simp add:   TMBegin_inv_trans_def)
  apply (unfold  read_prop_def)
  apply (subgoal_tac " tpc as ta = TPC.NotStarted")
  prefer 2
  apply (simp add: tr_rel_def)
  apply (metis global_rel_def)
  by simp


(**********Begin operation**********)

(*auxiliary lemma*)
lemma   tr_rel_BeginPending_self:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "TML_Begin  ta   cs   cs'"
and "Begin_inv ta  ((pc cs) ta) cs" 
and "((pc cs) ta)  = PC.BeginPending"
and"   tr_rel   cs as ta"
shows "   tr_rel   cs' as ta  "
  using assms
  by(simp add:TML_Begin_def tr_rel_def Begin_inv_def validity_prop_def  split: if_splits)


(*auxiliary lemma*)
lemma   tr_rel_BeginPending_stable:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "TML_Begin  ta   cs   cs'"
and "Begin_inv ta  ((pc cs) ta) cs" 
and "((pc cs) ta)  = PC.BeginPending"
and " t \<noteq> ta"
and " \<forall>t. tms_inv as  t "
and"   tr_rel   cs as t"
shows "   tr_rel   cs' as t  "
  using assms
  apply (simp add:TML_Begin_def tr_rel_def tms_inv_def  )
  apply (unfold  validity_prop_def in_flight_def )
  apply (cases "pc cs t ";simp)
  apply (intro conjI impI)
  apply metis
  apply blast
  apply meson
  apply blast
  by  blast

(*the simulation relation holds for BeginPending to Begin2 (stuttering step) *)
lemma  f_sim_begin_BeginPending :
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "Begin_inv ta  ((pc cs) ta) cs"   
and "TML_Begin  ta   cs   cs'"
and "((pc cs) ta)  = PC.BeginPending"
and " \<forall>t. tms_inv as  t "
and" f_sim  cs as   "
and " ta \<noteq> syst"
shows "  f_sim  cs' as  "
using assms
apply (simp add:   f_sim_def TML_Begin_def split:if_splits )
apply (intro conjI)
apply (simp add: global_rel_def )
apply (intro conjI impI)
apply( subgoal_tac " (logical_glb cs') = (logical_glb cs) ")
prefer 2
apply (simp add: logical_glb_def)
apply (simp add: option.case_eq_if)
apply presburger
apply (simp add: writes_def)
apply (simp add: fun_upd_same option.case_eq_if)
apply (subgoal_tac " tr_rel cs as ta ")
prefer 2
apply blast
apply (intro conjI allI impI)
apply (subgoal_tac "tpc as ta =  TPC.BeginPending ")
prefer 2
     apply (simp add: tr_rel_def)
    apply (simp add:  no_read_rdSet_empty_def tms_inv_def  global_rel_def)
    apply clarify
    apply (smt (z3) TPC.simps(137))
   apply (simp add:  no_write_wrSet_empty_def  tms_inv_def tr_rel_def global_rel_def)
   apply (smt (z3) TPC.simps(137))
  apply (simp add: write_wrSet_notEmpty_def)
  apply (simp add: read_rdSet_notEmpty_def Begin_inv_def)
 apply (simp add:  loc_in_wrSet_def tms_inv_def Begin_inv_def)
 apply (simp add: even_loc_wrSet_empty_def)
 apply (subgoal_tac " wrSet as ta = Map.empty ")
  prefer 2
  apply (simp add:tr_rel_def)
  apply clarify
  apply (subgoal_tac "  tpc as ta =  TPC.BeginPending  ")
   prefer 2
   apply (smt (z3) PC.simps(1642))
  apply (unfold tms_inv_def)
  apply (smt (z3) TPC.simps(137))
  apply (simp add: read_rdSet_notEmpty_def Begin_inv_def)
  apply (simp add:  loc_in_wrSet_def Begin_inv_def)
  apply (simp add:   even_loc_wrSet_empty_def Begin_inv_def)
  apply (simp add:  odd_loc_wrSet_notEmpty_def  Begin_inv_def)
  apply (metis assms(4) assms(6) thrdsvars_def tr_rel_BeginPending_self tr_rel_BeginPending_stable)
apply (unfold read_prop_def)
by simp






(*****************************************************************)
(*auxiliary lemma*)
lemma   tr_rel_Begin2_self:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "TML_Begin  ta   cs   cs'"
and "Begin_inv ta  ((pc cs) ta) cs" 
and "((pc cs) ta)  = PC.Begin2"
and " \<forall>t. tms_inv as  t "
and " f_sim cs as "
and"   tr_rel   cs as ta"
and " ta \<noteq> syst"
shows "   tr_rel   cs' as ta  "
  using assms
  apply (simp add:TML_Begin_def tr_rel_def Begin_inv_def  tms_inv_def  split: if_splits )
  apply (subgoal_tac " rdSet as ta = Map.empty ")
  prefer 2
  apply (smt (z3) TPC.simps(137))
  apply (simp add: validity_prop_def)
  by (metis loc_zero_read_con2)




(*auxiliary lemma*)
lemma   tr_rel_Begin2_stable:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "TML_Begin  ta   cs   cs'"
and "Begin_inv ta  ((pc cs) ta) cs" 
and "((pc cs) ta)  = PC.Begin2"
and " t \<noteq> ta "
and " \<forall>t. tms_inv as  t "
and"   tr_rel   cs as t"
and " ta \<noteq> syst"
shows "   tr_rel   cs' as t "
  using assms
  apply (simp add:TML_Begin_def tr_rel_def  tms_inv_def  )
  apply (unfold  validity_prop_def in_flight_def )
  apply (cases "pc cs t";  simp)
                      apply (metis  reg_same_ld_dr)
                      apply (metis reg_same_ld_dr)
                      apply (metis  reg_same_ld_dr)
                      apply (metis reg_same_ld_dr)
                      apply (metis (no_types, lifting) lastVal_ni reg_same_ld_dr)
                      apply (metis (no_types, lifting) lastVal_ni reg_same_ld_dr)
                      apply (metis reg_same_ld_dr)
                      apply (smt (z3) lastVal_ni reg_same_ld_dr)
                      apply (smt (z3) assms(6) lastVal_ni reg_same_ld_dr)
                     apply (metis (no_types, lifting) lastVal_ni reg_same_ld_dr)
  apply (metis (no_types, lifting) lastVal_ni reg_same_ld_dr)
  apply (smt (z3) assms(6) lastVal_ni reg_same_ld_dr)
  apply (metis lastVal_ni reg_same_ld_dr)
  apply (metis reg_same_ld_dr)
  apply (smt (z3) lastVal_ni reg_same_ld_dr)
  apply (smt (z3) lastVal_ni reg_same_ld_dr)
  apply (metis (no_types, lifting) lastVal_ni reg_same_ld_dr)
  apply (metis (no_types, lifting) lastVal_ni reg_same_ld_dr)
  apply (metis reg_same_ld_dr)
  apply (metis reg_same_ld_dr)
  apply (metis reg_same_ld_dr)
  apply (metis reg_same_ld_dr)
  apply (metis reg_same_ld_dr)
  apply (metis lastVal_ni reg_same_ld_dr)
  apply (metis (no_types, lifting) lastVal_ni reg_same_ld_dr)
  apply (metis assms(2) assms(6) lastVal_ni reg_same_ld_dr)
  apply (metis lastVal_ni reg_same_ld_dr)
  apply (metis (no_types, lifting) assms(2) assms(6) lastVal_ni reg_same_ld_dr)
  by (metis (no_types, lifting) lastVal_ni reg_same_ld_dr)


(*the simulation relation holds for  Begin2 to Begin3  (stuttering step) *)
lemma  f_sim_begin_Begin2 :
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "Begin_inv ta  ((pc cs) ta) cs" 
and "TML_Begin  ta   cs   cs'"
and "((pc cs) ta)  = PC.Begin2"
and " \<forall>t. tms_inv as  t "
and" f_sim  cs as  "
and " ta \<noteq> syst"
shows "  f_sim  cs' as  "
  using assms
  apply (simp add: f_sim_def TML_Begin_def )
  apply (intro conjI)
  apply (simp add:   global_rel_def Begin_inv_def write_count_def )
  apply (intro impI conjI)
  apply (simp add: logical_glb_def)
  apply (metis (no_types, lifting) fun_upd_other lastVal_ni option.case_eq_if option.discI option.expand option.sel)
  apply (subgoal_tac " writes cs' as = writes cs as ")
  prefer 2
  apply (simp add: writes_def)
  apply (smt (z3) fun_upd_other option.case_eq_if option.discI option.expand option.sel)
  apply (metis lastVal_ni)
  apply (intro allI impI conjI)
  apply (metis lastVal_ni)
  apply (simp add: Begin_inv_def  loc_in_wrSet_def)
  apply (intro allI conjI)
  apply (simp add:  no_read_rdSet_empty_def)
  apply (simp add:  no_write_wrSet_empty_def)
  apply (simp add: write_wrSet_notEmpty_def)
  apply (simp add: read_rdSet_notEmpty_def)
  apply (simp add:  loc_in_wrSet_def tms_inv_def Begin_inv_def)
  apply (metis lastVal_ni)
  apply (simp add:  even_loc_wrSet_empty_def  Begin_inv_def tr_rel_def tms_inv_def  odd_loc_wrSet_notEmpty_def)
  apply (smt (z3) PC.simps(1643) TPC.simps(137) reg_same_ld_dr)
  apply (simp add: odd_loc_wrSet_notEmpty_def Begin_inv_def tms_inv_def )
  apply (smt (z3) reg_same_ld_dr)
  apply (metis assms(4) assms(7) thrdsvars_def tr_rel_Begin2_self tr_rel_Begin2_stable)
  apply (unfold read_prop_def total_wfs_def)
  using  ld_lelim_nle_ni ld_valOf_nle_ni ld_comploc_ni
  by (metis (no_types, lifting) fun_upd_apply ld_step_mem nat_less_le)


(*****************************************************************)

(*auxiliary lemma*)
lemma tms_inv_begin_le_glb:
assumes "  beginIndex \<sigma> t < maxIndex \<sigma>  "
and "\<sigma>' =  TMBegin_trans ta  \<sigma>"
and "tmemory \<sigma> \<noteq> []"
shows  " beginIndex \<sigma>' t < maxIndex \<sigma>'"
  using assms
  apply (simp add: TMBegin_trans_def)
  apply (simp add: split: if_splits)
  apply (subgoal_tac "beginIndex \<sigma>' ta = maxIndex \<sigma> - Suc 0")
  prefer 2
  apply (simp add: maxIndex_def)
  apply (simp add: maxIndex_def)
  by auto


(*auxiliary lemma*)
lemma   tr_rel_Begin3_self_LP:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "TML_Begin  ta   cs   cs'"
and "Begin_inv ta  ((pc cs) ta) cs" 
and "((pc cs) ta)  = PC.Begin3"
and "((pc cs') ta)  = PC.BeginResponding"
and " \<forall>t. tms_inv as  t "
and"   tr_rel   cs as ta"
and"   f_sim   cs as "
and " pc cs  syst = RecIdle "
and " as' = TMBegin_trans ta  as "
and "tmemory as \<noteq> [] "
and "  \<forall>  t.   ((  even (lastVal glb  (\<tau> cs)) \<and> writer cs \<noteq> None) \<longrightarrow> pc cs  (the ( writer cs) )   \<noteq> Commit4  )"
and " ta \<noteq> syst"
shows "   tr_rel cs' as'  ta" 
using assms
  apply (subgoal_tac "  beginIndex as' ta < maxIndex as' ") 
  prefer 2
  apply (simp add: tr_rel_def)
  apply (subgoal_tac " tpc as' ta = TPC.BeginResponding  ")
  prefer 2
  apply (simp add: tr_rel_def TMBegin_trans_def )
  apply (simp add: TMBegin_trans_def)
  apply (simp add: maxIndex_def)
  apply (simp add:TML_Begin_def Begin_inv_def tr_rel_def tms_inv_def TMBegin_trans_def split: if_splits )
  apply (unfold  validity_prop_def  )
  apply (cases "pc cs ta";  simp)
  apply (intro conjI impI)
  apply (metis (no_types, opaque_lifting))
  apply (simp add: f_sim_def global_rel_def  )
  apply (subgoal_tac " logical_glb cs = lastVal glb (\<tau> cs') - recoveredGlb cs'")
  prefer 2
  apply (simp add:  logical_glb_def)
  apply (smt  (z3) assms(13) option.case_eq_if)
  by (metis le_refl maxIndex_def)










(*auxiliary lemma*)
lemma   tr_rel_Begin3_stable_LP:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "TML_Begin  ta   cs   cs'"
and "Begin_inv ta  ((pc cs) ta) cs" 
and "((pc cs) ta)  = PC.Begin3"
and "((pc cs') ta)  = PC.BeginResponding"
and " t \<noteq> ta"
and " \<forall>t. tms_inv as  t "
and"   tr_rel   cs as t"
and "tmemory as \<noteq> [] "
and "  \<forall>  t.   ((  even (lastVal glb  (\<tau> cs)) \<and> writer cs \<noteq> None) \<longrightarrow> pc cs  (the ( writer cs) )   \<noteq> Commit4  )"
and  " ((pc cs) syst) \<noteq> RecIdle   \<longrightarrow> (\<forall> t  \<noteq> syst.  ((pc cs) t)   \<in> {PC.NotStarted, PC.Aborted, PC.Committed})"
and " ta \<noteq> syst"
shows "   tr_rel cs' (TMBegin_trans ta  as) t" 
  using assms
  apply (simp add:TML_Begin_def tr_rel_def tms_inv_def TMBegin_trans_def  split: if_splits )
  apply (unfold  validity_prop_def in_flight_def  )
  apply (cases "pc cs t";  simp)
  apply meson
  apply presburger
  apply presburger
  apply presburger
  apply presburger
  apply blast
  apply (metis PC.distinct(247) PC.distinct(307) PC.distinct(5))
  apply (metis PC.distinct(247) PC.distinct(307) PC.distinct(5))
  by (metis PC.distinct(247) PC.distinct(307) PC.distinct(5))


(*the simulation relation holds for step  Begin3 to BeginResponding (linearization point) *)
lemma   f_sim_begin_begin3_LP:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "TML_Begin  ta   cs   cs'"
and "Begin_inv ta  ((pc cs) ta) cs" 
and " \<forall>t. tms_inv as  t "
and "((pc cs) ta)  = PC.Begin3"
and "((pc cs') ta)  = PC.BeginResponding"
and" f_sim  cs as "
and "  \<forall>  t.   ((  even (lastVal glb  (\<tau> cs)) \<and> writer cs \<noteq> None) \<longrightarrow> pc cs (the ( writer cs) )   \<noteq> Commit4  )"
and "tmemory as \<noteq> [] "
and "pc cs syst = RecIdle"
and  " ((pc cs) syst) \<noteq> RecIdle   \<longrightarrow> (\<forall> t  \<noteq> syst.  ((pc cs) t)   \<in> {PC.NotStarted, PC.Aborted, PC.Committed})"
and " ta \<noteq> syst"
shows "\<exists> as'. tmstep ta  TMBegin  as  as'  \<and> f_sim  cs' as'  "
  using assms
  apply(simp add: Begin_inv_def TML_Begin_def tmstep_def  split: if_splits )
  apply (simp add: f_sim_def)
  apply (intro conjI)
  apply (simp add: global_rel_def)
  apply (intro conjI impI)
  apply (simp add: write_count_def logical_glb_def TMBegin_trans_def)
  apply (metis (no_types, lifting) fun_upd_other option.case_eq_if option.distinct(1) option.expand option.sel)
  apply (intro allI)
  apply (subgoal_tac "  (writes cs' (TMBegin_trans ta as)) =  (writes cs as) ") 
  prefer 2
  apply (simp add: writes_def  )
  apply (case_tac"  writer cs' = None ")
  apply simp
  apply simp
  apply (simp add: TMBegin_trans_def split: if_splits)
  apply (simp add: TMBegin_trans_def)
  apply (intro allI conjI impI)
  apply (subgoal_tac "  (writes cs' (TMBegin_trans ta as)) =  (writes cs as) ") 
  prefer 2
  apply (simp add: writes_def  )
  apply (case_tac"  writer cs' = None ")
  apply simp
  apply simp
  apply (subgoal_tac " tmemory (TMBegin_trans ta as) =  tmemory as ")
  prefer 2
  apply (simp add: TMBegin_trans_def split: if_splits)
  apply (simp add: TMBegin_trans_def split: if_splits)
  apply (subgoal_tac " tmemory (TMBegin_trans ta as) =  tmemory as ")
  prefer 2
  apply (simp add: TMBegin_trans_def split: if_splits)
  apply (metis One_nat_def TMBegin_trans_def maxIndex_def)
  apply (simp add: TMBegin_trans_def )
  apply (simp add: maxIndex_def tms_state.update_convs(3) tms_state.update_convs(4))
  apply (simp add: writes_def TMBegin_trans_def maxIndex_def)
  apply (intro conjI allI)
  apply (simp add: no_read_rdSet_empty_def  TMBegin_trans_def)
  apply (simp add:  no_write_wrSet_empty_def TMBegin_trans_def)
  apply (simp add: write_wrSet_notEmpty_def  TMBegin_trans_def)
  apply (simp add: read_rdSet_notEmpty_def  TMBegin_trans_def)
  apply (simp add:  loc_in_wrSet_def tms_inv_def Begin_inv_def TMBegin_trans_def)
  apply (simp add:  even_loc_wrSet_empty_def  tms_inv_def Begin_inv_def TMBegin_trans_def  )
  apply (simp add:  odd_loc_wrSet_notEmpty_def   tms_inv_def Begin_inv_def TMBegin_trans_def  )
  apply clarify
  apply (case_tac " t = ta ")
  using  tr_rel_Begin3_self_LP[ where cs = cs and as= as and cs' = cs' ] 
  apply (metis assms(1) assms(3) assms(4) assms(7) assms(8) assms(9))
  using tr_rel_Begin3_stable_LP[ where cs = cs and as= as and cs' = cs' ] 
  apply (metis assms(1) assms(3) assms(4) assms(7) assms(9))
  apply (unfold read_prop_def total_wfs_def)
  by (simp add: TMBegin_trans_def)





(************************************************)

(*auxiliary lemma*)
lemma   tr_rel_Begin3_self_ST:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "TML_Begin  ta   cs   cs'"
and "Begin_inv ta  ((pc cs) ta) cs" 
and "((pc cs) ta)  = PC.Begin3"
and "((pc cs') ta)  = PC.Begin2"
and " \<forall>t. tms_inv as  t "
and"   tr_rel   cs as ta"
and " ta \<noteq> syst"
shows "   tr_rel   cs' as ta  "
  using assms
  by(simp add:TML_Begin_def tr_rel_def  tms_inv_def  split: if_splits )


(*auxiliary lemma*)
lemma   tr_rel_Begin3_stable_ST:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "TML_Begin  ta   cs   cs'"
and "Begin_inv ta  ((pc cs) ta) cs" 
and "((pc cs) ta)  = PC.Begin3"
and "((pc cs') ta)  = PC.Begin2"
and " t \<noteq> ta"
and " \<forall>t. tms_inv as  t "
and"   tr_rel   cs as t"
and  " ((pc cs) syst) \<noteq> RecIdle   \<longrightarrow> (\<forall> t  \<noteq> syst.  ((pc cs) t)   \<in> {PC.NotStarted, PC.Aborted, PC.Committed})"
and " ta \<noteq> syst"
shows "   tr_rel   cs' as t "
  using assms
  apply (simp add:TML_Begin_def tr_rel_def  tms_inv_def   split: if_splits )
  apply (unfold validity_prop_def in_flight_def)
  apply (cases "pc cs t";  simp)
  apply meson
  apply presburger
  apply presburger
  apply blast
  apply blast
  apply blast
  by blast

(*auxiliary lemma*)
lemma begin_dt:
assumes"  TML_Begin t' \<sigma> \<sigma>'"
and" t \<noteq> t' "
shows  " ((pc \<sigma>') t) = ((pc \<sigma>) t) "
  using assms
  apply (simp add: TML_Begin_def)
  apply (cases "pc \<sigma> t' ";  simp add: split if_splits  )
  using pc_aux 
  by (metis fun_upd_def)


(*the simulation relation holds for Begin3 to Begin2 (stuttering step) *)
lemma   f_sim_begin_begin3_ST:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "TML_Begin  ta   cs   cs'"
and "Begin_inv ta  ((pc cs) ta) cs" 
and "((pc cs) ta)  = PC.Begin3"
and "((pc cs') ta)  = PC.Begin2"
and " \<forall>t. tms_inv as  t "
and" f_sim  cs as "
and  " ((pc cs) syst) \<noteq> RecIdle   \<longrightarrow> (\<forall> t  \<noteq> syst.  ((pc cs) t)   \<in> {PC.NotStarted, PC.Aborted, PC.Committed})"
and " ta \<noteq> syst"
shows "  f_sim  cs' as  "
  using assms
  apply (simp add: f_sim_def TML_Begin_def split: if_splits )
  apply (intro conjI)
  apply (simp add: global_rel_def)
  apply (intro conjI allI impI)
  apply (simp add: logical_glb_def)
  apply (smt (verit) PC.distinct(169) PC.distinct(243) assms(3) assms(6)  begin_dt option.case_eq_if)
  apply (simp add: writes_def)
  apply (metis PC.distinct(169) PC.distinct(243) assms(6) fun_upd_other)
  apply (intro allI conjI)
  apply (simp add:  no_read_rdSet_empty_def)
  apply(simp add:  no_write_wrSet_empty_def)
  apply (simp add:  TMBegin_trans_def  write_wrSet_notEmpty_def)
  apply (simp add:  read_rdSet_notEmpty_def  TMBegin_trans_def )
  apply (simp add:  loc_in_wrSet_def tms_inv_def Begin_inv_def TMBegin_trans_def)
  apply (simp add: even_loc_wrSet_empty_def tms_inv_def Begin_inv_def )
  apply (simp add:  odd_loc_wrSet_notEmpty_def   tms_inv_def Begin_inv_def TMBegin_trans_def  )
  apply (metis PC.distinct(247) PC.distinct(307) PC.distinct(5) assms(1) assms(3) assms(6) tr_rel_Begin3_self_ST tr_rel_Begin3_stable_ST)
  apply (unfold read_prop_def total_wfs_def)
  by (metis fun_upd_apply)

(***********************resp(begin)***********************)


(*auxiliary lemma*)
lemma   tr_rel_BeginResponding_self_lp:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "  TML_Begin_response  ta cs  cs'  "
and "((pc cs) ta)  = PC.BeginResponding"
and "  Begin_Response_inv   ta  ((pc cs) ta) cs " 
and " f_sim cs as "
and"   tr_rel   cs as ta"
and " ta \<noteq> syst"
shows "  tr_rel cs' ( TMBegin_resp_trans  ta  as) ta "
  using assms
  by (simp add: TML_Begin_response_def tr_rel_def Begin_Response_inv_def TMBegin_resp_trans_def  validity_prop_def  split: if_splits )


(*auxiliary lemma*)
lemma   tr_rel_BeginResponding_stable_lp:
assumes  "thrdsvars"
and   "\<forall>t.  tms_inv as  t "
and "total_wfs (\<tau> cs) "
and "((pc cs) ta)  =PC.BeginResponding"
and "  Begin_Response_inv   ta  ((pc cs) ta) cs " 
and "   TML_Begin_response   ta cs  cs'  "
and " f_sim cs as "
and"   tr_rel   cs as t"
and " t \<noteq> ta "
and " ta \<noteq> syst"
shows "  tr_rel cs' ( TMBegin_resp_trans  ta  as) t "
  using assms
  apply (simp add: TML_Begin_response_def tr_rel_def  Begin_Response_inv_def  TMBegin_resp_trans_def split: if_splits )
  apply (unfold validity_prop_def  in_flight_def total_wfs_def  )
  apply (cases "pc cs t";  simp)
  apply metis
  apply metis
  apply (metis PC.distinct(1489) fun_upd_def)
  apply (metis PC.distinct(1491) fun_upd_def)
  by (metis PC.distinct(1493) fun_upd_def)



(*auxiliary lemma*)
lemma begin_beginResponding_logical_glb_ni:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and " TML_Begin_response  ta   cs cs'"
and "((pc cs) ta)  = PC.BeginResponding"
shows " logical_glb cs = logical_glb cs' "
  using assms
  apply (unfold total_wfs_def)
  apply (simp add: TML_Begin_response_def logical_glb_def)
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
  by (smt (z3) PC.distinct(315) PC.distinct(645) fun_upd_other fun_upd_same option.simps(5))



(*auxiliary lemma*)
lemma begin_beginResponding_writes_ni:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and " TML_Begin_response  ta   cs cs'"
and "((pc cs) ta)  =  PC.BeginResponding"
shows " writes cs as = writes  cs'  (TMBegin_resp_trans  ta  as) "
using assms
apply (unfold total_wfs_def)
apply (simp add: TML_Begin_response_def TMBegin_resp_trans_def logical_glb_def writes_def)
apply (cases "pc cs ta";  simp)
apply (cases " writer cs" )
apply simp
apply (intro conjI impI)
apply (cases " writer cs'" )
apply simp+
apply (cases " writer cs'" )
by  simp+




(*the simulation relation holds for resp(Begin) (linearization point) *)
lemma   f_sim_BeginResponding_lp:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "  TML_Begin_response   ta cs  cs'  "
and "((pc cs) ta)  =  PC.BeginResponding"
and " Begin_Response_inv ta  ((pc cs) ta) cs " 
and " f_sim  cs  as"
and   "\<forall>t.  tms_inv as  t "
and"pc cs  syst  = RecIdle "
and " ta \<noteq> syst"
shows "  \<exists> as'. tmstep ta  TMBeginResp  as  as'  \<and> f_sim  cs' as'  "
  using assms
  apply (unfold total_wfs_def)
  apply (simp add: TML_Begin_response_def Begin_Response_inv_def tmstep_def  f_sim_def)
  apply (subgoal_tac " memory ( \<tau>  cs) = memory( \<tau> cs' )")
  prefer 2
  apply presburger
  apply (cases "pc cs ta";  simp)
  apply (intro conjI)
  apply (simp add: global_rel_def)
  apply (intro conjI)
  apply (simp add: TMBegin_resp_trans_def  write_count_def) 
  apply (metis assms(1) assms(2) assms(3)  begin_beginResponding_logical_glb_ni)
  apply (simp add: maxIndex_def  TMBegin_resp_trans_def  ) 
  using    begin_beginResponding_writes_ni  TMBegin_resp_trans_def 
  using assms(1) assms(2) assms(3) apply presburger
  apply (simp add: maxIndex_def  TMRead_resp_trans_def apply_partial_def ) 
  apply (simp add: maxIndex_def  TMBegin_resp_trans_def apply_partial_def ) 
  apply (simp add:  TMBegin_resp_trans_def )
  apply (simp add: no_read_rdSet_empty_def  no_write_wrSet_empty_def write_wrSet_notEmpty_def odd_loc_wrSet_notEmpty_def  read_rdSet_notEmpty_def loc_in_wrSet_def even_loc_wrSet_empty_def TMBegin_resp_trans_def )
  apply (subgoal_tac " tpc as ta = TPC.BeginResponding")
  prefer 2
  apply (simp add: tr_rel_def)
  apply (smt (z3) PC.simps(1645))
    apply (intro conjI allI impI)
  apply (subgoal_tac " (as\<lparr>tpc := (tpc as)(ta := TPC.Ready)\<rparr>) =  (TMBegin_resp_trans  ta  as) ")
  prefer 2
  apply (simp add: TMBegin_resp_trans_def)
  apply (metis assms(1) assms(2) assms(3) assms(5) assms(6) tr_rel_BeginResponding_self_lp)
  apply (metis TMBegin_resp_trans_def assms(1) assms(2) assms(3) assms(5) assms(6) tr_rel_BeginResponding_stable_lp)
  apply blast
  apply linarith
  apply (unfold read_prop_def)
  by (simp add: maxIndex_def  TMBegin_resp_trans_def apply_partial_def ) 





end


