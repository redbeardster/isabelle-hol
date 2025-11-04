(*Showing that the simulation relation holds for the DTML Read operation*)

theory Ref_Read
imports "../Refinement"
begin

(*auxiliary lemma*)
lemma   tr_rel_Ready_self_lp:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "  TML_Read_invocation   ta cs  cs'  "
and "((pc cs) ta)  = PC.Ready"
and "  Read_invocation_inv   ta  ((pc cs) ta) cs " 
and " f_sim cs as "
and"   tr_rel   cs as ta"
and " ta \<noteq> syst"
shows "  tr_rel cs' (TMRead_inv_trans  ta  as) ta "
  using assms
  by (simp add: TML_Read_invocation_def tr_rel_def Read_invocation_inv_def TMRead_inv_trans_def  validity_prop_def  split: if_splits )


(*auxiliary lemma*)
lemma   tr_rel_Ready_stable_lp:
assumes  "thrdsvars"
and   "\<forall>t.  tms_inv as  t "
and "total_wfs (\<tau> cs) "
and "((pc cs) ta)  = PC.Ready"
and "  Read_invocation_inv   ta  ((pc cs) ta) cs " 
and "  TML_Read_invocation   ta cs  cs'  "
and " f_sim cs as "
and"   tr_rel   cs as t"
and " t \<noteq> ta "
and " ta \<noteq> syst"
shows "  tr_rel cs' (TMRead_inv_trans  ta  as) t "
  using assms
  apply (simp add: TML_Read_invocation_def tr_rel_def  Read_invocation_inv_def  TMRead_inv_trans_def split: if_splits )
  apply (unfold validity_prop_def  in_flight_def total_wfs_def  )
  apply (cases "pc cs t";  simp)
  apply metis
  apply metis
  apply (metis PC.distinct(1489) fun_upd_def)
  apply (metis PC.distinct(1491) fun_upd_def)
  by (metis PC.distinct(1493) fun_upd_def)

(*auxiliary lemma*)
lemma read_ready_logical_glb_ni:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and " TML_Read_invocation  ta   cs cs'"
and "((pc cs) ta)  = PC.Ready"
shows " logical_glb cs = logical_glb cs' "
  using assms
  apply (unfold total_wfs_def)
  apply (simp add: TML_Read_invocation_def logical_glb_def)
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
  by (smt (z3) PC.distinct(589) PC.distinct(645) fun_upd_other fun_upd_same option.simps(5))


(*auxiliary lemma*)
lemma read_ready_writes_ni:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and " TML_Read_invocation  ta   cs cs'"
and "((pc cs) ta)  = PC.Ready"
shows " writes cs as = writes  cs'  (TMRead_inv_trans  ta  as) "
  using assms
  apply (unfold total_wfs_def)
  apply (simp add: TML_Read_invocation_def TMRead_inv_trans_def logical_glb_def writes_def)
  apply (cases "pc cs ta";  simp)
  apply (cases " writer cs" )
  apply simp
  apply (intro conjI impI)
  apply (cases " writer cs'" )
  apply simp+
  apply (cases " writer cs'" )
  by simp+


(*the simulation relation holds for inv(Read) (non stuttering step) *)
lemma   f_sim_read_inv_ready_lp:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "  TML_Read_invocation   ta cs  cs'  "
and "((pc cs) ta)  = PC.Ready"
and " Read_invocation_inv ta  ((pc cs) ta) cs " 
and " f_sim  cs  as"
and   "\<forall>t.  tms_inv as  t "
and"pc cs  syst  = RecIdle "
and " ta \<noteq> syst"
shows " \<exists> as'. tmstep ta  TMReadInv  as  as'  \<and> f_sim  cs' as'  "
  using assms
  apply (unfold total_wfs_def)
  apply (simp add: TML_Read_invocation_def Read_invocation_inv_def tmstep_def f_sim_def)
  apply (subgoal_tac " memory ( \<tau>  cs) = memory( \<tau> cs' )")
  prefer 2
  apply presburger
  apply (cases "pc cs ta";  simp)
  apply (intro conjI)
  apply (simp add: global_rel_def)
  apply (intro conjI)
  apply (simp add: TMRead_inv_trans_def  write_count_def) 
  apply (metis assms(1) assms(2) assms(3) read_ready_logical_glb_ni)
  apply (simp add: maxIndex_def  TMRead_inv_trans_def  ) 
  using TMRead_inv_trans_def assms(2) assms(3) read_ready_writes_ni thrdsvars_def apply presburger
  apply (simp add: maxIndex_def  TMRead_inv_trans_def apply_partial_def ) 
  apply (simp add: maxIndex_def  TMRead_inv_trans_def apply_partial_def ) 
  apply (simp add:  TMRead_inv_trans_def )
  apply (simp add: no_read_rdSet_empty_def  no_write_wrSet_empty_def write_wrSet_notEmpty_def  odd_loc_wrSet_notEmpty_def read_rdSet_notEmpty_def loc_in_wrSet_def even_loc_wrSet_empty_def )
  apply (subgoal_tac " tpc as ta = TPC.Ready")
  prefer 2
  apply (simp add: tr_rel_def)
  apply (smt (z3) PC.simps(1680))
  apply simp
  apply (intro conjI allI impI)
  apply (metis TMRead_inv_trans_def assms(1) assms(2) assms(3) assms(5) assms(6) tr_rel_Ready_self_lp)
  using tr_rel_Ready_stable_lp [where as=as and cs=cs  and cs'=cs' and ta = ta] 
  apply (metis TMRead_inv_trans_def assms(1) assms(2) assms(3) assms(5) assms(6))
  apply (simp add:   TMRead_inv_trans_def)
  apply (unfold  read_prop_def)
  apply (subgoal_tac " tpc as ta = TPC.Ready")
  prefer 2
  apply (simp add: tr_rel_def)
  apply (smt (z3) PC.simps(1680))
  by simp

(*auxiliary lemma*)
lemma   tr_rel_ReadPending_self:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and " TML_Read  ta   cs cs'"
and "((pc cs) ta)  = PC.ReadPending"
and " Read_inv ta  ((pc cs) ta) cs " 
and " f_sim cs as "
and"   tr_rel   cs as ta"
and " ta \<noteq> syst"
shows "  tr_rel cs' as ta "
  using assms
  apply (simp add:TML_Read_def tr_rel_def Read_inv_def TMBegin_inv_trans_def  split: if_splits )
  apply (unfold validity_prop_def  in_flight_def read_consistent_def  total_wfs_def  )
  apply (subgoal_tac " memory (\<tau> cs) = memory (\<tau> cs' ) ")
  prefer 2
  apply presburger
  by presburger


(*auxiliary lemma*)
lemma   tr_rel_ReadPending_stable:
assumes  "thrdsvars"
and   "\<forall>t.  tms_inv as  t "
and "total_wfs (\<tau> cs) "
and " TML_Read  ta   cs cs'"
and "((pc cs) ta)  = PC.ReadPending"
and " Read_inv ta ((pc cs) ta) cs " 
and " f_sim cs as "
and"   tr_rel   cs as t"
and " t \<noteq> ta "
(* and  " pc cs  syst  = RecIdle \<longrightarrow> (\<forall>t.  (t \<noteq> syst  \<and> ((pc cs) t \<notin> {PC.NotStarted,PC.Aborted, PC.Committed,PC.Begin2   }) \<longrightarrow>   regs (\<tau> cs) t loc \<le> lastVal glb  (\<tau> cs) ))"*)
and " ta \<noteq> syst"
shows "  tr_rel cs' as  t"
  using assms
  apply (simp add:TML_Read_def tr_rel_def Read_inv_def  split: if_splits )
  apply (unfold validity_prop_def  in_flight_def read_consistent_def  total_wfs_def  )
  apply (subgoal_tac " memory (\<tau> cs) = memory (\<tau> cs' ) ")
  prefer 2
  apply (metis ld_step_mem)
  apply (cases "pc cs t";  simp)
  apply (metis reg_same_ld_dt)
  apply (metis reg_same_ld_dt)
  apply (metis reg_same_ld_dt)
  apply (metis reg_same_ld_dt)
  apply (metis reg_same_ld_dt)
  apply (simp add: f_sim_def write_count_def)
  apply(simp add: no_write_wrSet_empty_def write_wrSet_notEmpty_def)
  apply (intro conjI impI)
  apply ( elim disjE conjE)
  apply (metis assms(3) lastVal_ni)  apply (smt (z3) assms(3) case_optionE lastVal_ni option.simps(4) option.simps(5) reg_same_ld_dr)
  apply (metis assms(3) lastVal_ni reg_same_ld_dt)
  apply (metis assms(3) lastVal_ni reg_same_ld_dt)
  apply (metis assms(3) lastVal_ni reg_same_ld_dt)
  apply (metis assms(3) lastVal_ni reg_same_ld_dt)
  apply (metis assms(3) lastVal_ni reg_same_ld_dt)
  apply (subgoal_tac"(regs (\<tau> cs') t loc) = (regs (\<tau> cs) t loc)")
  prefer 2
  apply (metis reg_same_ld_dt)
  apply metis
  apply (metis reg_same_ld_dt)
  apply (metis reg_same_ld_dt)
  apply (metis reg_same_ld_dt)
  apply (metis reg_same_ld_dt)
  apply (metis assms(3) lastVal_ni reg_same_ld_dt)
  using  reg_same_ld_dt   apply metis
  using  reg_same_ld_dt   apply metis
  using  reg_same_ld_dt   
  apply (metis assms(3) lastVal_ni)
  using  reg_same_ld_dt     apply metis
  apply presburger+
  apply blast+
  by presburger



lemma read_ReadPending_logical_glb_ni:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and " TML_Read  ta   cs cs'"
and "((pc cs) ta)  = PC.ReadPending"
shows " logical_glb cs = logical_glb cs' "
  using assms
  apply (unfold total_wfs_def)
  apply (simp add: TML_Read_def logical_glb_def)
  apply (cases "pc cs ta";  simp)
  apply (subgoal_tac "  lastVal glb (\<tau> cs) =  lastVal glb (\<tau> cs') ")
  prefer 2
  apply (metis assms(2) lastVal_ni)
  apply (subgoal_tac "  recoveredGlb cs' =  recoveredGlb cs ")
  prefer 2
  apply presburger
  apply (cases " writer cs" )
  apply simp
  apply (simp add:  split if_splits )
  by (smt (verit) PC.distinct(589) PC.distinct(591) fun_upd_other fun_upd_same option.simps(5))



(*auxiliary lemma*)
lemma read_ReadPending_writes_ni:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and " TML_Read  ta   cs cs'"
and "((pc cs) ta)  = PC.ReadPending"
shows " writes cs as = writes  cs' as "
  using assms
  apply (unfold total_wfs_def)
  apply (simp add: TML_Read_def logical_glb_def writes_def)
  apply (cases "pc cs ta";  simp)
  apply (cases " writer cs" )
  apply simp
  by (metis PC.distinct(589) PC.distinct(591) fun_upd_apply)


(*the simulation relation holds from ReadPending to Read1 (stuttering step) *)
lemma   f_sim_read_ready_stuttering:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and " TML_Read  ta   cs cs'"
and "((pc cs) ta)  = PC.ReadPending"
and " Read_inv ta  ((pc cs) ta) cs " 
and " f_sim  cs  as"
and   "\<forall>t.  tms_inv as  t "
and"pc cs  syst  = RecIdle "
and " ta \<noteq> syst"
shows " f_sim  cs' as  "
  using assms
  apply (unfold total_wfs_def)
  apply (simp add: TML_Read_def Read_inv_def  f_sim_def)
  apply (cases "pc cs ta";  simp)
  apply (intro conjI)
  apply (simp add: global_rel_def)
  apply (intro conjI allI impI)
  apply (metis assms(1) assms(2) assms(3) read_ReadPending_logical_glb_ni)
  using assms(1) assms(2) assms(3) read_ReadPending_writes_ni apply presburger
  apply (subgoal_tac "\<forall>t.  tr_rel cs' as t ")
  prefer 2
  apply clarify
  apply (case_tac " t = ta ")
  apply (metis assms(1) assms(2) assms(3) assms(5) f_sim_def tr_rel_ReadPending_self)
  using tr_rel_ReadPending_stable [where as=as and cs=cs  and cs'=cs' ] 
  apply (metis assms(1)  assms(2) assms(3) assms(5) f_sim_def)
  apply (simp add: no_read_rdSet_empty_def  odd_loc_wrSet_notEmpty_def  no_write_wrSet_empty_def write_wrSet_notEmpty_def  read_rdSet_notEmpty_def loc_in_wrSet_def even_loc_wrSet_empty_def )
  apply (unfold  read_prop_def)
  by presburger


(*auxiliary lemma*)
lemma   tr_rel_Read1_self:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and " TML_Read  ta   cs cs'"
and "((pc cs) ta)  = PC.Read1"
and " Read_inv ta  ((pc cs) ta) cs " 
and " f_sim cs as "
and"   tr_rel   cs as ta"
and " ta \<noteq> syst"
and   " \<forall>  t.  (  writer cs = Some t \<longrightarrow> odd (lastVal glb  (\<tau> cs)) )"
shows " tr_rel cs' as  ta"
  using assms
  apply (simp add:TML_Read_def tr_rel_def Read_inv_def  split: if_splits )
  apply (unfold validity_prop_def  in_flight_def read_consistent_def  total_wfs_def  )
  apply (subgoal_tac " memory (\<tau> cs) = memory (\<tau> cs' ) ")
  prefer 2
  apply (metis ld_step_mem)
  apply (unfold Ready_total_def)
  apply (cases "pc cs ta";simp )
  apply (intro conjI impI)
  apply (metis assms(2) lastVal_ni reg_same_ld_dt)
  apply (metis assms(2) lastVal_ni reg_same_ld_dt)
  apply (simp add: f_sim_def )
  apply(simp add: no_write_wrSet_empty_def)
  using  reg_same_ld_dt
  apply (metis PC.distinct(23) PC.distinct(713) PC.distinct(883))
  apply (metis reg_same_ld_dt)
  apply (metis reg_same_ld_dt)
  apply (simp add: f_sim_def )
  apply(simp add: no_write_wrSet_empty_def write_wrSet_notEmpty_def)
  apply (metis PC.distinct(101) PC.distinct(23) PC.distinct(713) PC.distinct(845) PC.distinct(847) PC.distinct(849) PC.distinct(851) PC.distinct(853) PC.distinct(883) reg_same_ld_dt)
  apply (metis reg_same_ld_dt)
  apply (metis reg_same_ld_dt)
  apply (simp add: f_sim_def )
  apply(simp add: no_write_wrSet_empty_def write_wrSet_notEmpty_def)
  by (metis reg_same_ld_dt)


(*auxiliary lemma*)
lemma   tr_rel_Read1_stable:
assumes  "thrdsvars"
and   "\<forall>t.  tms_inv as  t "
and "total_wfs (\<tau> cs) "
and " TML_Read  ta   cs cs'"
and "((pc cs) ta)  = PC.Read1"
and " Read_inv ta ((pc cs) ta) cs " 
and " f_sim cs as "
and"   tr_rel   cs as t"
and " t \<noteq> ta "
and " ta \<noteq> syst"
shows "  tr_rel cs' as  t"
  using assms
  apply (simp add:TML_Read_def tr_rel_def Read_inv_def  split: if_splits )
  apply (unfold validity_prop_def  in_flight_def read_consistent_def  total_wfs_def Ready_total_def  )
  apply (subgoal_tac " memory (\<tau> cs) = memory (\<tau> cs' ) ")
  prefer 2
  apply (metis ld_step_mem)
  apply (cases "pc cs t";  simp)
  apply (metis reg_same_ld_dt)
  apply (metis reg_same_ld_dt)
  apply (metis reg_same_ld_dt)
  apply (metis reg_same_ld_dt)
  apply (simp add: f_sim_def write_count_def)
  apply(simp add: no_write_wrSet_empty_def write_wrSet_notEmpty_def)
  apply (intro conjI impI)
  apply ( elim disjE conjE)
  apply (metis assms(3) lastVal_ni)  apply (smt (z3) assms(3) case_optionE lastVal_ni option.simps(4) option.simps(5) reg_same_ld_dr)
  apply blast
  apply blast
  apply blast
  apply blast
  apply blast
  apply blast
  apply blast
  apply blast
  apply blast
  apply (simp add: write_count_def)
  apply (metis assms(3) lastVal_ni reg_same_ld_dt)
  apply (metis assms(3) lastVal_ni reg_same_ld_dt)
  apply (metis assms(3) lastVal_ni reg_same_ld_dt)
  apply (metis assms(3) lastVal_ni reg_same_ld_dt)
  apply (metis assms(3) lastVal_ni reg_same_ld_dt)
  apply (metis assms(3) lastVal_ni reg_same_ld_dr)
  apply (subgoal_tac"(regs (\<tau> cs') t loc) = (regs (\<tau> cs) t loc)")
  prefer 2
  apply (metis reg_same_ld_dt)
  apply metis
  apply (metis reg_same_ld_dt)
  apply (metis reg_same_ld_dt)
  apply (metis reg_same_ld_dt)
  apply (subgoal_tac"(regs (\<tau> cs') t loc) = (regs (\<tau> cs) t loc)")
  prefer 2
  apply (metis reg_same_ld_dt)
  apply (metis assms(3) lastVal_ni)
  apply (simp add: write_count_def)
  apply (metis reg_same_ld_dr)
  apply (metis reg_same_ld_dt)
  apply (simp add: write_count_def)
  apply (subgoal_tac " lastVal glb (\<tau> cs') = lastVal glb (\<tau> cs) ")
  prefer 2
  apply (metis assms(3) lastVal_ni)
  using  reg_same_ld_dt 
  apply metis
  apply (simp add: write_count_def)
  apply (subgoal_tac " lastVal glb (\<tau> cs') = lastVal glb (\<tau> cs) ")
  prefer 2
  apply (metis assms(3) lastVal_ni)
  using  reg_same_ld_dt 
  apply metis
  apply (simp add: write_count_def)
  apply (intro conjI)
  using  reg_same_ld_dt    
  apply (metis assms(3) lastVal_ni)
  using  reg_same_ld_dt    
  apply metis
  apply (metis assms(9) reg_same_ld_dr write_count_def)
  apply (metis assms(3) lastVal_ni reg_same_ld_dt)
  using  reg_same_ld_dt   apply metis
  using  reg_same_ld_dt   apply metis
  using  reg_same_ld_dt   
  apply (intro conjI)
  using  reg_same_ld_dt    
  apply (metis assms(3) lastVal_ni)
  using  reg_same_ld_dt    
  apply metis
  using  reg_same_ld_dt     apply metis
  apply (simp add: write_count_def)
  apply (subgoal_tac " lastVal glb (\<tau> cs') = lastVal glb (\<tau> cs) ")
  prefer 2
  apply (metis assms(3) lastVal_ni)
  using  reg_same_ld_dt 
  apply (metis reg_same_ld_dr)
  apply (simp add: write_count_def)
  apply (intro conjI)
  using  reg_same_ld_dt    
  apply (metis assms(3) lastVal_ni)
  using  reg_same_ld_dt    
  apply metis
  apply (metis assms(9) reg_same_ld_dr write_count_def)
  apply (simp add: write_count_def)
  apply (intro conjI)
  using  reg_same_ld_dt    
  apply (metis assms(3) lastVal_ni)
  using  reg_same_ld_dt    
  apply metis
  apply (metis assms(9) reg_same_ld_dr write_count_def)
  apply (simp add: write_count_def)
  apply (metis assms(3) lastVal_ni reg_same_ld_dr)
  apply (metis reg_same_ld_dt)
  apply (simp add: write_count_def)
  apply (metis reg_same_ld_dr)
  apply (simp add: write_count_def)
  apply (metis reg_same_ld_dr)
  apply (simp add: write_count_def)
  apply (intro conjI)
  using  reg_same_ld_dt    
  apply metis
  using  reg_same_ld_dt    
  apply metis
  apply (metis assms(9) reg_same_ld_dr )
  apply (metis reg_same_ld_dt)
  apply (simp add: write_count_def)
  apply (intro conjI)
  apply (metis assms(3) lastVal_ni reg_same_ld_dr)
  apply (metis reg_same_ld_dt)
  apply (metis assms(9) reg_same_ld_dr)
  apply (simp add: write_count_def)
  apply (intro conjI)
  apply (metis assms(3) lastVal_ni reg_same_ld_dr)
  apply (metis reg_same_ld_dr)
  by (metis reg_same_ld_dr)



(*auxiliary lemma*)
lemma read_read1_logical_glb_ni:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and " TML_Read  ta   cs cs'"
and "((pc cs) ta)  = PC.Read1"
shows " logical_glb cs = logical_glb cs' "
  using assms
  apply (unfold total_wfs_def)
  apply (simp add: TML_Read_def logical_glb_def)
  apply (cases "pc cs ta";  simp)
  apply (subgoal_tac "  lastVal glb (\<tau> cs) =  lastVal glb (\<tau> cs') ")
  prefer 2
  apply (metis assms(2) lastVal_ni)
  apply (subgoal_tac "  recoveredGlb cs' =  recoveredGlb cs ")
  prefer 2
  apply presburger
  apply (cases " writer cs" )
  apply simp
  apply (simp add:  split if_splits )
  by (smt (z3) PC.distinct(591) PC.distinct(593) fun_upd_other fun_upd_same option.simps(5))


(*auxiliary lemma*)
lemma read_read1_writes_ni:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and " TML_Read  ta   cs cs'"
and "((pc cs) ta)  = PC.Read1"
shows " writes cs as = writes  cs' as "
  using assms
  apply (unfold total_wfs_def)
  apply (simp add: TML_Read_def logical_glb_def writes_def)
  apply (cases "pc cs ta";  simp)
  apply (cases " writer cs" )
  apply simp
  by (metis PC.distinct(591) PC.distinct(593) fun_upd_apply)


(*the simulation relation holds from ReadPending to Read2  (stuttering step) *)
lemma   f_sim_read_read1_stuttering:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and " TML_Read  ta   cs cs'"
and "((pc cs) ta)  = PC.Read1"
and " Read_inv ta  ((pc cs) ta) cs " 
and " f_sim  cs  as"
and   "\<forall>t.  tms_inv as  t "
and"pc cs  syst  = RecIdle "
and " ta \<noteq> syst"
and   " \<forall>  t.  (  writer cs = Some t \<longrightarrow> odd (lastVal glb  (\<tau> cs)) )"
shows " f_sim  cs' as  "
  using assms
  apply (unfold total_wfs_def)
  apply (simp add: TML_Read_def Read_inv_def  f_sim_def)
  apply (cases "pc cs ta";  simp)
  apply (intro conjI)
  apply (simp add: global_rel_def)
  apply (intro conjI allI impI)
  apply (metis assms(1) assms(2) assms(3) read_read1_logical_glb_ni)
  apply (metis assms(1) assms(2) assms(3) lastVal_ni read_read1_writes_ni)
  apply (metis assms(2) lastVal_ni)
  apply (metis option.distinct(1))
  apply (subgoal_tac "\<forall>t.  tr_rel cs' as t ")
  prefer 2
  apply clarify
  apply (case_tac " t = ta ")
  apply (metis assms(1) assms(2) assms(3) assms(5) assms(6) tr_rel_Read1_self)
  using tr_rel_Read1_stable [where as=as and cs=cs  and cs'=cs' ] 
  apply (metis assms(1) assms(10) assms(2) assms(3) assms(5) assms(6))
  apply (simp add: no_read_rdSet_empty_def  no_write_wrSet_empty_def write_wrSet_notEmpty_def  odd_loc_wrSet_notEmpty_def read_rdSet_notEmpty_def even_loc_wrSet_empty_def loc_in_wrSet_def )
  apply (smt (verit) PC.distinct(101) PC.distinct(177) PC.distinct(23) PC.distinct(251) PC.distinct(713) PC.distinct(845) PC.distinct(847) PC.distinct(849) PC.distinct(851) PC.distinct(853) PC.distinct(883) assms(2) lastVal_ni reg_same_ld_dt)
  apply (unfold  read_prop_def)
  by (metis (no_types, lifting) assms(2) bot_nat_0.extremum last_entry_lim_bounded ld_le_lim_ni ld_step_mem ld_valOf_nle_ni)


(***********************************************************************************)


(*auxiliary lemma*)
lemma   tr_rel_Read2_self:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and " TML_Read  ta   cs cs'"
and "((pc cs) ta)  = PC.Read2"
and " Read_inv ta ((pc cs) ta) cs " 
and " f_sim cs as "
and"   tr_rel   cs as ta"
and " ta \<noteq> syst"
shows " tr_rel cs' as  ta"
  using assms
  apply (simp add:TML_Read_def tr_rel_def Read_inv_def  split: if_splits )
  apply (unfold validity_prop_def  in_flight_def read_consistent_def  total_wfs_def  )
  apply (subgoal_tac " memory (\<tau> cs) = memory (\<tau> cs' ) ")
  prefer 2
  apply (metis ld_step_mem)
  apply (cases "pc cs ta";  simp)
  apply (intro conjI impI)
  apply metis
  apply (simp add: f_sim_def)
  apply(simp add: no_read_rdSet_empty_def)
  using PC.distinct(25) PC.distinct(715) PC.distinct(937) apply presburger
  by metis



(*auxiliary lemma*)
lemma   tr_rel_Read2_stable:
assumes  "thrdsvars"
and   "\<forall>t.  tms_inv as  t "
and "total_wfs (\<tau> cs) "
and " TML_Read  ta   cs cs'"
and "((pc cs) ta)  = PC.Read2"
and " Read_inv ta  ((pc cs) ta) cs " 
and " f_sim cs as "
and"   tr_rel   cs as t"
and " t \<noteq> ta "
  shows "  tr_rel cs' as  t"
  using assms
  apply (simp add:TML_Read_def tr_rel_def Read_inv_def  split: if_splits )
  apply (unfold validity_prop_def  in_flight_def read_consistent_def  total_wfs_def  )
  apply (cases "pc cs t";  simp)
  by  metis+


(*auxiliary lemma*)
lemma read_read2_logical_glb_ni:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and " TML_Read  ta   cs cs'"
and "((pc cs) ta)  = PC.Read2"
shows " logical_glb cs = logical_glb cs' "
  using assms
  apply (unfold total_wfs_def)
  apply (simp add: TML_Read_def logical_glb_def)
  apply (cases "pc cs ta";  simp)
  apply ( simp add: split: if_split_asm)
  apply (cases " writer cs" )
  apply simp
  apply simp
  apply (smt (z3) PC.distinct(593) PC.distinct(595) fun_upd_other fun_upd_same option.simps(5))
  apply (cases " writer cs" )
  apply simp
  apply simp
  by (smt (verit) PC.distinct(593) PC.distinct(597) fun_upd_other fun_upd_same option.simps(5))



(*auxiliary lemma*)
lemma read_read2_writes_ni:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and " TML_Read  ta   cs cs'"
and "((pc cs) ta)  = PC.Read2"
shows " writes cs as = writes  cs' as "
  using assms
  apply (unfold total_wfs_def)
  apply (simp add: TML_Read_def logical_glb_def writes_def)
  apply ( simp add: split: if_split_asm)
  apply (metis PC.distinct(593) PC.distinct(595) fun_upd_apply)
  by (metis PC.distinct(593) PC.distinct(597) fun_upd_apply)




(*the simulation relation holds from Read2 to Read3 and from Read2 to Read5 (stuttering steps) *)
lemma   f_sim_read_Read2_stuttering:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and " TML_Read  ta   cs cs'"
and "((pc cs) ta)  = PC.Read2"
and " Read_inv ta  ((pc cs) ta) cs " 
and " f_sim  cs  as"
and   "\<forall>t.  tms_inv as  t "
and"pc cs  syst  = RecIdle "
and " ta \<noteq> syst"
shows " f_sim  cs' as  "
  using assms
  apply (unfold total_wfs_def)
  apply (simp add: TML_Read_def Read_inv_def  f_sim_def)
  apply (cases "pc cs ta";  simp)
  apply (intro conjI)
  apply (simp add: global_rel_def)
  apply (intro conjI impI)
  apply ( simp add: split: if_split_asm)
  apply (simp add: write_count_def)
  apply (metis assms(1) assms(2) assms(3) read_read2_logical_glb_ni)
  apply (metis assms(1) assms(2) assms(3) read_read2_logical_glb_ni)
  using assms(2) assms(3) read_read2_writes_ni thrdsvars_def apply presburger
  apply (metis option.distinct(1))
  apply ( simp add: split: if_split_asm)
  apply (subgoal_tac "\<forall>t.  tr_rel cs' as t ")
  prefer 2
  apply clarify
  apply (case_tac " t = ta ")
  using assms(1) assms(2) assms(3) assms(5) assms(6) tr_rel_Read2_self apply presburger
  using tr_rel_Read2_stable [where as=as and cs=cs  and cs'=cs' ]
  using assms(1) assms(2) assms(3) assms(5) assms(6) assms(9) apply presburger
  apply (simp add: no_read_rdSet_empty_def  odd_loc_wrSet_notEmpty_def  no_write_wrSet_empty_def write_wrSet_notEmpty_def  read_rdSet_notEmpty_def  even_loc_wrSet_empty_def loc_in_wrSet_def )
  apply ( simp add: split: if_split_asm)
  apply blast
  apply (unfold  read_prop_def)
  by presburger


(************************************************************************)


lemma   read_as_length_ni:
assumes" as' =  TMRead_trans ta   (inLoc cs t)(write_count (regs (\<tau> cs) t  DTML.loc - recoveredGlb  cs ))  as  "
shows"   length (tmemory as') =   length (tmemory as) "
using assms
by (simp add: TMRead_trans_def)

lemma   read_as_beginIndex_ni:
assumes" as' =  TMRead_trans ta   (inLoc cs t)  (write_count (regs (\<tau> cs) t  DTML.loc - recoveredGlb  cs ))  as  "
shows"   beginIndex as' t  =    beginIndex as t  "
using assms
by (simp add: TMRead_trans_def)


(*auxiliary lemma*)
lemma   read3_writecount_ni:  
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and " TML_Read  ta   cs cs'"
and "((pc cs) ta)  = PC.Read3"
and " Read_inv ta  ((pc cs) ta) cs " 
shows"   (write_count (regs (\<tau> cs) t  DTML.loc - recoveredGlb  cs )) =  (write_count (regs (\<tau> cs') t  DTML.loc - recoveredGlb  cs' )) "
  using assms
  apply (unfold total_wfs_def)
  apply (simp add:TML_Read_def   Read_inv_def write_count_def   split: if_splits )
  apply (cases "pc cs ta";  simp)
  apply (metis reg_same_CAS_dr reg_same_CAS_dt)
  by (metis reg_same_CAS_dr reg_same_CAS_dt)



(*auxiliary lemma*)
lemma   read3_logicalglb_ni:  
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and " TML_Read  ta   cs cs'"
and "((pc cs) ta)  = PC.Read3"
and " Read_inv ta  ((pc cs) ta) cs " 
shows"   logical_glb cs = logical_glb cs' "
  using assms
  apply (unfold total_wfs_def)
  apply (simp add:TML_Read_def   Read_inv_def logical_glb_def   split: if_splits )
  apply (cases "pc cs ta";  simp)
  apply (subgoal_tac "  lastVal glb (\<tau> cs) =  lastVal glb (\<tau> cs') ")
  prefer 2
  apply (metis cas_lc cas_nlv_lc lastVal_def numeral_1_eq_Suc_0 numeral_eq_one_iff zero_neq_one)
  apply (cases"  writer cs' ")
  apply simp
  apply simp
  apply (cases"  writer cs' ")
  apply simp
  apply (metis cas_fail_lv_ni cas_possible_lv_lc lastVal_def)
  apply simp
  by (metis (mono_tags, opaque_lifting) cas_fail_lv_ni cas_possible_lv_lc lastVal_def)

(*auxiliary lemma*)
lemma   read3_writes_ni:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and " TML_Read  ta   cs cs'"
and "((pc cs) ta)  = PC.Read3"
and " Read_inv ta  ((pc cs) ta) cs " 
and " f_sim  cs  as"
and" as' =  TMRead_trans ta   (inLoc cs ta)  (write_count (regs (\<tau> cs) ta  DTML.loc - recoveredGlb  cs ))  as  "
shows"   writes cs as  = writes cs' as' "
  using assms
  apply (unfold total_wfs_def)
  apply (simp add:TML_Read_def   Read_inv_def  split: if_splits )
  apply (cases "pc cs ta";  simp)
  apply (subgoal_tac"  wrSet  as = wrSet as' ")
  prefer 2
  apply (simp add: TMRead_trans_def)
  apply (cases " writer cs")
  apply (simp add:  writes_def )
  apply (case_tac "  pc cs ( the (writer cs))  = Commit4 ") 
  apply (subgoal_tac "  writes cs as = Map.empty ")
  prefer 2
  apply (simp add: writes_def)
  apply (smt (z3) option.sel option.simps(5))
  apply (subgoal_tac "  writes cs' as' = Map.empty ")
  prefer 2
  apply (subgoal_tac "  pc cs' ( the (writer cs'))  = Commit4  ")
  prefer 2
  using pc_aux   
  apply (metis option.sel update_def)
  apply (unfold  writes_def)
  apply (metis option.sel option.simps(5))
  apply presburger
  apply (subgoal_tac " writes cs as =   wrSet as (the (writer cs)) ")
  prefer 2
    apply (unfold  writes_def)
  apply (smt (z3) option.sel option.simps(5))
  apply (subgoal_tac "  writes cs' as' =  wrSet as' (the (writer cs')) ")
  prefer 2
  apply (subgoal_tac "  pc cs' ( the (writer cs'))  \<noteq> Commit4  ")
  prefer 2
  using update_def apply simp
  apply (unfold  writes_def)
  apply (smt (z3) option.sel option.simps(5))
  apply presburger
  apply (subgoal_tac"  wrSet  as = wrSet as' ")
  prefer 2
  apply (simp add: TMRead_trans_def)
  apply (cases " writer cs")
  apply (simp add:  writes_def )
  apply (case_tac "  pc cs ( the (writer cs))  = Commit4 ") 
  apply (subgoal_tac "  writes cs as = Map.empty ")
  prefer 2
  apply (simp add: writes_def)
  apply (smt (z3) option.sel option.simps(5))
  apply (subgoal_tac "  writes cs' as' = Map.empty ")
  prefer 2
  apply (subgoal_tac "  pc cs' ( the (writer cs'))  = Commit4  ")
  prefer 2
  using pc_aux   
  apply (metis option.sel update_def)
  apply (unfold  writes_def)
  apply (metis option.sel option.simps(5))
  apply presburger
  apply (subgoal_tac " writes cs as =   wrSet as (the (writer cs)) ")
  prefer 2
  apply (unfold  writes_def)
  apply (smt (z3) option.sel option.simps(5))
  apply (subgoal_tac "  writes cs' as' =  wrSet as' (the (writer cs')) ")
  prefer 2
  apply (subgoal_tac "  pc cs' ( the (writer cs'))  \<noteq> Commit4  ")
  prefer 2
  using update_def apply simp
  apply (unfold  writes_def)
  apply (smt (z3) option.sel option.simps(5))
  by  presburger


(*auxiliary lemma*)
lemma   read3_read_consistent_ni:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and " TML_Read  ta  cs cs'"
and "((pc cs) ta)  = PC.Read3"
and " Read_inv ta  ((pc cs) ta) cs " 
and " f_sim  cs  as"
and " t \<noteq> ta "
and " ((read_consistent ( (tmemory  as)! (write_count (regs (\<tau> cs) t  DTML.loc - recoveredGlb  cs ))) (rdSet  as t)))   "
shows  " ((read_consistent ( (tmemory   (TMRead_trans ta   (inLoc cs ta)  (write_count (regs (\<tau> cs) ta  DTML.loc - recoveredGlb  cs ))  as) )! (write_count (regs (\<tau> cs') t  DTML.loc - recoveredGlb  cs' ))) (rdSet   (TMRead_trans ta   (inLoc cs ta)  (write_count (regs (\<tau> cs) ta  DTML.loc - recoveredGlb  cs ))  as)  t))) "
  using assms
  apply (unfold total_wfs_def)
  apply (subgoal_tac " rdSet  as t  = rdSet   (TMRead_trans ta   (inLoc cs ta)  (write_count (regs (\<tau> cs) ta  DTML.loc - recoveredGlb  cs ))  as)  t ")
  prefer 2
  apply (simp add:  TMRead_trans_def)
  apply (subgoal_tac "    (write_count (regs (\<tau> cs) t  DTML.loc - recoveredGlb  cs )) =  (write_count (regs (\<tau> cs') t  DTML.loc - recoveredGlb  cs' )) "
      )
  prefer 2
  using  read3_writecount_ni [where cs = cs and cs' = cs' and t =t and ta = ta ]
  using assms(2) apply blast
  apply (subgoal_tac " tmemory   (TMRead_trans ta   (inLoc cs ta)  (write_count (regs (\<tau> cs) ta  DTML.loc - recoveredGlb  cs ))  as)  = tmemory  as ")
  prefer 2
  apply (simp add:  TMRead_trans_def)
  by(simp add:TML_Read_def   Read_inv_def  read_consistent_def   split: if_splits )






(*auxiliary lemma*)
lemma   ready3_ready_valid_loc:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and " TML_Read  ta   cs cs'"
and "((pc cs) ta)  = PC.Read3"
and "((pc cs') ta)  = PC.ReadResponding"
and " Read_inv ta  ((pc cs) ta) cs " 
and " f_sim  cs  as"
and   "\<forall>t.  tms_inv as  t "
and  " pc cs  syst  = RecIdle \<longrightarrow> (\<forall>t.  (t \<noteq> syst  \<and> ((pc cs) t \<notin> {PC.NotStarted, PC.Committed,PC.Begin2,PC.BeginPending ,PC.Aborted   }) \<longrightarrow>   regs (\<tau> cs) t loc \<le> lastVal glb  (\<tau> cs) ))"
and "pc cs  syst  = RecIdle  \<longrightarrow> ( lastVal glb (\<tau> cs)  \<ge>recoveredGlb cs ) " 
and   " \<forall>  t.  ( writer cs  = Some t \<longrightarrow> odd (lastVal glb  (\<tau> cs )) )"
and "tmemory as \<noteq> [] "
shows "   validIndex as ta (write_count (regs (\<tau> cs) ta DTML.loc - recoveredGlb cs))"
  using assms
  apply (unfold  total_wfs_def)
  apply (simp add:TML_Read_def   Read_inv_def   split: if_splits )
  apply (cases "pc cs ta";  simp)
  apply (simp add:   validIndex_def f_sim_def)
  apply (subgoal_tac "   tpc as ta = TPC.ReadPending \<and>
(even (lastVal glb (\<tau> cs)) \<and> regs (\<tau> cs) ta DTML.loc = lastVal glb (\<tau> cs) \<longrightarrow>
in_flight cs as ta) \<and>
rdSet as ta = Map.empty")
  prefer 2
  apply (subgoal_tac "  tr_rel cs as ta")
  prefer 2
  apply presburger
  apply (simp add: tr_rel_def  )
  apply (subgoal_tac "  in_flight cs as ta ")
  prefer 2
  apply (metis cas_fail_diff_lv numeral_1_eq_Suc_0 one_eq_numeral_iff zero_neq_one)
  apply (unfold in_flight_def validity_prop_def)
  apply (intro conjI)
  apply (simp add: global_rel_def)
  apply (subgoal_tac "  writer cs' = None")
  prefer 2 
  apply (metis cas_fail_diff_lv not_None_eq numeral_1_eq_Suc_0 numeral_eq_one_iff zero_neq_one)
  apply (simp add: global_rel_def maxIndex_def  logical_glb_def write_count_def)
  apply (metis Suc_pred cas_fail_diff_lv length_greater_0_conv lessI n_not_Suc_n)
  by presburger

(*auxiliary lemma*)
lemma   read3_validity_prop_ni:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and " TML_Read  ta  cs cs'"
and "((pc cs) ta)  = PC.Read3"
and " Read_inv ta  ((pc cs) ta) cs " 
and " f_sim  cs  as"
and " t \<noteq> ta "
and "  validity_prop  cs as t    "
shows  "  validity_prop  cs'  (TMRead_trans  ta   (inLoc cs ta) (write_count (regs (\<tau> cs) ta DTML.loc - recoveredGlb cs))     as) t   "
  using assms
  apply (unfold total_wfs_def validity_prop_def)
  apply (intro conjI impI)
  using assms(2) read3_read_consistent_ni [where cs = cs and as = as and t = t and cs' = cs' and ta = ta ] 
  apply blast
  apply (simp add: write_count_def TMRead_trans_def)
  by (metis assms(1) assms(2) read3_writecount_ni write_count_def)

(*auxiliary lemma*)
lemma   read3_in_flight_ni:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and " TML_Read  ta  cs cs'"
and "((pc cs) ta)  = PC.Read3"
and " Read_inv ta  ((pc cs) ta) cs " 
and " f_sim  cs  as"
and " t \<noteq> ta "
and "   in_flight  cs as t    "
shows  "  in_flight  cs'  (TMRead_trans  ta   (inLoc cs ta) (write_count (regs (\<tau> cs) ta DTML.loc - recoveredGlb cs))     as) t     "
  using assms
  apply (unfold  in_flight_def)
  apply (intro conjI impI)
  using  read3_validity_prop_ni  [where cs = cs and as = as and t = t and cs' = cs' and ta = ta ]
  apply blast
  apply  (simp add:  TMRead_trans_def  Read_inv_def TML_Read_def  f_sim_def )
  apply (intro conjI impI)
  apply (metis reg_same_CAS_dt)
  by (metis reg_same_CAS_dt)



(*auxiliary lemma*)
lemma   ready3_ready_readset:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and " TML_Read  ta   cs cs'"
and "((pc cs) ta)  = PC.Read3"
and "((pc cs') ta)  = PC.ReadResponding"
and " Read_inv ta  ((pc cs) ta) cs " 
and " f_sim  cs  as"
and   "\<forall>t.  tms_inv as  t "
and  " pc cs  syst  = RecIdle \<longrightarrow> (\<forall>t.  (t \<noteq> syst  \<and> ((pc cs) t \<notin> {PC.NotStarted, PC.Committed,PC.Begin2,PC.BeginPending , PC.Aborted  }) \<longrightarrow>   regs (\<tau> cs) t loc \<le> lastVal glb  (\<tau> cs) ))"
and "pc cs  syst  = RecIdle  \<longrightarrow> ( lastVal glb (\<tau> cs)  \<ge>recoveredGlb cs ) " 
and   " \<forall>  t.  ( writer cs  = Some t \<longrightarrow> odd (lastVal glb  (\<tau> cs )) )"
and "tmemory as \<noteq> [] "
and " ta \<noteq> syst"
shows "  rdSet (TMRead_trans ta   (inLoc cs ta)  (write_count (regs (\<tau> cs) ta  DTML.loc - recoveredGlb  cs ))  as) ta =   
(rdSet as ta)( (inLoc cs ta) \<mapsto> ((tmemory as!  (write_count (regs (\<tau> cs) ta  DTML.loc - recoveredGlb  cs )))  (inLoc cs ta)))"
  using assms
  apply (subgoal_tac "  validIndex as ta (write_count (regs (\<tau> cs) ta DTML.loc - recoveredGlb cs))")
  prefer 2
  using ready3_ready_valid_loc[where cs =cs and as= as  and cs' = cs']
  apply fastforce
  apply (simp add: TMRead_trans_def Read_inv_def TML_Read_def)
  apply (subgoal_tac " wrSet as ta = Map.empty ")
  prefer 2
  apply ( simp add: split: if_split_asm)
  apply (simp add: f_sim_def  no_write_wrSet_empty_def)
  using PC.distinct(27) PC.distinct(717) PC.distinct(989) apply presburger
  apply ( simp add: split: if_split_asm)
  apply (subgoal_tac " tpc as ta = TPC.ReadPending ")
  prefer 2
  apply (simp add: f_sim_def tr_rel_def)
  apply (smt (z3) PC.simps(1655))
  by blast


(*auxiliary lemma*)
lemma   tr_rel_Read3_ReadResponding_self:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and " TML_Read  ta   cs cs'"
and "((pc cs) ta)  = PC.Read3"
and "((pc cs') ta)  = PC.ReadResponding"
and " Read_inv ta  ((pc cs) ta) cs " 
and " f_sim cs as "
and"   tr_rel   cs as ta"
and   "\<forall>t.  tms_inv as  t "
and  " pc cs  syst  = RecIdle \<longrightarrow> (\<forall>t.  (t \<noteq> syst  \<and> ((pc cs) t \<notin> {PC.NotStarted, PC.Committed,PC.Begin2,PC.BeginPending, PC.Aborted   }) \<longrightarrow>   regs (\<tau> cs) t loc \<le> lastVal glb  (\<tau> cs) ))"
and "pc cs  syst  = RecIdle  \<longrightarrow> ( lastVal glb (\<tau> cs)  \<ge>recoveredGlb cs ) " 
and   " \<forall>  t.  ( writer cs  = Some t \<longrightarrow> odd (lastVal glb  (\<tau> cs )) )"
and "tmemory as \<noteq> [] "
and   "\<forall>t.  tms_inv as  t "
and " ta \<noteq> syst"
shows "    tr_rel  cs'  (TMRead_trans  ta   (inLoc cs ta) (write_count (regs (\<tau> cs) ta DTML.loc - recoveredGlb cs))     as)    ta  "
  using assms
  apply  (simp add:TML_Read_def tr_rel_def Read_inv_def  split: if_splits )
  apply (subgoal_tac " wrSet as ta = Map.empty ")
  prefer 2
  apply (simp add: f_sim_def  no_write_wrSet_empty_def)
  using PC.distinct(27) PC.distinct(717) PC.distinct(989) apply presburger
  apply (simp add:TMRead_trans_def)
  apply (unfold  in_flight_def validity_prop_def)
  apply (intro conjI)
  apply (subgoal_tac "rdSet  (TMRead_trans ta  (inLoc cs ta) (write_count (regs (\<tau> cs) ta DTML.loc - recoveredGlb cs)) as)   ta
=  (rdSet as ta)( (inLoc cs ta) \<mapsto> ((tmemory as!  (write_count (regs (\<tau> cs) ta  DTML.loc - recoveredGlb  cs )))  (inLoc cs ta)))" )
  prefer 2
  using ready3_ready_readset [where  cs =cs and cs' = cs' and as = as ]
  using assms(1) assms(10) assms(3) assms(5) assms(6) apply presburger
  apply (subgoal_tac "tmemory (TMRead_trans ta  (inLoc cs ta) (write_count (regs (\<tau> cs) ta DTML.loc - recoveredGlb cs')) as)  = 
tmemory as ")
  prefer 2
  apply (simp add: TMRead_trans_def)
  apply (simp add: f_sim_def)
  apply (simp add: global_rel_def)
  apply (unfold maxIndex_def)
  apply (subgoal_tac "(logical_glb cs) =  lastVal  glb (\<tau> cs) - recoveredGlb  cs  ")
  prefer 2
  apply (simp add: logical_glb_def)
  apply (smt (z3) cas_succ_eq numeral_1_eq_Suc_0 numerals(1) option.exhaust option.simps(4))
  apply (subgoal_tac " regs (\<tau> cs) ta DTML.loc =  lastVal  glb (\<tau> cs) ")
  prefer 2
  apply (metis One_nat_def cas_succ_eq)
  apply (simp add: read_consistent_def)
  prefer 2
  apply (subgoal_tac " beginIndex
(TMRead_trans ta  (inLoc cs ta)
(write_count (regs (\<tau> cs) ta DTML.loc - recoveredGlb cs')) as)
ta  = beginIndex as ta ")
  prefer 2
  apply (simp add: TMRead_trans_def)
  apply (subgoal_tac "  write_count (regs (\<tau> cs') ta DTML.loc - recoveredGlb cs') 
=  write_count (regs (\<tau> cs) ta DTML.loc - recoveredGlb cs) ")
  prefer 2
  apply (metis reg_same_CAS_dr)
  apply (metis assms(1) assms(10) assms(3) assms(5) assms(6) ready3_ready_valid_loc)
  apply (intro conjI)
  apply (smt (z3) reg_same_CAS_dr)
  apply (intro conjI impI)
  apply (smt (z3) option.case_eq_if reg_same_CAS_dr)
  apply (metis assms(1) assms(3) assms(6) read3_writecount_ni)
  apply (smt (verit) assms(1) assms(3) assms(6) option.case_eq_if read3_writecount_ni)
  apply (metis assms(1) assms(3) assms(6) read3_writecount_ni)
  apply simp
  apply (subgoal_tac "  apply_partial (tmemory as ! (length (tmemory as) - Suc 0)) (writes cs as)
(inLoc cs ta)  =  ((tmemory as!  (write_count (regs (\<tau> cs) ta  DTML.loc - recoveredGlb  cs )))  (inLoc cs ta))")
  prefer 2
  apply (simp add:  apply_partial_def write_count_def writes_def )
  by (metis domI domIff reg_same_CAS_dr)




lemma   tr_rel_Read3_stable:
assumes  "thrdsvars"
and   "\<forall>t.  tms_inv as  t "
and "total_wfs (\<tau> cs) "
and " TML_Read  ta   cs cs'"
and "((pc cs) ta)  = PC.Read3"
and "((pc cs') ta)  = PC.ReadResponding"
and " Read_inv ta  ((pc cs) ta) cs " 
and " f_sim cs as "
and"   tr_rel   cs as t"
and " t \<noteq> ta "
and  " pc cs  syst  = RecIdle \<longrightarrow> (\<forall>t.  (t \<noteq> syst  \<and> ((pc cs) t \<notin> {PC.NotStarted, PC.Committed,PC.Begin2,PC.BeginPending , PC.Aborted  }) \<longrightarrow>   regs (\<tau> cs) t loc \<le> lastVal glb  (\<tau> cs) ))"
and " ta \<noteq> syst"
shows "     tr_rel  cs'  (TMRead_trans  ta   (inLoc cs ta) (write_count (regs (\<tau> cs) ta DTML.loc - recoveredGlb cs))     as)    t "
using assms
apply (simp add:TML_Read_def tr_rel_def Read_inv_def  split: if_splits )
apply (cases "pc cs t";  simp)
apply (intro conjI impI)
apply (simp add: TMRead_trans_def)
using read3_read_consistent_ni [where cs = cs and as = as and t = t and cs' = cs' ]
using assms(1) assms(4) assms(7) apply presburger
apply (intro conjI)
apply (simp add: TMRead_trans_def)
using read3_read_consistent_ni [where cs = cs and as = as and t = t and cs' = cs' ]
using assms(1) assms(4) assms(7) apply presburger
apply (intro conjI)
apply (simp add: TMRead_trans_def)
using read3_read_consistent_ni [where cs = cs and as = as and t = t and cs' = cs' ]
using assms(1) assms(4) assms(7) apply presburger
apply (simp add: TMRead_trans_def)
using read3_read_consistent_ni [where cs = cs and as = as and t = t and cs' = cs' ]
using assms(1) assms(4) assms(7)
apply (metis reg_same_CAS_dt)
apply (intro conjI impI)
apply (simp add: TMRead_trans_def)
apply (subgoal_tac " validity_prop cs as t")
prefer 2
apply (subgoal_tac "  (even (lastVal glb (\<tau> cs)) \<and> regs (\<tau> cs) t DTML.loc = lastVal glb (\<tau> cs)) ")
prefer 2
apply (intro conjI)
apply (unfold total_wfs_def)
apply (metis cas_fail_diff_lv nat.discI)
apply (subgoal_tac " regs (\<tau> cs') t DTML.loc  = regs (\<tau> cs) t DTML.loc  ")
prefer 2
using reg_same_CAS_dt
apply metis
apply (metis cas_lc cas_nlv_lc lastVal_def numeral_1_eq_Suc_0 one_eq_numeral_iff zero_neq_one)
apply blast
using  read3_validity_prop_ni [where cs = cs and as = as and cs' = cs' ]
apply (metis assms(1) assms(3) assms(4) assms(7) reg_same_CAS_dt validity_prop_def)
apply (metis assms(1) assms(3) assms(4) assms(7) read3_validity_prop_ni reg_same_CAS_dt validity_prop_def)
apply (metis assms(1) assms(3) assms(4) assms(7) read3_read_consistent_ni read3_validity_prop_ni reg_same_CAS_dt validity_prop_def)
apply (intro conjI impI)
apply (simp add: TMRead_trans_def)
apply (subgoal_tac "  (even (lastVal glb (\<tau> cs)) \<and> regs (\<tau> cs) t DTML.loc = lastVal glb (\<tau> cs)) ")
prefer 2
apply (intro conjI)
apply (metis cas_fail_diff_lv nat.discI)
apply (subgoal_tac " regs (\<tau> cs') t DTML.loc  = regs (\<tau> cs) t DTML.loc  ")
prefer 2
using reg_same_CAS_dt
apply metis
apply (metis cas_lc cas_nlv_lc lastVal_def numeral_1_eq_Suc_0 one_eq_numeral_iff zero_neq_one)
apply (metis assms(1) assms(3) assms(4) assms(7) read3_validity_prop_ni reg_same_CAS_dt validity_prop_def)
apply (metis assms(1) assms(3) assms(4) assms(7) read3_validity_prop_ni reg_same_CAS_dt validity_prop_def)
apply (metis assms(1) assms(3) assms(4) assms(7) read3_read_consistent_ni read3_validity_prop_ni reg_same_CAS_dt validity_prop_def)
apply (intro conjI impI)
apply (simp add: TMRead_trans_def)
apply (metis (no_types, opaque_lifting) assms(1) assms(3) assms(4) assms(7) read3_in_flight_ni)
apply (intro conjI)
apply (simp add: TMRead_trans_def)
apply (metis assms(1) assms(3) assms(4) assms(7) assms(8) read3_in_flight_ni)
apply (simp add: TMRead_trans_def)
apply (simp add: TMRead_trans_def)
apply (simp add: TMRead_trans_def)
apply (intro conjI impI)
apply (simp add: TMRead_trans_def)
apply (metis assms(1) assms(3) assms(4) assms(7) assms(8) cas_succ_eq cas_succ_lv_lc lastVal_def numeral_1_eq_Suc_0 numerals(1) read3_validity_prop_ni reg_same_CAS_dt)
using \<open>\<And>ta t. \<lbrakk>thrdsvars; total_wfs (\<tau> cs); TML_Read ta cs cs'; pc cs ta = Read3; Read_inv ta (pc cs ta) cs; f_sim cs as; t \<noteq> ta; validity_prop cs as t\<rbrakk> \<Longrightarrow> validity_prop cs' (TMRead_trans ta (inLoc cs ta) (write_count (regs (\<tau> cs) ta DTML.loc - recoveredGlb cs)) as) t\<close> assms(1) assms(3) assms(4) assms(7) apply presburger
using \<open>\<And>ta t. \<lbrakk>thrdsvars; total_wfs (\<tau> cs); TML_Read ta cs cs'; pc cs ta = Read3; Read_inv ta (pc cs ta) cs; f_sim cs as; t \<noteq> ta; validity_prop cs as t\<rbrakk> \<Longrightarrow> validity_prop cs' (TMRead_trans ta (inLoc cs ta) (write_count (regs (\<tau> cs) ta DTML.loc - recoveredGlb cs)) as) t\<close> assms(1) assms(10) assms(3) assms(4) assms(7) assms(8) apply presburger
apply (intro conjI impI)
apply (simp add: TMRead_trans_def)
apply (metis assms(1) assms(10) assms(3) assms(4) assms(5) assms(7) assms(8) cas_fail_diff_lv cas_lc lastVal_def numeral_1_eq_Suc_0 numeral_eq_one_iff read3_validity_prop_ni reg_same_CAS_dt zero_neq_one)
using \<open>\<And>ta t. \<lbrakk>thrdsvars; total_wfs (\<tau> cs); TML_Read ta cs cs'; pc cs ta = Read3; Read_inv ta (pc cs ta) cs; f_sim cs as; t \<noteq> ta; validity_prop cs as t\<rbrakk> \<Longrightarrow> validity_prop cs' (TMRead_trans ta (inLoc cs ta) (write_count (regs (\<tau> cs) ta DTML.loc - recoveredGlb cs)) as) t\<close> assms(1) assms(3) assms(4) assms(7) apply presburger
using \<open>\<And>ta t. \<lbrakk>thrdsvars; total_wfs (\<tau> cs); TML_Read ta cs cs'; pc cs ta = Read3; Read_inv ta (pc cs ta) cs; f_sim cs as; t \<noteq> ta; validity_prop cs as t\<rbrakk> \<Longrightarrow> validity_prop cs' (TMRead_trans ta (inLoc cs ta) (write_count (regs (\<tau> cs) ta DTML.loc - recoveredGlb cs)) as) t\<close> assms(1) assms(3) assms(4) assms(7) apply presburger
apply (intro conjI impI)
apply (simp add: TMRead_trans_def)
apply (metis assms(1) assms(10) assms(3) assms(4) assms(5) assms(7) assms(8) cas_fail_diff_lv cas_lc lastVal_def numeral_1_eq_Suc_0 one_eq_numeral_iff read3_in_flight_ni reg_same_CAS_dt zero_neq_one)
apply (smt (verit) assms(1) assms(3) assms(4) assms(7) read3_in_flight_ni)
apply (smt (verit) assms(1) assms(3) assms(4) assms(7) read3_in_flight_ni)
apply (intro conjI impI)
apply (simp add: TMRead_trans_def)
apply (metis assms(1) assms(3) assms(4) assms(5) assms(7) cas_succ_eq cas_succ_lv_lc lastVal_def numeral_1_eq_Suc_0 numerals(1) read3_in_flight_ni reg_same_CAS_dt)
apply (simp add: TMRead_trans_def)
apply (intro conjI)
apply (simp add: TMRead_trans_def)
apply (metis assms(1) assms(3) assms(4) assms(7) read3_in_flight_ni)
apply (intro conjI)
apply (simp add: TMRead_trans_def)
apply (metis assms(1) assms(3) assms(4) assms(7) read3_in_flight_ni)
apply (intro conjI)
apply (simp add: TMRead_trans_def)
apply (smt (verit) assms(1) assms(3) assms(4) assms(7) cas_fail_diff_lv cas_lc lastVal_def numeral_1_eq_Suc_0 numerals(1) read3_validity_prop_ni reg_same_CAS_dt zero_neq_one)
apply (metis assms(1) assms(3) assms(4) assms(5) assms(7) assms(8) read3_validity_prop_ni)
using \<open>\<And>ta t. \<lbrakk>thrdsvars; total_wfs (\<tau> cs); TML_Read ta cs cs'; pc cs ta = Read3; Read_inv ta (pc cs ta) cs; f_sim cs as; t \<noteq> ta; validity_prop cs as t\<rbrakk> \<Longrightarrow> validity_prop cs' (TMRead_trans ta (inLoc cs ta) (write_count (regs (\<tau> cs) ta DTML.loc - recoveredGlb cs)) as) t\<close> assms(1) assms(3) assms(4) assms(7) apply presburger
apply (simp add: TMRead_trans_def)
apply (metis reg_same_CAS_dt)
apply (intro conjI)
apply (simp add: TMRead_trans_def)
apply (metis assms(1) assms(3) assms(4) assms(7) cas_succ_eq cas_succ_lv_lc lastVal_def numeral_1_eq_Suc_0 numerals(1) read3_validity_prop_ni reg_same_CAS_dt)
apply (metis assms(1) assms(10) assms(3) assms(4) assms(5) assms(7) assms(8) cas_fail_diff_lv numeral_1_eq_Suc_0 numeral_eq_one_iff read3_validity_prop_ni zero_neq_one)
using \<open>\<And>ta t. \<lbrakk>thrdsvars; total_wfs (\<tau> cs); TML_Read ta cs cs'; pc cs ta = Read3; Read_inv ta (pc cs ta) cs; f_sim cs as; t \<noteq> ta; validity_prop cs as t\<rbrakk> \<Longrightarrow> validity_prop cs' (TMRead_trans ta (inLoc cs ta) (write_count (regs (\<tau> cs) ta DTML.loc - recoveredGlb cs)) as) t\<close> assms(1) assms(3) assms(4) assms(7) apply presburger
apply (intro conjI)
apply (simp add: TMRead_trans_def)
apply (metis assms(1) assms(3) assms(4) assms(7) cas_succ_eq cas_succ_lv_lc lastVal_def numeral_1_eq_Suc_0 numerals(1) read3_validity_prop_ni reg_same_CAS_dt)
apply (metis assms(1) assms(3) assms(4) assms(7) read3_validity_prop_ni)
apply (metis assms(1) assms(3) assms(4) assms(7) read3_validity_prop_ni)
apply (intro conjI)
apply (simp add: TMRead_trans_def)
apply (intro conjI impI)
apply (metis assms(1) assms(3) assms(4) assms(7) cas_fail_diff_lv cas_lc lastVal_def numeral_1_eq_Suc_0 one_eq_numeral_iff read3_in_flight_ni reg_same_CAS_dt zero_neq_one)
apply (smt (verit) assms(1) assms(3) assms(4) assms(7) cas_succ_eq cas_succ_lv_lc in_flight_def lastVal_def numeral_1_eq_Suc_0 numerals(1) read3_in_flight_ni reg_same_CAS_dt)
apply (intro conjI)
apply (simp add: TMRead_trans_def)
apply (metis assms(1) assms(3) assms(4) assms(7) read3_validity_prop_ni)
apply (simp add: TMRead_trans_def)
apply (intro conjI)
apply (simp add: TMRead_trans_def)
apply (metis assms(1) assms(3) assms(4) assms(7) read3_validity_prop_ni)
apply (intro conjI)
apply (simp add: TMRead_trans_def)
apply (metis assms(1) assms(3) assms(4) assms(7) read3_validity_prop_ni)
apply (intro conjI)
apply (simp add: TMRead_trans_def)
apply (metis assms(1) assms(3) assms(4) assms(7) read3_validity_prop_ni)
apply (intro conjI)
apply (simp add: TMRead_trans_def)
apply (metis assms(1) assms(3) assms(4) assms(7) read3_validity_prop_ni)
apply (intro conjI)
apply (simp add: TMRead_trans_def)
apply (metis assms(1) assms(3) assms(4) assms(7) read3_in_flight_ni)
apply (intro conjI)
apply (simp add: TMRead_trans_def)
apply (metis assms(1) assms(3) assms(4) assms(7) cas_fail_diff_lv cas_lc lastVal_def numeral_1_eq_Suc_0 numerals(1) read3_validity_prop_ni reg_same_CAS_dt zero_neq_one)
apply (metis assms(1) assms(3) assms(4) assms(7) read3_validity_prop_ni)
apply (metis assms(1) assms(3) assms(4) assms(7) numeral_eq_one_iff read3_validity_prop_ni zero_neq_one)
apply (intro conjI)
apply (simp add: TMRead_trans_def)
apply (metis assms(1) assms(3) assms(4) assms(7) cas_succ_eq cas_succ_lv_lc lastVal_def numeral_1_eq_Suc_0 numerals(1) read3_validity_prop_ni reg_same_CAS_dt)
apply (metis assms(1) assms(3) assms(4) assms(7) read3_validity_prop_ni)
apply (metis assms(1) assms(3) assms(4) assms(7) read3_validity_prop_ni)
by (simp add: TMRead_trans_def)


(*auxiliary lemma*)
lemma   Read3_Ready_global_rel:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and " TML_Read  ta   cs cs'"
and "((pc cs) ta)  = PC.Read3"
and "((pc cs') ta)  = PC.ReadResponding"
and " Read_inv ta  ((pc cs) ta) cs " 
and " f_sim  cs  as"
and   "\<forall>t.  tms_inv as  t "
and " tmemory as \<noteq> [] "
and  " pc cs  syst  = RecIdle \<longrightarrow> (\<forall>t.  (t \<noteq> syst  \<and> ((pc cs) t \<notin> {PC.NotStarted, PC.Committed,PC.Begin2,PC.BeginPending , PC.Aborted  }) \<longrightarrow>   regs (\<tau> cs) t loc \<le> lastVal glb  (\<tau> cs) ))"
and "\<forall>t.  (t \<noteq> syst  \<and> ((pc cs) t \<notin> {PC.NotStarted,PC.Aborted, PC.Committed, PC.BeginPending  })  \<and> (writeAux cs t \<or> readAux cs t )) \<longrightarrow>  ( regs (\<tau> cs) t loc \<ge>  recoveredGlb cs )" 
and "pc cs  syst  = RecIdle  \<longrightarrow> ( lastVal glb (\<tau> cs)  \<ge>recoveredGlb cs ) " 
and   " \<forall>  t.  ( writer cs  = Some t \<longrightarrow> odd (lastVal glb  (\<tau> cs )) )"
and " ta \<noteq> syst"
shows "  global_rel cs'
(TMRead_trans ta  (inLoc cs ta)  (write_count (regs (\<tau> cs) ta DTML.loc - recoveredGlb cs'))
as) "
using assms
apply (subgoal_tac " tpc as ta = TPC.ReadPending")
prefer 2
apply (simp add: f_sim_def tr_rel_def)
apply (smt (z3) PC.simps(1655))

apply (subgoal_tac " wrSet as ta = Map.empty ")
prefer 2
apply (simp add: f_sim_def  Read_inv_def TML_Read_def  no_write_wrSet_empty_def)
apply (metis PC.distinct(27) PC.distinct(717) PC.distinct(989))



apply (subgoal_tac "rdSet  (TMRead_trans ta  (inLoc cs ta)  (write_count (regs (\<tau> cs) ta DTML.loc - recoveredGlb cs)) as)   ta
=  (rdSet as ta)( (inLoc cs ta)  \<mapsto> ((tmemory as!  (write_count (regs (\<tau> cs) ta  DTML.loc - recoveredGlb  cs )))  (inLoc cs ta) ))" )
prefer 2
using ready3_ready_readset [where  cs =cs and cs' = cs' and as = as ]
using assms(1) assms(10) assms(3) assms(5) assms(6) apply presburger

apply (subgoal_tac "tmemory (TMRead_trans ta  (inLoc cs ta)  (write_count (regs (\<tau> cs) ta DTML.loc - recoveredGlb cs')) as)  = 
tmemory as ")
prefer 2
apply (simp add: TMRead_trans_def)


apply (subgoal_tac "beginIndex (TMRead_trans ta  (inLoc cs ta)  (write_count (regs (\<tau> cs) ta DTML.loc - recoveredGlb cs')) as) ta  = 
beginIndex  as ta ")
prefer 2
apply (simp add: TMRead_trans_def)


apply (subgoal_tac "  validIndex as ta (write_count (regs (\<tau> cs) ta DTML.loc - recoveredGlb cs))")
prefer 2
using ready3_ready_valid_loc[where cs =cs and as= as  and cs' = cs']
apply fastforce
apply (unfold total_wfs_def)
apply (simp add: Read_inv_def  TML_Read_def f_sim_def tmstep_def  split: if_splits )
apply (simp add: global_rel_def)
apply (intro conjI impI)
apply (metis assms(1) assms(2) assms(3) assms(6) read3_logicalglb_ni)
apply (simp add: maxIndex_def)
apply (metis assms(1) assms(2) assms(3) assms(6) assms(7) cas_le_daddr read3_writes_ni)
apply (simp add: maxIndex_def)
apply (metis cas_le_daddr)
by (simp add: TMRead_trans_def)



(*the simulation relation holds from Read3 to RedResponding (non stuttering step) *)
lemma   f_sim_Read3_ReadResponding_LP:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and " TML_Read  ta   cs cs'"
and "((pc cs) ta)  = PC.Read3"
and "((pc cs') ta)  = PC.ReadResponding"
and " Read_inv ta  ((pc cs) ta) cs " 
and " f_sim  cs  as"
and   "\<forall>t.  tms_inv as  t "
and " tmemory as \<noteq> [] "
and  " pc cs  syst  = RecIdle \<longrightarrow> (\<forall>t.  (t \<noteq> syst  \<and> ((pc cs) t \<notin> {PC.NotStarted, PC.Committed,PC.Begin2,PC.BeginPending , PC.Aborted    }) \<longrightarrow>   regs (\<tau> cs) t loc \<le> lastVal glb  (\<tau> cs) ))"
and "\<forall>t.  (t \<noteq> syst  \<and> ((pc cs) t \<notin> {PC.NotStarted,PC.Aborted, PC.Committed, PC.BeginPending  })  \<and> (writeAux cs t \<or> readAux cs t )) \<longrightarrow>  ( regs (\<tau> cs) t loc \<ge>  recoveredGlb cs )" 
and "pc cs  syst  = RecIdle  \<longrightarrow> ( lastVal glb (\<tau> cs)  \<ge>recoveredGlb cs ) " 
and   " \<forall>  t.  ( writer cs  = Some t \<longrightarrow> odd (lastVal glb  (\<tau> cs )) )"
and " ta \<noteq> syst"
shows " \<exists> as'. tmstep ta (TMRead  (inLoc cs ta) )  as  as'   \<and> f_sim  cs' as'  "
using assms
apply (subgoal_tac " tpc as ta = TPC.ReadPending")
prefer 2
apply (simp add: f_sim_def tr_rel_def)
apply (smt (z3) PC.simps(1655))



apply (subgoal_tac " wrSet as ta = Map.empty ")
prefer 2
apply (simp add: f_sim_def  Read_inv_def TML_Read_def  no_write_wrSet_empty_def)
apply (metis PC.distinct(27) PC.distinct(717) PC.distinct(989))

apply (subgoal_tac "rdSet  (TMRead_trans ta  (inLoc cs ta)  (write_count (regs (\<tau> cs) ta DTML.loc - recoveredGlb cs)) as)   ta
=  (rdSet as ta)( (inLoc cs ta)  \<mapsto> ((tmemory as!  (write_count (regs (\<tau> cs) ta  DTML.loc - recoveredGlb  cs )))  (inLoc cs ta) ))" )
prefer 2
using ready3_ready_readset [where  cs =cs and cs' = cs' and as = as ]
using assms(1) assms(10) assms(3) assms(5) assms(6)
apply presburger

apply (subgoal_tac "tmemory (TMRead_trans ta  (inLoc cs ta)  (write_count (regs (\<tau> cs) ta DTML.loc - recoveredGlb cs')) as)  = 
tmemory as ")
prefer 2
apply (simp add: TMRead_trans_def)


apply (subgoal_tac "beginIndex (TMRead_trans ta  (inLoc cs ta)  (write_count (regs (\<tau> cs) ta DTML.loc - recoveredGlb cs')) as) ta  = 
beginIndex  as ta ")
prefer 2
apply (simp add: TMRead_trans_def)


apply (subgoal_tac "  validIndex as ta (write_count (regs (\<tau> cs) ta DTML.loc - recoveredGlb cs))")
prefer 2
using ready3_ready_valid_loc[where cs =cs and as= as  and cs' = cs' and ta = ta]
apply fastforce

apply (simp add: tmstep_def)
apply (rule_tac x=" TMRead_trans ta  (inLoc cs ta)   (write_count (regs (\<tau> cs) ta DTML.loc - recoveredGlb cs)) as " in exI)

apply (intro conjI)
apply (rule_tac x="  (write_count (regs (\<tau> cs) ta DTML.loc - recoveredGlb cs)) " in exI)
apply blast
apply (unfold total_wfs_def)
apply (simp add: Read_inv_def  TML_Read_def f_sim_def tmstep_def  split: if_splits )
apply (intro conjI)
using  Read3_Ready_global_rel [where cs = cs and as = as and cs' = cs'  ] 
apply (metis assms(1) assms(10) assms(11) assms(2) assms(3) assms(5) assms(6) assms(7))
apply (intro conjI allI)
apply (simp add: no_read_rdSet_empty_def TMRead_trans_def)
apply (simp add:  no_write_wrSet_empty_def   TMRead_trans_def)
apply (simp add:  write_wrSet_notEmpty_def  TMRead_trans_def)
apply (metis cas_fail_diff_lv nat.discI)
apply (simp add:  read_rdSet_notEmpty_def  TMRead_trans_def)
apply (simp add: loc_in_wrSet_def TMRead_trans_def)
apply (metis cas_fail_diff_lv even_Suc)
apply (simp add:  even_loc_wrSet_empty_def TMRead_trans_def   )
apply (subgoal_tac "  (regs (\<tau> cs') t DTML.loc) =  (regs (\<tau> cs) t DTML.loc) ")
prefer 2
using  reg_same_CAS_dt
apply (metis reg_same_CAS_dr)
apply presburger

apply (simp add:  odd_loc_wrSet_notEmpty_def TMRead_trans_def   )
apply (subgoal_tac "  (regs (\<tau> cs') t DTML.loc) =  (regs (\<tau> cs) t DTML.loc) ")
prefer 2
using  reg_same_CAS_dt
apply (metis reg_same_CAS_dr)

apply (smt (verit))




apply clarify
apply (case_tac " t = ta ")
using  tr_rel_Read3_ReadResponding_self [where cs = cs and as = as and cs' = cs' and ta = ta  ] 
apply (metis assms(1) assms(10) assms(2) assms(3) assms(5) assms(6) assms(7))
using    tr_rel_Read3_stable [where cs = cs and as = as and cs' = cs'] 
apply (metis assms(1) assms(10) assms(2) assms(3) assms(5) assms(6) f_sim_def)
(********************************)
apply (unfold read_prop_def)

apply (subgoal_tac " regs (\<tau> cs') ta c1 = 1")
prefer 2
using One_nat_def apply presburger

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
apply (subgoal_tac " writer cs = None ")
prefer 2
apply (metis One_nat_def cas_fail_diff_lv option.collapse zero_neq_one)
apply (subgoal_tac "  (valOf (length (memory (\<tau> cs))) glb (\<tau> cs')   = lastVal glb (\<tau> cs') ) ")
prefer 2
apply (metis cas_succ_valOf_le_lvx)
apply (subgoal_tac "  write_count (logical_glb cs') =  write_count (logical_glb cs) ")
prefer 2
apply (simp(no_asm) add: write_count_def)
using  read3_logicalglb_ni 
apply (metis assms(1) assms(2) assms(3) assms(4) assms(6))
apply (subgoal_tac " logical_glb cs' = (lastVal glb (\<tau> cs') - recoveredGlb cs') ")
prefer 2

apply (simp(no_asm) add: logical_glb_def)
apply (metis option.simps(4))

apply (subgoal_tac "   write_count
(valOf (length (memory (\<tau> cs))) glb (\<tau> cs') - recoveredGlb cs') = write_count(  logical_glb cs') ")
prefer 2
apply presburger
apply (subgoal_tac " global_rel cs'
(TMRead_trans ta   (inLoc cs ta)  (write_count (regs (\<tau> cs) ta DTML.loc - recoveredGlb cs'))
as) ")
prefer 2
using  Read3_Ready_global_rel [where cs = cs  and as = as and cs' = cs']
apply (metis (no_types, lifting) assms(1) assms(10) assms(11) assms(2) assms(3) assms(5) assms(6) assms(7))
apply (unfold  global_rel_def)
apply (subgoal_tac " (writes cs' (TMRead_trans ta   (inLoc cs ta)  (write_count (regs (\<tau> cs) ta DTML.loc - recoveredGlb cs'))
as) ) = Map.empty " )
prefer 2
apply (simp(no_asm) add: writes_def)
apply (metis option.simps(4))
apply (unfold apply_partial_def maxIndex_def )
apply (metis option.case_eq_if)
by (metis Nat.add_0_right add_Suc_right not_less_less_Suc_eq)


(********************************)
lemma logical_glb_bounded:
assumes "total_wfs (\<tau> cs)"
shows  " (logical_glb cs)  \<le>    ( lastVal  glb (\<tau> cs)  + 1) - recoveredGlb cs  "
using assms
apply (subgoal_tac "  lastVal  glb (\<tau> cs) \<ge> 0 ")
prefer 2
apply (unfold total_wfs_def)
apply blast
apply (simp add: logical_glb_def)
apply (cases " writer cs ")
apply (metis diff_le_mono le_add2 option.simps(4) plus_1_eq_Suc)
by force

lemma loc_le_logical_glb:
assumes "total_wfs (\<tau> cs)"
and "  regs (\<tau> cs) t loc \<le> lastVal glb  (\<tau> cs) "
shows  " (regs (\<tau> cs) t DTML.loc - recoveredGlb cs) \<le> (logical_glb cs) " 
using assms
apply (subgoal_tac "  lastVal  glb (\<tau> cs) \<ge> 0 ")
prefer 2
apply (unfold total_wfs_def)
apply blast
apply (simp add: logical_glb_def)
apply (cases " writer cs ")
apply (metis diff_le_mono option.simps(4))
using le_add_diff_inverse2 le_diff_conv nle_le by force


(****************************************************************************)




lemma   read5_writecount_ni:  
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and " TML_Read  ta   cs cs'"
and "((pc cs) ta)  = PC.Read5"
and " Read_inv ta  ((pc cs) ta) cs " 
shows"   (write_count (regs (\<tau> cs) t  DTML.loc - recoveredGlb  cs )) =  (write_count (regs (\<tau> cs') t  DTML.loc - recoveredGlb  cs' )) "
using assms
apply (unfold total_wfs_def)
by (simp add:TML_Read_def   Read_inv_def write_count_def   split: if_splits )

lemma   read5_logicalglb_ni:  
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and " TML_Read  ta   cs cs'"
and "((pc cs) ta)  = PC.Read5"
and " Read_inv ta  ((pc cs) ta) cs " 
shows"   logical_glb cs = logical_glb cs' "
using assms
apply (unfold total_wfs_def)
apply (simp add:TML_Read_def   Read_inv_def logical_glb_def   split: if_splits )
apply (cases "pc cs ta";  simp)
apply (subgoal_tac "  lastVal glb (\<tau> cs) =  lastVal glb (\<tau> cs') ")
prefer 2
apply (metis cas_lc cas_nlv_lc lastVal_def numeral_1_eq_Suc_0 numeral_eq_one_iff zero_neq_one)
apply (cases"  writer cs' ")
apply simp
apply simp
apply (cases"  writer cs' ")
apply simp
by (smt (z3) PC.distinct(289) PC.distinct(329) fun_upd_other fun_upd_same option.simps(5))


lemma   read5_writes_ni:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and " TML_Read  ta   cs cs'"
and "((pc cs) ta)  = PC.Read5"
and " Read_inv ta  ((pc cs) ta) cs " 
and " f_sim  cs  as"
assumes" as' =  TMRead_trans ta    (inLoc cs ta)   (write_count (regs (\<tau> cs) ta  DTML.loc - recoveredGlb  cs ))  as  "
shows"   writes cs as  = writes cs' as' "
using assms
apply (unfold total_wfs_def)
apply (subgoal_tac"  wrSet  as = wrSet as' ")
prefer 2
apply (simp add: TMRead_trans_def)
apply (simp add:TML_Read_def TMRead_trans_def writes_def  Read_inv_def  split: if_splits )
apply (cases " writer cs")
apply (simp add:  writes_def )
apply (simp add:  writes_def )
apply (cases " writer cs'")
apply simp
apply simp
apply (cases " writer cs'")
apply simp
apply simp
apply (cases " writer cs'")
apply simp
apply simp
apply (cases " writer cs'")
apply simp
apply simp
apply (cases " writer cs'")
apply simp
apply simp
apply (cases " writer cs'")
apply simp
by simp



lemma   read5_read_consistent_ni:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and " TML_Read  ta   cs cs'"
and "((pc cs) ta)  = PC.Read5"
and " Read_inv ta  ((pc cs) ta) cs " 
and " f_sim  cs  as"
and " t \<noteq> ta "
and " ((read_consistent ( (tmemory  as)! (write_count (regs (\<tau> cs) t  DTML.loc - recoveredGlb  cs ))) (rdSet  as t)))   "
shows  " ((read_consistent ( (tmemory   (TMRead_trans ta    (inLoc cs ta)    (write_count (regs (\<tau> cs) ta  DTML.loc - recoveredGlb  cs ))  as) )! (write_count (regs (\<tau> cs') t  DTML.loc - recoveredGlb  cs' ))) (rdSet   (TMRead_trans ta    (inLoc cs ta)    (write_count (regs (\<tau> cs) ta  DTML.loc - recoveredGlb  cs ))  as)  t))) "
using assms
apply (unfold total_wfs_def)
apply (subgoal_tac " rdSet  as t  = rdSet   (TMRead_trans ta    (inLoc cs ta)    (write_count (regs (\<tau> cs) ta  DTML.loc - recoveredGlb  cs ))  as)  t ")
prefer 2
apply (simp add:  TMRead_trans_def)
apply (subgoal_tac "    (write_count (regs (\<tau> cs) t  DTML.loc - recoveredGlb  cs )) =  (write_count (regs (\<tau> cs') t  DTML.loc - recoveredGlb  cs' )) "
)
prefer 2
apply (simp add: write_count_def)
apply (metis assms(1) assms(2) read5_writecount_ni write_count_def)
apply (subgoal_tac " tmemory   (TMRead_trans ta    (inLoc cs ta)    (write_count (regs (\<tau> cs) ta  DTML.loc - recoveredGlb  cs ))  as)  = tmemory  as ")
prefer 2
apply (simp add:  TMRead_trans_def)
by(simp add:TML_Read_def   Read_inv_def  read_consistent_def   split: if_splits )



(*************************************************************************)
(*auxiliary lemma*)
lemma   ready5_ready_valid_loc:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and " TML_Read  ta   cs cs'"
and "((pc cs) ta)  = PC.Read5"
and "((pc cs') ta)  = PC.ReadResponding"
and " Read_inv ta  ((pc cs) ta) cs " 
and " f_sim  cs  as"
and   "\<forall>t.  tms_inv as  t "
and  " pc cs  syst  = RecIdle \<longrightarrow> (\<forall>t.  (t \<noteq> syst  \<and> ((pc cs) t \<notin> {PC.NotStarted, PC.Committed,PC.Begin2,PC.BeginPending , PC.Aborted    }) \<longrightarrow>   regs (\<tau> cs) t loc \<le> lastVal glb  (\<tau> cs) ))"
and "pc cs  syst  = RecIdle  \<longrightarrow> ( lastVal glb (\<tau> cs)  \<ge>recoveredGlb cs ) " 
and   " \<forall>  t.  ( writer cs  = Some t \<longrightarrow> odd (lastVal glb  (\<tau> cs )) )"
and "tmemory as \<noteq> [] "
and " ta \<noteq> syst"
shows "   validIndex as ta (write_count (regs (\<tau> cs) ta DTML.loc - recoveredGlb cs))"
using assms
  apply (unfold  total_wfs_def)
  apply (simp add:TML_Read_def   Read_inv_def   split: if_splits )
  apply (cases "pc cs ta";  simp)
  apply (simp add:   validIndex_def f_sim_def)
  apply (subgoal_tac "  (tpc as) ta =  TPC.ReadPending \<and>    in_flight  cs as ta    ")
  prefer 2
  apply (simp add: tr_rel_def  )
  apply (cases "pc cs ta";  simp)
  apply (smt (z3) PC.simps(1657))

  apply (unfold in_flight_def validity_prop_def)
  apply (intro conjI)
  apply (simp add: global_rel_def)
  apply (simp add: global_rel_def  maxIndex_def)
  apply (subgoal_tac " (regs (\<tau> cs) ta DTML.loc - recoveredGlb cs) \<le> (logical_glb cs) ") 
  prefer 2
  apply (metis PC.distinct(1087) PC.distinct(109) PC.distinct(185) PC.distinct(31) PC.distinct(721) assms(2) loc_le_logical_glb)
  apply (simp add: write_count_def)
  apply (metis diff_less div_mono2 length_greater_0_conv lessI)
  by presburger



lemma   ready5_readResponding_readset_not_in_wrset:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and " TML_Read  ta   cs cs'"
and "((pc cs) ta)  = PC.Read5"
and "((pc cs') ta)  = PC.ReadResponding"
and " Read_inv ta ((pc cs) ta) cs " 
and " f_sim  cs  as"
and   "\<forall>t.  tms_inv as  t "
and  " pc cs  syst  = RecIdle \<longrightarrow> (\<forall>t.  (t \<noteq> syst  \<and> ((pc cs) t \<notin> {PC.NotStarted, PC.Committed,PC.Begin2,PC.BeginPending, PC.Aborted     }) \<longrightarrow>   regs (\<tau> cs) t loc \<le> lastVal glb  (\<tau> cs) ))"
and "pc cs  syst  = RecIdle  \<longrightarrow> ( lastVal glb (\<tau> cs)  \<ge>recoveredGlb cs ) " 
and   " \<forall>  t.  ( writer cs  = Some t \<longrightarrow> odd (lastVal glb  (\<tau> cs )) )"
and "tmemory as \<noteq> [] "
and " ( (inLoc cs ta)  \<notin> dom (wrSet as ta))"
and " ta \<noteq> syst"
shows "  rdSet (TMRead_trans ta    (inLoc cs ta)    (write_count (regs (\<tau> cs) ta  DTML.loc - recoveredGlb  cs ))  as) ta =   
(rdSet as ta)(  (inLoc cs ta)   \<mapsto> ((tmemory as!  (write_count (regs (\<tau> cs) ta  DTML.loc - recoveredGlb  cs )))   (inLoc cs ta)  ))"
using assms
  apply (subgoal_tac "  validIndex as ta (write_count (regs (\<tau> cs) ta DTML.loc - recoveredGlb cs))")
  prefer 2
  using ready5_ready_valid_loc[where cs =cs and as= as  and cs' = cs']
  apply fastforce
  apply (simp add: TMRead_trans_def Read_inv_def TML_Read_def)
  apply ( simp add: split: if_split_asm)
  apply (subgoal_tac " tpc as ta = TPC.ReadPending ")
  prefer 2
  apply (simp add: f_sim_def tr_rel_def)
  apply (smt (z3) PC.simps(1657))
  by blast


(*auxiliary lemma*)
lemma   ready5_readResponding_readset_in_wrset:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and " TML_Read  ta   cs cs'"
and "((pc cs) ta)  = PC.Read5"
and "((pc cs') ta)  = PC.ReadResponding"
and " Read_inv ta  ((pc cs) ta) cs " 
and " f_sim  cs  as"
and   "\<forall>t.  tms_inv as  t "
and  " pc cs  syst  = RecIdle \<longrightarrow> (\<forall>t.  (t \<noteq> syst  \<and> ((pc cs) t \<notin> {PC.NotStarted, PC.Committed,PC.Begin2,PC.BeginPending  , PC.Aborted   }) \<longrightarrow>   regs (\<tau> cs) t loc \<le> lastVal glb  (\<tau> cs) ))"
and "pc cs  syst  = RecIdle  \<longrightarrow> ( lastVal glb (\<tau> cs)  \<ge>recoveredGlb cs ) " 
and   " \<forall>  t.  ( writer cs  = Some t \<longrightarrow> odd (lastVal glb  (\<tau> cs )) )"
and "tmemory as \<noteq> [] "
and " ( (inLoc cs ta)  \<in> dom (wrSet as ta))"
and " ta \<noteq> syst"
shows "  rdSet (TMRead_trans ta   (inLoc cs ta)   (write_count (regs (\<tau> cs) ta  DTML.loc - recoveredGlb  cs ))  as) ta =   
rdSet as  ta "
  using assms
  apply (subgoal_tac "  validIndex as ta (write_count (regs (\<tau> cs) ta DTML.loc - recoveredGlb cs))")
  prefer 2
  using ready5_ready_valid_loc[where cs =cs and as= as  and cs' = cs']
  apply fastforce
  by (simp add: TMRead_trans_def Read_inv_def TML_Read_def)

lemmas [simp del] = compval_def comploc_def  


(*auxiliary lemma*)
lemma  Read5_ReadResponding_value_read:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and " TML_Read  ta   cs cs'"
and "((pc cs) ta)  = PC.Read5"
and "((pc cs') ta)  = PC.ReadResponding"
and " Read_inv ta  ((pc cs) ta) cs " 
and " f_sim cs as "
(*and"   tr_rel   cs as ta"*)
and   "\<forall>t.  tms_inv as  t "
and  " pc cs  syst  = RecIdle \<longrightarrow> (\<forall>t.  (t \<noteq> syst  \<and> ((pc cs) t \<notin> {PC.NotStarted, PC.Committed,PC.Begin2,PC.BeginPending, PC.Aborted     }) \<longrightarrow>   regs (\<tau> cs) t loc \<le> lastVal glb  (\<tau> cs) ))"
and "pc cs  syst  = RecIdle  \<longrightarrow> ( lastVal glb (\<tau> cs)  \<ge>recoveredGlb cs ) " 
and   " \<forall>  t.  ( writer cs  = Some t \<longrightarrow> odd (lastVal glb  (\<tau> cs )) )"
and   "\<forall>t.  tms_inv as  t "
and "tmemory as \<noteq> [] "
and " as' = TMRead_trans ta   (inLoc cs ta)   (write_count (regs (\<tau> cs) ta  DTML.loc - recoveredGlb  cs ))  as  "
and "  readAux cs ta = True  \<and> writeAux cs ta  = False "
and " ta \<noteq> syst"
shows "  ( rdSet as' ta)  (inLoc cs ta)  = Some  (regs (\<tau> cs') ta val)    "
  using assms
  apply  (simp add:TML_Read_def f_sim_def  Read_inv_def  split: if_splits )
  apply (subgoal_tac "  validIndex as ta (write_count (regs (\<tau> cs) ta DTML.loc - recoveredGlb cs))")
  prefer 2
  using  ready5_ready_valid_loc [where cs= cs and as = as  and cs' = cs'] 
  using assms(1) assms(3) assms(5) assms(6) assms(7) assms(9) apply presburger
  apply (subgoal_tac " ( rdSet as' ta)  (inLoc cs ta)   = Some ( ((tmemory as' )!   (write_count (regs (\<tau> cs) ta  DTML.loc - recoveredGlb  cs )) )  (inLoc cs ta)   ) ")
  prefer 2
  apply (simp add: "TMRead_trans_def")
  apply (simp add: tr_rel_def)
  apply (smt (z3) PC.simps(1657) domIff in_flight_def)
  apply (simp add: read_pre_def) 
  apply (subgoal_tac " tmemory as'  = tmemory as  ")
  prefer 2
  apply (simp add: "TMRead_trans_def")
  apply (unfold total_wfs_def)
  apply simp
  apply (subgoal_tac "  comploc (memory (\<tau> cs') ! (coh (\<tau> cs') ta glb) ) glb  = glb ")
  prefer 2
  apply blast
  apply (subgoal_tac " 0 <  (coh (\<tau> cs') ta glb) \<and>
(coh (\<tau> cs') ta glb) < length (memory (\<tau> cs'))   ")
  prefer 2
  apply (unfold vbounded_def)
  apply (metis (mono_tags, opaque_lifting))
  by (metis read_prop_def)


(*auxiliary lemma*)
lemma   tr_rel_Read5_ReadResponding_self:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and " TML_Read  ta   cs cs'"
and "((pc cs) ta)  = PC.Read5"
and "((pc cs') ta)  = PC.ReadResponding"
and " Read_inv ta  ((pc cs) ta) cs " 
and " f_sim cs as "
and"   tr_rel   cs as ta"
and   "\<forall>t.  tms_inv as  t "
and  " pc cs  syst  = RecIdle \<longrightarrow> (\<forall>t.  (t \<noteq> syst  \<and> ((pc cs) t \<notin> {PC.NotStarted, PC.Committed,PC.Begin2,PC.BeginPending , PC.Aborted    }) \<longrightarrow>   regs (\<tau> cs) t loc \<le> lastVal glb  (\<tau> cs) ))"
and "pc cs  syst  = RecIdle  \<longrightarrow> ( lastVal glb (\<tau> cs)  \<ge>recoveredGlb cs ) " 
and   " \<forall>  t.  ( writer cs  = Some t \<longrightarrow> odd (lastVal glb  (\<tau> cs )) )"
and   "\<forall>t.  tms_inv as  t "
and "tmemory as \<noteq> [] "
and " ta \<noteq> syst"
shows "    tr_rel  cs'  (TMRead_trans  ta   (inLoc cs ta)  (write_count (regs (\<tau> cs) ta DTML.loc - recoveredGlb cs))     as)    ta  "
  using assms
  apply  (simp add:TML_Read_def tr_rel_def Read_inv_def  split: if_splits )
  apply (subgoal_tac "  validIndex as ta (write_count (regs (\<tau> cs) ta DTML.loc - recoveredGlb cs))")
  prefer 2
  using  ready5_ready_valid_loc [where cs= cs and as = as and cs' = cs'] 
  using assms(1) assms(10) assms(3) assms(5) assms(6) apply presburger
  apply (elim disjE)
  apply (case_tac " ( (inLoc cs ta)  \<notin> dom (wrSet as ta))")
  apply (intro conjI impI)
  apply (simp add: TMRead_trans_def)
  apply metis
  apply (subgoal_tac " rdSet (TMRead_trans ta  (inLoc cs ta)   (write_count (regs (\<tau> cs) ta  DTML.loc - recoveredGlb  cs ))  as) ta =   
(rdSet as ta)( (inLoc cs ta)  \<mapsto> ((tmemory as!  (write_count (regs (\<tau> cs) ta  DTML.loc - recoveredGlb  cs )))  (inLoc cs ta) ) ) ")
  prefer 2
  using read_set_Read_from_mem apply blast
  apply (subgoal_tac "tmemory (TMRead_trans ta  (inLoc cs ta)  (write_count (regs (\<tau> cs) ta DTML.loc - recoveredGlb cs')) as)  = 
tmemory as ")
  prefer 2
  apply (simp add: TMRead_trans_def)
  apply (simp add: f_sim_def)
  apply (simp add: global_rel_def)
  apply (unfold maxIndex_def)
  apply (subgoal_tac "(logical_glb cs) =  lastVal  glb (\<tau> cs) - recoveredGlb  cs  ")
  prefer 2
  apply (simp add: logical_glb_def)
  apply (subgoal_tac " regs (\<tau> cs) ta DTML.loc =  lastVal  glb (\<tau> cs) ")
  prefer 2
  apply (metis One_nat_def cas_succ_eq)
  apply (simp add: read_consistent_def)
  apply (simp add:  validity_prop_def)
  apply (intro conjI)
  apply (unfold in_flight_def validity_prop_def)
  apply (simp add: f_sim_def global_rel_def)
  apply (simp add: read_consistent_def)
  apply (metis read_as_beginIndex_ni)
  apply (intro impI conjI)
  apply (simp add: logical_glb_def maxIndex_def write_count_def) 
  apply (simp add: read_consistent_def)
  apply (smt (z3) option.case_eq_if)
  apply (metis read_as_beginIndex_ni)
    (************)
  apply (intro conjI)
  apply (simp add: logical_glb_def maxIndex_def write_count_def) 
  apply (simp add: read_consistent_def TMRead_trans_def)
  apply (metis read_as_beginIndex_ni)
  apply (simp add: f_sim_def)
  apply (simp add:  TMRead_trans_def Read_inv_def global_rel_def writes_def apply_partial_def)

  apply (smt (z3) PC.distinct(599) PC.distinct(623) domIff logical_glb_def maxIndex_def option.case_eq_if option.simps(5))
  apply (subgoal_tac " rdSet (TMRead_trans ta   (inLoc cs ta)   (write_count (regs (\<tau> cs) ta  DTML.loc - recoveredGlb  cs ))  as) ta =   
(rdSet as ta) ")
  prefer 2
  using  ready5_readResponding_readset_in_wrset[where as =as and cs =cs and cs' = cs' ] 
  apply (metis assms(1) assms(10) assms(14) assms(15) assms(2) assms(3) assms(4) assms(5) assms(6) assms(7))

  apply (subgoal_tac "tmemory (TMRead_trans ta  (inLoc cs ta)  (write_count (regs (\<tau> cs) ta DTML.loc - recoveredGlb cs')) as)  = 
tmemory as ")
  prefer 2
  apply (simp add: TMRead_trans_def)
  apply (intro conjI impI)
  apply (simp add: TMRead_trans_def)
  apply metis
  apply metis
  apply (metis TMRead_trans_def)
  apply (metis read_as_beginIndex_ni)
  apply metis
  apply (metis read_as_beginIndex_ni)
  apply (simp add: f_sim_def TMRead_trans_def  loc_in_wrSet_def)

(**********************************************)
  apply (unfold f_sim_def )
  apply (subgoal_tac " wrSet as ta = Map.empty ")
  prefer 2
  apply metis

  apply (subgoal_tac " rdSet (TMRead_trans ta   (inLoc cs ta)   (write_count (regs (\<tau> cs) ta  DTML.loc - recoveredGlb  cs ))  as) ta =   
(rdSet as ta)( (inLoc cs ta)  \<mapsto> ((tmemory as!  (write_count (regs (\<tau> cs) ta  DTML.loc - recoveredGlb  cs )))  (inLoc cs ta) ) ) ")
  prefer 2
  using read_set_Read_from_mem 
  apply (metis (no_types, lifting) dom_eq_empty_conv equals0D)


  apply (subgoal_tac "tmemory (TMRead_trans ta  (inLoc cs ta)  (write_count (regs (\<tau> cs) ta DTML.loc - recoveredGlb cs')) as)  = 
tmemory as ")
  prefer 2
  apply (simp add: TMRead_trans_def)
  apply (subgoal_tac " comploc (memory (\<tau> cs') ! (coh (\<tau> cs') ta glb)) glb = glb  ")
  prefer 2
  apply (simp add: read_pre_def total_wfs_def)
  apply (subgoal_tac " regs (\<tau> cs) ta DTML.loc = regs (\<tau> cs') ta DTML.loc ")
  prefer 2
  apply presburger
  apply (intro conjI impI)
  apply (simp add: TMRead_trans_def)
  apply (simp add: read_consistent_def)
  apply (metis read_as_beginIndex_ni)
  apply (simp add:  read_consistent_def)
  apply (metis read_as_beginIndex_ni)
  apply (simp add:  read_consistent_def)
  apply  presburger
  apply (simp add: f_sim_def TMRead_trans_def)
  by (smt (verit) Read5_ReadResponding_value_read assms(1) assms(10) assms(3) assms(5) assms(6) assms(7) domIff map_upd_Some_unfold ready5_readResponding_readset_not_in_wrset)




(*auxiliary lemma*)
lemma   tr_rel_Read5_stable:
assumes  "thrdsvars"
and   "\<forall>t.  tms_inv as  t "
and "total_wfs (\<tau> cs) "
and " TML_Read  ta   cs cs'"
and "((pc cs) ta)  = PC.Read5"
and "((pc cs') ta)  = PC.ReadResponding"
and " Read_inv ta  ((pc cs) ta) cs " 
and " f_sim cs as "
and"   tr_rel   cs as t"
and " t \<noteq> ta "
and  " pc cs  syst  = RecIdle \<longrightarrow> (\<forall>t.  (t \<noteq> syst  \<and> ((pc cs) t \<notin> {PC.NotStarted, PC.Committed,PC.Begin2,PC.BeginPending , PC.Aborted    }) \<longrightarrow>   regs (\<tau> cs) t loc \<le> lastVal glb  (\<tau> cs) ))"
and " ta \<noteq> syst"
shows "     tr_rel  cs'  (TMRead_trans  ta   (inLoc cs ta)  (write_count (regs (\<tau> cs) ta DTML.loc - recoveredGlb cs))     as)    t "
  using assms
  apply (simp add:TML_Read_def tr_rel_def Read_inv_def  split: if_splits )
  apply ( unfold in_flight_def   )
  apply (cases "pc cs t";  simp)
  apply (intro conjI impI)
  apply (simp add: TMRead_trans_def)
  using read5_read_consistent_ni [where cs = cs and as = as and t = t  and cs' = cs' ]
  using assms(1) assms(4) assms(7) apply presburger
  apply (intro conjI)
  apply (simp add: TMRead_trans_def)
  using read5_read_consistent_ni [where cs = cs and as = as and t = t  and cs' = cs' ]
  using assms(1) assms(4) assms(7) apply presburger
  apply (intro conjI)
  apply (simp add: TMRead_trans_def)
  using read5_read_consistent_ni [where cs = cs and as = as and t = t and cs' = cs' ]
  using assms(1) assms(4) assms(7) apply presburger
  apply (intro conjI)
  apply (simp add: TMRead_trans_def)
  using read5_read_consistent_ni [where cs = cs and as = as and t = t and cs' = cs' ]
  using assms(1) assms(4) assms(7) apply presburger
  apply (unfold  validity_prop_def)
  apply (intro conjI)
  apply (simp add: TMRead_trans_def)
  apply (simp add: TMRead_trans_def)
  apply (simp add: TMRead_trans_def)
  apply (simp add: TMRead_trans_def)
  apply (simp add: TMRead_trans_def)
  apply (simp add: TMRead_trans_def)
  apply (simp add: TMRead_trans_def)
  apply (simp add: TMRead_trans_def)
  apply (simp add: TMRead_trans_def)
  apply (simp add: TMRead_trans_def)
  apply (simp add: TMRead_trans_def)
  apply (simp add: TMRead_trans_def)
  apply (simp add: TMRead_trans_def)
  apply (simp add: TMRead_trans_def)
  apply metis
  apply (simp add: TMRead_trans_def)
  apply (simp add: TMRead_trans_def)
  apply (simp add: TMRead_trans_def)
  apply (simp add: TMRead_trans_def)
  apply (simp add: TMRead_trans_def)
  apply (simp add: TMRead_trans_def)
  apply blast
  apply (simp add: TMRead_trans_def)
  apply (simp add: TMRead_trans_def)
  apply (simp add: TMRead_trans_def)
  apply (simp add: TMRead_trans_def)
  apply (simp add: TMRead_trans_def)
  apply (simp add: TMRead_trans_def)
  apply (simp add: TMRead_trans_def)
  apply (simp add: TMRead_trans_def)
  by (simp add: TMRead_trans_def)


(*the simulation relation holds from Read5 to RedResponding (non stuttering step) *)
lemma   f_sim_Read5_ReadResponding_lp:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and " TML_Read  ta   cs cs'"
and "((pc cs) ta)  = PC.Read5"
and "((pc cs') ta)  = PC.ReadResponding"
and " Read_inv ta  ((pc cs) ta) cs " 
and " f_sim  cs  as"
and   "\<forall>t.  tms_inv as  t "
and " tmemory as \<noteq> [] "
and  " pc cs  syst  = RecIdle \<longrightarrow> (\<forall>t.  (t \<noteq> syst  \<and> ((pc cs) t \<notin> {PC.NotStarted, PC.Committed,PC.Begin2,PC.BeginPending , PC.Aborted    }) \<longrightarrow>   regs (\<tau> cs) t loc \<le> lastVal glb  (\<tau> cs) ))"

and "\<forall>t.  (t \<noteq> syst  \<and> ((pc cs) t \<notin> {PC.NotStarted,PC.Aborted, PC.Committed, PC.BeginPending })  \<and> (writeAux cs t \<or> readAux cs t )) \<longrightarrow>  ( regs (\<tau> cs) t loc \<ge>  recoveredGlb cs )"

and "pc cs  syst  = RecIdle  \<longrightarrow> ( lastVal glb (\<tau> cs)  \<ge>recoveredGlb cs ) " 
and   " \<forall>  t.  ( writer cs  = Some t \<longrightarrow> odd (lastVal glb  (\<tau> cs )) )"
and " ta \<noteq> syst"
shows " \<exists> as'. tmstep ta (TMRead  (inLoc cs ta))  as  as'   \<and> f_sim  cs' as'  "
  using assms
  apply (subgoal_tac " tpc as ta = TPC.ReadPending")
  prefer 2
  apply (simp add: f_sim_def tr_rel_def)
  apply (smt (z3) PC.simps(1657))
  apply (subgoal_tac "tmemory (TMRead_trans ta  (inLoc cs ta) (write_count (regs (\<tau> cs) ta DTML.loc - recoveredGlb cs')) as)  = 
tmemory as ")
  prefer 2
  apply (simp add: TMRead_trans_def)
  apply (subgoal_tac "beginIndex (TMRead_trans ta  (inLoc cs ta) (write_count (regs (\<tau> cs) ta DTML.loc - recoveredGlb cs')) as) ta  = 
beginIndex  as ta ")
  prefer 2
  apply (simp add: TMRead_trans_def)
  apply (subgoal_tac "  validIndex as ta (write_count (regs (\<tau> cs) ta DTML.loc - recoveredGlb cs))")
  prefer 2
  using ready5_ready_valid_loc[where cs =cs and as= as  and cs' = cs']
  apply fastforce
  apply (simp add: tmstep_def)
  apply (rule_tac x=" TMRead_trans ta  (inLoc cs ta)  (write_count (regs (\<tau> cs) ta DTML.loc - recoveredGlb cs)) as " in exI)
  apply (intro conjI)
  apply (rule_tac x="  (write_count (regs (\<tau> cs) ta DTML.loc - recoveredGlb cs)) " in exI)
  apply blast
  apply (unfold total_wfs_def)
  apply (simp add: Read_inv_def  TML_Read_def f_sim_def tmstep_def  split: if_splits )
  apply (intro conjI)
  apply (simp add: global_rel_def)
  apply (intro allI conjI impI)
  apply (metis assms(1) assms(2) assms(3) assms(6) read5_logicalglb_ni)
  apply (simp add: maxIndex_def)
  apply (metis assms(1) assms(2) assms(3) assms(6) assms(7) read5_writes_ni)
  apply (simp add: maxIndex_def)
  apply (simp add: maxIndex_def)
  apply (metis option.discI)
  apply (simp add: TMRead_trans_def)
  apply (intro conjI allI)
  apply (simp add: no_read_rdSet_empty_def  TMRead_trans_def )
  apply fastforce
  apply (simp add:  no_write_wrSet_empty_def   TMRead_trans_def)
  apply (simp add:  write_wrSet_notEmpty_def  TMRead_trans_def)
  apply (simp add:  TMRead_trans_def  read_rdSet_notEmpty_def)
  apply (simp add: loc_in_wrSet_def  TMRead_trans_def)
  apply (simp add: even_loc_wrSet_empty_def  TMRead_trans_def)
  apply (simp add: odd_loc_wrSet_notEmpty_def  TMRead_trans_def)
  apply clarify
  apply (case_tac " t = ta ")
  using  tr_rel_Read5_ReadResponding_self [where cs = cs and as = as and cs' = cs'  ] 
  apply (metis assms(1) assms(10) assms(2) assms(3) assms(5) assms(6) assms(7))
  using    tr_rel_Read5_stable [where cs = cs and as = as and cs' = cs'  ] 
  apply (metis assms(1) assms(10) assms(2) assms(3) assms(5) assms(6) f_sim_def)
  apply (unfold  read_prop_def)
  by metis

(*****************************************************)



(*auxiliary lemma*)
lemma read_inv_dt:
assumes"   TML_Read_invocation t' \<sigma> \<sigma>'"
and" tb \<noteq> t' "
shows  "((pc \<sigma>') tb) = ((pc \<sigma>) tb) "
  using assms
  apply (simp add: TML_Read_invocation_def)
  by (cases "pc \<sigma> t' ";  simp add: split if_splits  )



(*auxiliary lemma*)
lemma   read3_abort_writes_ni:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and " TML_Read  ta   cs cs'"
and "((pc cs) ta)  = PC.Read3"
and " Read_inv ta  ((pc cs) ta) cs " 
and " f_sim  cs  as"
and" as' =  ( TMAbort_trans  ta  as)   "
shows"   writes cs as  = writes cs' as' "
  using assms
  apply (unfold total_wfs_def)
  apply (simp add:TML_Read_def   Read_inv_def  split: if_splits )
  apply (cases "pc cs ta";  simp)
  apply (subgoal_tac"  wrSet  as = wrSet as' ")
  prefer 2
  apply (simp add: TMAbort_trans_def)
  apply (cases " writer cs")
  apply (simp add:  writes_def )
  apply (case_tac "  pc cs ( the (writer cs))  = Commit4 ") 
  apply (subgoal_tac "  writes cs as = Map.empty ")
  prefer 2
  apply (simp add: writes_def)
  apply (smt (z3) option.sel option.simps(5))
  apply (subgoal_tac "  writes cs' as' = Map.empty ")
  prefer 2
  apply (subgoal_tac "  pc cs' ( the (writer cs'))  = Commit4  ")
  prefer 2
  using pc_aux   
  apply (metis option.sel update_def)
  apply (unfold  writes_def)
  apply (metis option.sel option.simps(5))
  apply presburger
  apply (subgoal_tac " writes cs as =   wrSet as (the (writer cs)) ")
  prefer 2
  apply (unfold  writes_def)
  apply (smt (z3) option.sel option.simps(5))
  apply (subgoal_tac "  writes cs' as' =  wrSet as' (the (writer cs')) ")
  prefer 2
  apply (subgoal_tac "  pc cs' ( the (writer cs'))  \<noteq> Commit4  ")
  prefer 2
  using update_def apply simp
  apply (unfold  writes_def)
  apply (smt (z3) option.sel option.simps(5))
  apply presburger
  apply (subgoal_tac"  wrSet  as = wrSet as' ")
  prefer 2
  apply (simp add: TMAbort_trans_def)
  apply (simp add:  writes_def )
  apply (case_tac "  pc cs ( the (writer cs))  = Commit4 ") 
  apply (subgoal_tac "  writes cs as = Map.empty ")
  prefer 2
  apply (simp add: writes_def)
  apply (smt (verit) option.case_eq_if)
  apply (cases " writer cs'")
  apply simp
  apply simp
  apply (simp(no_asm) add: TMAbort_trans_def)
  apply blast
  apply (cases " writer cs'")
  apply simp
  by  simp


(*auxiliary lemma*)
lemma   read5_abort_writes_ni:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and " TML_Read  ta   cs cs'"
and "((pc cs) ta)  = PC.Read5"
and "((pc cs') ta)  = PC.Aborted"
and " Read_inv ta  ((pc cs) ta) cs " 
and " f_sim  cs  as"
and" as' =  ( TMAbort_trans  ta  as)   "
shows"   writes cs as  = writes cs' as' "
  using assms
  apply (unfold total_wfs_def)
  apply (simp add:TML_Read_def   Read_inv_def  TMAbort_trans_def writes_def split: if_splits )
  apply (cases " writer cs")
  apply (simp add:  writes_def )
  apply (simp add:  writes_def )
  apply (cases " writer cs'")
  apply (simp add:  writes_def )
  apply (simp add:  writes_def )
  apply (cases " writer cs'")
  apply (simp add:  writes_def )
  by (simp add:  writes_def )



(*auxiliary lemma*)
lemma   read3_abort_read_consistent_ni:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and " TML_Read  ta  cs cs'"
and "((pc cs) ta)  = PC.Read3"
and " Read_inv ta  ((pc cs) ta) cs " 
and " f_sim  cs  as"
and " t \<noteq> ta "
and " ((read_consistent ( (tmemory  as)! (write_count (regs (\<tau> cs) t  DTML.loc - recoveredGlb  cs ))) (rdSet  as t)))   "
shows  " ((read_consistent ( (tmemory   ( ( TMAbort_trans  ta  as)  ) )! (write_count (regs (\<tau> cs') t  DTML.loc - recoveredGlb  cs' ))) (rdSet   ( TMAbort_trans  ta  as)  t))) "
  using assms
  apply (unfold total_wfs_def)
  apply (subgoal_tac " rdSet  as t  = rdSet   ( ( TMAbort_trans  ta  as)  )  t ")
  prefer 2
  apply (simp add:  TMAbort_trans_def)
  apply (subgoal_tac "    (write_count (regs (\<tau> cs) t  DTML.loc - recoveredGlb  cs )) =  (write_count (regs (\<tau> cs') t  DTML.loc - recoveredGlb  cs' )) "
      )
  prefer 2
  using  read3_writecount_ni [where cs = cs and cs' = cs' and t =t and ta = ta ]
  using assms(2) apply blast
  apply (subgoal_tac " tmemory   ( ( TMAbort_trans  ta  as)  )  = tmemory  as ")
  prefer 2
  apply (simp add:  TMAbort_trans_def)
  by(simp add:TML_Read_def   Read_inv_def  read_consistent_def   split: if_splits )





(*auxiliary lemma*)
lemma   read3_abort_validity_prop_ni:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and " TML_Read  ta  cs cs'"
and "((pc cs) ta)  = PC.Read3"
and " Read_inv ta  ((pc cs) ta) cs " 
and " f_sim  cs  as"
and " t \<noteq> ta "
and "  validity_prop  cs as t    "
shows  "  validity_prop  cs'   ( TMAbort_trans  ta  as)t   "
  using assms
  apply (unfold total_wfs_def validity_prop_def  TMAbort_trans_def)
  apply (intro conjI impI)
  using assms(2)  read3_abort_read_consistent_ni[where cs = cs and as = as and t = t and cs' = cs' and ta = ta ] 
  apply (smt (verit) TMAbort_trans_def assms(4) tms_state.unfold_congs(5))
  apply (simp add: write_count_def TMAbort_trans_def)
  by (metis assms(1) assms(2) read3_writecount_ni write_count_def)




(*auxiliary lemma*)
lemma   read3_abort_in_flight_ni:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and " TML_Read  ta  cs cs'"
and "((pc cs) ta)  = PC.Read3"
and " Read_inv ta  ((pc cs) ta) cs " 
and " f_sim  cs  as"
and " t \<noteq> ta "
and "   in_flight  cs as t    "
shows  "  in_flight  cs'  (TMAbort_trans  ta  as) t     "
  using assms
  apply (unfold  in_flight_def)
  apply (intro conjI impI)
  using  read3_abort_validity_prop_ni  [where cs = cs and as = as and t = t and cs' = cs' and ta = ta ]
  apply blast
  apply  (simp add:  TMAbort_trans_def  Read_inv_def TML_Read_def  f_sim_def )
  apply (intro conjI impI)
  apply (metis reg_same_CAS_dt)
  by (metis reg_same_CAS_dt)+


(*auxiliary lemma*)
lemma   tr_rel_Read3_Aborted_self:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and " TML_Read  ta   cs cs'"
and "((pc cs) ta)  = PC.Read3"
and "((pc cs') ta)  = PC.Aborted"
and " Read_inv ta  ((pc cs) ta) cs " 
and"   tr_rel   cs as ta"
and   "\<forall>t.  tms_inv as  t "
shows "    tr_rel  cs'  ( TMAbort_trans  ta  as)   ta  "
  using assms
  by  (simp add:TML_Read_def tr_rel_def Read_inv_def TMAbort_trans_def  split: if_splits )


(*auxiliary lemma*)
lemma   tr_rel_Read3_Aborted_stable:
assumes  "thrdsvars"
and   "\<forall>t.  tms_inv as  t "
and "total_wfs (\<tau> cs) "
and " TML_Read  ta   cs cs'"
and "((pc cs) ta)  = PC.Read3"
and "((pc cs') ta)  = PC.Aborted"
and " Read_inv ta  ((pc cs) ta) cs " 
and " f_sim cs as "
and"   tr_rel   cs as t"
and " t \<noteq> ta "
and  " pc cs  syst  = RecIdle \<longrightarrow> (\<forall>t.  (t \<noteq> syst  \<and> ((pc cs) t \<notin> {PC.NotStarted, PC.Committed,PC.Begin2,PC.BeginPending , PC.Aborted    }) \<longrightarrow>   regs (\<tau> cs) t loc \<le> lastVal glb  (\<tau> cs) ))"
and " ta \<noteq> syst"
shows "  tr_rel cs'  ( TMAbort_trans  ta  as)  t"
  using assms
  apply (simp add:TML_Read_def tr_rel_def Read_inv_def split: if_splits )
  apply (subgoal_tac " regs (\<tau> cs') t DTML.loc = regs (\<tau> cs) t DTML.loc ")
  prefer 2
  using reg_same_CAS_dt
  apply metis
  apply (cases "pc cs t";  simp)
  apply (intro conjI)
  apply (simp add: TMAbort_trans_def)
  apply (metis assms(1) assms(4) assms(7) read3_abort_read_consistent_ni)
  apply (intro conjI)
  apply (simp add: TMAbort_trans_def)
  apply (metis assms(1) assms(4) assms(7) read3_abort_read_consistent_ni)
  apply (intro conjI)
  apply (simp add: TMAbort_trans_def)
  apply (metis assms(1) assms(4) assms(7) read3_abort_read_consistent_ni)
  apply (intro conjI)
  apply (simp add: TMAbort_trans_def)
  apply (metis assms(1) assms(4) assms(7) read3_abort_read_consistent_ni)
  apply (intro conjI)
  apply (simp add: TMAbort_trans_def)
  apply (unfold total_wfs_def)
  apply (metis assms(1) assms(3) assms(4) assms(7) cas_fail_lastVal_same cas_sv_lc numeral_1_eq_Suc_0 numerals(1) read3_abort_validity_prop_ni)
  using assms(1) assms(3) assms(4) assms(7) read3_abort_validity_prop_ni apply presburger
  using assms(1) assms(3) assms(4) assms(7) read3_abort_validity_prop_ni apply presburger
  apply (intro conjI)
  apply (simp add: TMAbort_trans_def)
  apply (smt (verit) assms(1) assms(3) assms(4) assms(7) cas_fail_lastVal_same cas_sv_lc numeral_1_eq_Suc_0 numerals(1) read3_abort_validity_prop_ni)
  using assms(1) assms(3) assms(4) assms(7) read3_abort_validity_prop_ni apply presburger
  using assms(1) assms(3) assms(4) assms(7) read3_abort_validity_prop_ni apply presburger
  apply (intro conjI)
  apply (simp add: TMAbort_trans_def)
  using assms(1) assms(3) assms(4) assms(7) read3_abort_in_flight_ni apply presburger
  apply (intro conjI)
  apply (simp add: TMAbort_trans_def)
  using assms(1) assms(3) assms(4) assms(7) read3_abort_in_flight_ni apply presburger
  apply (simp add: TMAbort_trans_def)
  apply (simp add: TMAbort_trans_def)
  apply (simp add: TMAbort_trans_def)
  apply (intro conjI)
  apply (simp add: TMAbort_trans_def)
  apply (metis assms(1) assms(3) assms(4) assms(7) cas_fail_lastVal_same cas_sv_lc numeral_1_eq_Suc_0 numerals(1) read3_abort_validity_prop_ni)
  using assms(1) assms(3) assms(4) assms(7) read3_abort_validity_prop_ni apply presburger
  apply (metis assms(1) assms(3) assms(4) assms(7) read3_abort_validity_prop_ni)
  apply (intro conjI)
  apply (simp add: TMAbort_trans_def)
  apply (metis assms(1) assms(3) assms(4) assms(7) cas_fail_lastVal_same cas_sv_lc numeral_1_eq_Suc_0 numerals(1) read3_abort_validity_prop_ni)
  using assms(1) assms(3) assms(4) assms(7) read3_abort_validity_prop_ni apply presburger
  apply (metis assms(1) assms(3) assms(4) assms(7) read3_abort_validity_prop_ni)
  apply (intro conjI)
  apply (simp add: TMAbort_trans_def)
  apply (metis assms(1) assms(3) assms(4) assms(7) cas_fail_lastVal_same cas_sv_lc numeral_1_eq_Suc_0 numerals(1) read3_abort_in_flight_ni)
  using assms(1) assms(3) assms(4) assms(7) read3_abort_in_flight_ni apply presburger
  using assms(1) assms(3) assms(4) assms(7) read3_abort_in_flight_ni apply presburger
  apply (intro conjI)
  apply (simp add: TMAbort_trans_def)
  apply (metis assms(1) assms(3) assms(4) assms(7) cas_fail_lastVal_same cas_sv_lc numeral_1_eq_Suc_0 numerals(1) read3_abort_in_flight_ni)
  apply (simp add: TMAbort_trans_def)
  apply (intro conjI)
  apply (simp add: TMAbort_trans_def)
  using assms(1) assms(3) assms(4) assms(7) read3_abort_in_flight_ni apply presburger
  apply (intro conjI)
  apply (simp add: TMAbort_trans_def)
  using assms(1) assms(3) assms(4) assms(7) read3_abort_in_flight_ni apply presburger
  apply (intro conjI)
  apply (simp add: TMAbort_trans_def)
  apply (metis assms(1) assms(3) assms(4) assms(7) cas_fail_lastVal_same cas_sv_lc numeral_1_eq_Suc_0 numerals(1) read3_abort_validity_prop_ni)
  using assms(1) assms(3) assms(4) assms(7) read3_abort_validity_prop_ni apply presburger
  using assms(1) assms(3) assms(4) assms(7) read3_abort_validity_prop_ni apply presburger
  apply (simp add: TMAbort_trans_def)
  apply (metis reg_same_CAS_dt)
  apply (intro conjI)
  apply (simp add: TMAbort_trans_def)
  apply (metis assms(1) assms(3) assms(4) assms(7) cas_fail_lastVal_same cas_sv_lc numeral_1_eq_Suc_0 numerals(1) read3_abort_validity_prop_ni)
  using assms(1) assms(3) assms(4) assms(7) read3_abort_validity_prop_ni apply presburger
  using assms(1) assms(3) assms(4) assms(7) read3_abort_validity_prop_ni apply presburger
  apply (intro conjI impI)
  apply (simp add: TMAbort_trans_def)
  apply (metis assms(1) assms(3) assms(4) assms(7) cas_fail_lastVal_same cas_sv_lc numeral_1_eq_Suc_0 numerals(1) read3_abort_validity_prop_ni)
  using assms(1) assms(3) assms(4) assms(7) read3_abort_validity_prop_ni apply presburger
  using assms(1) assms(3) assms(4) assms(7) read3_abort_validity_prop_ni apply presburger
  apply (intro conjI impI)
  apply (simp add: TMAbort_trans_def)
  apply (metis assms(1) assms(3) assms(4) assms(7) cas_fail_lastVal_same cas_sv_lc numeral_1_eq_Suc_0 numerals(1) read3_abort_in_flight_ni)
  apply (simp add: TMAbort_trans_def)
  apply (metis cas_fail_lv_ni cas_possible_lv_lc lastVal_def)
  apply (intro conjI impI)
  apply (simp add: TMAbort_trans_def)
  using assms(1) assms(3) assms(4) assms(7) read3_abort_validity_prop_ni apply presburger
  apply (simp add: TMAbort_trans_def)
  apply (intro conjI impI)
  apply (simp add: TMAbort_trans_def)
  using assms(1) assms(3) assms(4) assms(7) read3_abort_validity_prop_ni apply presburger
  apply (intro conjI impI)
  apply (simp add: TMAbort_trans_def)
  using assms(1) assms(3) assms(4) assms(7) read3_abort_validity_prop_ni apply presburger
  apply (intro conjI impI)
  apply (simp add: TMAbort_trans_def)
  using assms(1) assms(3) assms(4) assms(7) read3_abort_validity_prop_ni apply presburger
  apply (intro conjI impI)
  apply (simp add: TMAbort_trans_def)
  using assms(1) assms(3) assms(4) assms(7) read3_abort_validity_prop_ni apply presburger
  apply (intro conjI impI)
  apply (simp add: TMAbort_trans_def)
  using assms(1) assms(3) assms(4) assms(7) read3_abort_in_flight_ni apply presburger
  apply (intro conjI impI)
  apply (simp add: TMAbort_trans_def)
  apply (metis assms(1) assms(3) assms(4) assms(7) cas_fail_lv_ni cas_possible_lv_lc lastVal_def read3_abort_validity_prop_ni)
  using assms(1) assms(3) assms(4) assms(7) read3_abort_validity_prop_ni apply presburger
  using assms(1) assms(3) assms(4) assms(7) read3_abort_validity_prop_ni apply presburger
  apply (intro conjI impI)
  apply (simp add: TMAbort_trans_def)
  apply (metis assms(1) assms(3) assms(4) assms(7) cas_fail_lv_ni cas_possible_lv_lc lastVal_def read3_abort_validity_prop_ni)
  using assms(1) assms(3) assms(4) assms(7) read3_abort_validity_prop_ni apply presburger
  using assms(1) assms(3) assms(4) assms(7) read3_abort_validity_prop_ni apply presburger
  by (simp add: TMAbort_trans_def)




(*auxiliary lemma*)
lemma   read3_aborted_writes_ni:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and " TML_Read  ta   cs cs'"
and "((pc cs) ta)  = PC.Read3"
and "((pc cs') ta)  = PC.Aborted"
and " Read_inv ta  ((pc cs) ta) cs " 
and " f_sim  cs  as"
and " ta \<noteq> syst"
shows"   writes cs as  = writes cs'  ( TMAbort_trans  ta  as)  "
  using assms
  apply (unfold total_wfs_def)
  apply (simp add:TML_Read_def  TMAbort_trans_def   Read_inv_def split: if_splits )
  apply (cases "pc cs ta";  simp)
  apply (unfold   writes_def)
  apply (cases" writer cs' ")
  apply (metis option.simps(4))
  by simp



(*the simulation relation holds from Read3 to Aborted (non stuttering step) *)
lemma   f_sim_read_Read3_abort_lp:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and " TML_Read  ta   cs cs'"
and "((pc cs) ta)  = PC.Read3"
and "((pc cs') ta)  = PC.Aborted"
and " Read_inv ta  ((pc cs) ta) cs " 
and " f_sim  cs  as"
and   "\<forall>t.  tms_inv as  t "
and"pc cs  syst  = RecIdle "
and  " pc cs  syst  = RecIdle \<longrightarrow> (\<forall>t.  (t \<noteq> syst  \<and> ((pc cs) t \<notin> {PC.NotStarted, PC.Committed,PC.Begin2,PC.BeginPending , PC.Aborted    }) \<longrightarrow>   regs (\<tau> cs) t loc \<le> lastVal glb  (\<tau> cs) ))"
and " ta \<noteq> syst"
shows "  \<exists> as'. tmstep ta  TMAbort  as  as'  \<and> f_sim  cs' as' "
  using assms
  apply (unfold total_wfs_def)
  apply (simp add: TML_Read_def Read_inv_def tmstep_def  f_sim_def)
  apply (subgoal_tac " maxIndex (TMAbort_trans ta as)  = maxIndex as ")
  prefer 2
  apply (simp add: maxIndex_def TMAbort_trans_def)
  apply (subgoal_tac " tmemory (TMAbort_trans ta as) = tmemory as ")
  prefer 2
  apply (simp add:  TMAbort_trans_def)
  apply (cases "pc cs ta";  simp)
  apply (intro conjI)
  apply (simp add: global_rel_def)
  apply (intro conjI impI)
  apply ( simp add: split: if_split_asm)
  apply (simp add: write_count_def)
  apply (subgoal_tac " logical_glb cs' = logical_glb cs ")
  prefer 2
  using  read3_logicalglb_ni[where cs= cs and cs' = cs' ]  
  apply (metis assms(1) assms(2) assms(3) assms(6))
  apply (simp add: TMAbort_trans_def)
  apply ( simp add: split: if_split_asm)
  apply (metis assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) cas_le_daddr read3_aborted_writes_ni)
  apply (simp add: maxIndex_def)
  apply (metis cas_le_daddr)
  apply ( simp add: split: if_split_asm)
  apply (simp add:  TMAbort_trans_def)
  apply (simp add: no_read_rdSet_empty_def  no_write_wrSet_empty_def write_wrSet_notEmpty_def  read_rdSet_notEmpty_def   )
  apply (subgoal_tac " \<forall> t.  loc_in_wrSet cs' as t ")
  prefer 2
  apply (simp add:  loc_in_wrSet_def)
  apply (metis cas_fail_lv_ni cas_le_daddr cas_possible_lv_lc lastVal_def)
  apply (subgoal_tac " \<forall> t.  even_loc_wrSet_empty cs' as t ")
  prefer 2
  apply (simp add:  even_loc_wrSet_empty_def)
  using  cas_dt_ni reg_same_CAS_dt 
  apply (metis pc_aux)
  apply (subgoal_tac " \<forall> t.  odd_loc_wrSet_notEmpty cs' as t ")
  prefer 2
  apply (simp add:  odd_loc_wrSet_notEmpty_def)
  using  cas_dt_ni reg_same_CAS_dt 
  apply (smt (verit) pc_aux)
  apply ( simp add: split: if_split_asm)
  apply (intro allI impI conjI)
  apply linarith
  using loc_in_wrSet_def 
  apply metis
  using even_loc_wrSet_empty_def
  apply (metis assms(5) insertI1 insert_commute tNotCrashed_def)
  using  odd_loc_wrSet_notEmpty_def 
  apply (metis reg_same_CAS_dr)
  using   tr_rel_Read3_Aborted_self [where as=as and cs=cs  and cs'=cs' ]
  using assms(1) assms(2) assms(3) assms(5) assms(6)
  apply metis
  apply (simp add:  TMAbort_trans_def)
  apply (simp add:  TMAbort_trans_def)
  apply (simp add:  TMAbort_trans_def)
  apply (simp add:  TMAbort_trans_def)
  apply (simp add:  TMAbort_trans_def loc_in_wrSet_def)
  apply (metis assms(2) cas_fail_lastVal_same cas_le_daddr cas_sv_lc numeral_1_eq_Suc_0 numerals(1))
  apply (simp add:  TMAbort_trans_def even_loc_wrSet_empty_def)
  apply (smt (verit) reg_same_CAS_dt)
  apply (simp add: odd_loc_wrSet_notEmpty_def  TMAbort_trans_def)
  apply (smt (verit) reg_same_CAS_dt)
  using  tr_rel_Read3_Aborted_stable  [where as=as and cs=cs  and cs'=cs' ] 
  apply (metis assms(1) assms(10) assms(2) assms(3) assms(5) assms(6) assms(7))
  apply (unfold  read_prop_def)
  apply ( simp add: split: if_split_asm)
  apply clarify
  apply (subgoal_tac "  regs (\<tau> cs') ta c1 = 0  ")
  prefer 2
  apply (metis cas_sv_lc numeral_1_eq_Suc_0 one_eq_numeral_iff)
  apply (subgoal_tac "    valOf (last_entry_lim (\<tau> cs') l n) l (\<tau> cs') =    valOf (last_entry_lim (\<tau> cs) l n) l (\<tau> cs) ")
  prefer 2
  using cas_succ_lelim_daddr_ni 
  apply (metis less_or_eq_imp_le)
  apply (subgoal_tac  " memory (\<tau> cs) = memory (\<tau> cs') ")
  prefer 2
  apply (metis cas_fail_mem_same)
  apply (subgoal_tac " valOf n glb (\<tau> cs')  = valOf n glb (\<tau> cs)  ")
  prefer 2
  apply (simp(no_asm) add: valOf_def compval_def)
  apply (metis survived_val_preserved_cas)
by metis

(********************************************************************)



(*auxiliary lemma*)
lemma   tr_rel_Read5_Aborted_self:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and " TML_Read  ta   cs cs'"
and "((pc cs) ta)  = PC.Read5"
and "((pc cs') ta)  = PC.Aborted"
and " Read_inv ta  ((pc cs) ta) cs " 
and"   tr_rel   cs as ta"
and   "\<forall>t.  tms_inv as  t "
shows "    tr_rel  cs'   ( TMAbort_trans  ta  as)     ta  "
  using assms
  by  (simp add:TML_Read_def tr_rel_def Read_inv_def TMAbort_trans_def  split: if_splits )




(*auxiliary lemma*)
lemma   read5_abort_read_consistent_ni:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and " TML_Read  ta  cs cs'"
and "((pc cs) ta)  = PC.Read5"
and " Read_inv ta  ((pc cs) ta) cs " 
and " f_sim  cs  as"
and " t \<noteq> ta "
and " ((read_consistent ( (tmemory  as)! (write_count (regs (\<tau> cs) t  DTML.loc - recoveredGlb  cs ))) (rdSet  as t)))   "
shows  " ((read_consistent ( (tmemory   ( ( TMAbort_trans  ta  as)  ) )! (write_count (regs (\<tau> cs') t  DTML.loc - recoveredGlb  cs' ))) (rdSet   ( TMAbort_trans  ta  as)  t))) "
  using assms
  apply (unfold total_wfs_def)
  apply (subgoal_tac " rdSet  as t  = rdSet   ( ( TMAbort_trans  ta  as)  )  t ")
  prefer 2
  apply (simp add:  TMAbort_trans_def)
  apply (subgoal_tac "    (write_count (regs (\<tau> cs) t  DTML.loc - recoveredGlb  cs )) =  (write_count (regs (\<tau> cs') t  DTML.loc - recoveredGlb  cs' )) "
      )
  prefer 2
  using  read5_writecount_ni [where cs = cs and cs' = cs' and t =t and ta = ta ]
  using assms(2) apply blast
  apply (subgoal_tac " tmemory   ( ( TMAbort_trans  ta  as)  )  = tmemory  as ")
  prefer 2
  apply (simp add:  TMAbort_trans_def)
  by(simp add:TML_Read_def   Read_inv_def  read_consistent_def   split: if_splits )


(*auxiliary lemma*)
lemma   read5_abort_validity_prop_ni:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and " TML_Read  ta  cs cs'"
and "((pc cs) ta)  = PC.Read5"
and " Read_inv ta  ((pc cs) ta) cs " 
and " f_sim  cs  as"
and " t \<noteq> ta "
and "  validity_prop  cs as t    "
shows  "  validity_prop  cs'   ( TMAbort_trans  ta  as)t   "
  using assms
  apply (unfold total_wfs_def validity_prop_def  TMAbort_trans_def)
  apply (intro conjI impI)
  using assms(2)  read5_abort_read_consistent_ni[where cs = cs and as = as and t = t and cs' = cs' and ta = ta ] 
  apply (smt (verit) TMAbort_trans_def assms(4) tms_state.unfold_congs(5))
  apply (simp add: write_count_def TMAbort_trans_def)
  by (metis assms(1) assms(2) read5_writecount_ni write_count_def)


(*auxiliary lemma*)
lemma   read5_abort_in_flight_ni:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and " TML_Read  ta  cs cs'"
and "((pc cs) ta)  = PC.Read5"
and " Read_inv ta  ((pc cs) ta) cs " 
and " f_sim  cs  as"
and " t \<noteq> ta "
and "   in_flight  cs as t    "
shows  "  in_flight  cs'  (TMAbort_trans  ta  as) t     "
  using assms
  apply (unfold  in_flight_def)
  apply (intro conjI impI)
  using  read5_abort_validity_prop_ni  [where cs = cs and as = as and t = t and cs' = cs' and ta = ta ]
  apply blast
  apply  (simp add:  TMAbort_trans_def  Read_inv_def TML_Read_def  f_sim_def )
  apply (intro conjI impI)
  apply (metis reg_same_CAS_dt)
  by (metis reg_same_CAS_dt)+


(*auxiliary lemma*)
lemma   tr_rel_Read5_Aborted_stable:
assumes  "thrdsvars"
and   "\<forall>t.  tms_inv as  t "
and "total_wfs (\<tau> cs) "
and " TML_Read  ta   cs cs'"
and "((pc cs) ta)  = PC.Read5"
and "((pc cs') ta)  = PC.Aborted"
and " Read_inv ta  ((pc cs) ta) cs " 
and " f_sim cs as "
and"   tr_rel   cs as t"
and " t \<noteq> ta "
and  " pc cs  syst  = RecIdle \<longrightarrow> (\<forall>t.  (t \<noteq> syst  \<and> ((pc cs) t \<notin> {PC.NotStarted, PC.Committed,PC.Begin2,PC.BeginPending , PC.Aborted    }) \<longrightarrow>   regs (\<tau> cs) t loc \<le> lastVal glb  (\<tau> cs) ))"
and " ta \<noteq> syst"
shows "  tr_rel cs'  ( TMAbort_trans  ta  as)  t"
  using assms
  apply (simp add:TML_Read_def tr_rel_def Read_inv_def split: if_splits )
  apply (cases "pc cs t";  simp add: split: if_splits)
  apply (intro conjI)
  apply (simp add: TMAbort_trans_def)
  apply (metis assms(1) assms(4) assms(7) read5_abort_read_consistent_ni)
  apply (intro conjI)
  apply (simp add: TMAbort_trans_def)
  apply (metis assms(1) assms(4) assms(7) read5_abort_read_consistent_ni)
  apply (intro conjI)
  apply (simp add: TMAbort_trans_def)
  apply (metis assms(1) assms(4) assms(7) read5_abort_read_consistent_ni)
  apply (intro conjI)
  apply (simp add: TMAbort_trans_def)
  apply (metis assms(1) assms(4) assms(7) read5_abort_read_consistent_ni)
  apply (intro conjI)
  apply (simp add: TMAbort_trans_def)
  apply (unfold total_wfs_def)
  apply (metis assms(1) assms(3) assms(4) assms(7) cas_fail_lastVal_same cas_sv_lc numeral_1_eq_Suc_0 numerals(1) read5_abort_validity_prop_ni)
  using assms(1) assms(3) assms(4) assms(7) read5_abort_validity_prop_ni apply blast
  using assms(1) assms(3) assms(4) assms(7) read5_abort_validity_prop_ni apply blast
  apply (intro conjI)
  apply (simp add: TMAbort_trans_def)
  apply (smt (verit) assms(1) assms(3) assms(4) assms(7) cas_fail_lastVal_same cas_sv_lc numeral_1_eq_Suc_0 numerals(1) read5_abort_validity_prop_ni)
  using assms(1) assms(3) assms(4) assms(7) read5_abort_validity_prop_ni apply blast
  using assms(1) assms(3) assms(4) assms(7) read5_abort_validity_prop_ni apply blast
  apply (intro conjI)
  apply (simp add: TMAbort_trans_def)
  using assms(1) assms(3) assms(4) assms(7) read5_abort_in_flight_ni apply blast
  apply (intro conjI)
  apply (simp add: TMAbort_trans_def)
  using assms(1) assms(3) assms(4) assms(7) read5_abort_in_flight_ni apply blast
  apply (simp add: TMAbort_trans_def)
  apply (simp add: TMAbort_trans_def)
  apply (simp add: TMAbort_trans_def)
  apply (intro conjI)
  apply (simp add: TMAbort_trans_def)
  apply (metis assms(1) assms(3) assms(4) assms(7) cas_fail_lastVal_same cas_sv_lc numeral_1_eq_Suc_0 numerals(1) read5_abort_validity_prop_ni)
  using assms(1) assms(3) assms(4) assms(7) read5_abort_validity_prop_ni apply blast
  apply (metis assms(1) assms(3) assms(4) assms(7) read5_abort_validity_prop_ni)
  apply (intro conjI)
  apply (simp add: TMAbort_trans_def)
  apply (metis assms(1) assms(3) assms(4) assms(7) cas_fail_lastVal_same cas_sv_lc numeral_1_eq_Suc_0 numerals(1) read5_abort_validity_prop_ni)
  using assms(1) assms(3) assms(4) assms(7) read5_abort_validity_prop_ni apply blast
  apply (metis assms(1) assms(3) assms(4) assms(7) read5_abort_validity_prop_ni)
  apply (intro conjI)
  apply (simp add: TMAbort_trans_def)
  apply (metis assms(1) assms(3) assms(4) assms(7) cas_fail_lastVal_same cas_sv_lc numeral_1_eq_Suc_0 numerals(1) read5_abort_in_flight_ni)
  using assms(1) assms(3) assms(4) assms(7) read5_abort_in_flight_ni apply blast
  using assms(1) assms(3) assms(4) assms(7) read5_abort_in_flight_ni apply blast
  apply (intro conjI)
  apply (simp add: TMAbort_trans_def)
  apply (metis assms(1) assms(3) assms(4) assms(7) cas_fail_lastVal_same cas_sv_lc numeral_1_eq_Suc_0 numerals(1) read5_abort_in_flight_ni)
  apply (simp add: TMAbort_trans_def)
  apply (intro conjI)
  apply (simp add: TMAbort_trans_def)
  using assms(1) assms(3) assms(4) assms(7) read5_abort_in_flight_ni apply blast
  apply (intro conjI)
  apply (simp add: TMAbort_trans_def)
  using assms(1) assms(3) assms(4) assms(7) read5_abort_in_flight_ni apply blast
  apply (intro conjI)
  apply (simp add: TMAbort_trans_def)
  apply (metis assms(1) assms(3) assms(4) assms(7) cas_fail_lastVal_same cas_sv_lc numeral_1_eq_Suc_0 numerals(1) read5_abort_validity_prop_ni)
  using assms(1) assms(3) assms(4) assms(7) read5_abort_validity_prop_ni apply blast
  using assms(1) assms(3) assms(4) assms(7) read5_abort_validity_prop_ni apply blast
  apply (simp add: TMAbort_trans_def)
  apply (intro conjI)
  apply (simp add: TMAbort_trans_def)
  apply (metis assms(1) assms(3) assms(4) assms(7) cas_fail_lastVal_same cas_sv_lc numeral_1_eq_Suc_0 numerals(1) read5_abort_validity_prop_ni)
  using assms(1) assms(3) assms(4) assms(7) read5_abort_validity_prop_ni apply blast
  using assms(1) assms(3) assms(4) assms(7) read5_abort_validity_prop_ni apply blast
  apply (intro conjI impI)
  apply (simp add: TMAbort_trans_def)
  apply (metis assms(1) assms(3) assms(4) assms(7) cas_fail_lastVal_same cas_sv_lc numeral_1_eq_Suc_0 numerals(1) read5_abort_validity_prop_ni)
  using assms(1) assms(3) assms(4) assms(7) read5_abort_validity_prop_ni apply blast
  using assms(1) assms(3) assms(4) assms(7) read5_abort_validity_prop_ni apply blast
  apply (intro conjI impI)
  apply (simp add: TMAbort_trans_def)
  apply (metis assms(1) assms(3) assms(4) assms(7) cas_fail_lastVal_same cas_sv_lc numeral_1_eq_Suc_0 numerals(1) read5_abort_in_flight_ni)
  apply (simp add: TMAbort_trans_def)
  apply (metis cas_fail_lv_ni cas_possible_lv_lc lastVal_def)
  apply (intro conjI impI)
  apply (simp add: TMAbort_trans_def)
  using assms(1) assms(3) assms(4) assms(7) read5_abort_validity_prop_ni apply blast
  apply (simp add: TMAbort_trans_def)
  apply (intro conjI impI)
  apply (simp add: TMAbort_trans_def)
  using assms(1) assms(3) assms(4) assms(7) read5_abort_validity_prop_ni apply blast
  apply (intro conjI impI)
  apply (simp add: TMAbort_trans_def)
  using assms(1) assms(3) assms(4) assms(7) read5_abort_validity_prop_ni apply blast
  apply (intro conjI impI)
  apply (simp add: TMAbort_trans_def)
  using assms(1) assms(3) assms(4) assms(7) read5_abort_validity_prop_ni apply blast
  apply (intro conjI impI)
  apply (simp add: TMAbort_trans_def)
  using assms(1) assms(3) assms(4) assms(7) read5_abort_validity_prop_ni apply blast
  apply (intro conjI impI)
  apply (simp add: TMAbort_trans_def)
  using assms(1) assms(3) assms(4) assms(7) read5_abort_in_flight_ni apply blast
  apply (intro conjI impI)
  apply (simp add: TMAbort_trans_def)
  apply (metis assms(1) assms(3) assms(4) assms(7) cas_fail_lv_ni cas_possible_lv_lc lastVal_def read5_abort_validity_prop_ni)
  using assms(1) assms(3) assms(4) assms(7) read5_abort_validity_prop_ni apply blast
  using assms(1) assms(3) assms(4) assms(7) read5_abort_validity_prop_ni apply blast
  apply (intro conjI impI)
  apply (simp add: TMAbort_trans_def)
  apply (metis assms(1) assms(3) assms(4) assms(7) cas_fail_lv_ni cas_possible_lv_lc lastVal_def read5_abort_validity_prop_ni)
  using assms(1) assms(3) assms(4) assms(7) read5_abort_validity_prop_ni apply blast
  using assms(1) assms(3) assms(4) assms(7) read5_abort_validity_prop_ni apply blast
  by (simp add: TMAbort_trans_def)


(*auxiliary lemma*)
lemma   read5_aborted_writes_ni:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and " TML_Read  ta   cs cs'"
and "((pc cs) ta)  = PC.Read5"
and "((pc cs') ta)  = PC.Aborted"
and " Read_inv ta  ((pc cs) ta) cs " 
and " f_sim  cs  as"
and " ta \<noteq> syst"
shows"   writes cs as  = writes cs'  ( TMAbort_trans  ta  as)  "
  using assms
  apply (unfold total_wfs_def)
  apply (simp add:TML_Read_def  TMAbort_trans_def   Read_inv_def split: if_splits )
  apply (cases "pc cs ta";  simp)
  apply (unfold   writes_def)
  apply (cases" writer cs' ")
  apply (metis option.simps(4))
  by simp


(*the simulation relation holds from Read5 to Aborted (non stuttering step) *)
lemma   f_sim_read_Read5_aborted_lp:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and " TML_Read  ta   cs cs'"
and "((pc cs) ta)  = PC.Read5"
and "((pc cs') ta)  = PC.Aborted"
and " Read_inv ta  ((pc cs) ta) cs " 
and " f_sim  cs  as"
and   "\<forall>t.  tms_inv as  t "
and"pc cs  syst  = RecIdle "
and  " pc cs  syst  = RecIdle \<longrightarrow> (\<forall>t.  (t \<noteq> syst  \<and> ((pc cs) t \<notin> {PC.NotStarted, PC.Committed,PC.Begin2,PC.BeginPending, PC.Aborted     }) \<longrightarrow>   regs (\<tau> cs) t loc \<le> lastVal glb  (\<tau> cs) ))"
and " ta \<noteq> syst"
shows "  \<exists> as'. tmstep ta  TMAbort  as  as'  \<and> f_sim  cs' as' "
  using assms
  apply (unfold total_wfs_def)
  apply (simp add: TML_Read_def Read_inv_def tmstep_def  f_sim_def)
  apply (subgoal_tac " maxIndex (TMAbort_trans ta as)  = maxIndex as ")
  prefer 2
  apply (simp add: maxIndex_def TMAbort_trans_def)
  apply (subgoal_tac " tmemory (TMAbort_trans ta as) = tmemory as ")
  prefer 2
  apply (simp add:  TMAbort_trans_def)
  apply (cases "pc cs ta";  simp)
  apply (intro conjI)
  apply (simp add: global_rel_def)
  apply (intro conjI impI)
  apply ( simp add: split: if_split_asm)
  apply (simp add: write_count_def)
  apply (subgoal_tac " logical_glb cs' = logical_glb cs ")
  prefer 2
  using  read5_logicalglb_ni[where cs= cs and cs' = cs' ]  
  apply (metis assms(1) assms(2) assms(3) assms(6))
  apply (simp add: TMAbort_trans_def)
  apply ( simp add: split: if_split_asm)
  apply (metis assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) cas_le_daddr read5_aborted_writes_ni)
  apply (simp add: maxIndex_def)
  apply ( simp add: split: if_split_asm)
  apply (simp add:  TMAbort_trans_def)
  apply (metis option.distinct(1))
  apply ( simp add: split: if_split_asm)
  apply (simp add:  TMAbort_trans_def)
  apply ( simp add: split: if_split_asm)
  apply (simp add: no_read_rdSet_empty_def odd_loc_wrSet_notEmpty_def  no_write_wrSet_empty_def write_wrSet_notEmpty_def  read_rdSet_notEmpty_def   )
  apply (subgoal_tac " \<forall> t.  loc_in_wrSet cs' as t ")
  prefer 2
  apply (simp add:  loc_in_wrSet_def)
  apply (intro allI  conjI impI)
  apply (metis loc_in_wrSet_def)
  apply (metis assms(5) even_loc_wrSet_empty_def insertI1 insert_commute tNotCrashed_def)
  apply (meson assms(1) assms(2) assms(3) assms(5) assms(6) tr_rel_Read5_Aborted_self)
  apply (simp add:  TMAbort_trans_def)
  apply (simp add:  TMAbort_trans_def)
  apply (simp add:  TMAbort_trans_def)
  apply (simp add:  TMAbort_trans_def)
  apply (simp add:  loc_in_wrSet_def  TMAbort_trans_def)
  apply(simp add: even_loc_wrSet_empty_def  TMAbort_trans_def)
  apply(simp add: odd_loc_wrSet_notEmpty_def  TMAbort_trans_def)
  apply (metis assms(1) assms(10) assms(2) assms(3) assms(5) assms(6) assms(7) tr_rel_Read5_Aborted_stable)
  by (smt (verit) read_prop_def)


(***************************************************************)

(*auxiliary lemma*)
lemma   tr_rel_Read4_self:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and " TML_Read  ta   cs cs'"
and "((pc cs) ta)  = PC.Read4"
and " Read_inv ta  ((pc cs) ta) cs " 
and"   tr_rel   cs as ta"
and   "\<forall>t.  tms_inv as  t "
and " ta \<noteq> syst"
shows "    tr_rel  cs'  as   ta  "
  using assms
  apply (simp add:TML_Read_def tr_rel_def Read_inv_def  )
  apply (unfold validity_prop_def maxIndex_def  in_flight_def read_consistent_def write_count_def  total_wfs_def  )
  apply (subgoal_tac " regs (\<tau> cs') ta DTML.loc  = regs (\<tau> cs) ta DTML.loc  ")
  prefer 2
  using reg_same_ld_dt apply blast
  apply (cases "pc cs ta";  simp)
  by presburger

(*auxiliary lemma*)
lemma   tr_rel_Read4_stable:
assumes  "thrdsvars"
and   "\<forall>t.  tms_inv as  t "
and "total_wfs (\<tau> cs) "
and " TML_Read  ta   cs cs'"
and "((pc cs) ta)  = PC.Read4"
and " Read_inv ta  ((pc cs) ta) cs " 
and"   tr_rel   cs as t"
and " t \<noteq> ta "
and " ta \<noteq> syst"
shows "  tr_rel cs' as  t"
  using assms
  apply (simp add:TML_Read_def tr_rel_def Read_inv_def  split: if_splits )
  apply (subgoal_tac " regs (\<tau> cs') t DTML.loc  = regs (\<tau> cs) t DTML.loc  ")
  prefer 2
  using reg_same_ld_dt apply blast
  apply (unfold validity_prop_def maxIndex_def  in_flight_def read_consistent_def  total_wfs_def  )
  apply (cases "pc cs t";  simp)
  apply metis
  apply metis
  apply metis
  apply metis
  apply (metis assms(3) lastVal_ni)
  apply (metis assms(3) lastVal_ni)
  apply presburger
  apply presburger
  apply (metis assms(3) lastVal_ni)
  apply (metis lastVal_def ld_crash ld_last_entry ld_step_mem)
  apply (metis assms(3) lastVal_ni)
  apply (metis assms(3) lastVal_ni)
  apply presburger
  apply presburger
  apply (simp add:  write_count_def)
  apply (metis lastVal_def ld_crash ld_last_entry ld_step_mem reg_same_ld_dt)
  apply (metis assms(3) lastVal_ni)
  apply (metis assms(3) lastVal_ni)
  apply (metis assms(3) lastVal_ni)
  apply presburger+
  by (metis assms(3) lastVal_ni)+

(*auxiliary lemma*)
lemma read_read4_logical_glb_ni:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and " TML_Read  ta   cs cs'"
and "((pc cs) ta)  = PC.Read4"
shows " logical_glb cs = logical_glb cs' "
using assms
  apply (unfold total_wfs_def)
  apply (simp add: TML_Read_def logical_glb_def)
  apply (cases "pc cs ta";  simp)
  apply (subgoal_tac " lastVal glb (\<tau> cs') = lastVal glb (\<tau> cs) ")
  prefer 2
  using assms(2) lastVal_ni apply blast
  apply (subgoal_tac "  recoveredGlb cs' =  recoveredGlb cs ")
  prefer 2
  apply presburger
  apply (cases " writer cs'" )
  apply simp
  by simp

(*auxiliary lemma*)
lemma read_read4_writes_ni:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and " TML_Read  ta   cs cs'"
and "((pc cs) ta)  = PC.Read4"
shows " writes cs as = writes  cs' as "
using assms
apply (unfold total_wfs_def)
apply (simp add: TML_Read_def  writes_def)
by (metis PC.distinct(597) PC.distinct(599) fun_upd_apply)



(*the simulation relation holds from Read4 to RedRead5 (stuttering step) *)
lemma   f_sim_read_Read4_stuttering:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and " TML_Read  ta   cs cs'"
and "((pc cs) ta)  = PC.Read4"
and " Read_inv ta  ((pc cs) ta) cs " 
and " f_sim  cs  as"
and   "\<forall>t.  tms_inv as  t "
and " ta \<noteq> syst"
shows " f_sim  cs' as  "
  using assms
  apply (unfold total_wfs_def)
  apply (simp add: TML_Read_def Read_inv_def  f_sim_def)
  apply (cases "pc cs ta";  simp)
  apply (intro conjI)
  apply (subgoal_tac " lastVal glb (\<tau> cs') = lastVal glb (\<tau> cs) ")
  prefer 2
  using assms(2) lastVal_ni apply blast
  apply (simp add: global_rel_def)
  apply (metis assms(1) assms(2) assms(3) lastVal_ni read_read4_logical_glb_ni read_read4_writes_ni)
  apply (simp add: no_read_rdSet_empty_def  no_write_wrSet_empty_def write_wrSet_notEmpty_def  read_rdSet_notEmpty_def )
  apply (subgoal_tac " \<forall> t.  loc_in_wrSet cs' as t ")
  prefer 2
  apply (simp add:  loc_in_wrSet_def)
  apply (metis assms(2) lastVal_ni)
  apply (subgoal_tac " \<forall> t.  even_loc_wrSet_empty cs' as t ")
  prefer 2
  apply (simp add:  even_loc_wrSet_empty_def)
  apply (subgoal_tac "\<forall> t.  regs (\<tau> cs') t DTML.loc =   regs (\<tau> cs) t DTML.loc  ")
  prefer 2
  using reg_same_ld_dr 
  apply (metis reg_same_ld_dt)
  using PC.distinct(1039) PC.distinct(29) PC.distinct(719) apply presburger
  apply (simp add: odd_loc_wrSet_notEmpty_def)
  apply (smt (verit) PC.distinct(1001) PC.distinct(1003) PC.distinct(1005) PC.distinct(1007) PC.distinct(1009) PC.distinct(107) assms(1) assms(2) assms(3) assms(5) reg_same_ld_dt tr_rel_Read4_self tr_rel_Read4_stable)
  apply (unfold read_prop_def)
  by (metis (no_types, opaque_lifting) assms(2) ld_crash ld_le_lim_ni ld_step_mem valOf_def)


(***************************************************)



(*auxiliary lemma*)
lemma   tr_rel_ReadResponding_self_lp:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "  TML_Read_response  ta cs  cs'  "
and "((pc cs) ta)  = PC.ReadResponding"
and "  Read_Response_inv   ta  ((pc cs) ta) cs " 
and " f_sim cs as "
and"   tr_rel   cs as ta"
and " ta \<noteq> syst"
shows "  tr_rel cs' ( TMRead_resp_trans  ta  as) ta "
using assms
  by (simp add: TML_Read_response_def tr_rel_def Read_Response_inv_def TMRead_resp_trans_def  validity_prop_def  split: if_splits )


(*auxiliary lemma*)
lemma   tr_rel_ReadResponding_stable_lp:
assumes  "thrdsvars"
and   "\<forall>t.  tms_inv as  t "
and "total_wfs (\<tau> cs) "
and "((pc cs) ta)  =PC.ReadResponding"
and "  Read_Response_inv   ta  ((pc cs) ta) cs " 
and "   TML_Read_response   ta cs  cs'  "
and " f_sim cs as "
and"   tr_rel   cs as t"
and " t \<noteq> ta "
and " ta \<noteq> syst"
shows "  tr_rel cs' ( TMRead_resp_trans  ta  as) t "
  using assms
  apply (simp add: TML_Read_response_def tr_rel_def  Read_Response_inv_def  TMRead_resp_trans_def split: if_splits )
  apply (unfold validity_prop_def  in_flight_def total_wfs_def  )
  apply (cases "pc cs t";  simp)
  apply metis
  apply metis
  apply (metis PC.distinct(1489) fun_upd_def)
  apply (metis PC.distinct(1491) fun_upd_def)
  by (metis PC.distinct(1493) fun_upd_def)



lemma read_readResponding_logical_glb_ni:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and " TML_Read_response  ta   cs cs'"
and "((pc cs) ta)  = PC.ReadResponding"
shows " logical_glb cs = logical_glb cs' "
  using assms
  apply (unfold total_wfs_def)
  apply (simp add: TML_Read_response_def logical_glb_def)
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
  by (smt (verit) PC.distinct(601) PC.distinct(645) fun_upd_other fun_upd_same option.simps(5))




(*auxiliary lemma*)
lemma read_readResponding_writes_ni:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and " TML_Read_response  ta   cs cs'"
and "((pc cs) ta)  =  PC.ReadResponding"
shows " writes cs as = writes  cs'  (TMRead_resp_trans  ta  as) "
  using assms
  apply (unfold total_wfs_def)
  apply (simp add: TML_Read_response_def TMRead_resp_trans_def logical_glb_def writes_def)
  apply (cases "pc cs ta";  simp)
  apply (cases " writer cs" )
  apply simp
  apply (intro conjI impI)
  apply (cases " writer cs'" )
  apply simp+
  apply (cases " writer cs'" )
  by simp+

(*the simulation relation holds for resp(Read)(non stuttering step) *)
lemma   f_sim_read_inv_readResponding_lp:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "  TML_Read_response   ta cs  cs'  "
and "((pc cs) ta)  =  PC.ReadResponding"
and " Read_Response_inv ta  ((pc cs) ta) cs " 
and " f_sim  cs  as"
and   "\<forall>t.  tms_inv as  t "
and"pc cs  syst  = RecIdle "
and " ta \<noteq> syst"
shows "  \<exists> as'. tmstep ta  TMReadResp  as  as'  \<and> f_sim  cs' as' "
  using assms
  apply (unfold total_wfs_def)
  apply (simp add: TML_Read_response_def Read_Response_inv_def tmstep_def f_sim_def)
  apply (subgoal_tac " memory ( \<tau>  cs) = memory( \<tau> cs' )")
  prefer 2
  apply presburger
  apply (cases "pc cs ta";  simp)
  apply (intro conjI)
  apply (simp add: global_rel_def)
  apply (intro conjI)
  apply (simp add: TMRead_resp_trans_def  write_count_def) 
  apply (metis assms(1) assms(2) assms(3)  read_readResponding_logical_glb_ni)
  apply (simp add: maxIndex_def  TMRead_resp_trans_def  ) 
  using  read_readResponding_writes_ni TMRead_resp_trans_def 
  using assms(1) assms(2) assms(3) apply presburger
  apply (simp add: maxIndex_def  TMRead_resp_trans_def apply_partial_def ) 
  apply (simp add: maxIndex_def  TMRead_resp_trans_def apply_partial_def ) 
  apply (simp add:  TMRead_resp_trans_def )
  apply (simp add: no_read_rdSet_empty_def odd_loc_wrSet_notEmpty_def  no_write_wrSet_empty_def write_wrSet_notEmpty_def  read_rdSet_notEmpty_def loc_in_wrSet_def even_loc_wrSet_empty_def )
  apply (subgoal_tac " tpc as ta = TPC.ReadResponding")
  prefer 2
  apply (simp add: tr_rel_def)
  apply (smt (z3) PC.simps(1658))
  apply simp
  apply (intro conjI allI impI)
  apply (metis TMRead_resp_trans_def assms(1) assms(2) assms(3) assms(5) assms(6) tr_rel_ReadResponding_self_lp)
  apply (metis TMRead_resp_trans_def assms(1) assms(2) assms(3) assms(5) assms(6) tr_rel_ReadResponding_stable_lp)
  apply (simp add:   TMRead_resp_trans_def)
  apply (unfold  read_prop_def)
  apply (subgoal_tac " tpc as ta = TPC.ReadResponding")
  prefer 2
  apply (simp add: tr_rel_def)
  apply (smt (z3) PC.simps(1658))
  by simp




end













