(*Showing that the simulation relation holds for the DTML Recover operation*)
theory Ref_Recover
imports "../Refinement"
begin


(*auxiliary lemma*)
lemma   tr_rel_readyToRec_self:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "  Recover_inv  syst  ((pc cs) syst)  cs"
and " TML_Recover syst   cs cs' "
and"   tr_rel   cs as syst"
and "((pc cs) syst)  = PC.ReadyToRecover"
and    "\<forall>t.  tms_inv as  t "
and  " ((pc cs) syst) \<noteq> RecIdle   \<longrightarrow> (\<forall> t  \<noteq> syst.  ((pc cs) t)   \<in> {PC.NotStarted, PC.Aborted, PC.Committed})"
shows " tr_rel cs' as syst"
  using assms
  apply (simp add:TML_Recover_def tr_rel_def  Recover_inv_def total_wfs_def tmstep_def tms_inv_def  )
  apply (case_tac " log cs = Map.empty")
   apply simp
  by simp


(*auxiliary lemma*)
lemma   tr_rel_readyToRec_stable:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "  Recover_inv  syst  ((pc cs) syst)  cs"
and " TML_Recover syst   cs cs' "
and"   tr_rel   cs as t"
and "((pc cs) syst)  = PC.ReadyToRecover"
and    "\<forall>t.  tms_inv as  t "
and " t \<noteq> syst"
and  " ((pc cs) syst) \<noteq> RecIdle   \<longrightarrow> (\<forall> t  \<noteq> syst.  ((pc cs) t)   \<in> {PC.NotStarted, PC.Aborted, PC.Committed})"
shows " tr_rel cs' as t"
  using assms
  apply (simp add:TML_Recover_def tr_rel_def  Recover_inv_def total_wfs_def tmstep_def tms_inv_def  )
  apply (case_tac " log cs = Map.empty")
   apply simp
   apply (cases "pc cs t ";simp)
  apply (smt (z3) TPC.simps(133) loc_zero_read_con2)
  apply (metis PC.distinct(1) PC.distinct(157) PC.distinct(97))
  apply (metis PC.distinct(173) PC.distinct(233) PC.distinct(3))
  apply (metis PC.distinct(247) PC.distinct(307) PC.distinct(5))
  apply (metis PC.distinct(319) PC.distinct(379) PC.distinct(7))
  apply (metis PC.distinct(389) PC.distinct(449) PC.distinct(9))
  apply (metis PC.distinct(11) PC.distinct(457) PC.distinct(517))
  apply (metis PC.distinct(13) PC.distinct(523) PC.distinct(583))
  apply (metis PC.distinct(21) PC.distinct(711) PC.distinct(827))
  apply (metis PC.distinct(23) PC.distinct(713) PC.distinct(883))
  apply (metis PC.distinct(25) PC.distinct(715) PC.distinct(937))
  apply (metis PC.distinct(27) PC.distinct(717) PC.distinct(989))
  apply (metis PC.distinct(1039) PC.distinct(29) PC.distinct(719))
  apply (metis PC.distinct(1087) PC.distinct(31) PC.distinct(721))
  apply (metis PC.distinct(1133) PC.distinct(33) PC.distinct(723))
  apply (metis PC.distinct(1177) PC.distinct(35) PC.distinct(725))
  apply (metis PC.distinct(1219) PC.distinct(37) PC.distinct(727))
  apply (metis PC.distinct(1259) PC.distinct(39) PC.distinct(729))
  apply (metis PC.distinct(1297) PC.distinct(41) PC.distinct(731))
  apply (metis PC.distinct(1333) PC.distinct(43) PC.distinct(733))
  apply (metis PC.distinct(1367) PC.distinct(45) PC.distinct(735))
  apply (metis PC.distinct(1399) PC.distinct(47) PC.distinct(737))
  apply (metis PC.distinct(1429) PC.distinct(49) PC.distinct(739))
  apply (metis PC.distinct(1457) PC.distinct(51) PC.distinct(741))
  apply (metis PC.distinct(1483) PC.distinct(53) PC.distinct(743))
  apply (metis PC.distinct(1639) PC.distinct(767) PC.distinct(77))
  apply (simp add: split if_splits)
  apply (cases "pc cs t ";simp)
  apply (smt (z3) TPC.simps(133) loc_zero_read_con2)
  apply (metis PC.distinct(1) PC.distinct(157) PC.distinct(97))
  apply (metis PC.distinct(173) PC.distinct(233) PC.distinct(3))
  apply (metis PC.distinct(247) PC.distinct(307) PC.distinct(5))
  apply (metis PC.distinct(319) PC.distinct(379) PC.distinct(7))
  apply (metis PC.distinct(389) PC.distinct(449) PC.distinct(9))
  apply (metis PC.distinct(11) PC.distinct(457) PC.distinct(517))
  apply (metis PC.distinct(13) PC.distinct(523) PC.distinct(583))
  apply (metis PC.distinct(21) PC.distinct(711) PC.distinct(827))
  apply (metis PC.distinct(23) PC.distinct(713) PC.distinct(883))
  apply (metis PC.distinct(25) PC.distinct(715) PC.distinct(937))
  apply (metis PC.distinct(27) PC.distinct(717) PC.distinct(989))
  apply (metis PC.distinct(1039) PC.distinct(29) PC.distinct(719))
  apply (metis PC.distinct(1087) PC.distinct(31) PC.distinct(721))
  apply (metis PC.distinct(1133) PC.distinct(33) PC.distinct(723))
  apply (metis PC.distinct(1177) PC.distinct(35) PC.distinct(725))
  apply (metis PC.distinct(1219) PC.distinct(37) PC.distinct(727))
  apply (metis PC.distinct(1259) PC.distinct(39) PC.distinct(729))
  apply (metis PC.distinct(1297) PC.distinct(41) PC.distinct(731))
  apply (metis PC.distinct(1333) PC.distinct(43) PC.distinct(733))
  apply (metis PC.distinct(1367) PC.distinct(45) PC.distinct(735))
  apply (metis PC.distinct(1399) PC.distinct(47) PC.distinct(737))
  apply (metis PC.distinct(1429) PC.distinct(49) PC.distinct(739))
  apply (metis PC.distinct(1457) PC.distinct(51) PC.distinct(741))
  apply (metis PC.distinct(1483) PC.distinct(53) PC.distinct(743))
  by (metis PC.distinct(1639) PC.distinct(767) PC.distinct(77))


(*the simulation relation holds for ReadyToRecover to Rec1 and ReadyToRecover to Rec6 (stuttering step) *)
lemma  f_sim_recover_readyToRec :
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "  Recover_inv  syst  ((pc cs) syst)  cs"
and " TML_Recover syst   cs cs' "
and "((pc cs) syst)  = PC.ReadyToRecover"
and " \<forall>t. tms_inv as  t "
and  " ((pc cs) syst) \<noteq> RecIdle   \<longrightarrow> (\<forall> t  \<noteq> syst.  ((pc cs) t)   \<in> {PC.NotStarted, PC.Aborted, PC.Committed})"
and" f_sim  cs as   "
shows "  f_sim  cs' as  "
  using assms
  apply (simp add:   f_sim_def TML_Recover_def split:if_splits )
  apply (intro conjI)
  apply (simp add: global_rel_def )
  apply (simp add:  no_read_rdSet_empty_def  no_write_wrSet_empty_def write_wrSet_notEmpty_def  read_rdSet_notEmpty_def  loc_in_wrSet_def even_loc_wrSet_empty_def odd_loc_wrSet_notEmpty_def)
  apply (simp add: global_rel_def )
  apply (metis assms(1) assms(4) assms(7) tr_rel_readyToRec_self tr_rel_readyToRec_stable)
  apply (unfold read_prop_def)
  apply (metis PC.distinct(1495) fun_upd_same)
  apply (intro conjI)
  apply (simp add: global_rel_def )
  apply (simp add:  no_read_rdSet_empty_def  no_write_wrSet_empty_def write_wrSet_notEmpty_def  read_rdSet_notEmpty_def  loc_in_wrSet_def even_loc_wrSet_empty_def odd_loc_wrSet_notEmpty_def)
  apply (metis assms(4) assms(7) thrdsvars_def tr_rel_readyToRec_self tr_rel_readyToRec_stable)
  by (metis PC.distinct(1485) fun_upd_same)

(***********************************************************************************************************)

(*auxiliary lemma*)
lemma   tr_rel_Rec1_self:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "  Recover_inv  syst  ((pc cs) syst)  cs"
and " TML_Recover syst   cs cs' "
and"   tr_rel   cs as syst"
and "((pc cs) syst)  = PC.Rec1 "
and    "\<forall>t.  tms_inv as  t "
and  " ((pc cs) syst) \<noteq> RecIdle   \<longrightarrow> (\<forall> t  \<noteq> syst.  ((pc cs) t)   \<in> {PC.NotStarted, PC.Aborted, PC.Committed})"
shows " tr_rel cs' as syst"
  using assms
  by (simp add:TML_Recover_def tr_rel_def  Recover_inv_def total_wfs_def tmstep_def tms_inv_def  )

(*auxiliary lemma*)
lemma   tr_rel_Rec1_stable:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "  Recover_inv  syst  ((pc cs) syst)  cs"
and " TML_Recover syst   cs cs' "
and"   tr_rel   cs as t"
and "((pc cs) syst)  = PC.Rec1"
and    "\<forall>t.  tms_inv as  t "
and " t \<noteq> syst"
and  " ((pc cs) syst) \<noteq> RecIdle   \<longrightarrow> (\<forall> t  \<noteq> syst.  ((pc cs) t)   \<in> {PC.NotStarted, PC.Aborted, PC.Committed})"
shows " tr_rel cs' as t"
using assms
  apply (simp add:TML_Recover_def tr_rel_def  Recover_inv_def total_wfs_def tmstep_def tms_inv_def  )
  apply (cases "pc cs t ";simp)
  apply (smt (z3) TPC.simps(133) loc_zero_read_con2)
  apply (metis PC.distinct(1) PC.distinct(157) PC.distinct(97))
  apply (metis PC.distinct(173) PC.distinct(233) PC.distinct(3))
  apply (metis PC.distinct(247) PC.distinct(307) PC.distinct(5))
  apply (metis PC.distinct(319) PC.distinct(379) PC.distinct(7))
  apply (metis PC.distinct(389) PC.distinct(449) PC.distinct(9))
  apply (metis PC.distinct(11) PC.distinct(457) PC.distinct(517))
  apply (metis PC.distinct(13) PC.distinct(523) PC.distinct(583))
  apply (metis PC.distinct(21) PC.distinct(711) PC.distinct(827))
  apply (metis PC.distinct(23) PC.distinct(713) PC.distinct(883))
  apply (metis PC.distinct(25) PC.distinct(715) PC.distinct(937))
  apply (metis PC.distinct(27) PC.distinct(717) PC.distinct(989))
  apply (metis PC.distinct(1039) PC.distinct(29) PC.distinct(719))
  apply (metis PC.distinct(1087) PC.distinct(31) PC.distinct(721))
  apply (metis PC.distinct(1133) PC.distinct(33) PC.distinct(723))
  apply (metis PC.distinct(1177) PC.distinct(35) PC.distinct(725))
  apply (metis PC.distinct(1219) PC.distinct(37) PC.distinct(727))
  apply (metis PC.distinct(1259) PC.distinct(39) PC.distinct(729))
  apply (metis PC.distinct(1297) PC.distinct(41) PC.distinct(731))
  apply (metis PC.distinct(1333) PC.distinct(43) PC.distinct(733))
  apply (metis PC.distinct(1367) PC.distinct(45) PC.distinct(735))
  apply (metis PC.distinct(1399) PC.distinct(47) PC.distinct(737))
  apply (metis PC.distinct(1429) PC.distinct(49) PC.distinct(739))
  apply (metis PC.distinct(1457) PC.distinct(51) PC.distinct(741))
  apply (metis PC.distinct(1483) PC.distinct(53) PC.distinct(743))
  by (metis PC.distinct(1639) PC.distinct(767) PC.distinct(77))




(*auxiliary lemma*)
lemma  f_sim_recover_Rec1 :
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "  Recover_inv  syst  ((pc cs) syst)  cs"
and " TML_Recover syst   cs cs' "
and "((pc cs) syst)  = PC.Rec1"
and " \<forall>t. tms_inv as  t "
and  " ((pc cs) syst) \<noteq> RecIdle   \<longrightarrow> (\<forall> t  \<noteq> syst.  ((pc cs) t)   \<in> {PC.NotStarted, PC.Aborted, PC.Committed})"
and" f_sim  cs as   "
shows "  f_sim  cs' as  "
  using assms
  apply (simp add:   f_sim_def TML_Recover_def split:if_splits )
  apply (intro conjI)
  apply (simp add: global_rel_def )
  apply (intro conjI allI)
  using reg_write_lastVal_ni apply presburger
  apply (metis option.distinct(1))
  apply (simp add:  no_read_rdSet_empty_def  no_write_wrSet_empty_def write_wrSet_notEmpty_def read_rdSet_notEmpty_def odd_loc_wrSet_notEmpty_def  loc_in_wrSet_def even_loc_wrSet_empty_def  Recover_inv_def)
  apply (metis PC.distinct(901) assms(1) assms(2) assms(3) assms(4) assms(7) tr_rel_Rec1_self tr_rel_Rec1_stable)
  apply (meson assms(1) assms(3) assms(4) assms(7) tr_rel_Rec1_self tr_rel_Rec1_stable)
  apply (unfold read_prop_def)
  by (metis (no_types, lifting) PC.distinct(1487) fun_upd_same)


(**********************************************************************************)

(*auxiliary lermma*)
lemma   tr_rel_Rec2_self:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "  Recover_inv  syst  ((pc cs) syst)  cs"
and " TML_Recover syst   cs cs' "
and"   tr_rel   cs as syst"
and "((pc cs) syst)  = PC.Rec2 "
and" f_sim  cs as   "
and    "\<forall>t.  tms_inv as  t "
and  " ((pc cs) syst) \<noteq> RecIdle   \<longrightarrow> (\<forall> t  \<noteq> syst.  ((pc cs) t)   \<in> {PC.NotStarted, PC.Aborted, PC.Committed})"
shows " tr_rel cs' as syst"
  using assms
  apply  (simp add:TML_Recover_def tr_rel_def  Recover_inv_def total_wfs_def tmstep_def tms_inv_def  )
  apply (simp add: f_sim_def global_rel_def)
  apply (simp add: maxIndex_def)
  by (metis domIff reg_same_st st_lastVal_lc)

(*auxliary lemma*)
lemma   tr_rel_Rec2_stable:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "  Recover_inv  syst  ((pc cs) syst)  cs"
and " TML_Recover syst   cs cs' "
and"   tr_rel   cs as t"
and "((pc cs) syst)  = PC.Rec2"
and    "\<forall>t.  tms_inv as  t "
and " t \<noteq> syst"
and  " ((pc cs) syst) \<noteq> RecIdle   \<longrightarrow> (\<forall> t  \<noteq> syst.  ((pc cs) t)   \<in> {PC.NotStarted, PC.Aborted, PC.Committed})"
shows " tr_rel cs' as t"
  using assms
  apply (simp add:TML_Recover_def tr_rel_def  Recover_inv_def total_wfs_def tmstep_def tms_inv_def  )
  apply (cases "pc cs t ";simp)
  apply (smt (z3) TPC.simps(133) loc_zero_read_con2)
  apply (metis PC.distinct(1) PC.distinct(157) PC.distinct(97))
  apply (metis PC.distinct(173) PC.distinct(233) PC.distinct(3))
  apply (metis PC.distinct(247) PC.distinct(307) PC.distinct(5))
  apply (metis PC.distinct(319) PC.distinct(379) PC.distinct(7))
  apply (metis PC.distinct(389) PC.distinct(449) PC.distinct(9))
  apply (metis PC.distinct(11) PC.distinct(457) PC.distinct(517))
  apply (metis PC.distinct(13) PC.distinct(523) PC.distinct(583))
  apply (metis PC.distinct(21) PC.distinct(711) PC.distinct(827))
  apply (metis PC.distinct(23) PC.distinct(713) PC.distinct(883))
  apply (metis PC.distinct(25) PC.distinct(715) PC.distinct(937))
  apply (metis PC.distinct(27) PC.distinct(717) PC.distinct(989))
  apply (metis PC.distinct(1039) PC.distinct(29) PC.distinct(719))
  apply (metis PC.distinct(1087) PC.distinct(31) PC.distinct(721))
  apply (metis PC.distinct(1133) PC.distinct(33) PC.distinct(723))
  apply (metis PC.distinct(1177) PC.distinct(35) PC.distinct(725))
  apply (metis PC.distinct(1219) PC.distinct(37) PC.distinct(727))
  apply (metis PC.distinct(1259) PC.distinct(39) PC.distinct(729))
  apply (metis PC.distinct(1297) PC.distinct(41) PC.distinct(731))
  apply (metis PC.distinct(1333) PC.distinct(43) PC.distinct(733))
  apply (metis PC.distinct(1367) PC.distinct(45) PC.distinct(735))
  apply (metis PC.distinct(1399) PC.distinct(47) PC.distinct(737))
  apply (metis PC.distinct(1429) PC.distinct(49) PC.distinct(739))
  apply (metis PC.distinct(1457) PC.distinct(51) PC.distinct(741))
  apply (metis PC.distinct(1483) PC.distinct(53) PC.distinct(743))
  by (metis PC.distinct(1639) PC.distinct(767) PC.distinct(77))


(*auxiliary lemma*)
lemma  pc_recover_Rec2 :
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "  Recover_inv  syst  ((pc cs) syst)  cs"
and " TML_Recover syst   cs cs' "
and "((pc cs) syst)  = PC.Rec2"
shows " ((pc cs') syst) \<noteq> RecIdle   "
  using assms
  by (simp add:  TML_Recover_def Recover_inv_def )




(*the simulation relation holds for Rec2 to Rec3 (stuttering step) *)
lemma  f_sim_recover_Rec2 :
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "  Recover_inv  syst  ((pc cs) syst)  cs"
and " TML_Recover syst   cs cs' "
and "((pc cs) syst)  = PC.Rec2"
and " \<forall>t. tms_inv as  t "
and  " ((pc cs) syst) \<noteq> RecIdle   \<longrightarrow> (\<forall> t  \<noteq> syst.  ((pc cs) t)   \<in> {PC.NotStarted, PC.Aborted, PC.Committed})"
and "  (  compval (\<tau> cs) (memory (\<tau> cs) ! 0) glb = survived_val (\<tau> cs) glb  \<and> (pc cs syst = RecIdle  \<longrightarrow>survived_val (\<tau> cs) glb   \<le>   recoveredGlb cs  )) "
and" f_sim  cs as   "
shows "  f_sim  cs' as  "
  using assms
  apply (simp add:   f_sim_def TML_Recover_def Recover_inv_def total_wfs_def  split:if_splits )
  apply (intro conjI)
    apply (simp add: global_rel_def)
    apply (intro conjI allI)
     apply (metis assms(2) domIff st_lv__daddr_ni)
    apply (metis option.distinct(1))
   apply (simp add:  no_read_rdSet_empty_def  no_write_wrSet_empty_def write_wrSet_notEmpty_def read_rdSet_notEmpty_def  loc_in_wrSet_def even_loc_wrSet_empty_def odd_loc_wrSet_notEmpty_def )
   apply (metis assms(1) assms(2) assms(3) assms(4) assms(7) assms(9) tr_rel_Rec2_self tr_rel_Rec2_stable)
  apply (unfold read_prop_def)
  by (metis assms(2) assms(3) assms(4) pc_recover_Rec2 thrdsvars_def)





(********************************************************************************)

(*auxiliary lemma*)
lemma   tr_rel_Rec3_self:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "  Recover_inv  syst  ((pc cs) syst)  cs"
and " TML_Recover syst   cs cs' "
and"   tr_rel   cs as syst"
and "((pc cs) syst)  = PC.Rec3 "
and" f_sim  cs as   "
and    "\<forall>t.  tms_inv as  t "
and  " ((pc cs) syst) \<noteq> RecIdle   \<longrightarrow> (\<forall> t  \<noteq> syst.  ((pc cs) t)   \<in> {PC.NotStarted, PC.Aborted, PC.Committed})"
shows " tr_rel cs' as syst"
  using assms
  apply  (simp add:TML_Recover_def tr_rel_def  Recover_inv_def total_wfs_def tmstep_def tms_inv_def  )
  apply (simp add: f_sim_def global_rel_def)
  apply (simp add: maxIndex_def)
  by (metis assms(2) domIff flo_lastVal_ni reg_same_flo)


(*auxiliary lemma*)
lemma   tr_rel_Rec3_stable:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "  Recover_inv  syst  ((pc cs) syst)  cs"
and " TML_Recover syst   cs cs' "
and"   tr_rel   cs as t"
and "((pc cs) syst)  = PC.Rec3"
and    "\<forall>t.  tms_inv as  t "
and " t \<noteq> syst"
and  " ((pc cs) syst) \<noteq> RecIdle   \<longrightarrow> (\<forall> t  \<noteq> syst.  ((pc cs) t)   \<in> {PC.NotStarted, PC.Aborted, PC.Committed})"
shows " tr_rel cs' as t"
  using assms
  apply (simp add:TML_Recover_def tr_rel_def  Recover_inv_def total_wfs_def tmstep_def tms_inv_def  )
  apply (cases "pc cs t ";simp)
  apply (smt (z3) TPC.simps(133) loc_zero_read_con2)
  apply (metis PC.distinct(1) PC.distinct(157) PC.distinct(97))
  apply (metis PC.distinct(173) PC.distinct(233) PC.distinct(3))
  apply (metis PC.distinct(247) PC.distinct(307) PC.distinct(5))
  apply (metis PC.distinct(319) PC.distinct(379) PC.distinct(7))
  apply (metis PC.distinct(389) PC.distinct(449) PC.distinct(9))
  apply (metis PC.distinct(11) PC.distinct(457) PC.distinct(517))
  apply (metis PC.distinct(13) PC.distinct(523) PC.distinct(583))
  apply (metis PC.distinct(21) PC.distinct(711) PC.distinct(827))
  apply (metis PC.distinct(23) PC.distinct(713) PC.distinct(883))
  apply (metis PC.distinct(25) PC.distinct(715) PC.distinct(937))
  apply (metis PC.distinct(27) PC.distinct(717) PC.distinct(989))
  apply (metis PC.distinct(1039) PC.distinct(29) PC.distinct(719))
  apply (metis PC.distinct(1087) PC.distinct(31) PC.distinct(721))
  apply (metis PC.distinct(1133) PC.distinct(33) PC.distinct(723))
  apply (metis PC.distinct(1177) PC.distinct(35) PC.distinct(725))
  apply (metis PC.distinct(1219) PC.distinct(37) PC.distinct(727))
  apply (metis PC.distinct(1259) PC.distinct(39) PC.distinct(729))
  apply (metis PC.distinct(1297) PC.distinct(41) PC.distinct(731))
  apply (metis PC.distinct(1333) PC.distinct(43) PC.distinct(733))
  apply (metis PC.distinct(1367) PC.distinct(45) PC.distinct(735))
  apply (metis PC.distinct(1399) PC.distinct(47) PC.distinct(737))
  apply (metis PC.distinct(1429) PC.distinct(49) PC.distinct(739))
  apply (metis PC.distinct(1457) PC.distinct(51) PC.distinct(741))
  apply (metis PC.distinct(1483) PC.distinct(53) PC.distinct(743))
  by (metis PC.distinct(1639) PC.distinct(767) PC.distinct(77))



(*auxiliary lemma*)
lemma  pc_recover_Rec3 :
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "  Recover_inv  syst  ((pc cs) syst)  cs"
and " TML_Recover syst   cs cs' "
and "((pc cs) syst)  = PC.Rec3"
shows " ((pc cs') syst) \<noteq> RecIdle   "
using assms
by (simp add:  TML_Recover_def Recover_inv_def )



(*the simulation relation holds for Rec3 to Rec4 (stuttering step) *)
lemma  f_sim_recover_Rec3 :
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "  Recover_inv  syst  ((pc cs) syst)  cs"
and " TML_Recover syst   cs cs' "
and "((pc cs) syst)  = PC.Rec3"
and " \<forall>t. tms_inv as  t "
and  " ((pc cs) syst) \<noteq> RecIdle   \<longrightarrow> (\<forall> t  \<noteq> syst.  ((pc cs) t)   \<in> {PC.NotStarted, PC.Aborted, PC.Committed})"
and" f_sim  cs as   "
shows "  f_sim  cs' as  "
  using assms
  apply (simp add:   f_sim_def TML_Recover_def Recover_inv_def total_wfs_def  split:if_splits )
  apply (intro conjI)
  apply (simp add: global_rel_def)
  apply (intro conjI allI)
  apply (metis assms(2) flo_lastVal_ni)
  apply (metis option.distinct(1))
  apply (simp add:  no_read_rdSet_empty_def  no_write_wrSet_empty_def write_wrSet_notEmpty_def read_rdSet_notEmpty_def  loc_in_wrSet_def even_loc_wrSet_empty_def odd_loc_wrSet_notEmpty_def)
  apply (metis assms(1) assms(2) assms(3) assms(4) assms(7) assms(8) tr_rel_Rec3_self tr_rel_Rec3_stable)
  apply (unfold read_prop_def)
  by (metis assms(1) assms(2) assms(3) assms(4) pc_recover_Rec3)



(*****************************************************************)
(*auxiliary lemma*)
lemma   tr_rel_Rec4_self:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "  Recover_inv  syst  ((pc cs) syst)  cs"
and " TML_Recover syst   cs cs' "
and"   tr_rel   cs as syst"
and "((pc cs) syst)  = PC.Rec4 "
and" f_sim  cs as   "
and    "\<forall>t.  tms_inv as  t "
and  " ((pc cs) syst) \<noteq> RecIdle   \<longrightarrow> (\<forall> t  \<noteq> syst.  ((pc cs) t)   \<in> {PC.NotStarted, PC.Aborted, PC.Committed})"
shows " tr_rel cs' as syst"
  using assms
  apply  (simp add:TML_Recover_def tr_rel_def  Recover_inv_def total_wfs_def tmstep_def tms_inv_def  )
  apply (simp add: f_sim_def global_rel_def)
  apply (simp add: maxIndex_def)
  by (metis empty_iff insert_iff reg_same_sfence sfence_lastVal_ni)


(*auxiliary lemma*)
lemma   tr_rel_Rec4_stable:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "  Recover_inv  syst  ((pc cs) syst)  cs"
and " TML_Recover syst   cs cs' "
and"   tr_rel   cs as t"
and "((pc cs) syst)  = PC.Rec4"
and    "\<forall>t.  tms_inv as  t "
and " t \<noteq> syst"
and  " ((pc cs) syst) \<noteq> RecIdle   \<longrightarrow> (\<forall> t  \<noteq> syst.  ((pc cs) t)   \<in> {PC.NotStarted, PC.Aborted, PC.Committed})"
shows " tr_rel cs' as t"
  using assms
  apply (simp add:TML_Recover_def tr_rel_def  Recover_inv_def total_wfs_def tmstep_def tms_inv_def  )
  apply (cases "pc cs t ";simp)
  apply (smt (z3) TPC.simps(133) loc_zero_read_con2)
  apply (metis PC.distinct(1) PC.distinct(157) PC.distinct(97))
  apply (metis PC.distinct(173) PC.distinct(233) PC.distinct(3))
  apply (metis PC.distinct(247) PC.distinct(307) PC.distinct(5))
  apply (metis PC.distinct(319) PC.distinct(379) PC.distinct(7))
  apply (metis PC.distinct(389) PC.distinct(449) PC.distinct(9))
  apply (metis PC.distinct(11) PC.distinct(457) PC.distinct(517))
  apply (metis PC.distinct(13) PC.distinct(523) PC.distinct(583))
  apply (metis PC.distinct(21) PC.distinct(711) PC.distinct(827))
  apply (metis PC.distinct(23) PC.distinct(713) PC.distinct(883))
  apply (metis PC.distinct(25) PC.distinct(715) PC.distinct(937))
  apply (metis PC.distinct(27) PC.distinct(717) PC.distinct(989))
  apply (metis PC.distinct(1039) PC.distinct(29) PC.distinct(719))
  apply (metis PC.distinct(1087) PC.distinct(31) PC.distinct(721))
  apply (metis PC.distinct(1133) PC.distinct(33) PC.distinct(723))
  apply (metis PC.distinct(1177) PC.distinct(35) PC.distinct(725))
  apply (metis PC.distinct(1219) PC.distinct(37) PC.distinct(727))
  apply (metis PC.distinct(1259) PC.distinct(39) PC.distinct(729))
  apply (metis PC.distinct(1297) PC.distinct(41) PC.distinct(731))
  apply (metis PC.distinct(1333) PC.distinct(43) PC.distinct(733))
  apply (metis PC.distinct(1367) PC.distinct(45) PC.distinct(735))
  apply (metis PC.distinct(1399) PC.distinct(47) PC.distinct(737))
  apply (metis PC.distinct(1429) PC.distinct(49) PC.distinct(739))
  apply (metis PC.distinct(1457) PC.distinct(51) PC.distinct(741))
  apply (metis PC.distinct(1483) PC.distinct(53) PC.distinct(743))
  by (metis PC.distinct(1639) PC.distinct(767) PC.distinct(77))



(*auxiliary lemma*)
lemma  pc_recover_Rec4 :
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "  Recover_inv  syst  ((pc cs) syst)  cs"
and " TML_Recover syst   cs cs' "
and "((pc cs) syst)  = PC.Rec4"
shows " ((pc cs') syst) \<noteq> RecIdle   "
using assms
by (simp add:  TML_Recover_def Recover_inv_def )


(*the simulation relation holds for Rec4 to Rec5 (stuttering step) *)
lemma  f_sim_recover_Rec4 :
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "  Recover_inv  syst  ((pc cs) syst)  cs"
and " TML_Recover syst   cs cs' "
and "((pc cs) syst)  = PC.Rec4"
and " \<forall>t. tms_inv as  t "
and  " ((pc cs) syst) \<noteq> RecIdle   \<longrightarrow> (\<forall> t  \<noteq> syst.  ((pc cs) t)   \<in> {PC.NotStarted, PC.Aborted, PC.Committed})"
and" f_sim  cs as   "
shows "  f_sim  cs' as  "
  using assms
  apply (simp add:   f_sim_def TML_Recover_def Recover_inv_def total_wfs_def  split:if_splits )
  apply (intro conjI)
  apply (simp add: global_rel_def)
  apply (intro conjI allI)
  apply (meson sfence_lastVal_ni)
  apply (metis option.distinct(1))
  apply (simp add:  no_read_rdSet_empty_def  no_write_wrSet_empty_def write_wrSet_notEmpty_def  read_rdSet_notEmpty_def  loc_in_wrSet_def even_loc_wrSet_empty_def odd_loc_wrSet_notEmpty_def)
  apply (metis assms(1) assms(2) assms(3) assms(4) assms(7) assms(8) tr_rel_Rec4_self tr_rel_Rec4_stable)
  apply (unfold read_prop_def)
  by (metis assms(1) assms(2) assms(3) assms(4) pc_recover_Rec4)




(*************************************************************************************************)

(*auxiliary lemma*)
lemma   tr_rel_Rec5_self:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "  Recover_inv  syst  ((pc cs) syst)  cs"
and " TML_Recover syst   cs cs' "
and"   tr_rel   cs as syst"
and "((pc cs) syst)  = PC.Rec5 "
and" f_sim  cs as   "
and    "\<forall>t.  tms_inv as  t "
and  " ((pc cs) syst) \<noteq> RecIdle   \<longrightarrow> (\<forall> t  \<noteq> syst.  ((pc cs) t)   \<in> {PC.NotStarted, PC.Aborted, PC.Committed})"
shows " tr_rel cs' as syst"
  using assms
  by  (simp add:TML_Recover_def tr_rel_def  Recover_inv_def total_wfs_def tmstep_def tms_inv_def  )

(*auxiliary lemma*)
lemma   tr_rel_Rec5_stable:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "  Recover_inv  syst  ((pc cs) syst)  cs"
and " TML_Recover syst   cs cs' "
and"   tr_rel   cs as t"
and "((pc cs) syst)  = PC.Rec5"
and    "\<forall>t.  tms_inv as  t "
and " t \<noteq> syst"
and  " ((pc cs) syst) \<noteq> RecIdle   \<longrightarrow> (\<forall> t  \<noteq> syst.  ((pc cs) t)   \<in> {PC.NotStarted, PC.Aborted, PC.Committed})"
shows " tr_rel cs' as t"
  using assms
  apply (simp add:TML_Recover_def tr_rel_def  Recover_inv_def total_wfs_def tmstep_def tms_inv_def  )
  apply (cases "pc cs t ";simp)
  apply (smt (z3) TPC.simps(133) loc_zero_read_con2)
  apply (metis PC.distinct(1) PC.distinct(157) PC.distinct(97))
  apply (metis PC.distinct(173) PC.distinct(233) PC.distinct(3))
  apply (metis PC.distinct(247) PC.distinct(307) PC.distinct(5))
  apply (metis PC.distinct(319) PC.distinct(379) PC.distinct(7))
  apply (metis PC.distinct(389) PC.distinct(449) PC.distinct(9))
  apply (metis PC.distinct(11) PC.distinct(457) PC.distinct(517))
  apply (metis PC.distinct(13) PC.distinct(523) PC.distinct(583))
  apply (metis PC.distinct(21) PC.distinct(711) PC.distinct(827))
  apply (metis PC.distinct(23) PC.distinct(713) PC.distinct(883))
  apply (metis PC.distinct(25) PC.distinct(715) PC.distinct(937))
  apply (metis PC.distinct(27) PC.distinct(717) PC.distinct(989))
  apply (metis PC.distinct(1039) PC.distinct(29) PC.distinct(719))
  apply (metis PC.distinct(1087) PC.distinct(31) PC.distinct(721))
  apply (metis PC.distinct(1133) PC.distinct(33) PC.distinct(723))
  apply (metis PC.distinct(1177) PC.distinct(35) PC.distinct(725))
  apply (metis PC.distinct(1219) PC.distinct(37) PC.distinct(727))
  apply (metis PC.distinct(1259) PC.distinct(39) PC.distinct(729))
  apply (metis PC.distinct(1297) PC.distinct(41) PC.distinct(731))
  apply (metis PC.distinct(1333) PC.distinct(43) PC.distinct(733))
  apply (metis PC.distinct(1367) PC.distinct(45) PC.distinct(735))
  apply (metis PC.distinct(1399) PC.distinct(47) PC.distinct(737))
  apply (metis PC.distinct(1429) PC.distinct(49) PC.distinct(739))
  apply (metis PC.distinct(1457) PC.distinct(51) PC.distinct(741))
  apply (metis PC.distinct(1483) PC.distinct(53) PC.distinct(743))
  by (metis PC.distinct(1639) PC.distinct(767) PC.distinct(77))




(*the simulation relation holds for Rec5 to Rec6 (stuttering step) *)
lemma  f_sim_recover_Rec5 :
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "  Recover_inv  syst  ((pc cs) syst)  cs"
and " TML_Recover syst   cs cs' "
and "((pc cs) syst)  = PC.Rec5"
and " \<forall>t. tms_inv as  t "
and  " ((pc cs) syst) \<noteq> RecIdle   \<longrightarrow> (\<forall> t  \<noteq> syst.  ((pc cs) t)   \<in> {PC.NotStarted, PC.Aborted, PC.Committed})"
and" f_sim  cs as   "
shows "  f_sim  cs' as  "
  using assms
  apply (simp add:   f_sim_def TML_Recover_def Recover_inv_def total_wfs_def  split:if_splits )
  apply (intro conjI)
  apply (simp add: global_rel_def)
  apply (intro conjI allI)
  apply blast
  apply (simp add: tr_rel_def)
  apply (smt (z3) One_nat_def PC.simps(1674) domIff)
  apply (simp add:  no_read_rdSet_empty_def  no_write_wrSet_empty_def write_wrSet_notEmpty_def read_rdSet_notEmpty_def  loc_in_wrSet_def even_loc_wrSet_empty_def odd_loc_wrSet_notEmpty_def)
  apply  (metis assms(1) assms(2) assms(3) assms(4) assms(7) assms(8) tr_rel_Rec5_self tr_rel_Rec5_stable)
  apply (unfold read_prop_def)
  by (metis PC.distinct(1503) fun_upd_same)

(*********************************************************)
(*auxiliary lemma*)
lemma   tr_rel_Rec6_self:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "  Recover_inv  syst  ((pc cs) syst)  cs"
and " TML_Recover syst   cs cs' "
and"   tr_rel   cs as syst"
and "((pc cs) syst)  = PC.Rec6 "
and" f_sim  cs as   "
and    "\<forall>t.  tms_inv as  t "
and  " ((pc cs) syst) \<noteq> RecIdle   \<longrightarrow> (\<forall> t  \<noteq> syst.  ((pc cs) t)   \<in> {PC.NotStarted, PC.Aborted, PC.Committed})"
shows " tr_rel cs' as syst"
  using assms
  by  (simp add:TML_Recover_def tr_rel_def  Recover_inv_def total_wfs_def tmstep_def tms_inv_def  )



(*auxiliary lemma*)
lemma   tr_rel_Rec6_stable:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "  Recover_inv  syst  ((pc cs) syst)  cs"
and " TML_Recover syst   cs cs' "
and"   tr_rel   cs as t"
and "((pc cs) syst)  = PC.Rec6"
and    "\<forall>t.  tms_inv as  t "
and " t \<noteq> syst"
and  " ((pc cs) syst) \<noteq> RecIdle   \<longrightarrow> (\<forall> t  \<noteq> syst.  ((pc cs) t)   \<in> {PC.NotStarted, PC.Aborted, PC.Committed})"
shows " tr_rel cs' as t"
  using assms
  apply (simp add:TML_Recover_def tr_rel_def  Recover_inv_def total_wfs_def tmstep_def tms_inv_def  )
    (* apply (subgoal_tac "pc cs t   \<in> {PC.NotStarted, PC.Aborted, PC.Committed} ")
prefer 2
using PC.distinct(785) assms(9) apply presburger
apply (simp add: in_flight_def)
using [[simp_trace_new]]

by (smt (z3) PC.simps(931) PC.simps(937) PC.simps(961) TPC.simps(13) loc_zero_read_con2)*)
  apply (cases "pc cs t ";simp)
    (*  apply (subgoal_tac" False ")
prefer 2
sledgehammer*)  apply (smt (z3) TPC.simps(133) loc_zero_read_con2)
  apply (metis PC.distinct(1) PC.distinct(157) PC.distinct(97))
  apply (metis PC.distinct(173) PC.distinct(233) PC.distinct(3))
  apply (metis PC.distinct(247) PC.distinct(307) PC.distinct(5))
  apply (metis PC.distinct(319) PC.distinct(379) PC.distinct(7))
  apply (metis PC.distinct(389) PC.distinct(449) PC.distinct(9))
  apply (metis PC.distinct(11) PC.distinct(457) PC.distinct(517))
  apply (metis PC.distinct(13) PC.distinct(523) PC.distinct(583))
  apply (metis PC.distinct(21) PC.distinct(711) PC.distinct(827))
  apply (metis PC.distinct(23) PC.distinct(713) PC.distinct(883))
  apply (metis PC.distinct(25) PC.distinct(715) PC.distinct(937))
  apply (metis PC.distinct(27) PC.distinct(717) PC.distinct(989))
  apply (metis PC.distinct(1039) PC.distinct(29) PC.distinct(719))
  apply (metis PC.distinct(1087) PC.distinct(31) PC.distinct(721))
  apply (metis PC.distinct(1133) PC.distinct(33) PC.distinct(723))
  apply (metis PC.distinct(1177) PC.distinct(35) PC.distinct(725))
  apply (metis PC.distinct(1219) PC.distinct(37) PC.distinct(727))
  apply (metis PC.distinct(1259) PC.distinct(39) PC.distinct(729))
  apply (metis PC.distinct(1297) PC.distinct(41) PC.distinct(731))
  apply (metis PC.distinct(1333) PC.distinct(43) PC.distinct(733))
  apply (metis PC.distinct(1367) PC.distinct(45) PC.distinct(735))
  apply (metis PC.distinct(1399) PC.distinct(47) PC.distinct(737))
  apply (metis PC.distinct(1429) PC.distinct(49) PC.distinct(739))
  apply (metis PC.distinct(1457) PC.distinct(51) PC.distinct(741))
  apply (metis PC.distinct(1483) PC.distinct(53) PC.distinct(743))
  by (metis PC.distinct(1639) PC.distinct(767) PC.distinct(77))




(*auxiliary lemma*)
lemma  pc_recover_Rec6 :
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "  Recover_inv  syst  ((pc cs) syst)  cs"
and " TML_Recover syst   cs cs' "
and "((pc cs) syst)  = PC.Rec6"
shows " ((pc cs') syst) \<noteq> RecIdle   "
  using assms
  by (simp add:  TML_Recover_def Recover_inv_def )




(*the simulation relation holds for Rec6 to Rec7 (stuttering step) *)
lemma  f_sim_recover_Rec6 :
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "  Recover_inv  syst  ((pc cs) syst)  cs"
and " TML_Recover syst   cs cs' "
and "((pc cs) syst)  = PC.Rec6"
and " \<forall>t. tms_inv as  t "
and  " ((pc cs) syst) \<noteq> RecIdle   \<longrightarrow> (\<forall> t  \<noteq> syst.  ((pc cs) t)   \<in> {PC.NotStarted, PC.Aborted, PC.Committed})"
and" f_sim  cs as   "
shows "  f_sim  cs' as  "
  using assms
  apply (simp add:   f_sim_def TML_Recover_def Recover_inv_def total_wfs_def  split:if_splits )
  apply (intro conjI)
  apply (simp add: global_rel_def)
  apply (intro conjI allI)
  using assms(2) lastVal_ni apply presburger
  apply (simp add:  no_read_rdSet_empty_def  no_write_wrSet_empty_def write_wrSet_notEmpty_def read_rdSet_notEmpty_def loc_in_wrSet_def even_loc_wrSet_empty_def odd_loc_wrSet_notEmpty_def)
  apply (metis assms(1) assms(2) assms(3) assms(4) assms(7) assms(8) tr_rel_Rec6_self tr_rel_Rec6_stable)
  apply (unfold read_prop_def)
  by (metis assms(1) assms(2) assms(3) assms(4) pc_recover_Rec6)


(**********************************************************)

(*auxiliary lemma*)
lemma   tr_rel_Rec7_self:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "  Recover_inv  syst  ((pc cs) syst)  cs"
and " TML_Recover syst   cs cs' "
and"   tr_rel   cs as syst"
and "((pc cs) syst)  = PC.Rec7 "
and" f_sim  cs as   "
and    "\<forall>t.  tms_inv as  t "
and  " ((pc cs) syst) \<noteq> RecIdle   \<longrightarrow> (\<forall> t  \<noteq> syst.  ((pc cs) t)   \<in> {PC.NotStarted, PC.Aborted, PC.Committed})"
shows " tr_rel cs' as syst"
  using assms
  by (simp add:TML_Recover_def tr_rel_def  Recover_inv_def total_wfs_def tmstep_def tms_inv_def  split:if_splits )


(*auxiliary lemma*)
lemma   tr_rel_Rec7_stable:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "  Recover_inv  syst  ((pc cs) syst)  cs"
and " TML_Recover syst   cs cs' "
and"   tr_rel   cs as t"
and "((pc cs) syst)  = PC.Rec7"
and    "\<forall>t.  tms_inv as  t "
and " t \<noteq> syst"
and  " ((pc cs) syst) \<noteq> RecIdle   \<longrightarrow> (\<forall> t  \<noteq> syst.  ((pc cs) t)   \<in> {PC.NotStarted, PC.Aborted, PC.Committed})"
shows " tr_rel cs' as t"
  using assms
  apply (simp add:TML_Recover_def tr_rel_def  Recover_inv_def total_wfs_def tmstep_def tms_inv_def   )
  apply (case_tac " even (survived_val (\<tau> cs) glb)")
   apply simp
   apply (cases "pc cs t ";simp)
  apply (smt (z3) TPC.simps(133) loc_zero_read_con2)
  apply (metis PC.distinct(1) PC.distinct(157) PC.distinct(97))
  apply (metis PC.distinct(173) PC.distinct(233) PC.distinct(3))
  apply (metis PC.distinct(247) PC.distinct(307) PC.distinct(5))
  apply (metis PC.distinct(319) PC.distinct(379) PC.distinct(7))
  apply (metis PC.distinct(389) PC.distinct(449) PC.distinct(9))
  apply (metis PC.distinct(11) PC.distinct(457) PC.distinct(517))
  apply (metis PC.distinct(13) PC.distinct(523) PC.distinct(583))
  apply (metis PC.distinct(21) PC.distinct(711) PC.distinct(827))
  apply (metis PC.distinct(23) PC.distinct(713) PC.distinct(883))
  apply (metis PC.distinct(25) PC.distinct(715) PC.distinct(937))
  apply (metis PC.distinct(27) PC.distinct(717) PC.distinct(989))
  apply (metis PC.distinct(1039) PC.distinct(29) PC.distinct(719))
  apply (metis PC.distinct(1087) PC.distinct(31) PC.distinct(721))
  apply (metis PC.distinct(1133) PC.distinct(33) PC.distinct(723))
  apply (metis PC.distinct(1177) PC.distinct(35) PC.distinct(725))
  apply (metis PC.distinct(1219) PC.distinct(37) PC.distinct(727))
  apply (metis PC.distinct(1259) PC.distinct(39) PC.distinct(729))
  apply (metis PC.distinct(1297) PC.distinct(41) PC.distinct(731))
  apply (metis PC.distinct(1333) PC.distinct(43) PC.distinct(733))
  apply (metis PC.distinct(1367) PC.distinct(45) PC.distinct(735))
  apply (metis PC.distinct(1399) PC.distinct(47) PC.distinct(737))
  apply (metis PC.distinct(1429) PC.distinct(49) PC.distinct(739))
  apply (metis PC.distinct(1457) PC.distinct(51) PC.distinct(741))
  apply (metis PC.distinct(1483) PC.distinct(53) PC.distinct(743))
  apply (metis PC.distinct(1639) PC.distinct(767) PC.distinct(77))
  apply (cases "pc cs t ";simp)
  apply (smt (z3) TPC.simps(133) loc_zero_read_con2)
  apply (metis PC.distinct(1) PC.distinct(157) PC.distinct(97))
  apply (metis PC.distinct(173) PC.distinct(233) PC.distinct(3))
  apply (metis PC.distinct(247) PC.distinct(307) PC.distinct(5))
  apply (metis PC.distinct(319) PC.distinct(379) PC.distinct(7))
  apply (metis PC.distinct(389) PC.distinct(449) PC.distinct(9))
  apply (metis PC.distinct(11) PC.distinct(457) PC.distinct(517))
  apply (metis PC.distinct(13) PC.distinct(523) PC.distinct(583))
  apply (metis PC.distinct(21) PC.distinct(711) PC.distinct(827))
  apply (metis PC.distinct(23) PC.distinct(713) PC.distinct(883))
  apply (metis PC.distinct(25) PC.distinct(715) PC.distinct(937))
  apply (metis PC.distinct(27) PC.distinct(717) PC.distinct(989))
  apply (metis PC.distinct(1039) PC.distinct(29) PC.distinct(719))
  apply (metis PC.distinct(1087) PC.distinct(31) PC.distinct(721))
  apply (metis PC.distinct(1133) PC.distinct(33) PC.distinct(723))
  apply (metis PC.distinct(1177) PC.distinct(35) PC.distinct(725))
  apply (metis PC.distinct(1219) PC.distinct(37) PC.distinct(727))
  apply (metis PC.distinct(1259) PC.distinct(39) PC.distinct(729))
  apply (metis PC.distinct(1297) PC.distinct(41) PC.distinct(731))
  apply (metis PC.distinct(1333) PC.distinct(43) PC.distinct(733))
  apply (metis PC.distinct(1367) PC.distinct(45) PC.distinct(735))
  apply (metis PC.distinct(1399) PC.distinct(47) PC.distinct(737))
  apply (metis PC.distinct(1429) PC.distinct(49) PC.distinct(739))
  apply (metis PC.distinct(1457) PC.distinct(51) PC.distinct(741))
  apply (metis PC.distinct(1483) PC.distinct(53) PC.distinct(743))
  by (metis PC.distinct(1639) PC.distinct(767) PC.distinct(77))


(*the simulation relation holds for Rec7 to Rec8 and  for Rec7 to Rec9  (stuttering step) *)
lemma  f_sim_recover_Rec7 :
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "  Recover_inv  syst  ((pc cs) syst)  cs"
and " TML_Recover syst   cs cs' "
and "((pc cs) syst)  = PC.Rec7"
and " \<forall>t. tms_inv as  t "
and  " ((pc cs) syst) \<noteq> RecIdle   \<longrightarrow> (\<forall> t  \<noteq> syst.  ((pc cs) t)   \<in> {PC.NotStarted, PC.Aborted, PC.Committed})"
and" f_sim  cs as   "
shows "  f_sim  cs' as  "
  using assms
  apply (simp add:   f_sim_def TML_Recover_def Recover_inv_def total_wfs_def  split:if_splits )
  apply (intro conjI)
  apply (simp add: global_rel_def)
  apply (simp add:  no_read_rdSet_empty_def  no_write_wrSet_empty_def write_wrSet_notEmpty_def read_rdSet_notEmpty_def  loc_in_wrSet_def even_loc_wrSet_empty_def odd_loc_wrSet_notEmpty_def)
  apply (metis assms(1) assms(2) assms(3) assms(4) assms(7) assms(8) tr_rel_Rec7_self tr_rel_Rec7_stable)
  apply (simp(no_asm) add:  read_prop_def)
  apply (metis (no_types, opaque_lifting) comploc_def i_noteqo_loc)
  apply (intro conjI)
  apply (simp add: global_rel_def)
  apply (simp add:  no_read_rdSet_empty_def  no_write_wrSet_empty_def write_wrSet_notEmpty_def read_rdSet_notEmpty_def loc_in_wrSet_def even_loc_wrSet_empty_def odd_loc_wrSet_notEmpty_def)
  apply (metis assms(1) assms(2) assms(3) assms(4) assms(7) assms(8) tr_rel_Rec7_self tr_rel_Rec7_stable)
  apply (simp(no_asm) add:  read_prop_def)
  by (metis (no_types, opaque_lifting) comploc_def i_noteqo_loc)



(*******************************************)
(*auxiliary lemma*)
lemma   tr_rel_Rec8_self:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "  Recover_inv  syst  ((pc cs) syst)  cs"
and " TML_Recover syst   cs cs' "
and"   tr_rel   cs as syst"
and "((pc cs) syst)  = PC.Rec8 "
and" f_sim  cs as   "
and    "\<forall>t.  tms_inv as  t "
and  " ((pc cs) syst) \<noteq> RecIdle   \<longrightarrow> (\<forall> t  \<noteq> syst.  ((pc cs) t)   \<in> {PC.NotStarted, PC.Aborted, PC.Committed})"
shows " tr_rel cs' as syst"
  using assms
  by (simp add:TML_Recover_def tr_rel_def  Recover_inv_def total_wfs_def tmstep_def tms_inv_def  split:if_splits )

(*auxiliary lemma*)
lemma   tr_rel_Rec8_stable:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "  Recover_inv  syst  ((pc cs) syst)  cs"
and " TML_Recover syst   cs cs' "
and"   tr_rel   cs as t"
and "((pc cs) syst)  = PC.Rec8"
and    "\<forall>t.  tms_inv as  t "
and " t \<noteq> syst"
and  " ((pc cs) syst) \<noteq> RecIdle   \<longrightarrow> (\<forall> t  \<noteq> syst.  ((pc cs) t)   \<in> {PC.NotStarted, PC.Aborted, PC.Committed})"
shows " tr_rel cs' as t"
  using assms
  apply (simp add:TML_Recover_def tr_rel_def  Recover_inv_def total_wfs_def tmstep_def tms_inv_def   )
  apply (cases "pc cs t ";simp)
  apply (smt (z3) TPC.simps(133) loc_zero_read_con2)
  apply (metis PC.distinct(1) PC.distinct(157) PC.distinct(97))
  apply (metis PC.distinct(173) PC.distinct(233) PC.distinct(3))
  apply (metis PC.distinct(247) PC.distinct(307) PC.distinct(5))
  apply (metis PC.distinct(319) PC.distinct(379) PC.distinct(7))
  apply (metis PC.distinct(389) PC.distinct(449) PC.distinct(9))
  apply (metis PC.distinct(11) PC.distinct(457) PC.distinct(517))
  apply (metis PC.distinct(13) PC.distinct(523) PC.distinct(583))
  apply (metis PC.distinct(21) PC.distinct(711) PC.distinct(827))
  apply (metis PC.distinct(23) PC.distinct(713) PC.distinct(883))
  apply (metis PC.distinct(25) PC.distinct(715) PC.distinct(937))
  apply (metis PC.distinct(27) PC.distinct(717) PC.distinct(989))
  apply (metis PC.distinct(1039) PC.distinct(29) PC.distinct(719))
  apply (metis PC.distinct(1087) PC.distinct(31) PC.distinct(721))
  apply (metis PC.distinct(1133) PC.distinct(33) PC.distinct(723))
  apply (metis PC.distinct(1177) PC.distinct(35) PC.distinct(725))
  apply (metis PC.distinct(1219) PC.distinct(37) PC.distinct(727))
  apply (metis PC.distinct(1259) PC.distinct(39) PC.distinct(729))
  apply (metis PC.distinct(1297) PC.distinct(41) PC.distinct(731))
  apply (metis PC.distinct(1333) PC.distinct(43) PC.distinct(733))
  apply (metis PC.distinct(1367) PC.distinct(45) PC.distinct(735))
  apply (metis PC.distinct(1399) PC.distinct(47) PC.distinct(737))
  apply (metis PC.distinct(1429) PC.distinct(49) PC.distinct(739))
  apply (metis PC.distinct(1457) PC.distinct(51) PC.distinct(741))
  apply (metis PC.distinct(1483) PC.distinct(53) PC.distinct(743))
  by (metis PC.distinct(1639) PC.distinct(767) PC.distinct(77))







lemma apply_partial_none:
assumes "  (log cs') = Map.empty"
shows " apply_partial ((tmemory as) ! 0) (log cs') l  = ((tmemory as) ! 0) l   "
using assms
  by (simp add: apply_partial_def)


(*auxiliary lemma*)
lemma  golbal_rel__im_recover_Rec8 :
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "  Recover_inv  syst  ((pc cs) syst)  cs"
and " TML_Recover syst   cs cs' "
and "((pc cs) syst)  = PC.Rec8"
and " (tmemory as) \<noteq> [] "
and " \<forall>t. tms_inv as  t "
and  " ((pc cs) syst) \<noteq> RecIdle   \<longrightarrow> (\<forall> t  \<noteq> syst.  ((pc cs) t)   \<in> {PC.NotStarted, PC.Aborted, PC.Committed})"
and "  (  compval (\<tau> cs) (memory (\<tau> cs) ! 0) glb = survived_val (\<tau> cs) glb  \<and> (pc cs syst = RecIdle  \<longrightarrow>survived_val (\<tau> cs) glb   \<le>   recoveredGlb cs  )) "
and" f_sim  cs as   "
shows "  global_rel  cs' as  "
  using assms
  apply (simp add:   f_sim_def TML_Recover_def Recover_inv_def total_wfs_def  split:if_splits )
  apply (simp add: global_rel_def)
  apply (intro conjI allI)
  apply (simp add:  write_count_def logical_glb_def tr_rel_def)
  apply (smt (z3) One_nat_def PC.simps(1677) assms(5) diff_self_eq_0 even_Suc_div_two even_zero one_div_two_eq_zero st_lastVal_lc)
  apply (simp add:  writes_def  maxIndex_def  write_count_def)
  apply (subgoal_tac " log cs'= Map.empty")
  prefer 2
  apply presburger
  apply (intro impI)
  apply (subgoal_tac " lastVal l (\<tau> cs') = lastVal l (\<tau> cs) ")
  prefer 2
  apply (metis assms(2) st_lv__daddr_ni)
  apply (simp(no_asm) add: apply_partial_def)
  apply (metis option.simps(4))
  apply (metis assms(2) st_lv__daddr_ni)
  by (metis option.distinct(1))

(*auxiliary lemma*)
lemma  logical_glb_recover_Rec8 :
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "  Recover_inv  syst  ((pc cs) syst)  cs"
and " TML_Recover syst   cs cs' "
and "((pc cs) syst)  = PC.Rec8"
shows "  logical_glb  cs'  = 0  "
  using assms
  apply (simp add:  TML_Recover_def Recover_inv_def logical_glb_def total_wfs_def  split:if_splits )
  using eq_imp_le st_lastVal_lc by presburger


(*auxiliary lemma*)
lemma  pc_recover_Rec8 :
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "  Recover_inv  syst  ((pc cs) syst)  cs"
and " TML_Recover syst   cs cs' "
and "((pc cs) syst)  = PC.Rec8"
shows " ((pc cs') syst) = RecIdle   "
  using assms
  by (simp add:  TML_Recover_def Recover_inv_def )



(*the simulation relation holds for Rec8 to Rec9 (stuttering step) *)
lemma  f_sim_recover_Rec8 :
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "  Recover_inv  syst  ((pc cs) syst)  cs"
and " TML_Recover syst   cs cs' "
and "((pc cs) syst)  = PC.Rec8"
and " (tmemory as) \<noteq> [] "
and " \<forall>t. tms_inv as  t "
and  " ((pc cs) syst) \<noteq> RecIdle   \<longrightarrow> (\<forall> t  \<noteq> syst.  ((pc cs) t)   \<in> {PC.NotStarted, PC.Aborted, PC.Committed})"
and "  (  compval (\<tau> cs) (memory (\<tau> cs) ! 0) glb = survived_val (\<tau> cs) glb  \<and> (pc cs syst = RecIdle  \<longrightarrow>survived_val (\<tau> cs) glb   \<le>   recoveredGlb cs  )) "
and" f_sim  cs as   "
shows "  f_sim  cs' as  "
  using assms
  apply (simp add:   f_sim_def TML_Recover_def Recover_inv_def total_wfs_def  split:if_splits )
  apply (intro conjI)
  apply (meson assms(1) assms(10) assms(2) assms(3) assms(4) assms(8) assms(9) golbal_rel__im_recover_Rec8)
  apply (intro conjI allI )
  apply (simp add: no_read_rdSet_empty_def )
  apply (simp add: no_write_wrSet_empty_def )
  apply (simp add: write_wrSet_notEmpty_def)
  apply (simp add: read_rdSet_notEmpty_def)
  apply (simp add:  loc_in_wrSet_def )
  apply (simp add: even_loc_wrSet_empty_def)
  apply blast
  apply (simp add: odd_loc_wrSet_notEmpty_def)
  apply blast
  apply (metis assms(1) assms(2) assms(3) assms(4) assms(8) f_sim_def tr_rel_Rec8_self tr_rel_Rec8_stable)
  apply (unfold read_prop_def)
  apply (subgoal_tac " global_rel cs' as")
  prefer 2
  apply (meson assms(1) assms(10) assms(2) assms(3) assms(4) assms(8) assms(9) golbal_rel__im_recover_Rec8)
  apply (unfold global_rel_def)
  apply (subgoal_tac "  lastVal glb (\<tau> cs') = recoveredGlb cs' ")
  prefer 2
  apply (metis st_lastVal_lc)
  apply (subgoal_tac " maxIndex  as  =1 ")
  prefer 2
  apply (subgoal_tac "  (logical_glb cs') = 0" )
  prefer 2
  apply (metis assms(1) assms(2) assms(3) assms(4) logical_glb_recover_Rec8)
  apply (simp(no_asm) add:  maxIndex_def)
  apply (subgoal_tac " write_count (logical_glb cs')  = 0 ")
  prefer 2
  apply (simp (no_asm) add:  write_count_def)
  apply (metis bits_div_0)
  apply (metis Suc_diff_1 assms(1) assms(2) assms(3) assms(4) length_greater_0_conv pc_recover_Rec8)
  apply (intro allI conjI impI)
  apply (case_tac "  n = length (memory (\<tau> cs)) ")
  apply (subgoal_tac " valOf   (last_entry_lim (\<tau> cs') l (length (memory (\<tau> cs))) ) l (\<tau> cs')    =  lastVal l (\<tau> cs')")
  prefer 2
  apply (metis st_succ_lv_lim_eq_lv_val)
  apply (subgoal_tac "  (valOf (length (memory (\<tau> cs))) glb (\<tau> cs')   = lastVal glb (\<tau> cs') ) ")
  prefer 2
  apply (metis st_lastEntry_lc st_lv_lim_eq_lv st_succ_lv_lim_eq_lv_val)
  apply (subgoal_tac "  write_count (valOf n glb (\<tau> cs') - recoveredGlb cs') = 0 ")
  prefer 2
  apply (simp(no_asm) add:  write_count_def)
  apply (metis bits_div_0 diff_self_eq_0)
  apply (metis diff_self_eq_0)
  apply (subgoal_tac "(\<forall> n l. (0 < n \<and> n < length(memory (\<tau> cs)  )) \<longrightarrow>  comploc ((memory (\<tau> cs') ) !n) l  \<noteq> glb  )"
      )
  prefer 2
  apply (simp(no_asm) add: comploc_def)
  apply (subgoal_tac " mem_structured (\<tau> cs') ")
  prefer 2
  apply (metis mem_structured_preserved)
  apply (unfold  mem_structured_def)
  apply (subgoal_tac "  \<forall>n. 0 \<le> n \<and> n < length (memory (\<tau> cs)) \<longrightarrow>
memory (\<tau> cs') ! n =    memory (\<tau> cs) ! n  ")
  prefer 2
  apply (metis mem_l_step)
  apply (metis le0)
  apply (subgoal_tac " length(memory (\<tau> cs'))  =  length(memory (\<tau> cs))  + 1  ")
  prefer 2
  apply (metis st_mem_length)
  by (metis Suc_eq_plus1 less_SucE)




(***********************************************************************)
(*auxiliary lemma*)
lemma   tr_rel_Rec9_self:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "  Recover_inv  syst  ((pc cs) syst)  cs"
and " TML_Recover syst   cs cs' "
and"   tr_rel   cs as syst"
and "((pc cs) syst)  = PC.Rec9 "
and" f_sim  cs as   "
and    "\<forall>t.  tms_inv as  t "
and  " ((pc cs) syst) \<noteq> RecIdle   \<longrightarrow> (\<forall> t  \<noteq> syst.  ((pc cs) t)   \<in> {PC.NotStarted, PC.Aborted, PC.Committed})"
shows " tr_rel cs' as syst"
  using assms
  by (simp add:TML_Recover_def tr_rel_def  Recover_inv_def total_wfs_def tmstep_def tms_inv_def  split:if_splits )


(*auxiliary lemma*)
lemma   tr_rel_Rec9_stable:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "  Recover_inv  syst  ((pc cs) syst)  cs"
and " TML_Recover syst   cs cs' "
and"   tr_rel   cs as t"
and "((pc cs) syst)  = PC.Rec9"
and    "\<forall>t.  tms_inv as  t "
and " t \<noteq> syst"
and  " ((pc cs) syst) \<noteq> RecIdle   \<longrightarrow> (\<forall> t  \<noteq> syst.  ((pc cs) t)   \<in> {PC.NotStarted, PC.Aborted, PC.Committed})"
shows " tr_rel cs' as t"
  using assms
  apply (simp add:TML_Recover_def tr_rel_def  Recover_inv_def total_wfs_def tmstep_def tms_inv_def   )
  apply (cases "pc cs t ";simp)
  apply (smt (z3) TPC.simps(133) loc_zero_read_con2)
  apply (metis PC.distinct(1) PC.distinct(157) PC.distinct(97))
  apply (metis PC.distinct(173) PC.distinct(233) PC.distinct(3))
  apply (metis PC.distinct(247) PC.distinct(307) PC.distinct(5))
  apply (metis PC.distinct(319) PC.distinct(379) PC.distinct(7))
  apply (metis PC.distinct(389) PC.distinct(449) PC.distinct(9))
  apply (metis PC.distinct(11) PC.distinct(457) PC.distinct(517))
  apply (metis PC.distinct(13) PC.distinct(523) PC.distinct(583))
  apply (metis PC.distinct(21) PC.distinct(711) PC.distinct(827))
  apply (metis PC.distinct(23) PC.distinct(713) PC.distinct(883))
  apply (metis PC.distinct(25) PC.distinct(715) PC.distinct(937))
  apply (metis PC.distinct(27) PC.distinct(717) PC.distinct(989))
  apply (metis PC.distinct(1039) PC.distinct(29) PC.distinct(719))
  apply (metis PC.distinct(1087) PC.distinct(31) PC.distinct(721))
  apply (metis PC.distinct(1133) PC.distinct(33) PC.distinct(723))
  apply (metis PC.distinct(1177) PC.distinct(35) PC.distinct(725))
  apply (metis PC.distinct(1219) PC.distinct(37) PC.distinct(727))
  apply (metis PC.distinct(1259) PC.distinct(39) PC.distinct(729))
  apply (metis PC.distinct(1297) PC.distinct(41) PC.distinct(731))
  apply (metis PC.distinct(1333) PC.distinct(43) PC.distinct(733))
  apply (metis PC.distinct(1367) PC.distinct(45) PC.distinct(735))
  apply (metis PC.distinct(1399) PC.distinct(47) PC.distinct(737))
  apply (metis PC.distinct(1429) PC.distinct(49) PC.distinct(739))
  apply (metis PC.distinct(1457) PC.distinct(51) PC.distinct(741))
  apply (metis PC.distinct(1483) PC.distinct(53) PC.distinct(743))
  by (metis PC.distinct(1639) PC.distinct(767) PC.distinct(77))



(*auxiliary lemma*)
lemma  global_rel_recover_Rec9 :
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "  Recover_inv  syst  ((pc cs) syst)  cs"
and " TML_Recover syst   cs cs' "
and "((pc cs) syst)  = PC.Rec9"
and " (tmemory as) \<noteq> [] "
and " \<forall>t. tms_inv as  t "
and  " ((pc cs) syst) \<noteq> RecIdle   \<longrightarrow> (\<forall> t  \<noteq> syst.  ((pc cs) t)   \<in> {PC.NotStarted, PC.Aborted, PC.Committed})"
and" f_sim  cs as   "
shows "  global_rel  cs' as  "
  using assms
  apply (simp add:   f_sim_def TML_Recover_def Recover_inv_def total_wfs_def  split:if_splits )
  apply (simp add: global_rel_def)
  apply (intro conjI allI)
  apply (simp add:  write_count_def logical_glb_def tr_rel_def)
  apply (smt (z3) One_nat_def PC.simps(1678) cancel_comm_monoid_add_class.diff_cancel even_Suc_div_two even_zero one_div_two_eq_zero st_lastVal_lc)
  apply (simp add:  writes_def  maxIndex_def  write_count_def)
  apply (subgoal_tac " log cs'= Map.empty")
  prefer 2
  apply presburger
  apply (intro impI)
  apply (subgoal_tac " lastVal l (\<tau> cs') = lastVal l (\<tau> cs) ")
  prefer 2
  apply (metis assms(2) st_lv__daddr_ni)
  apply (simp(no_asm) add: apply_partial_def)
  apply (metis option.simps(4))
  apply (metis assms(2) st_lv__daddr_ni)
  by (metis option.distinct(1))



(*auxiliary lemma*)
lemma  logical_glb_recover_Rec9 :
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "  Recover_inv  syst  ((pc cs) syst)  cs"
and " TML_Recover syst   cs cs' "
and "((pc cs) syst)  = PC.Rec9"
shows "  logical_glb  cs'  = 0  "
  using assms
  apply (simp add:  TML_Recover_def Recover_inv_def logical_glb_def total_wfs_def  split:if_splits )
  using eq_imp_le st_lastVal_lc by presburger

(*auxiliary lemma*)
lemma  pc_recover_Rec9 :
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "  Recover_inv  syst  ((pc cs) syst)  cs"
and " TML_Recover syst   cs cs' "
and "((pc cs) syst)  = PC.Rec9"
shows " ((pc cs') syst) = RecIdle   "
  using assms
  by (simp add:  TML_Recover_def Recover_inv_def )




(*the simulation relation holds for Rec9 to RecIdle (stuttering step) *)
lemma  f_sim_recover_Rec9 :
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "  Recover_inv  syst  ((pc cs) syst)  cs"
and " TML_Recover syst   cs cs' "
and "((pc cs) syst)  = PC.Rec9"
and " (tmemory as) \<noteq> [] "
and " \<forall>t. tms_inv as  t "
and  " ((pc cs) syst) \<noteq> RecIdle   \<longrightarrow> (\<forall> t  \<noteq> syst.  ((pc cs) t)   \<in> {PC.NotStarted, PC.Aborted, PC.Committed})"
and" f_sim  cs as   "
shows "  f_sim  cs' as  "
  using assms
  apply (simp add:   f_sim_def TML_Recover_def Recover_inv_def total_wfs_def  split:if_splits )
  apply (intro conjI)
    apply (meson assms(1) assms(2) assms(3) assms(4) assms(8) assms(9) global_rel_recover_Rec9)
   apply (intro conjI allI )
          apply (simp add: no_read_rdSet_empty_def )
  apply (simp add: no_write_wrSet_empty_def )
  apply (simp add: write_wrSet_notEmpty_def)
  apply (simp add: read_rdSet_notEmpty_def)
  apply (simp add:  loc_in_wrSet_def )
  apply (simp add: even_loc_wrSet_empty_def)
  apply blast
  apply (simp add: odd_loc_wrSet_notEmpty_def)
  apply blast
  apply (metis PC.distinct(791) assms(1) assms(2) assms(3) assms(4) assms(8) f_sim_def tr_rel_Rec9_self tr_rel_Rec9_stable)
  apply (unfold read_prop_def)
  apply (subgoal_tac " global_rel cs' as")
  prefer 2
  apply (metis assms(1) assms(2) assms(3) assms(4) assms(8) assms(9) global_rel_recover_Rec9)
  apply (unfold global_rel_def)
  apply (subgoal_tac "  lastVal glb (\<tau> cs') = recoveredGlb cs' ")
  prefer 2
  apply (metis st_lastVal_lc)
  apply (subgoal_tac " maxIndex  as  =1 ")
  prefer 2
  apply (subgoal_tac "  (logical_glb cs') = 0" )
  prefer 2
  apply (metis assms(1) assms(2) assms(3) assms(4) logical_glb_recover_Rec9)
  apply (simp(no_asm) add:  maxIndex_def)
  apply (subgoal_tac " write_count (logical_glb cs')  = 0 ")
  prefer 2
  apply (simp (no_asm) add:  write_count_def)
  apply (metis bits_div_0)
  apply (metis Suc_diff_1 assms(1) assms(2) assms(3) assms(4) length_greater_0_conv pc_recover_Rec9)
  apply (intro allI conjI impI)
  apply (case_tac "  n = length (memory (\<tau> cs)) ")
  apply (subgoal_tac " valOf   (last_entry_lim (\<tau> cs') l (length (memory (\<tau> cs))) ) l (\<tau> cs')    =  lastVal l (\<tau> cs')")
  prefer 2
  apply (metis st_succ_lv_lim_eq_lv_val)
  apply (subgoal_tac "  (valOf (length (memory (\<tau> cs))) glb (\<tau> cs')   = lastVal glb (\<tau> cs') ) ")
  prefer 2
  apply (metis st_lastEntry_lc st_lv_lim_eq_lv st_succ_lv_lim_eq_lv_val)

  apply (subgoal_tac "  write_count (valOf n glb (\<tau> cs') - recoveredGlb cs') = 0 ")
  prefer 2
  apply (simp(no_asm) add:  write_count_def)
  apply (metis bits_div_0 diff_self_eq_0)
  apply (metis diff_self_eq_0) 

  apply (subgoal_tac "(\<forall> n l. (0 < n \<and> n < length(memory (\<tau> cs)  )) \<longrightarrow>  comploc ((memory (\<tau> cs') ) !n) l  \<noteq> glb  )"
      )
  prefer 2
  apply (simp(no_asm) add: comploc_def)
  apply (subgoal_tac " mem_structured (\<tau> cs') ")
  prefer 2
  apply (metis mem_structured_preserved)
  apply (unfold  mem_structured_def)
  apply (subgoal_tac "  \<forall>n. 0 \<le> n \<and> n < length (memory (\<tau> cs)) \<longrightarrow>
memory (\<tau> cs') ! n =    memory (\<tau> cs) ! n  ")
  prefer 2
  apply (metis mem_l_step)
  apply (metis le0)

  apply (subgoal_tac " length(memory (\<tau> cs'))  =  length(memory (\<tau> cs))  + 1  ")
  prefer 2
  apply (metis st_mem_length)
  by (metis Suc_eq_plus1 less_SucE)



end







