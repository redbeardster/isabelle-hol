(*Showing that the simulation relation holds for the DTML Commit  operation*)

theory Ref_Commit
imports "../Refinement"
begin

(*auxiliary lemma*)
lemma   tr_rel_Commit_self_lp:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "  TML_Commit_invocation   ta cs  cs'  "
and "((pc cs) ta)  = PC.Ready"
and "  Commit_invocation_inv   ta  ((pc cs) ta) cs "
and " f_sim cs as "
and"   tr_rel   cs as ta"
and " ta \<noteq> syst"
shows "  tr_rel cs' (TMCommit_inv_trans  ta  as) ta "
  using assms
  by (simp add: TML_Commit_invocation_def tr_rel_def Commit_invocation_inv_def TMCommit_inv_trans_def  validity_prop_def  split: if_splits )




(*auxiliary lemma*)
lemma   tr_rel_Ready_stable_lp:
assumes  "thrdsvars"
and   "\<forall>t.  tms_inv as  t "
and "total_wfs (\<tau> cs) "
and "((pc cs) ta)  = PC.Ready"
and "  Commit_invocation_inv   ta  ((pc cs) ta) cs "
and "  TML_Commit_invocation   ta cs  cs'  "
and " f_sim cs as "
and"   tr_rel   cs as t"
and " t \<noteq> ta "
and " ta \<noteq> syst"
shows "  tr_rel cs' (TMCommit_inv_trans  ta  as) t "
using assms
  apply (simp add: TML_Commit_invocation_def tr_rel_def  Commit_invocation_inv_def  TMCommit_inv_trans_def split: if_splits )
  apply (unfold validity_prop_def  in_flight_def total_wfs_def  )
  apply (cases "pc cs t";  simp)
  apply metis
  apply metis
  apply (metis PC.distinct(1489) fun_upd_def)
  apply (metis PC.distinct(1491) fun_upd_def)
  by (metis PC.distinct(1493) fun_upd_def)


(*auxiliary lemma*)
lemma commit_ready_logical_glb_ni:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and " TML_Commit_invocation  ta   cs cs'"
and "((pc cs) ta)  = PC.Ready"
shows " logical_glb cs = logical_glb cs' "
  using assms
  apply (unfold total_wfs_def)
  apply (simp add: TML_Commit_invocation_def logical_glb_def)
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
  by (smt (z3) PC.distinct(385) PC.distinct(645) fun_upd_other fun_upd_same option.simps(5))

(*auxiliary lemma*)
lemma read_ready_writes_ni:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and " TML_Commit_invocation  ta   cs cs'"
and "((pc cs) ta)  = PC.Ready"
shows " writes cs as = writes  cs'  (TMCommit_inv_trans  ta  as) "
  using assms
  apply (unfold total_wfs_def)
  apply (simp add: TML_Commit_invocation_def TMCommit_inv_trans_def logical_glb_def writes_def)
  apply (cases "pc cs ta";  simp)
  apply (cases " writer cs" )
  apply simp
  apply (intro conjI impI)
  apply (cases " writer cs'" )
  apply simp+
  apply (cases " writer cs'" )
  by simp+


(*the simulation relation holds for inv(Commit)  (non stuttering step) *)
lemma   f_sim_commit_inv_ready_lp:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "  TML_Commit_invocation   ta cs  cs'  "
and "((pc cs) ta)  = PC.Ready"
and " Commit_invocation_inv ta  ((pc cs) ta) cs "
and " f_sim  cs  as"
and   "\<forall>t.  tms_inv as  t "
and"pc cs  syst  = RecIdle "
and " ta \<noteq> syst"
shows "  \<exists> as'. tmstep ta  TMCommitInv  as  as'  \<and> f_sim  cs' as' "
  using assms
  apply (unfold total_wfs_def)
  apply (simp add: TML_Commit_invocation_def Commit_invocation_inv_def tmstep_def  f_sim_def)
  apply (subgoal_tac " memory ( \<tau>  cs) = memory( \<tau> cs' )")
  prefer 2
  apply presburger
  apply (cases "pc cs ta";  simp)
  apply (intro conjI)
  apply (simp add: global_rel_def)
  apply (intro conjI)
  apply (simp add: TMCommit_inv_trans_def  write_count_def)
  apply (metis assms(1) assms(2) assms(3) commit_ready_logical_glb_ni)
  apply (simp add: maxIndex_def  TMCommit_inv_trans_def  )
  using TMCommit_inv_trans_def assms(2) assms(3) read_ready_writes_ni thrdsvars_def apply presburger
  apply (simp add: maxIndex_def  TMCommit_inv_trans_def apply_partial_def )
  apply (simp add: maxIndex_def  TMCommit_inv_trans_def apply_partial_def )
  apply (simp add:  TMCommit_inv_trans_def )
  apply (simp add: no_read_rdSet_empty_def  no_write_wrSet_empty_def write_wrSet_notEmpty_def  odd_loc_wrSet_notEmpty_def read_rdSet_notEmpty_def loc_in_wrSet_def even_loc_wrSet_empty_def )
  apply (subgoal_tac " tpc as ta = TPC.Ready")
  prefer 2
  apply (simp add: tr_rel_def)
  apply (smt (z3) PC.simps(1680))
  apply simp
  apply (intro conjI allI impI)
  apply (metis TMCommit_inv_trans_def assms(1) assms(2) assms(3) assms(5) assms(6) tr_rel_Commit_self_lp)
  using tr_rel_Ready_stable_lp [where as=as and cs=cs  and cs'=cs' and ta = ta]
  apply (metis TMCommit_inv_trans_def assms(1) assms(2) assms(3) assms(5) assms(6))
  apply (simp add:   TMCommit_inv_trans_def)
  apply (unfold  read_prop_def)
  apply (subgoal_tac " tpc as ta = TPC.Ready")
  prefer 2
  apply (simp add: tr_rel_def)
  apply (smt (z3) PC.simps(1680))
  by simp



(****************************************************)

(*auxiliary lemma*)
lemma    tr_rel_commitPending_commit2_self:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "TML_Commit ta cs  cs'"
and "((pc cs) ta)  = PC.CommitPending"
and "((pc cs') ta)  = PC.Commit2"
and " Commit_inv  ta ((pc cs) ta) cs "
and"   tr_rel   cs as ta"
and " f_sim  cs  as"
and   "\<forall>t.  tms_inv as  t "
and"pc cs  syst  = RecIdle "
and " ta \<noteq> syst"
shows "   tr_rel   cs' as ta  "
  using assms
  apply (simp add:TML_Commit_def tr_rel_def in_flight_def validity_prop_def total_wfs_def Commit_inv_def  tms_inv_def  split: if_splits )
  apply (subgoal_tac "  writeAux cs ta ")
  prefer 2
  using Ready_total_def apply blast
  apply (simp add: global_rel_def)
  apply(simp add: f_sim_def  write_wrSet_notEmpty_def)
  by (smt (z3) PC.distinct(411) PC.distinct(413) PC.distinct(415) PC.distinct(417) PC.distinct(419) PC.distinct(87) Ready_total_def)

(*auxiliary lemma*)
lemma    tr_rel_ready_commitPending_stable:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "TML_Commit ta cs  cs'"
and "((pc cs) ta)  =  PC.CommitPending"
and "((pc cs') ta)  = PC.Commit2"
and " Commit_inv  ta ((pc cs) ta) cs "
and " t \<noteq> ta "
and"   tr_rel   cs as t"
and " f_sim  cs  as"
and   "\<forall>t.  tms_inv as  t "
and " ta \<noteq> syst"
shows "   tr_rel   cs' as t  "
  using assms
  apply (simp add:TML_Commit_def tr_rel_def in_flight_def validity_prop_def total_wfs_def Commit_inv_def  split: if_splits )
  apply (unfold in_flight_def validity_prop_def Ready_total_def)
  by (cases "pc cs t";  simp)




lemma   f_sim_commit_commitPending_commit2:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "TML_Commit ta cs  cs'"
and "((pc cs) ta)  =  PC.CommitPending"
and "((pc cs') ta)  = PC.Commit2"
and " Commit_inv  ta ((pc cs) ta) cs "
and " f_sim  cs  as"
and   "\<forall>t.  tms_inv as  t "
and"pc cs  syst  = RecIdle "
and " ta \<noteq> syst"
shows " f_sim  cs' as  "
  using assms
  apply (simp add: Commit_inv_def TML_Commit_def   Ready_total_def split:if_splits)
  apply (simp add:  f_sim_def)
  apply (intro conjI)
    apply (simp add: global_rel_def)
    apply (intro conjI impI)
     apply (simp add: logical_glb_def)
    apply (simp add: writes_def)
   apply (simp add: no_read_rdSet_empty_def no_write_wrSet_empty_def write_wrSet_notEmpty_def  odd_loc_wrSet_notEmpty_def  read_rdSet_notEmpty_def loc_in_wrSet_def  even_loc_wrSet_empty_def)
  using assms(3) assms(5) assms(6) assms(7) thrdsvars_def tr_rel_commitPending_commit2_self tr_rel_ready_commitPending_stable apply presburger
  apply (unfold read_prop_def)
  by presburger






(********************************************************)
(*auxiliary lemma*)
lemma   commitPending_commitResponding_trans:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "TML_Commit ta cs  cs'"
and "((pc cs) ta)  = PC.CommitPending"
and "((pc cs') ta)  = PC.CommitResponding"
and " Commit_inv  ta ((pc cs) ta) cs "
and"   tr_rel   cs as ta"
and " f_sim  cs  as"
and   "\<forall>t.  tms_inv as  t "
and"pc cs  syst  = RecIdle "
and " tmemory as \<noteq> [] "
and  " pc cs  syst  = RecIdle \<longrightarrow> (\<forall>t.  (t \<noteq> syst  \<and> ((pc cs) t \<notin> {PC.NotStarted,PC.BeginPending, PC.Committed,PC.Begin2, PC.Aborted   }) \<longrightarrow>   regs (\<tau> cs) t loc \<le> lastVal glb  (\<tau> cs) ))"
and "\<forall>t.  (t \<noteq> syst  \<and> ((pc cs) t \<notin> {PC.NotStarted,PC.Aborted, PC.Committed, PC.BeginPending })  \<and> (writeAux cs t \<or> readAux cs t )) \<longrightarrow>  ( regs (\<tau> cs) t loc \<ge>  recoveredGlb cs )"
and " ( lastVal glb (\<tau> cs)  \<ge>recoveredGlb cs ) "
and " ta \<noteq> syst"
shows "  TMCommit_trans  ta as   =   as\<lparr> tpc := (tpc as)(ta := CommitResponding) \<rparr>"
  using assms
  apply (simp add:TML_Commit_def tr_rel_def in_flight_def total_wfs_def  Commit_inv_def  tms_inv_def  Ready_total_def  split: if_splits )
  apply (subgoal_tac "  wrSet as ta = Map.empty ")
   prefer 2
   apply (simp add: f_sim_def no_write_wrSet_empty_def  )
  apply (unfold TMCommit_trans_def)
  apply (case_tac "\<not> readAux cs ta  ")
   apply (subgoal_tac " validIndex as ta  ( write_count (logical_glb cs) ) ")
    prefer 2
    apply (simp add: validIndex_def)
    apply (intro conjI)
      apply(simp add: f_sim_def )
      apply (simp add: global_rel_def)
      apply (subgoal_tac "  beginIndex as ta < maxIndex as")
       prefer 2
       apply (metis (no_types, lifting) TPC.simps(143))
      apply (simp add: maxIndex_def)
     apply (simp add: maxIndex_def)
     apply (simp add: f_sim_def)
     apply (simp add: global_rel_def)
    apply (subgoal_tac " rdSet as ta = Map.empty  ")
     prefer 2
     apply (simp add: f_sim_def)
     apply (simp add: global_rel_def)
     apply (simp add:  no_read_rdSet_empty_def)
    apply (simp add: read_consistent_def)
   apply presburger
  apply (subgoal_tac "  validIndex as  ta ( write_count (regs (\<tau> cs) ta DTML.loc - recoveredGlb cs))   ")
  prefer 2
  apply (simp add: validIndex_def)
  apply (intro conjI)
   apply (simp add: validity_prop_def)
   apply (simp add: f_sim_def global_rel_def maxIndex_def )
   apply (case_tac "writer cs = None")
    apply (simp add: logical_glb_def)
    apply (subgoal_tac"regs (\<tau> cs) ta DTML.loc - recoveredGlb cs \<le>lastVal glb (\<tau> cs) - recoveredGlb cs ")
  prefer 2
  apply (metis PC.distinct(163) PC.distinct(389) PC.distinct(449) PC.distinct(87) PC.distinct(9) diff_le_mono)
  apply (simp add: logical_glb_def write_count_def)
  apply (metis diff_less div_mono2 le_less_Suc_eq le_numeral_extra(3) length_greater_0_conv)
  apply (simp add: split: if_splits)
  apply (subgoal_tac"regs (\<tau> cs) ta DTML.loc - recoveredGlb cs \<le>lastVal glb (\<tau> cs) - recoveredGlb cs ")
  prefer 2
  apply (metis PC.distinct(163) PC.distinct(389) PC.distinct(449) PC.distinct(87) PC.distinct(9) diff_le_mono)
  apply (simp add: logical_glb_def write_count_def)
  apply (simp add: split: if_splits )
  apply (metis Suc_diff_Suc Suc_diff_le assms(14) div_le_mono le_SucI length_greater_0_conv less_Suc_eq_le minus_nat.diff_0)
  apply (metis diff_Suc_less div_mono2 length_greater_0_conv)
  using validity_prop_def apply blast
  apply (simp add: split: if_splits )
  by blast


(*auxiliary lemma*)
lemma    tr_rel_commitPending_commitResponding_self:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "TML_Commit ta cs  cs'"
and "((pc cs) ta)  = PC.CommitPending"
and "((pc cs') ta)  = PC.CommitResponding"
and " Commit_inv  ta ((pc cs) ta) cs "
and"   tr_rel   cs as ta"
and " f_sim  cs  as"
and   "\<forall>t.  tms_inv as  t "
and"pc cs  syst  = RecIdle "
and " tmemory as \<noteq> [] "
and  " pc cs  syst  = RecIdle \<longrightarrow> (\<forall>t.  (t \<noteq> syst  \<and> ((pc cs) t \<notin> {PC.NotStarted,PC.BeginPending, PC.Committed,PC.Begin2, PC.Aborted   }) \<longrightarrow>   regs (\<tau> cs) t loc \<le> lastVal glb  (\<tau> cs) ))"
and "\<forall>t.  (t \<noteq> syst  \<and> ((pc cs) t \<notin> {PC.NotStarted,PC.Aborted,PC.Committed, PC.BeginPending})  \<and> (writeAux cs t \<or> readAux cs t )) \<longrightarrow>  ( regs (\<tau> cs) t loc \<ge>  recoveredGlb cs )"
and " ( lastVal glb (\<tau> cs)  \<ge>recoveredGlb cs ) "
and " ta \<noteq> syst"
shows "   tr_rel cs' (TMCommit_trans ta  as) ta"
  using assms
  apply (subgoal_tac " TMCommit_trans ta  as =  as\<lparr> tpc := (tpc as)(ta := CommitResponding) \<rparr> ")
  prefer 2
  using   commitPending_commitResponding_trans [where cs = cs and as = as]
  apply blast
  by (simp add: tr_rel_def)



(*auxiliary lemma*)
lemma    tr_rel_commitPending_commitResponding_stable:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "TML_Commit ta cs  cs'"
and "((pc cs) ta)  = PC.CommitPending"
and "((pc cs') ta)  = PC.CommitResponding"
and " Commit_inv  ta ((pc cs) ta) cs "
and"   tr_rel   cs as t"
and " f_sim  cs  as"
and   "\<forall>t.  tms_inv as  t "
and"pc cs  syst  = RecIdle "
and " tmemory as \<noteq> [] "
and "tr_rel   cs as ta"
and  " pc cs  syst  = RecIdle \<longrightarrow> (\<forall>t.  (t \<noteq> syst  \<and> ((pc cs) t \<notin> {PC.NotStarted,PC.BeginPending, PC.Committed,PC.Begin2, PC.Aborted    }) \<longrightarrow>   regs (\<tau> cs) t loc \<le> lastVal glb  (\<tau> cs) ))"
and "\<forall>t.  (t \<noteq> syst  \<and> ((pc cs) t \<notin> {PC.NotStarted,PC.Aborted, PC.Committed,PC.BeginPending })  \<and> (writeAux cs t \<or> readAux cs t )) \<longrightarrow>  ( regs (\<tau> cs) t loc \<ge>  recoveredGlb cs )"
and " ( lastVal glb (\<tau> cs)  \<ge>recoveredGlb cs ) "
and " t \<noteq> ta "
and " ta \<noteq> syst"
shows "   tr_rel cs' (TMCommit_trans ta  as) t"
  using assms
  apply (subgoal_tac " TMCommit_trans ta  as =  as\<lparr> tpc := (tpc as)(ta := CommitResponding) \<rparr> ")
  prefer 2
  using    commitPending_commitResponding_trans [where cs = cs and as = as]
  apply presburger
  apply (simp add: TML_Commit_def tr_rel_def tms_inv_def  total_wfs_def Commit_inv_def
      tmstep_def  split: if_splits)
  apply (unfold validity_prop_def  in_flight_def)
  apply (cases "pc cs t";  simp)
  apply ( elim conjE)
  apply metis
  by fastforce


(*auxiliary lemma*)
lemma   commitPending_commitResponding_writes_ni:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "TML_Commit ta cs  cs'"
and "((pc cs) ta)  = PC.CommitPending"
and "((pc cs') ta)  = PC.CommitResponding"
and " Commit_inv  ta ((pc cs) ta) cs "
shows " writes cs  as   = writes cs'  (as\<lparr> tpc := (tpc as)(ta := CommitResponding) \<rparr>)  "
  using assms
  apply (simp add: TML_Commit_def Commit_inv_def writes_def total_wfs_def Ready_total_def)
  apply (simp add: split: if_splits )
  apply (case_tac "  writer cs ")
  apply simp
  apply  (subgoal_tac " pc cs' ( the (writer cs'))  = pc cs (the(writer cs)) ")
  prefer 2
  apply simp
  by (simp add: split: if_splits)


(*auxiliary lemma*)
lemma tmem_commitPending_commitPending:
shows  "  tmemory (as\<lparr>tpc := (tpc as)(ta := TPC.CommitPending)\<rparr>) = tmemory as "
by auto

(*the simulation relation holds from   CommitPending to  CommitResponding  (non stuttering step)  *)
lemma   f_sim_commitPending_commitResponding_LP:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "TML_Commit ta cs  cs'"
and "((pc cs) ta)  = PC.CommitPending"
and "((pc cs') ta)  = PC.CommitResponding"
and " Commit_inv  ta ((pc cs) ta) cs "
and " f_sim  cs  as"
and   "\<forall>t.  tms_inv as  t "
and"pc cs  syst  = RecIdle "
and " tmemory as \<noteq> [] "
and  " pc cs  syst  = RecIdle \<longrightarrow> (\<forall>t.  (t \<noteq> syst  \<and> ((pc cs) t \<notin> {PC.NotStarted,PC.BeginPending, PC.Committed,PC.Begin2 , PC.Aborted    }) \<longrightarrow>   regs (\<tau> cs) t loc \<le> lastVal glb  (\<tau> cs) ))"
and "\<forall>t.  (t \<noteq> syst  \<and> ((pc cs) t \<notin> {PC.NotStarted,PC.Aborted, PC.Committed, PC.BeginPending })  \<and> (writeAux cs t \<or> readAux cs t )) \<longrightarrow>  ( regs (\<tau> cs) t loc \<ge>  recoveredGlb cs )"
and " ( lastVal glb (\<tau> cs)  \<ge>recoveredGlb cs ) "
and " ta \<noteq> syst"
shows " \<exists> as'. tmstep ta TMCommit  as  as'   \<and> f_sim  cs' as'  "
using assms
  apply (subgoal_tac "tr_rel   cs as ta")
  prefer 2
  apply (simp add: f_sim_def)
  apply (subgoal_tac " TMCommit_trans ta  as =  as\<lparr> tpc := (tpc as)(ta := CommitResponding) \<rparr> ")
  prefer 2
  using  commitPending_commitResponding_trans [where cs = cs and as = as]
  apply blast
  apply (subgoal_tac " writes cs as  = writes cs'  (as\<lparr> tpc := (tpc as)(ta :=  CommitResponding) \<rparr>)")
  prefer 2
  using   commitPending_commitResponding_writes_ni[where cs = cs and as = as and cs' = cs']
  using assms(1) assms(3) assms(5) assms(6) apply blast
  apply (simp add: Commit_inv_def TML_Commit_def tmstep_def split:if_splits)
  apply (simp add:  f_sim_def)
  apply (intro conjI)
  apply (simp add: global_rel_def )
  apply (intro conjI allI)
  apply (simp add: logical_glb_def write_count_def) (*see*)
  apply (cases"  writer cs")
  apply (metis option.simps(4))
  apply simp
  apply (smt (verit) PC.distinct(385) Suc_eq_plus1)
  apply (simp add: maxIndex_def)
  apply (simp add: maxIndex_def)
  apply (simp add: maxIndex_def)
  apply (intro conjI allI impI)
  apply (simp add:  no_read_rdSet_empty_def)
  apply (simp add: no_write_wrSet_empty_def)
  apply (simp add: write_wrSet_notEmpty_def)
  apply (simp add: read_rdSet_notEmpty_def)
  apply (simp add: loc_in_wrSet_def)
  apply (simp add: even_loc_wrSet_empty_def)
  apply (simp add: odd_loc_wrSet_notEmpty_def)
  apply (case_tac " t = ta ")
  apply simp
  using tr_rel_commitPending_commitResponding_self[where cs = cs and as = as and cs' =cs and ta= ta]
  apply (smt (z3) assms(1) assms(11) assms(12) assms(3) assms(5) assms(6) assms(7) tr_rel_commitPending_commitResponding_self)
  apply (smt (z3) assms(10) assms(11) assms(12) assms(3) assms(5) assms(6) assms(7) thrdsvars_def tr_rel_commitPending_commitResponding_stable)
  apply (unfold read_prop_def)
  apply (subgoal_tac " memory (\<tau> cs) = memory (\<tau> cs') ")
  prefer 2
  apply presburger
  apply (subgoal_tac"  tmemory (as\<lparr>tpc := (tpc as)(ta := TPC.CommitResponding)\<rparr>) = tmemory as ")
  prefer 2
  apply (simp(no_asm) add: TMCommit_trans_def)
  by presburger



(*****************************************************)
(*auxiliary lemma*)
lemma   commit3_commit4_trans:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "TML_Commit ta cs  cs'"
and "((pc cs) ta)  = PC.Commit3"
and "((pc cs') ta)  = PC.Commit4"
and " Commit_inv  ta ((pc cs) ta) cs "
and"   tr_rel   cs as ta"
and " f_sim  cs  as"
and   "\<forall>t.  tms_inv as  t "
and"pc cs  syst  = RecIdle "
shows "  TMCommit_trans  ta as   =   as\<lparr>  tpc := (tpc as)(ta := CommitResponding),
tmemory := write_back (wrSet as ta) ( tmemory as)
\<rparr>"
  using assms
  apply (simp add:TML_Commit_def tr_rel_def in_flight_def total_wfs_def  Commit_inv_def  tms_inv_def  split: if_splits )
  apply (unfold TMCommit_trans_def)
  apply (subgoal_tac "read_consistent  (( tmemory as)! ((maxIndex as) -1) ) (rdSet as ta) ")
  prefer 2
  apply (simp add: validity_prop_def f_sim_def global_rel_def )
  apply (subgoal_tac " logical_glb cs =  lastVal glb (\<tau> cs) - recoveredGlb cs ")
  prefer 2
  apply (simp add: logical_glb_def)
  apply (simp add: maxIndex_def)
  apply (simp add: split: if_splits )
  by (metis PC.distinct(559))


(*auxiliary lemma*)
lemma    tr_rel_commit3_commit4_self:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "TML_Commit ta cs  cs'"
and "((pc cs) ta)  = PC.Commit3"
and "((pc cs') ta)  = PC.Commit4"
and " Commit_inv  ta ((pc cs) ta) cs "
and"   tr_rel   cs as ta"
and " f_sim  cs  as"
and   "\<forall>t.  tms_inv as  t "
and"pc cs  syst  = RecIdle "
shows "   tr_rel cs' (TMCommit_trans ta  as) ta"
  using assms
  apply (subgoal_tac " TMCommit_trans ta  as =    as\<lparr>  tpc := (tpc as)(ta := CommitResponding),
  tmemory := write_back (wrSet as ta) ( tmemory as)  \<rparr>")
  prefer 2
  using  commit3_commit4_trans
  apply blast
  by (simp add: tr_rel_def Commit_inv_def TML_Commit_def  )




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

(*auxiliary lemma*)
lemma  tr_rel_commit3_commit4_read_consistent:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "TML_Commit ta cs  cs'"
and "((pc cs) ta)  = PC.Commit3"
and "((pc cs') ta)  = PC.Commit4"
and " Commit_inv  ta ((pc cs) ta) cs "
and " t \<noteq> ta "
and "     write_count (regs (\<tau> cs') t DTML.loc - recoveredGlb cs') < length (tmemory as) "
and " tmemory as \<noteq> [] "
and "read_consistent
((tmemory as ) ! write_count (regs (\<tau> cs) t DTML.loc - recoveredGlb cs))  (rdSet as t)"
and  " pc cs  syst  = RecIdle \<longrightarrow> (\<forall>t.  (t \<noteq> syst  \<and> ((pc cs) t \<notin> {PC.NotStarted,PC.BeginPending, PC.Committed,PC.Begin2, PC.Aborted     }) \<longrightarrow>   regs (\<tau> cs) t loc \<le> lastVal glb  (\<tau> cs) ))"
shows "read_consistent ( (tmemory as @  [apply_partial (tmemory as ! (length (tmemory as) - Suc 0)) (wrSet as ta)]) !  write_count (regs (\<tau> cs) t DTML.loc - recoveredGlb cs))  (rdSet as t)"
  using assms
  apply (simp add: TML_Commit_def   total_wfs_def Commit_inv_def
      split: if_splits)
  apply (cases"  pc cs ta "; simp )
  apply (subgoal_tac " length ( tmemory as @  [apply_partial (tmemory as ! (length (tmemory as) - Suc 0)) (wrSet as ta)]) = length (tmemory as) +1 ")
  prefer 2
  apply (metis add_Suc_shift length_append list.size(3) list.size(4) numeral_1_eq_Suc_0 numerals(1) plus_1_eq_Suc)
  apply (subgoal_tac " \<forall> i. 0 \<le> i \<and> i < length (tmemory as) \<longrightarrow> ( tmemory as @  [apply_partial (tmemory as ! (length (tmemory as) - Suc 0)) (wrSet as ta)])!i =  (tmemory as)!i ")
  prefer 2
  apply (metis nth_append)
  by  (simp add: read_consistent_def)

(*auxiliary lemma*)
lemma    tr_rel_commit3_commit4_stable:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "TML_Commit ta cs  cs'"
and "((pc cs) ta)  = PC.Commit3"
and "((pc cs') ta)  = PC.Commit4"
and " Commit_inv  ta ((pc cs) ta) cs "
and"   tr_rel   cs as t"
and " f_sim  cs  as"
and   "\<forall>t.  tms_inv as  t "
and"pc cs  syst  = RecIdle "
and " tmemory as \<noteq> [] "
and "tr_rel   cs as ta"
and  " pc cs  syst  = RecIdle \<longrightarrow> (\<forall>t.  (t \<noteq> syst  \<and> ((pc cs) t \<notin> {PC.NotStarted,PC.BeginPending, PC.Committed,PC.Begin2, PC.Aborted     }) \<longrightarrow>   regs (\<tau> cs) t loc \<le> lastVal glb  (\<tau> cs) ))"
and "\<forall>t.  (t \<noteq> syst  \<and> ((pc cs) t \<notin> {PC.NotStarted,PC.Aborted, PC.Committed,PC.BeginPending })  \<and> (writeAux cs t \<or> readAux cs t )) \<longrightarrow>  ( regs (\<tau> cs) t loc \<ge>  recoveredGlb cs )"
and  " \<forall>  t.  (   writer cs = Some t \<longrightarrow> odd (lastVal glb  (\<tau> cs)) )"
and " ( lastVal glb (\<tau> cs)  \<ge>recoveredGlb cs ) "
and " t \<noteq> ta "
and"(\<forall>t. ((pc cs) t) \<in> {Commit2, Commit3,Commit4,Write3,Write4, Write5, Write6, Write7,Write8} \<longrightarrow> writer cs  =  Some t )"
and   " \<forall>  t.  (  writer cs = Some t \<longrightarrow> odd (lastVal glb  (\<tau> cs)) )"
and "ta \<noteq> syst"
shows "   tr_rel cs' (TMCommit_trans ta  as) t"
  using assms
  apply (subgoal_tac " TMCommit_trans ta  as =    as\<lparr>  tpc := (tpc as)(ta := CommitResponding),
tmemory := write_back (wrSet as ta) ( tmemory as)  \<rparr>")
  prefer 2
  using  commit3_commit4_trans
  apply blast
  apply (simp add: tr_rel_def total_wfs_def Commit_inv_def
      split: if_splits)
  apply (unfold   TML_Commit_def)
  apply (cases"  pc cs t "; simp )
  apply (simp add:  read_consistent_def apply_partial_def write_count_def )
  apply (subgoal_tac "  rdSet ( as ) t = Map.empty ")
  prefer 2
  apply (unfold  tms_inv_def)
  apply (smt (z3) TPC.simps(133))
  apply (subgoal_tac "  rdSet ( as ) t = Map.empty ")
  prefer 2
  apply (smt (z3) TPC.simps(13))
  apply (simp add:  read_consistent_def)
  apply (simp add:  f_sim_def global_rel_def)
  apply (simp add:logical_glb_def write_count_def)
  apply (subgoal_tac "  rdSet ( as ) t = Map.empty ")
  prefer 2
  apply (smt (z3) TPC.simps(137))
  apply (simp add:  read_consistent_def)
  apply (subgoal_tac "  rdSet ( as ) t = Map.empty ")
  prefer 2
  apply (smt (z3) TPC.simps(137))
  apply (simp add: read_consistent_def)
  apply (subgoal_tac "  rdSet ( as ) t = Map.empty ")
  prefer 2
  apply (smt (z3) TPC.simps(137))
  apply (simp add: read_consistent_def)
  apply (subgoal_tac "               write_count  (regs (\<tau> cs) t DTML.loc - recoveredGlb cs)
\<le> length (tmemory as) - Suc 0  ")
  prefer 2
  apply (simp add:  write_count_def)
  apply (subgoal_tac "   regs (\<tau> cs) t loc \<le> lastVal glb  (\<tau> cs) ")
  prefer 2
  using loc_le_logical_glb [where cs= cs and t = t]
  apply (metis PC.distinct(161) PC.distinct(319) PC.distinct(355) PC.distinct(379) PC.distinct(7) PC.distinct(85))
  apply (simp add: f_sim_def global_rel_def)
  apply (simp add: write_count_def)
  apply (metis \<open>\<lbrakk>total_wfs (\<tau> cs); regs (\<tau> cs) t DTML.loc \<le> lastVal glb (\<tau> cs)\<rbrakk> \<Longrightarrow> regs (\<tau> cs) t DTML.loc - recoveredGlb cs \<le> logical_glb cs\<close> assms(2) div_le_mono)
  apply (simp add: in_flight_def validity_prop_def  f_sim_def
      global_rel_def                 )
  apply (intro conjI impI)
  apply (subgoal_tac "               write_count  (regs (\<tau> cs) t DTML.loc - recoveredGlb cs)
\<le> length (tmemory as) - Suc 0  ")
  prefer 2
  apply (simp add:  write_count_def)
  using loc_le_logical_glb [where cs= cs and t = t]
  apply (metis Suc_diff_Suc le_imp_less_Suc length_greater_0_conv minus_nat.diff_0 nth_append)
  apply (metis Suc_diff_Suc le_imp_less_Suc length_greater_0_conv minus_nat.diff_0 nth_append)
  apply (simp add: in_flight_def validity_prop_def  f_sim_def
      global_rel_def                 )
  apply (intro conjI impI)
  apply (subgoal_tac "               write_count  (regs (\<tau> cs) t DTML.loc - recoveredGlb cs)
\<le> length (tmemory as) - Suc 0  ")
  prefer 2
  apply (simp add:  write_count_def)
  using loc_le_logical_glb [where cs= cs and t = t]
  apply (metis PC.distinct(163) PC.distinct(389) PC.distinct(425) PC.distinct(449) PC.distinct(87) PC.distinct(9) assms(2) div_le_mono)
  apply (metis Suc_diff_Suc le_imp_less_Suc length_greater_0_conv minus_nat.diff_0 nth_append)
  apply (simp add: read_consistent_def apply_partial_def write_count_def)
  apply (subgoal_tac "               write_count  (regs (\<tau> cs) t DTML.loc - recoveredGlb cs)
\<le> length (tmemory as) - Suc 0  ")
  prefer 2
  apply (simp add:  write_count_def)
  using loc_le_logical_glb [where cs= cs and t = t]
  apply (metis PC.distinct(163) PC.distinct(389) PC.distinct(425) PC.distinct(449) PC.distinct(87) PC.distinct(9) assms(2) div_le_mono)
  apply (subgoal_tac "  write_count (regs (\<tau> cs') t DTML.loc - recoveredGlb cs') < length (tmemory as) ")
  prefer 2
  apply (metis Suc_pred le_imp_less_Suc length_greater_0_conv)
  using  tr_rel_commit3_commit4_read_consistent  [where cs= cs and t = t and ta = ta and cs' = cs' and as = as]
  apply (metis nth_append write_count_def)
  apply (simp add: in_flight_def validity_prop_def  f_sim_def
      global_rel_def                 )
  apply (subgoal_tac "               write_count  (regs (\<tau> cs) t DTML.loc - recoveredGlb cs)
\<le> length (tmemory as) - Suc 0  ")
  prefer 2
  apply (simp add:  write_count_def)
  using loc_le_logical_glb [where cs= cs and t = t]
  apply (metis option.sel)
  apply (metis Suc_pred le_imp_less_Suc length_greater_0_conv nth_append)
  apply (simp add: in_flight_def validity_prop_def  f_sim_def
      global_rel_def                 )
  apply (metis option.sel)
  apply (simp add: in_flight_def validity_prop_def  f_sim_def
      global_rel_def                 )
  apply (intro conjI impI)
  apply (subgoal_tac "               write_count  (regs (\<tau> cs) t DTML.loc - recoveredGlb cs)
\<le> length (tmemory as) - Suc 0  ")
  prefer 2
  apply (simp add:  write_count_def)
  using loc_le_logical_glb [where cs= cs and t = t]
  apply (metis PC.distinct(175) PC.distinct(21) PC.distinct(711) PC.distinct(803) PC.distinct(827) PC.distinct(99) assms(2) div_le_mono)
  apply (metis Suc_pred le_imp_less_Suc length_greater_0_conv nth_append)
  apply (simp add: in_flight_def validity_prop_def  f_sim_def
      global_rel_def                 )
  apply (subgoal_tac "               write_count  (regs (\<tau> cs) t DTML.loc - recoveredGlb cs)
\<le> length (tmemory as) - Suc 0  ")
  prefer 2
  apply (simp add:  write_count_def)
  using loc_le_logical_glb [where cs= cs and t = t]
  apply (metis PC.distinct(175) PC.distinct(21) PC.distinct(711) PC.distinct(803) PC.distinct(827) PC.distinct(99) assms(2) div_le_mono)
  apply (metis Suc_pred le_imp_less_Suc length_greater_0_conv nth_append)

  apply (simp add: in_flight_def validity_prop_def  f_sim_def
      global_rel_def                 )

  apply (subgoal_tac "               write_count  (regs (\<tau> cs) t DTML.loc - recoveredGlb cs)
\<le> length (tmemory as) - Suc 0  ")
  prefer 2
  apply (simp add:  write_count_def)
  using loc_le_logical_glb [where cs= cs and t = t]
  apply (metis PC.distinct(101) PC.distinct(177) PC.distinct(23) PC.distinct(713) PC.distinct(859) PC.distinct(883) assms(2) div_le_mono)

  apply (metis Suc_pred le_imp_less_Suc length_greater_0_conv nth_append)


  apply (simp add: in_flight_def validity_prop_def  f_sim_def
      global_rel_def                 )

  apply (subgoal_tac "               write_count  (regs (\<tau> cs) t DTML.loc - recoveredGlb cs)
\<le> length (tmemory as) - Suc 0  ")
  prefer 2
  apply (simp add:  write_count_def)
  using loc_le_logical_glb [where cs= cs and t = t]
  apply (metis PC.distinct(103) PC.distinct(179) PC.distinct(25) PC.distinct(715) PC.distinct(913) PC.distinct(937) assms(2) div_le_mono)


  apply (metis Suc_pred le_imp_less_Suc length_greater_0_conv nth_append)

  apply (simp add: in_flight_def validity_prop_def  f_sim_def
      global_rel_def                 )
  apply (subgoal_tac "               write_count  (regs (\<tau> cs) t DTML.loc - recoveredGlb cs)
\<le> length (tmemory as) - Suc 0  ")
  prefer 2
  apply (simp add:  write_count_def)
  using loc_le_logical_glb [where cs= cs and t = t]
  apply (metis PC.distinct(1015) PC.distinct(1039) PC.distinct(107) PC.distinct(183) PC.distinct(29) PC.distinct(719) assms(2) div_le_mono)

  apply (metis Suc_pred le_imp_less_Suc length_greater_0_conv nth_append)

  apply (simp add: in_flight_def validity_prop_def  f_sim_def
      global_rel_def                 )

  apply(subgoal_tac "   write_count (regs (\<tau> cs') t DTML.loc - recoveredGlb cs')
< length (tmemory as) ")
  prefer 2
  apply (simp add:  write_count_def)
  using loc_le_logical_glb [where cs= cs and t = t]
  apply (metis PC.distinct(1063) PC.distinct(1087) PC.distinct(109) PC.distinct(185) PC.distinct(31) PC.distinct(721) assms(2) diff_Suc_less div_mono2 length_greater_0_conv)

  apply (metis nth_append)

  apply (simp add: in_flight_def validity_prop_def  f_sim_def
      global_rel_def                 )

  apply (intro conjI impI)
  apply (subgoal_tac "               write_count  (regs (\<tau> cs) t DTML.loc - recoveredGlb cs)
\<le> length (tmemory as) - Suc 0  ")
  prefer 2
  apply (simp add:  write_count_def)
  using loc_le_logical_glb [where cs= cs and t = t]
  apply (metis (no_types, lifting) PC.distinct(1109) PC.distinct(111) PC.distinct(1133) PC.distinct(187) PC.distinct(33) PC.distinct(723) assms(2) div_le_mono)

  apply (metis Suc_pred le_imp_less_Suc length_greater_0_conv nth_append)


  apply(subgoal_tac "   write_count (regs (\<tau> cs') t DTML.loc - recoveredGlb cs')
< length (tmemory as) ")
  prefer 2
  apply (simp add:  write_count_def)
  using loc_le_logical_glb [where cs= cs and t = t]
  apply (metis PC.distinct(1109) PC.distinct(111) PC.distinct(1133) PC.distinct(187) PC.distinct(33) PC.distinct(723) assms(2) diff_less div_mono2 length_greater_0_conv less_nat_zero_code not_less_eq)
  apply (metis nth_append)

  apply (simp add: in_flight_def validity_prop_def  f_sim_def
      global_rel_def                 )
  apply (intro conjI impI)
  apply (subgoal_tac "               write_count  (regs (\<tau> cs) t DTML.loc - recoveredGlb cs)
\<le> length (tmemory as) - Suc 0  ")
  prefer 2
  apply (simp add:  write_count_def)
  using loc_le_logical_glb [where cs= cs and t = t]
  apply (metis PC.distinct(113) PC.distinct(1153) PC.distinct(1177) PC.distinct(189) PC.distinct(35) PC.distinct(725) assms(2) div_le_mono)


  apply (metis Suc_pred le_imp_less_Suc length_greater_0_conv nth_append)
  apply(subgoal_tac "   write_count (regs (\<tau> cs') t DTML.loc - recoveredGlb cs')
< length (tmemory as) ")
  prefer 2
  apply (simp add:  write_count_def)
  using loc_le_logical_glb [where cs= cs and t = t]
  apply (metis PC.distinct(113) PC.distinct(1153) PC.distinct(1177) PC.distinct(189) PC.distinct(35) PC.distinct(725) assms(10) assms(11) assms(2) diff_Suc_less div_mono2 length_greater_0_conv)

  apply (metis nth_append)

  apply (simp add: in_flight_def validity_prop_def  f_sim_def
      global_rel_def                 )
  apply (intro conjI impI)
  apply (subgoal_tac "               write_count  (regs (\<tau> cs) t DTML.loc - recoveredGlb cs)
\<le> length (tmemory as) - Suc 0  ")
  prefer 2
  apply (simp add:  write_count_def)
  using loc_le_logical_glb [where cs= cs and t = t]
  apply (metis PC.distinct(115) PC.distinct(1195) PC.distinct(1219) PC.distinct(191) PC.distinct(37) PC.distinct(727) assms(2) div_le_mono)

  apply (metis Suc_pred le_imp_less_Suc length_greater_0_conv nth_append)


  apply (subgoal_tac "               write_count  (regs (\<tau> cs) t DTML.loc - recoveredGlb cs)
\<le> length (tmemory as) - Suc 0  ")
  prefer 2
  apply (simp add:  write_count_def)
  using loc_le_logical_glb [where cs= cs and t = t]
  apply (metis PC.distinct(115) PC.distinct(1195) PC.distinct(1219) PC.distinct(191) PC.distinct(37) PC.distinct(727) assms(2) div_le_mono)
  apply (metis Suc_pred le_imp_less_Suc length_greater_0_conv nth_append)
  apply (metis option.inject)
  apply (metis option.inject)
  apply (metis option.inject)
  apply (metis option.inject)
  apply (metis option.inject)
  apply (metis option.inject)
  apply (simp add: in_flight_def validity_prop_def  f_sim_def
      global_rel_def                 )
  apply (subgoal_tac "               write_count  (regs (\<tau> cs) t DTML.loc - recoveredGlb cs)
\<le> length (tmemory as) - Suc 0  ")
  prefer 2
  apply (simp add:  write_count_def)
  using loc_le_logical_glb [where cs= cs and t = t]
  apply (metis option.sel)
  apply  (metis Suc_pred le_imp_less_Suc length_greater_0_conv nth_append)


  apply (simp add: in_flight_def validity_prop_def  f_sim_def
      global_rel_def                 )

  apply (subgoal_tac "               write_count  (regs (\<tau> cs) t DTML.loc - recoveredGlb cs)
\<le> length (tmemory as) - Suc 0  ")
  prefer 2
  apply (simp add:  write_count_def)
  using loc_le_logical_glb [where cs= cs and t = t]
  apply (metis PC.distinct(131) PC.distinct(1459) PC.distinct(1483) PC.distinct(207) PC.distinct(53) PC.distinct(743) assms(2) div_le_mono)
  apply (metis Suc_pred le_imp_less_Suc length_greater_0_conv nth_append)

  apply (simp add: in_flight_def validity_prop_def  f_sim_def
      global_rel_def                 )

  apply (subgoal_tac "               write_count  (regs (\<tau> cs) t DTML.loc - recoveredGlb cs)
\<le> length (tmemory as) - Suc 0  ")
  prefer 2
  apply (simp add:  write_count_def)
  using loc_le_logical_glb [where cs= cs and t = t]
  apply (metis PC.distinct(1505) PC.distinct(155) PC.distinct(1639) PC.distinct(231) PC.distinct(767) PC.distinct(77) assms(2) div_le_mono)
  by (metis (no_types, lifting) Suc_pred \<open>\<lbrakk>thrdsvars; total_wfs (\<tau> cs); TML_Commit ta cs cs'; pc cs ta = Commit3; pc cs' ta = Commit4; Commit_inv ta (pc cs ta) cs; t \<noteq> ta; write_count (regs (\<tau> cs') t DTML.loc - recoveredGlb cs') < length (tmemory as); tmemory as \<noteq> []; read_consistent (tmemory as ! write_count (regs (\<tau> cs) t DTML.loc - recoveredGlb cs)) (rdSet as t); pc cs syst = RecIdle \<longrightarrow> (\<forall>t. t \<noteq> syst \<and> pc cs t \<notin> {PC.NotStarted, PC.BeginPending, PC.Committed, Begin2, PC.Aborted} \<longrightarrow> regs (\<tau> cs) t DTML.loc \<le> lastVal glb (\<tau> cs))\<rbrakk> \<Longrightarrow> read_consistent ((tmemory as @ [apply_partial (tmemory as ! (length (tmemory as) - Suc 0)) (wrSet as ta)]) ! write_count (regs (\<tau> cs) t DTML.loc - recoveredGlb cs)) (rdSet as t)\<close> assms(1) assms(13) assms(2) assms(3) assms(5) assms(6) le_imp_less_Suc length_greater_0_conv)







(*auxiliary lemma*)
lemma  commit3_commit4_global_rel:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "TML_Commit ta cs  cs'"
and "((pc cs) ta)  = PC.Commit3"
and "((pc cs') ta)  = PC.Commit4"
and " Commit_inv  ta ((pc cs) ta) cs "
and " f_sim  cs  as"
and   "\<forall>t. tms_inv as t"
and"pc cs  syst  = RecIdle "
and " tmemory as \<noteq> [] "
and  " pc cs  syst  = RecIdle \<longrightarrow> (\<forall>t.  (t \<noteq> syst  \<and> ((pc cs) t \<notin> {PC.NotStarted,PC.BeginPending, PC.Committed,PC.Begin2, PC.Aborted   }) \<longrightarrow>   regs (\<tau> cs) t loc \<le> lastVal glb  (\<tau> cs) ))"

and "\<forall>t.  (t \<noteq> syst  \<and> ((pc cs) t \<notin> {PC.NotStarted,PC.Aborted,PC.BeginPending, PC.Committed })  \<and> (writeAux cs t \<or> readAux cs t )) \<longrightarrow>  ( regs (\<tau> cs) t loc \<ge>  recoveredGlb cs )"
and  " \<forall>  t.  (   writer cs = Some t \<longrightarrow> odd (lastVal glb  (\<tau> cs)) )"
and " ( lastVal glb (\<tau> cs)  \<ge>recoveredGlb cs ) "
and " pc cs  syst  = RecIdle \<longrightarrow> even (recoveredGlb cs ) "
and"(\<forall>t. ((pc cs) t) \<in> {Commit2, Commit3,Commit4,Write3,Write4, Write5, Write6, Write7,Write8} \<longrightarrow> writer cs  =  Some t )"
and " ta \<noteq> syst"
shows "   global_rel cs'
(as\<lparr>tpc := (tpc as)(ta := TPC.CommitResponding),
tmemory :=
tmemory as @
[apply_partial (tmemory as ! (length (tmemory as) - Suc 0))
(wrSet as ta)]\<rparr>) "
  using assms
  apply (simp add: f_sim_def)
  apply (subgoal_tac " TMCommit_trans  ta as   =   as\<lparr>  tpc := (tpc as)(ta := CommitResponding),
tmemory := write_back (wrSet as ta) ( tmemory as)
\<rparr>"  )
   prefer 2
  using assms(1) assms(7) commit3_commit4_trans apply presburger
  apply (simp add: Commit_inv_def TML_Commit_def tmstep_def split:if_splits)
  apply (simp add: global_rel_def)
  apply (intro conjI impI)
    apply (simp add: maxIndex_def writes_def )
    apply (subgoal_tac " logical_glb cs = lastVal glb (\<tau> cs) - recoveredGlb cs")
     prefer 2
     apply (simp add: logical_glb_def)
     apply (subgoal_tac " writer cs' = Some ta ")
      prefer 2
      apply presburger
     apply (simp split: if_splits)
    apply (subgoal_tac " (logical_glb cs' = logical_glb cs +1 )")
     prefer 2
     apply (simp add: logical_glb_def)
     apply (subgoal_tac " writer cs' = Some ta ")
      prefer 2
      apply presburger
     apply (simp split: if_splits)
    apply (simp add:  write_count_def)
   apply (subgoal_tac " writes cs' ( TMCommit_trans  ta as )  = Map.empty  ")
    prefer 2
    apply (simp add:  writes_def)
    apply (simp split: if_splits)
    apply (smt (verit, best) assms(5) option.simps(5))
   apply (simp add: TMCommit_trans_def)
   apply (subgoal_tac " writes cs (  as )  = wrSet as ta  ")
    prefer 2
    apply (simp add:  writes_def)
    apply (simp split: if_splits)
  apply (smt (verit, best) assms(5) option.simps(5))
     apply (smt (verit) PC.distinct(519) option.simps(5))
  apply (smt (verit) PC.distinct(519) option.simps(5))
  apply (simp add: apply_partial_def)
  apply (simp add: maxIndex_def)
  apply (subgoal_tac "  apply_partial (apply_partial (tmemory as ! (length (tmemory as) - Suc 0)) (wrSet as ta))
Map.empty   =  (apply_partial (tmemory as ! (length (tmemory as) - Suc 0)) (wrSet as ta))   ")
  prefer 2
  apply (subgoal_tac " writes cs' ( TMCommit_trans  ta as )  = Map.empty  ")
  prefer 2
  apply (simp add:  writes_def)
  apply (simp split: if_splits)
  apply (smt (verit, best) assms(5) option.simps(5))
  apply (subgoal_tac " writes cs (  as )  = wrSet as ta  ")
  prefer 2
  apply (simp add:  writes_def)
  apply (smt (verit, best) assms(5) option.simps(5))
  apply (smt (z3) assms(5) option.simps(5))
  apply (unfold apply_partial_def )
  apply (metis option.simps(4))
  apply (simp add: TMCommit_trans_def  maxIndex_def  apply_partial_def)
  apply (unfold  maxIndex_def )
  apply (smt (z3) PC.distinct(245) option.simps(5) writes_def)
  apply (simp add: writes_def)
  by (smt (z3) PC.distinct(519) option.simps(5))


(*auxiliary lemma*)
lemma  commit3_commit4_read_prop:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "TML_Commit ta cs  cs'"
and "((pc cs) ta)  = PC.Commit3"
and "((pc cs') ta)  = PC.Commit4"
and " Commit_inv  ta ((pc cs) ta) cs "
and " f_sim  cs  as"
and   "\<forall>t. tms_inv as t"
and"pc cs  syst  = RecIdle "
and " tmemory as \<noteq> [] "
and  " pc cs  syst  = RecIdle \<longrightarrow> (\<forall>t.  (t \<noteq> syst  \<and> ((pc cs) t \<notin> {PC.NotStarted,PC.BeginPending, PC.Committed,PC.Begin2, PC.Aborted  }) \<longrightarrow>   regs (\<tau> cs) t loc \<le> lastVal glb  (\<tau> cs) ))"
and "\<forall>t.  (t \<noteq> syst  \<and> ((pc cs) t \<notin> {PC.NotStarted,PC.Aborted, PC.Committed,PC.BeginPending })  \<and> (writeAux cs t \<or> readAux cs t )) \<longrightarrow>  ( regs (\<tau> cs) t loc \<ge>  recoveredGlb cs )"
and  " \<forall>  t.  (   writer cs = Some t \<longrightarrow> odd (lastVal glb  (\<tau> cs)) )"
and " ( lastVal glb (\<tau> cs)  \<ge>recoveredGlb cs ) "
and " pc cs  syst  = RecIdle \<longrightarrow> even (recoveredGlb cs ) "
and"(\<forall>t. ((pc cs) t) \<in> {Commit2, Commit3,Commit4,Write3,Write4, Write5, Write6, Write7,Write8} \<longrightarrow> writer cs  =  Some t )"
and " TMCommit_trans  ta as   =   as\<lparr>  tpc := (tpc as)(ta := CommitResponding),
tmemory := write_back (wrSet as ta) ( tmemory as)
\<rparr>"
and " global_rel cs'  (TMCommit_trans  ta as )"
and "   (\<forall> n. (0 \<le> n \<and> n  < length (memory (\<tau> cs))  \<and> comploc ((memory (\<tau> cs))!n) glb= glb) \<longrightarrow>  (valOf n glb  (\<tau> cs)) \<le> lastVal glb  (\<tau> cs) ) "
and " ta \<noteq> syst"
shows"read_prop cs' (TMCommit_trans  ta as )"
  using assms
  apply (unfold total_wfs_def  read_prop_def global_rel_def)

  apply (subgoal_tac "  write_count ( lastVal glb (\<tau> cs') - recoveredGlb cs') < write_count (logical_glb cs' ) ")
  prefer 2
  apply (subgoal_tac " logical_glb cs' = lastVal glb (\<tau> cs)+1 - recoveredGlb cs")
  prefer 2
  apply (simp add: logical_glb_def)
  apply (subgoal_tac " writer cs' = Some ta ")
   prefer 2
   apply (simp add:  Commit_inv_def TML_Commit_def)

  apply (simp split: if_splits)
  apply (simp add: write_count_def)
  apply (unfold  Commit_inv_def TML_Commit_def)
  apply (smt (z3) PC.simps(1648))
  apply (simp(no_asm) add: write_count_def)
  apply (subgoal_tac " lastVal glb (\<tau> cs') = lastVal glb (\<tau> cs) ")
  prefer 2

  apply (smt (z3) PC.simps(1648))
  using  Suc_diff_le dvd_diff_nat even_Suc lessI odd_Suc_div_two
   apply (smt (z3) Nat.add_0_right One_nat_def PC.simps(1648) add_Suc_right)
  apply (subgoal_tac "   write_count (lastVal glb (\<tau> cs') - recoveredGlb cs') <
length (tmemory  (  TMCommit_trans ta as)) -  1 ")
   prefer 2
   apply (subgoal_tac " pc cs' syst = RecIdle ")
    prefer 2
    apply (smt (z3) PC.simps(1648) pc_aux)
   apply (smt (z3) PC.simps(1061) assms(9) pc_aux)
  apply (subgoal_tac " memory(\<tau> cs) = memory(\<tau>  cs') ")
   prefer 2
   apply (smt (z3) PC.simps(1648))

  apply (subgoal_tac "   (\<forall> n. (0 \<le> n \<and> n  < length (memory (\<tau> cs'))  \<and> comploc ((memory (\<tau> cs'))!n) glb= glb) \<longrightarrow>
write_count ( (valOf n glb  (\<tau> cs')) - recoveredGlb cs')  \<le>   write_count (lastVal glb (\<tau> cs') - recoveredGlb cs') ) ")
   prefer 2
   apply (subgoal_tac " pc cs' syst = RecIdle ")
    prefer 2
    apply (smt (z3) PC.simps(1648) pc_aux)
   apply (subgoal_tac " recoveredGlb cs'  = recoveredGlb cs ")
    prefer 2
    apply (smt (z3) PC.simps(1648))
   apply (subgoal_tac " memory (\<tau> cs) = memory (\<tau> cs' )")
    prefer 2
    apply blast
   apply (unfold write_count_def)
   apply clarify
   apply (subgoal_tac " valOf n glb (\<tau> cs')  \<le>  lastVal glb (\<tau> cs')")
    prefer 2
    apply (smt (z3) PC.simps(1648))
  using diff_le_mono div_le_mono apply presburger
  apply (subgoal_tac "   (\<forall> n. (0 \<le> n \<and> n  < length (memory (\<tau> cs'))  \<and> comploc ((memory (\<tau> cs'))!n) glb= glb) \<longrightarrow>
write_count ( (valOf n glb  (\<tau> cs')) - recoveredGlb cs') < length (tmemory  (  TMCommit_trans ta as)) -  1  ) ")
   prefer 2
  using  le_antisym le_neq_implies_less le_trans less_or_eq_imp_le write_count_def
   apply (smt (z3) Nat.add_diff_assoc2 PC.simps(1061) assms(4) even_add even_diff_nat odd_one odd_succ_div_two trans_le_add1)
  apply (subgoal_tac " \<forall> i. 0 \<le> i \<and> i <  (length (tmemory (  as)) )    \<longrightarrow> (tmemory as !i = (tmemory (  TMCommit_trans ta as)) !i)")
   apply (subgoal_tac "   (length (tmemory (  as) )  =  length (tmemory  (  TMCommit_trans ta as)) -  1  ) ")
    apply (subgoal_tac "  pc cs' syst  =  pc cs syst  ")
     prefer 2
     apply (smt (z3) PC.simps(1648) pc_aux)
    apply (subgoal_tac "  (\<forall>n l. 0 \<le> n \<and>
n < length (memory (\<tau> cs')) \<longrightarrow>  comploc (memory (\<tau> cs') ! n) glb =  comploc (memory (\<tau> cs) ! n) glb  ) ")
     prefer 2
     apply (smt (z3) PC.simps(1061))
    apply (subgoal_tac "  (\<forall>n l. 0 \<le> n \<and>
n < length (memory (\<tau> cs')) \<longrightarrow>   valOf n  l (\<tau> cs') =   valOf n l (\<tau> cs')) ")
     prefer 2
     apply (smt (z3) PC.simps(935))
    apply (subgoal_tac "  (\<forall>n l. 0 \<le> n \<and>
n < length (memory (\<tau> cs')) \<longrightarrow>   (last_entry_lim (\<tau> cs') l n)  =   (last_entry_lim (\<tau> cs) l n)) ")
     prefer 2
     apply (smt (z3) PC.simps(1648))
    apply (subgoal_tac " (\<forall>n l. 0 \<le> n \<and> n < length (memory (\<tau> cs')) \<and> comploc (memory (\<tau> cs') ! n) glb = glb \<longrightarrow>
(tmemory (TMCommit_trans ta as) ! ((valOf n glb (\<tau> cs') - recoveredGlb cs') div 2)) =  tmemory ( as) ! ((valOf n glb (\<tau> cs') - recoveredGlb cs') div 2))")
     prefer 2
     apply (subgoal_tac " (\<forall>n l. 0 \<le> n \<and> n < length (memory (\<tau> cs')) \<and> comploc (memory (\<tau> cs') ! n) glb = glb \<longrightarrow>
( ((valOf n glb (\<tau> cs') - recoveredGlb cs') div 2)) \<le> ((lastVal glb (\<tau> cs') - recoveredGlb cs') div 2))")
      prefer 2
      apply clarify
      apply (subgoal_tac " lastVal glb (\<tau> cs') - recoveredGlb cs'  \<ge> 0 ")
       prefer 2
       apply blast
      apply (case_tac " valOf n glb (\<tau> cs') < recoveredGlb cs' ")
       prefer 2
       apply (subgoal_tac " valOf n glb (\<tau> cs') \<le> lastVal glb (\<tau> cs')")
        prefer 2
        apply (smt (z3) PC.simps(1648))
       apply (subgoal_tac " valOf n glb (\<tau> cs')\<ge> recoveredGlb cs'")
        prefer 2
        apply linarith
       apply (subgoal_tac " valOf n glb (\<tau> cs') - recoveredGlb cs' \<le> lastVal glb (\<tau> cs')  - recoveredGlb cs'")
        prefer 2
        apply (subgoal_tac " lastVal glb (\<tau> cs') \<ge> recoveredGlb cs'")
         prefer 2
  using PC.simps(935) assms(14) apply linarith
        apply (metis (no_types, opaque_lifting) diff_le_mono)
       apply (meson div_le_mono)
      apply (subgoal_tac " valOf n glb (\<tau> cs') - recoveredGlb cs'  = 0 ")
       prefer 2
  using valOf_def
       apply (metis diff_is_0_eq' less_or_eq_imp_le)
  using div_le_mono
      apply metis
     apply (subgoal_tac "   (\<forall> n. (0 \<le> n \<and> n  < length (memory (\<tau> cs'))  \<and> comploc ((memory (\<tau> cs'))!n) glb= glb) \<longrightarrow>
write_count ( (valOf n glb  (\<tau> cs')) - recoveredGlb cs') <length (tmemory as))  ")
      apply (metis (no_types, lifting) Euclidean_Division.div_eq_0_iff div_le_dividend write_count_def)
  apply (subgoal_tac "   (\<forall> n. (0 \<le> n \<and> n  < length (memory (\<tau> cs'))  \<and> comploc ((memory (\<tau> cs'))!n) glb= glb) \<longrightarrow>
write_count ( (valOf n glb  (\<tau> cs')) - recoveredGlb cs') < length (tmemory  (  TMCommit_trans ta as)) -  1  ) ")
  prefer 2
  apply (smt (z3) le_antisym le_neq_implies_less le_trans less_or_eq_imp_le write_count_def)
  apply presburger
  apply (unfold f_sim_def)
  apply (unfold    read_prop_def)
  apply (smt (z3) Euclidean_Division.div_eq_0_iff PC.simps(1648) div_le_dividend write_count_def)
  using assms(17) tmem_commit_length [where  \<sigma> = as and t = ta]
  apply (metis Nat.add_0_right Nat.add_diff_assoc bits_div_by_1 diff_self_eq_0 div_le_dividend)
  using assms(17) tmem_l_commitWr[where  \<sigma> = as and t = ta]
  by presburger



(*
lemma  test:
shows "(\<forall> a :: nat . \<forall> b :: nat.  a < b \<longrightarrow> a -b = 0)"
by simp*)

(*the simulation relation holds from Commit3 to  Commit4  (non stuttering step)  *)
lemma   f_sim_commit3_commit4_LP:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "TML_Commit ta cs  cs'"
and "((pc cs) ta)  = PC.Commit3"
and "((pc cs') ta)  = PC.Commit4"
and " Commit_inv  ta ((pc cs) ta) cs "
and " f_sim  cs  as"
and   "\<forall>t. tms_inv as t"
and"pc cs  syst  = RecIdle "
and " tmemory as \<noteq> [] "
and  " pc cs  syst  = RecIdle \<longrightarrow> (\<forall>t.  (t \<noteq> syst  \<and> ((pc cs) t \<notin> {PC.NotStarted, PC.BeginPending,  PC.Committed,PC.Begin2 ,PC.Aborted  }) \<longrightarrow>   regs (\<tau> cs) t loc \<le> lastVal glb  (\<tau> cs) ))"
and "\<forall>t.  (t \<noteq> syst  \<and> ((pc cs) t \<notin> {PC.NotStarted,PC.Aborted, PC.Committed, PC.BeginPending })  \<and> (writeAux cs t \<or> readAux cs t )) \<longrightarrow>  ( regs (\<tau> cs) t loc \<ge>  recoveredGlb cs )"
and  " \<forall>  t.  (   writer cs = Some t \<longrightarrow> odd (lastVal glb  (\<tau> cs)) )"
and " ( lastVal glb (\<tau> cs)  \<ge>recoveredGlb cs ) "
and " pc cs  syst  = RecIdle \<longrightarrow> even (recoveredGlb cs ) "
and"(\<forall>t. ((pc cs) t) \<in> {Commit2, Commit3,Commit4,Write3,Write4, Write5, Write6, Write7,Write8} \<longrightarrow> writer cs  =  Some t )"
and "   (\<forall> n. (0 \<le> n \<and> n  < length (memory (\<tau> cs))  \<and> comploc ((memory (\<tau> cs))!n) glb= glb) \<longrightarrow>  (valOf n glb  (\<tau> cs)) \<le> lastVal glb  (\<tau> cs) ) "
and " ta \<noteq> syst"
and " \<forall>t. writer cs = Some t \<longrightarrow>
odd (lastVal glb (\<tau> cs))"
shows " \<exists> as'. tmstep ta TMCommit  as  as'   \<and> f_sim  cs' as'  "
  using assms
  apply (simp add: f_sim_def)
  apply (subgoal_tac " TMCommit_trans  ta as   =   as\<lparr>  tpc := (tpc as)(ta := CommitResponding),
tmemory := write_back (wrSet as ta) ( tmemory as)
\<rparr>"  )
   prefer 2
  using assms(1) assms(7) commit3_commit4_trans apply presburger
  apply (simp add: Commit_inv_def TML_Commit_def tmstep_def split:if_splits)
  apply (intro conjI impI)
  using  commit3_commit4_global_rel[where as= as and cs= cs and cs' = cs' and ta=ta ]
  using assms(1) assms(11) assms(12) assms(16) assms(3) assms(5) assms(6) assms(7)
  apply (smt (z3) insertCI)
  apply (intro allI conjI)
  apply (simp add: no_read_rdSet_empty_def)
  apply (simp add: no_write_wrSet_empty_def)
  apply (simp add: write_wrSet_notEmpty_def)
  apply (simp add: read_rdSet_notEmpty_def)
  apply (simp add: loc_in_wrSet_def)
  apply (simp add: even_loc_wrSet_empty_def)
  apply (simp add:  odd_loc_wrSet_notEmpty_def)
  apply (case_tac "t = ta")
  apply (metis assms(1) assms(10) assms(3) assms(5) assms(6) f_sim_def tr_rel_commit3_commit4_self)
  apply (subgoal_tac " tr_rel cs as t" )
  prefer 2
  apply presburger
  using   tr_rel_commit3_commit4_stable[where cs = cs and as = as and cs' = cs' and ta=ta ]
  using assms(1) assms(11) assms(12) assms(16) assms(3) assms(5) assms(6) assms(7)
  apply (metis (mono_tags, lifting))
  apply (subgoal_tac  " TMCommit_trans  ta as   =   as\<lparr>  tpc := (tpc as)(ta := CommitResponding),
tmemory := write_back (wrSet as ta) ( tmemory as)
\<rparr>" )
  prefer 2
  apply (metis dvd_1_left nat_dvd_1_iff_1)
  apply (subgoal_tac "  global_rel cs'  (TMCommit_trans  ta as )" )
  prefer 2
  using  commit3_commit4_global_rel[where as= as and cs= cs and cs' = cs' and ta=ta ]
  apply (smt (z3) assms(1) assms(11) assms(12) assms(16) assms(3) assms(5) assms(6) assms(7) insert_commute)
  using commit3_commit4_read_prop [where cs= cs and as = as and cs' = cs' and ta=ta]
  by (smt (z3) assms(1) assms(11) assms(12) assms(16) assms(17) assms(3) assms(5) assms(6) assms(7))




(********************************************)
(*auxiliary lemma*)
lemma    tr_rel_commit2_commit3_self:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "TML_Commit ta cs  cs'"
and "((pc cs) ta)  = PC.Commit2"
and "((pc cs') ta)  = PC.Commit3"
and " Commit_inv  ta ((pc cs) ta) cs "
and"   tr_rel   cs as ta"
and " f_sim  cs  as"
and   "\<forall>t.  tms_inv as  t "
and"pc cs  syst  = RecIdle "
shows "   tr_rel   cs' as ta  "
  using assms
  apply (simp add:TML_Commit_def tr_rel_def in_flight_def validity_prop_def total_wfs_def Commit_inv_def  tms_inv_def  split: if_splits )
  by (metis reg_same_sfence)


(*auxiliary lemma*)
lemma    tr_rel_commit2_commit3_stable:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "TML_Commit ta cs  cs'"
and "((pc cs) ta)  = PC.Commit2"
and "((pc cs') ta)  = PC.Commit3"
and " Commit_inv  ta ((pc cs) ta) cs "
and " t \<noteq> ta "
and"   tr_rel   cs as t"
and " f_sim  cs  as"
and   "\<forall>t.  tms_inv as  t "
and " ta \<noteq> syst"
shows "   tr_rel   cs' as t  "
  using assms
  apply (simp add:TML_Commit_def tr_rel_def in_flight_def validity_prop_def total_wfs_def Commit_inv_def  split: if_splits )
  apply (unfold in_flight_def validity_prop_def )
  apply(cases "pc cs t";  simp)
  apply (metis reg_same_sfence)
  apply (metis reg_same_sfence)
  apply (metis reg_same_sfence)
  apply (metis reg_same_sfence)
  apply (metis lastVal_def reg_same_sfence sf_nlv_ni)
  apply (metis lastVal_def reg_same_sfence sf_nlv_ni)
  apply (metis reg_same_sfence)
  apply (intro conjI impI)
  apply (metis reg_same_sfence)
  apply (metis reg_same_sfence)
  apply (metis reg_same_sfence)
  apply (metis lastVal_def reg_same_sfence sf_nlv_ni)
  apply (metis lastVal_def reg_same_sfence sf_nlv_ni)
  apply (metis (no_types, lifting) lastVal_def reg_same_sfence sf_nlv_ni)
  apply (metis lastVal_def reg_same_sfence sf_nlv_ni)
  apply (metis reg_same_sfence)
  apply (metis reg_same_sfence)
  apply (metis lastVal_def reg_same_sfence sf_nlv_ni)
  apply (metis lastVal_def reg_same_sfence sf_nlv_ni)
  apply (metis lastVal_def reg_same_sfence sf_nlv_ni)
  apply (metis assms(2) sf_ov_ni sf_wfs_preserved singleton_iff total_wfs_def)
  apply (metis reg_same_sfence)
  apply (metis reg_same_sfence)
  apply (metis reg_same_sfence)
  apply (metis reg_same_sfence)
  apply (metis reg_same_sfence)
  apply (metis reg_same_sfence)
  apply (metis lastVal_def reg_same_sfence sf_nlv_ni)
  by (metis lastVal_def reg_same_sfence sf_nlv_ni)



(*the simulation relation holds from Commit2 to  Commit3  (stuttering step)  *)
lemma   f_sim_commit_commit2_commit3:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "TML_Commit ta cs  cs'"
and "((pc cs) ta)  = PC.Commit2"
and "((pc cs') ta)  = PC.Commit3"
and " Commit_inv  ta ((pc cs) ta) cs "
and " f_sim  cs  as"
and   "\<forall>t.  tms_inv as  t "
and"pc cs  syst  = RecIdle "
and " ta \<noteq> syst"
shows " f_sim  cs' as  "
  using assms
  apply (simp add: Commit_inv_def total_wfs_def TML_Commit_def split:if_splits)
  apply (simp add:  f_sim_def)
  apply (intro conjI)
    apply (simp add: global_rel_def)
    apply (unfold writes_def logical_glb_def maxIndex_def write_count_def)
    apply (intro conjI allI impI)
       apply simp
       apply (metis assms(2) insert_absorb insert_iff insert_not_empty sf_ov_ni sf_wfs_preserved total_wfs_def)
      apply simp
      apply (metis assms(2) sf_ov_ni sf_wfs_preserved singletonD total_wfs_def)
     apply simp
     apply (metis One_nat_def maxIndex_def sfence_lastVal_ni)
    apply simp
   apply (simp add:  no_read_rdSet_empty_def  no_write_wrSet_empty_def  odd_loc_wrSet_notEmpty_def write_wrSet_notEmpty_def read_rdSet_notEmpty_def  )
   apply (subgoal_tac " \<forall> t.  even_loc_wrSet_empty cs' as t ")
    prefer 2
    apply (simp add:   even_loc_wrSet_empty_def  )
    apply clarify
    apply (intro conjI impI)
     apply (metis reg_same_sfence)
    apply (metis reg_same_sfence)
   apply (subgoal_tac " \<forall> t.  loc_in_wrSet cs' as t ")
    prefer 2
    apply (simp add:   loc_in_wrSet_def)
    apply (meson sfence_lastVal_ni)
   apply (simp add: odd_loc_wrSet_notEmpty_def)
   apply (smt (verit) assms(1) assms(2) assms(3) assms(5) assms(6) assms(7) reg_same_sfence tr_rel_commit2_commit3_self tr_rel_commit2_commit3_stable)
  apply (unfold read_prop_def)
  by (smt (z3) assms(2) sf_le_lim_ni sfence_crash step_mem_sfence valOf_def)



(*************************************************)

(*auxiliary lemma*)
lemma    tr_rel_commit4_commitResponding_self:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "TML_Commit ta cs  cs'"
and "((pc cs) ta)  = PC.Commit4"
and "((pc cs') ta)  = PC.CommitResponding"
and " Commit_inv  ta ((pc cs) ta) cs "
and"   tr_rel   cs as ta"
and " f_sim  cs  as"
and   "\<forall>t.  tms_inv as  t "
shows "   tr_rel   cs' as ta  "
  using assms
  by(simp add:TML_Commit_def tr_rel_def in_flight_def validity_prop_def total_wfs_def Commit_inv_def  tms_inv_def  split: if_splits )


(*auxiliary lemma*)
lemma    tr_rel_commit4_commitResponding_stable:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "TML_Commit ta cs  cs'"
and "((pc cs) ta)  = PC.Commit4"
and "((pc cs') ta)  = PC.CommitResponding"
and " Commit_inv  ta ((pc cs) ta) cs "
and " t \<noteq> ta "
and"   tr_rel   cs as t"
and  " pc cs syst  = RecIdle \<longrightarrow> (\<forall>t.  (t \<noteq> syst  \<and> ((pc cs) t \<notin> {PC.NotStarted,PC.BeginPending, PC.Committed,PC.Begin2 ,PC.Aborted    }) \<longrightarrow>   regs (\<tau> cs) t loc \<le> lastVal glb  (\<tau> cs) ))"
and " f_sim  cs  as"
and   "\<forall>t.  tms_inv as  t "
and " ta \<noteq> syst"
shows "   tr_rel   cs' as t  "
  using assms
  apply (simp add:TML_Commit_def tr_rel_def in_flight_def validity_prop_def total_wfs_def Commit_inv_def  split: if_splits )
  apply (unfold in_flight_def validity_prop_def )
  apply(cases "pc cs t";  simp)
  apply (metis reg_same_st)
  apply (metis reg_same_st)
  apply (metis reg_same_st)
  apply (metis reg_same_st)
  apply (metis PC.distinct(161) PC.distinct(319) PC.distinct(355) PC.distinct(379) PC.distinct(7) PC.distinct(85) Suc_n_not_le_n reg_same_st st_lastVal_lc)
  apply (metis PC.distinct(163) PC.distinct(389) PC.distinct(425) PC.distinct(449) PC.distinct(87) PC.distinct(9) Suc_n_not_le_n reg_same_st st_lastVal_lc)
  apply (metis PC.distinct(163) PC.distinct(389) PC.distinct(425) PC.distinct(87) PC.distinct(9) Suc_n_not_le_n reg_same_st st_lastVal_lc)
  apply (metis reg_same_st)
  apply (metis PC.distinct(175) PC.distinct(21) PC.distinct(711) PC.distinct(803) PC.distinct(827) PC.distinct(99) Suc_n_not_le_n reg_same_st st_lastVal_lc)
  apply (metis PC.distinct(101) PC.distinct(177) PC.distinct(23) PC.distinct(713) PC.distinct(859) PC.distinct(883) Suc_n_not_le_n reg_same_st st_lastVal_lc)
  apply (metis PC.distinct(103) PC.distinct(179) PC.distinct(25) PC.distinct(715) PC.distinct(913) PC.distinct(937) Suc_n_not_le_n reg_same_st st_lastVal_lc)
  apply (metis PC.distinct(105) PC.distinct(181) PC.distinct(27) PC.distinct(717) PC.distinct(965) PC.distinct(989) Store_Rules.st_lv_lc Suc_n_not_le_n lastVal_def reg_same_st)
  apply (metis PC.distinct(101) PC.distinct(177) PC.distinct(23) PC.distinct(713) PC.distinct(859) Suc_n_not_le_n reg_same_st st_lastVal_lc)
  apply (smt (verit) Nat.diff_add_assoc2 PC.distinct(103) PC.distinct(179) PC.distinct(25) PC.distinct(715) PC.distinct(913) add_le_imp_le_right diff_add_inverse le_numeral_extra(4) not_one_le_zero numeral_1_eq_Suc_0 numerals(1) plus_1_eq_Suc reg_same_st st_lastVal_lc)
  apply (metis PC.distinct(1109) PC.distinct(111) PC.distinct(1133) PC.distinct(187) PC.distinct(33) PC.distinct(723) Suc_n_not_le_n reg_same_st st_lastVal_lc)
  apply (metis PC.distinct(113) PC.distinct(1153) PC.distinct(1177) PC.distinct(189) PC.distinct(35) PC.distinct(725) Suc_n_not_le_n reg_same_st st_lastVal_lc)
  apply (metis PC.distinct(115) PC.distinct(1195) PC.distinct(1219) PC.distinct(191) PC.distinct(37) PC.distinct(727) Suc_n_not_le_n reg_same_st st_lastVal_lc)
  apply (metis PC.distinct(117) PC.distinct(1235) PC.distinct(1259) PC.distinct(193) PC.distinct(39) PC.distinct(729) Suc_n_not_le_n reg_same_st st_lastVal_lc)
  apply (metis PC.distinct(105) PC.distinct(181) PC.distinct(27) PC.distinct(717) PC.distinct(965) Store_Rules.st_lv_lc Suc_n_not_le_n lastVal_def reg_same_st)
  apply (metis reg_same_st)
  apply (metis reg_same_st)
  apply (smt (verit) PC.distinct(1109) PC.distinct(111) PC.distinct(187) PC.distinct(33) PC.distinct(723) Suc_n_not_le_n reg_same_st st_lastVal_lc)
  apply (metis PC.distinct(113) PC.distinct(1153) PC.distinct(189) PC.distinct(35) PC.distinct(725) Suc_n_not_le_n reg_same_st st_lastVal_lc)
  apply (smt (verit) PC.distinct(115) PC.distinct(1195) PC.distinct(191) PC.distinct(37) PC.distinct(727) add_le_same_cancel2 le_less_Suc_eq less_Suc_eq_0_disj nat_neq_iff plus_1_eq_Suc reg_same_st st_lastVal_lc)
  apply (metis PC.distinct(131) PC.distinct(1459) PC.distinct(1483) PC.distinct(207) PC.distinct(53) PC.distinct(743) Suc_n_not_le_n reg_same_st st_lastVal_lc)
  by (metis PC.distinct(1505) PC.distinct(155) PC.distinct(1639) PC.distinct(231) PC.distinct(767) PC.distinct(77) Suc_n_not_le_n reg_same_st st_lastVal_lc)





(*auxiliary lemma*)
lemma  commit4_commitResponding_logical_glb_ni:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "TML_Commit ta cs  cs'"
and "((pc cs) ta)  = PC.Commit4"
and "((pc cs') ta)  = PC.CommitResponding"
and " Commit_inv  ta ((pc cs) ta) cs "
shows " logical_glb cs = logical_glb cs' "
  using assms
  apply (unfold total_wfs_def logical_glb_def)
  apply (simp add: TML_Commit_def   Commit_inv_def)
  by (metis st_lastVal_lc)

(*auxiliary lemma*)
lemma  commit4_commitResponding_global_rel:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "TML_Commit ta cs  cs'"
and "((pc cs) ta)  = PC.Commit4"
and "((pc cs') ta)  = PC.CommitResponding"
and " Commit_inv  ta ((pc cs) ta) cs "
and " f_sim  cs  as"
and   "\<forall>t. tms_inv as t"
and " tmemory as \<noteq> [] "
and  " pc cs  syst  = RecIdle \<longrightarrow> (\<forall>t.  (t \<noteq> syst  \<and> ((pc cs) t \<notin> {PC.NotStarted, PC.Committed,PC.Begin2, PC.BeginPending,PC.Aborted   }) \<longrightarrow>   regs (\<tau> cs) t loc \<le> lastVal glb  (\<tau> cs) ))"
and "\<forall>t.  (t \<noteq> syst  \<and> ((pc cs) t \<notin> {PC.NotStarted,PC.Aborted, PC.Committed, PC.BeginPending  })  \<and> (writeAux cs t \<or> readAux cs t )) \<longrightarrow>  ( regs (\<tau> cs) t loc \<ge>  recoveredGlb cs )"
and"(\<forall>t. ((pc cs) t) \<in> {Commit2, Commit3,Commit4,Write3,Write4, Write5, Write6, Write7,Write8} \<longrightarrow> writer cs  =  Some t)"
and  " \<forall>  t.  (   writer cs = Some t \<longrightarrow> odd (lastVal glb  (\<tau> cs)) )"
and " ta \<noteq> syst"
shows "   global_rel cs' as "
  using assms
  apply (unfold total_wfs_def)
  apply (simp add: f_sim_def global_rel_def Commit_inv_def TML_Commit_def )
  apply (intro conjI impI allI)
  apply (simp add: write_count_def logical_glb_def)
  apply (subgoal_tac " lastVal glb (\<tau> cs')  = Suc (lastVal glb (\<tau> cs))  ")
  prefer 2
  apply (metis st_lastVal_lc)
  apply presburger
  apply (simp add: writes_def)
  apply (metis assms(2) st_lv__daddr_ni)
  apply (simp add: writes_def)
  by (metis assms(2) st_lv__daddr_ni)


(*auxiliary lemma*)
lemma  commit4_commit_read_prop:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "TML_Commit ta cs  cs'"
and "((pc cs) ta)  = PC.Commit4"
and "((pc cs') ta)  = PC.CommitResponding"
and " Commit_inv  ta ((pc cs) ta) cs "
and " f_sim  cs  as"
and   "\<forall>t. tms_inv as t"
and " tmemory as \<noteq> [] "
and  " pc cs  syst  = RecIdle \<longrightarrow> (\<forall>t.  (t \<noteq> syst  \<and> ((pc cs) t \<notin> {PC.NotStarted,PC.BeginPending, PC.Committed,PC.Begin2, PC.Aborted   }) \<longrightarrow>   regs (\<tau> cs) t loc \<le> lastVal glb  (\<tau> cs) ))"
and "\<forall>t.  (t \<noteq> syst  \<and> ((pc cs) t \<notin> {PC.NotStarted,PC.Aborted, PC.Committed ,PC.BeginPending})  \<and> (writeAux cs t \<or> readAux cs t )) \<longrightarrow>  ( regs (\<tau> cs) t loc \<ge>  recoveredGlb cs )"
and"(\<forall>t. ((pc cs) t) \<in> {Commit2, Commit3,Commit4,Write3,Write4, Write5, Write6, Write7,Write8} \<longrightarrow> writer cs  =  Some t)"
and  " \<forall>  t.  (   writer cs = Some t \<longrightarrow> odd (lastVal glb  (\<tau> cs)) )"
and "   global_rel cs' as "
and " ta \<noteq> syst"
shows"read_prop cs' as"
  using assms
  apply (unfold total_wfs_def  read_prop_def f_sim_def  global_rel_def  TML_Commit_def  Commit_inv_def)
  apply (subgoal_tac " length (memory (\<tau> cs') ) = length (memory (\<tau> cs)) + 1 ")
  prefer 2
  apply (metis (no_types, lifting) PC.simps(1649) st_mem_length)
  apply (subgoal_tac " \<forall>i. 0 \<le> i \<and> i < length (memory (\<tau> cs) ) \<longrightarrow> (memory (\<tau> cs'))!i = (memory (\<tau> cs))!i ")
  prefer 2
  apply (metis (no_types, lifting) PC.simps(1649) mem_l_step)
  apply (simp add: split if_splits)
  apply (intro allI  impI)
  apply (case_tac "  n < length (memory (\<tau> cs)) ")
  using st_valOf_nle_ni st_succ_lelim_nle_ni
  apply (metis le0)
  apply (case_tac "  n = length (memory (\<tau> cs)) ")
  apply clarify
  apply (subgoal_tac " valOf   (last_entry_lim (\<tau> cs') l (length (memory (\<tau> cs))) ) l (\<tau> cs')    =  lastVal l (\<tau> cs')")
  prefer 2
  apply (metis (no_types, lifting) PC.simps(1062) st_succ_lv_lim_eq_lv_val)
  apply (subgoal_tac "  (valOf (length (memory (\<tau> cs))) glb (\<tau> cs')   = lastVal glb (\<tau> cs') ) ")
  prefer 2
  apply (metis (no_types, lifting) PC.simps(1062) st_lastEntry_lc st_lv_lim_eq_lv st_succ_lv_lim_eq_lv_val)
  apply (subgoal_tac "  last_entry (\<tau> cs') glb =  length (memory (\<tau> cs)) ")
  prefer 2
  apply (metis (no_types, lifting) PC.simps(1062) st_lastEntry_lc)
  apply (subgoal_tac "  write_count (logical_glb cs') =  write_count (logical_glb cs) ")
  prefer 2
  apply presburger
  apply (subgoal_tac " logical_glb cs' = (lastVal glb (\<tau> cs') - recoveredGlb cs') ")
  prefer 2
  apply (simp(no_asm) add: logical_glb_def)
  apply (smt (z3) PC.simps(1062) option.simps(4))
  apply (subgoal_tac "   write_count
(valOf (length (memory (\<tau> cs))) glb (\<tau> cs') - recoveredGlb cs') = write_count(  logical_glb cs') ")
  prefer 2
  apply presburger
  apply (subgoal_tac " writes cs' as = writes cs as ")
  prefer 2
  apply (simp(no_asm) add: writes_def)
  apply ( unfold tr_rel_def)
  apply (smt (z3) PC.simps(1062) assms(4) option.simps(4) option.simps(5))
  apply (subgoal_tac " (writes cs' as) = Map.empty " )
  prefer 2
  apply (simp(no_asm) add: writes_def)
  apply (smt (z3) PC.simps(1062) option.simps(4))
  apply (unfold  maxIndex_def)
  apply (simp(no_asm) add: apply_partial_def)
  apply (metis st_succ_lv_lim_eq_lv_val)
  apply safe
  apply (meson not_less_less_Suc_eq)
  by (meson not_less_less_Suc_eq)



(*the simulation relation holds from Commit4 to  CommitResponding  (stuttering step)  *)
lemma f_sim_commit4_commitResponding:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "TML_Commit ta cs  cs'"
and "((pc cs) ta)  = PC.Commit4"
and "((pc cs') ta)  = PC.CommitResponding"
and " Commit_inv  ta ((pc cs) ta) cs "
and " f_sim  cs  as"
and   "\<forall>t. tms_inv as t"
and " tmemory as \<noteq> [] "
and  " pc cs  syst  = RecIdle \<longrightarrow> (\<forall>t.  (t \<noteq> syst  \<and> ((pc cs) t \<notin> {PC.NotStarted, PC.Committed,PC.Begin2, PC.BeginPending, PC.Aborted   }) \<longrightarrow>   regs (\<tau> cs) t loc \<le> lastVal glb  (\<tau> cs) ))"
and "\<forall>t.  (t \<noteq> syst  \<and> ((pc cs) t \<notin> {PC.NotStarted,PC.Aborted, PC.Committed, PC.BeginPending    })  \<and> (writeAux cs t \<or> readAux cs t )) \<longrightarrow>  ( regs (\<tau> cs) t loc \<ge>  recoveredGlb cs )"
and"(\<forall>t. ((pc cs) t) \<in> {Commit2, Commit3,Commit4,Write3,Write4, Write5, Write6, Write7,Write8} \<longrightarrow> writer cs  =  Some t)"
and  " \<forall>  t.  (   writer cs = Some t \<longrightarrow> odd (lastVal glb  (\<tau> cs)) )"
and " ta \<noteq> syst"
shows"f_sim  cs' as"
using assms
  apply (unfold  f_sim_def)
  apply (intro conjI)
  using assms(7) commit4_commitResponding_global_rel apply presburger
  apply (intro allI conjI impI)
  prefer 8
  apply (subgoal_tac " global_rel cs' as ")
  prefer 2
  using assms(7) commit4_commitResponding_global_rel apply presburger
  prefer 9
  apply (subgoal_tac " global_rel cs' as ")
  prefer 2
  using assms(7) commit4_commitResponding_global_rel apply presburger
  apply (smt (z3) assms(7) commit4_commit_read_prop insert_commute)
  apply (case_tac " t = ta ")
  using f_sim_def tr_rel_commit4_commitResponding_self apply presburger
  using   tr_rel_commit4_commitResponding_stable [where cs = cs and as = as and cs' = cs']
  apply (smt (verit) assms(7) insert_iff)
  apply (simp add: no_read_rdSet_empty_def  Commit_inv_def TML_Commit_def )
  apply (simp add:  no_write_wrSet_empty_def  Commit_inv_def TML_Commit_def )
  apply (simp add:  write_wrSet_notEmpty_def  Commit_inv_def TML_Commit_def )
  apply (simp add:  read_rdSet_notEmpty_def  Commit_inv_def TML_Commit_def )
  apply (simp add:  loc_in_wrSet_def  Commit_inv_def TML_Commit_def )
  apply (simp add:  even_loc_wrSet_empty_def  Commit_inv_def TML_Commit_def )
  apply (metis reg_same_st)
  apply (simp add: odd_loc_wrSet_notEmpty_def Commit_inv_def TML_Commit_def )
  by (metis reg_same_st)

(**********************************************)


(*auxiliary lemma*)
lemma   tr_rel_CommitResponding_self_lp:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "  TML_Commit_response  ta cs  cs'  "
and "((pc cs) ta)  = PC.CommitResponding"
and "  Commit_Response_inv   ta  ((pc cs) ta) cs "
and " f_sim cs as "
and"   tr_rel   cs as ta"
and " ta \<noteq> syst"
shows "  tr_rel cs' ( TMCommit_resp_trans  ta  as) ta "
  using assms
  by (simp add: TML_Commit_response_def tr_rel_def Commit_Response_inv_def TMCommit_resp_trans_def  validity_prop_def  split: if_splits )


(*auxiliary lemma*)
lemma   tr_rel_CommitResponding_stable_lp:
assumes  "thrdsvars"
and   "\<forall>t.  tms_inv as  t "
and "total_wfs (\<tau> cs) "
and "((pc cs) ta)  =PC.CommitResponding"
and "  Commit_Response_inv   ta  ((pc cs) ta) cs "
and "   TML_Commit_response   ta cs  cs'  "
and " f_sim cs as "
and"   tr_rel   cs as t"
and " t \<noteq> ta "
and " ta \<noteq> syst"
shows "  tr_rel cs' ( TMCommit_resp_trans  ta  as) t "
  using assms
  apply (simp add: TML_Commit_response_def tr_rel_def  Commit_Response_inv_def  TMCommit_resp_trans_def split: if_splits )
  apply (unfold validity_prop_def  in_flight_def total_wfs_def  )
  apply (cases "pc cs t";  simp)
  apply metis
  apply metis
  apply (metis PC.distinct(1489) fun_upd_def)
  apply (metis PC.distinct(1491) fun_upd_def)
  by (metis PC.distinct(1493) fun_upd_def)



(*auxiliary lemma*)
lemma commit_CommitResponding_logical_glb_ni:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and " TML_Commit_response  ta   cs cs'"
and "((pc cs) ta)  = PC.CommitResponding"
shows " logical_glb cs = logical_glb cs' "
  using assms
  apply (unfold total_wfs_def)
  apply (simp add: TML_Commit_response_def logical_glb_def)
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
  by (smt (z3) PC.distinct(585) PC.distinct(587) fun_upd_def option.simps(5))


(*auxiliary lemma*)
lemma commit_CommitResponding_writes_ni:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and " TML_Commit_response  ta   cs cs'"
and "((pc cs) ta)  =  PC.CommitResponding"
shows " writes cs as = writes  cs'  (TMCommit_resp_trans  ta  as) "
  using assms
  apply (unfold total_wfs_def)
  apply (simp add: TML_Commit_response_def TMCommit_resp_trans_def logical_glb_def writes_def)
  apply (cases "pc cs ta";  simp)
  apply (cases " writer cs" )
  apply simp
  apply (intro conjI impI)
  apply (cases " writer cs'" )
  apply simp+
  apply (cases " writer cs'" )
  by simp+


(*the simulation relation holds for res(Commit)  (non stuttering step)  *)
lemma   f_sim_commit_resp_CommitResponding_lp:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "  TML_Commit_response   ta cs  cs'  "
and "((pc cs) ta)  =  PC.CommitResponding"
and " Commit_Response_inv ta  ((pc cs) ta) cs "
and " f_sim  cs  as"
and   "\<forall>t.  tms_inv as  t "
and"pc cs  syst  = RecIdle "
and " ta \<noteq> syst"
shows "  \<exists> as'. tmstep ta  TMCommitResp  as  as'  \<and> f_sim  cs' as'"
  using assms
  apply (unfold total_wfs_def)
  apply (simp add: TML_Commit_response_def Commit_Response_inv_def tmstep_def read_prop_def  f_sim_def )
  apply (subgoal_tac " memory ( \<tau>  cs) = memory( \<tau> cs' )")
  prefer 2
  apply presburger
  apply (cases "pc cs ta";  simp)
  apply (intro conjI)
  apply (simp add: global_rel_def)
  apply (intro conjI)
  apply (simp add: TMCommit_resp_trans_def  write_count_def)
  apply (metis assms(1) assms(2) assms(3) commit_CommitResponding_logical_glb_ni)
  apply (simp add: maxIndex_def  TMCommit_resp_trans_def  )
  using TMCommit_resp_trans_def assms(1) assms(2) assms(3) commit_CommitResponding_writes_ni apply presburger
  apply (simp add: maxIndex_def  TMCommit_resp_trans_def apply_partial_def )
  apply (simp add: maxIndex_def  TMCommit_resp_trans_def apply_partial_def )
  apply (simp add:  TMCommit_resp_trans_def )
  apply (simp add: no_read_rdSet_empty_def   no_write_wrSet_empty_def write_wrSet_notEmpty_def  read_rdSet_notEmpty_def loc_in_wrSet_def even_loc_wrSet_empty_def odd_loc_wrSet_notEmpty_def )
  apply (subgoal_tac " tpc as ta = TPC.CommitResponding")
  prefer 2
  apply (simp add: tr_rel_def)
  apply (smt (z3) PC.simps(1650))
  apply simp
  apply (intro conjI allI impI)
  apply (metis TMCommit_resp_trans_def assms(1) assms(2) assms(3) assms(5) assms(6) tr_rel_CommitResponding_self_lp)
  apply (metis TMCommit_resp_trans_def assms(1) assms(2) assms(3) assms(5) assms(6) tr_rel_CommitResponding_stable_lp)
  by (simp add:   TMCommit_resp_trans_def)




end
