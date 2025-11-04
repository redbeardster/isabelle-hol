(*Showing that the simulation relation holds on a crash event*)

theory Ref_Crash
imports "../Refinement"
begin


(*auxiliary lemma*)
lemma   tr_rel_crash_t:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "TML_Crash  cs  cs'"
and"   tr_rel   cs as ta"
and    "\<forall>t.  tms_inv as  t "
and " ta \<noteq> syst "
shows " tr_rel cs' (TMCrash_trans   as) ta"
using assms
  apply (simp add:TML_Crash_def tr_rel_def TMCrash_trans_def  total_wfs_def tmstep_def tms_inv_def  split: if_splits )
  apply (cases "pc cs ta";  simp)
  apply (simp add: read_consistent_def)
  by (smt (z3) TPC.simps(133) option.simps(4))


(*auxiliary lemma*)
lemma   tr_rel_crash_syst:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "TML_Crash  cs  cs'"
and"   tr_rel   cs as syst"
and    "\<forall>t.  tms_inv as  t "
shows " tr_rel cs' (TMCrash_trans   as) syst"
  using assms
  by (simp add:TML_Crash_def tr_rel_def TMCrash_trans_def  total_wfs_def tmstep_def tms_inv_def  split: if_splits )


(*the simulation relation holds son TMCrash (non stuttering step) *)
lemma   f_sim_crash_lp:
assumes  "thrdsvars"
and "total_wfs (\<tau> cs) "
and "TML_Crash  cs  cs'"
and "  pm_inv cs  "
and" f_sim  cs as "
and   "\<forall>t.  tms_inv as  t "
shows "\<exists> as'. tmstep t (TMCrash ) as  as'   \<and> f_sim  cs' as'  "
  using assms
  apply (simp add:  TML_Crash_def f_sim_def tms_inv_def  total_wfs_def tmstep_def pm_inv_def  )
  apply (intro conjI allI)
  apply (simp add:  global_rel_def)
  apply (intro conjI allI impI)
  apply (simp add: TMCrash_trans_def maxIndex_def)
  apply (metis domIff lv_ni)
  apply (simp add: TMCrash_trans_def maxIndex_def)
  apply (metis option.distinct(1))
  apply (simp add: TMCrash_trans_def )
  prefer 3
  apply (simp add: write_wrSet_notEmpty_def )
  apply (simp add: no_read_rdSet_empty_def)
  apply (simp add: TMCrash_trans_def)
  apply (simp add: no_write_wrSet_empty_def TMCrash_trans_def)
  apply (simp add: read_rdSet_notEmpty_def  TMCrash_trans_def)
  apply (simp add:  loc_in_wrSet_def  TMCrash_trans_def)
  apply (simp add:  even_loc_wrSet_empty_def  TMCrash_trans_def)
  apply (simp add: odd_loc_wrSet_notEmpty_def   TMCrash_trans_def)
  apply (metis assms(1) assms(2) assms(3) assms(6) tr_rel_crash_syst tr_rel_crash_t)
  apply (unfold read_prop_def)
  using PC.distinct(1503) by presburger




end
