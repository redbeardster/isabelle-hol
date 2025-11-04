(*Complete proof of refinenent between DTML and DTMS2*)

theory Complete_DTML_DTMS2_Refinement_Proof
imports 
"Refinement" "refinement/Ref_Begin"  "refinement/Ref_Commit"   "refinement/Ref_Crash"   "refinement/Ref_Recover"  "refinement/Ref_Read"  "refinement/Ref_Write"
begin 



(*stuttering steps of DTML*)
definition " stuttering_step  \<sigma> \<sigma>' t  \<equiv>
((pc \<sigma>) t)  = PC.BeginPending  \<and> ((pc \<sigma>') t)  = PC.Begin2
| ((pc \<sigma>) t)  = PC.Begin2  \<and> ((pc \<sigma>') t)  = PC.Begin3 
|((pc \<sigma>) t)  = PC.Begin3 \<and> ((pc \<sigma>') t)  = PC.Begin2 

|((pc \<sigma>) t)  = PC.WritePending  \<and> ((pc \<sigma>') t)  = PC.Write1 
|((pc \<sigma>) t)  = PC.Write1  \<and> ((pc \<sigma>') t)  = PC.Write2 
|((pc \<sigma>) t)  = PC.Write1  \<and> ((pc \<sigma>') t)  = PC.Write4 
|((pc \<sigma>) t)  = PC.Write2  \<and> ((pc \<sigma>') t)  = PC.Write3
|((pc \<sigma>) t)  = PC.Write3  \<and> ((pc \<sigma>') t)  = PC.Write4
|((pc \<sigma>) t)  = PC.Write4  \<and> ((pc \<sigma>') t)  = PC.Write5
|((pc \<sigma>) t)  = PC.Write4  \<and> ((pc \<sigma>') t)  = PC.Write7
|((pc \<sigma>) t)  = PC.Write5  \<and> ((pc \<sigma>') t)  = PC.Write6
|((pc \<sigma>) t)  = PC.Write6  \<and> ((pc \<sigma>') t)  = PC.Write7
|((pc \<sigma>) t)  = PC.Write8  \<and> ((pc \<sigma>') t)  = PC.WriteResponding

|((pc \<sigma>) t)  = PC.ReadPending  \<and> ((pc \<sigma>') t)   = PC.Read1
|((pc \<sigma>) t)  = PC.Read1  \<and> ((pc \<sigma>') t)  = PC.Read2
|((pc \<sigma>) t)  = PC.Read2  \<and> ((pc \<sigma>') t)  = PC.Read3
|((pc \<sigma>) t)  = PC.Read2  \<and> ((pc \<sigma>') t)  = PC.Read4
|((pc \<sigma>) t)  = PC.Read4  \<and> ((pc \<sigma>') t)  = PC.Read5 

|((pc \<sigma>) t)  = PC.CommitPending   \<and> ((pc \<sigma>') t)  = PC.Commit2
|((pc \<sigma>) t)  = PC.Commit2   \<and> ((pc \<sigma>') t)  = PC.Commit3
|((pc \<sigma>) t)  = PC.Commit4   \<and> ((pc \<sigma>') t)  = PC.CommitResponding

|((pc \<sigma>) syst)  = PC.ReadyToRecover   \<and> ((pc \<sigma>') syst)  = PC.Rec6
|((pc \<sigma>) syst)  = PC.ReadyToRecover   \<and> ((pc \<sigma>') syst)  = PC.Rec1
|((pc \<sigma>) syst)  = PC.Rec1  \<and> ((pc \<sigma>') syst)  = PC.Rec2
|((pc \<sigma>) syst)  = PC.Rec2  \<and> ((pc \<sigma>') syst)  = PC.Rec3
|((pc \<sigma>) syst)  = PC.Rec3  \<and> ((pc \<sigma>') syst)  = PC.Rec4
|((pc \<sigma>) syst)  = PC.Rec4  \<and> ((pc \<sigma>') syst)  = PC.Rec5
|((pc \<sigma>) syst)  = PC.Rec5  \<and> ((pc \<sigma>') syst)  = PC.Rec6
|((pc \<sigma>) syst)  = PC.Rec6  \<and> ((pc \<sigma>') syst)  = PC.Rec7
|((pc \<sigma>) syst)  = PC.Rec7  \<and> ((pc \<sigma>') syst)  = PC.Rec8
|((pc \<sigma>) syst)  = PC.Rec7  \<and> ((pc \<sigma>') syst)  = PC.Rec9
|((pc \<sigma>) syst)  = PC.Rec8  \<and> ((pc \<sigma>') syst)  = PC.RecIdle
|((pc \<sigma>) syst)  = PC.Rec9  \<and> ((pc \<sigma>') syst)  = PC.RecIdle "

(*non stuttering steps of DTML*)
definition "not_stuttering_step  \<sigma> \<sigma>' t  \<equiv>
((pc \<sigma>) t)  = PC.NotStarted  \<and> ((pc \<sigma>') t)  = PC.BeginPending 
|((pc \<sigma>) t)  = PC.Begin3 \<and> ((pc \<sigma>') t)  = PC.BeginResponding
|((pc \<sigma>) t)  = PC.BeginResponding  \<and> ((pc \<sigma>') t)  = PC.Ready 

|((pc \<sigma>) t)  = PC.Ready \<and> ((pc \<sigma>') t)  = PC.ReadPending
|((pc \<sigma>) t)  = PC.Read3 \<and> ((pc \<sigma>') t)  = PC.ReadResponding
|((pc \<sigma>) t)  = PC.Read5 \<and> ((pc \<sigma>') t)  = PC.ReadResponding
|((pc \<sigma>) t)  = PC.Read3  \<and> ((pc \<sigma>') t)  = PC.Aborted  \<and> ((pc \<sigma>') syst)  = PC.RecIdle
|((pc \<sigma>) t)  = PC.Read5  \<and> ((pc \<sigma>') t)  = PC.Aborted  \<and> ((pc \<sigma>') syst)  = PC.RecIdle

|((pc \<sigma>) t)  = PC.CommitPending \<and> ((pc \<sigma>') t)  = PC.CommitResponding
|((pc \<sigma>) t)  = PC.Commit3 \<and> ((pc \<sigma>') t)  = PC.Commit4
|((pc \<sigma>) t)  = PC.CommitResponding \<and> ((pc \<sigma>') t)  = PC.Committed

|((pc \<sigma>) t)  = PC.Ready \<and> ((pc \<sigma>') t)  = PC.WritePending
|((pc \<sigma>) t)  =  PC.WriteResponding  \<and> ((pc \<sigma>') t)  =PC.Ready
|((pc \<sigma>) t)  = PC.Write7\<and> ((pc \<sigma>') t)  = PC.Write8
"


lemma a:
assumes  "  (  pc cs  syst  = RecIdle \<longrightarrow> (\<forall>t.  (t \<noteq> syst  \<and> ((pc cs) t \<notin> {PC.NotStarted,PC.Aborted, PC.Committed,PC.Begin2   }) \<longrightarrow>   regs (\<tau> cs) t loc \<le> lastVal glb  (\<tau> cs) ))) "
shows "  (pc cs syst = RecIdle \<longrightarrow>
(\<forall>t. t \<noteq> syst \<and> pc cs t \<noteq> PC.NotStarted \<and> pc cs t \<noteq> PC.Aborted \<and> pc cs t \<noteq> PC.Committed \<and> pc cs t \<noteq> Begin2 \<longrightarrow> regs (\<tau> cs) t DTML.loc \<le> lastVal glb (\<tau> cs))) "
using assms
by blast

lemma b:
assumes " (pc cs syst = RecIdle \<longrightarrow>
(\<forall>t. t \<noteq> syst \<and> pc cs t \<noteq> PC.NotStarted \<and> pc cs t \<noteq> PC.Aborted \<and> pc cs t \<noteq> PC.Committed \<and> pc cs t \<noteq> Begin2 \<longrightarrow> regs (\<tau> cs) t DTML.loc \<le> lastVal glb (\<tau> cs)))"
shows " (  pc cs  syst  = RecIdle \<longrightarrow> (\<forall>t.  (t \<noteq> syst  \<and> ((pc cs) t \<notin> {PC.NotStarted,PC.Aborted, PC.Committed,PC.Begin2   }) \<longrightarrow>   regs (\<tau> cs) t loc \<le> lastVal glb  (\<tau> cs) ))) "
using assms
by blast

(*refinement of DTML non stuttering steps*)
lemma   f_sim_not_stuttering_step:
assumes  "thrdsvars"
and "DTML_total_persistent_invariant cs"
and  "  DTML_total_program_annotations t  ((pc cs) t)   cs"
and "not_stuttering_step  cs cs'  t"
and " dTML  cs cs' t"
and " \<forall>t. tms_inv as  t \<and> tmemory as \<noteq> [] "
and" f_sim  cs as "
shows " \<exists> ac as'  . tmstep t ac  as  as'   \<and> f_sim  cs' as'  "
  using assms
  apply (unfold  DTML_total_program_annotations_def)
  apply (simp add: not_stuttering_step_def )
  apply (elim disjE)
               apply (case_tac " t \<noteq> syst ")
                apply (simp add: dTML_def )
                apply (elim disjE conjE)
                      apply (simp add: TML_Begin_def)
                      apply (simp add: TML_Read_def)
                      apply (simp add: TML_Write_def)
                      apply (simp add: TML_Commit_def)
                      apply (rule_tac x="  TMBeginInv" in exI)
  using  DTML_total_persistent_invariant_def assms(1)  f_sim_notStarted_beginPending_lp 
    [where as  = as and cs =cs and cs' =cs' and ta = t ] 
                      apply (smt (verit))
                      apply (simp add: TML_Begin_response_def)
                      apply (simp add: TML_Read_invocation_def)
                     apply (simp add: TML_Read_response_def)
                    apply (simp add: TML_Write_invocation_def)
                   apply (simp add: TML_Write_response_def)
                  apply (simp add: TML_Commit_invocation_def)
                 apply (simp add: TML_Commit_response_def)
                apply (simp add: TML_Crash_def)
               apply (simp add: dTML_def)
               apply (simp add: TML_Recover_def TML_Crash_def)
               apply (metis PC.distinct(1) PC.distinct(153))
    (*****************)
              apply (unfold dTML_def )
              apply (rule_tac x="  TMBegin" in exI)
              apply (elim disjE conjE)
                      apply (case_tac " t \<noteq> syst ")
                      apply (subgoal_tac " pc cs syst = RecIdle")
                      prefer 2
                      apply (simp add: Begin_inv_def)
                      apply (subgoal_tac " thrdsvars \<and>
total_wfs (\<tau> cs)  \<and>
TML_Begin t cs cs'  \<and>
Begin_inv t (pc cs t) cs  \<and>
(  \<forall>t. tms_inv as t)  \<and>
pc cs t = Begin3  \<and>
pc cs' t = PC.BeginResponding  \<and>
f_sim cs as  \<and>
( \<forall>  t.   ((  even (lastVal glb  (\<tau> cs)) \<and> writer cs \<noteq> None) \<longrightarrow> pc cs (the ( writer cs) )   \<noteq> Commit4  )
)
\<and>
tmemory as \<noteq> []  \<and>
pc cs syst = RecIdle  \<and>
( pc cs syst \<noteq> RecIdle \<longrightarrow>
(\<forall>t. t \<noteq> syst \<longrightarrow>
pc cs t
\<in> {PC.NotStarted, PC.Aborted,
PC.Committed}))  \<and>
t \<noteq> syst ")
                      prefer 2
  using  DTML_total_persistent_invariant_def  
                      apply (intro conjI)
  using assms(1) apply blast  
                      apply blast
                      apply blast
                      apply meson
                      apply blast
                      apply meson
                      apply blast
                      apply meson
                      apply (smt (verit))  
                      apply blast
                      apply meson
                      apply blast
                      apply blast
  using  assms(1) DTML_total_persistent_invariant_def   f_sim_begin_begin3_LP [where as  = as and cs =cs and cs' =cs' and ta = t ]
                      apply blast
                      apply meson
                      apply (simp add:   TML_Read_def)
                      apply (simp add:  TML_Write_def)
                      apply (simp add: TML_Commit_def)
                      apply (simp add:  TML_Begin_invocation_def)
                      apply (simp add: TML_Begin_response_def)
                     apply (simp add: TML_Read_invocation_def)
                    apply (simp add: TML_Read_response_def)
                   apply (simp add: TML_Write_invocation_def)
                  apply (simp add: TML_Write_response_def)
                 apply (simp add: TML_Commit_invocation_def)
                apply (simp add: TML_Commit_response_def)
               apply (simp add: TML_Crash_def)
               apply (simp add:  TML_Recover_def)
              apply (simp add: TML_Crash_def)
  using PC.distinct(235) PC.distinct(375) PC.distinct(379) apply presburger
    (***********************)
             apply (rule_tac x="  TMBeginResp" in exI)
             apply (elim disjE conjE)
                      apply (case_tac " t \<noteq> syst ")
                      apply (simp add: TML_Begin_def)
                      apply (simp add: TML_Begin_def)
                      apply (simp add: TML_Read_def)
                      apply (simp add:  TML_Write_def)
                      apply (simp add: TML_Commit_def)
                      apply (simp add:  TML_Begin_invocation_def)
                     apply (subgoal_tac " pc cs syst = RecIdle")
                      prefer 2
                      apply (simp add: Begin_Response_inv_def TML_Begin_response_def)
                      apply (metis fun_upd_other)
  using  DTML_total_persistent_invariant_def assms(1)   f_sim_BeginResponding_lp
    [where as  = as and cs =cs and cs' =cs' and ta = t ] 
                     apply blast
                    apply (simp add: TML_Read_invocation_def)
                   apply (simp add: TML_Read_response_def)
                  apply (simp add: TML_Write_invocation_def)
                 apply (simp add: TML_Write_response_def)
                apply (simp add: TML_Commit_invocation_def)
               apply (simp add: TML_Commit_response_def)
              apply (simp add: TML_Crash_def)
              apply (simp add:  TML_Recover_def)
             apply (simp add: TML_Crash_def)
  using PC.distinct(1635) PC.distinct(1639) PC.distinct(377) apply presburger
    (******************)
            apply (rule_tac x="  TMReadInv" in exI)
            apply (elim disjE conjE)
                      apply (case_tac " t \<noteq> syst ")
                      apply (simp add: TML_Begin_def)
                      apply (simp add: TML_Begin_def)
                      apply (simp add: TML_Read_def)
                      apply (simp add:  TML_Write_def)
                      apply (simp add: TML_Commit_def)
                     apply (simp add:  TML_Begin_invocation_def)
                    apply (simp add:TML_Begin_response_def)
  using  DTML_total_persistent_invariant_def assms(1)   f_sim_read_inv_ready_lp
    [where as  = as and cs =cs and cs' =cs' and ta = t ] 
                   apply (smt (verit) PC.distinct(1639) PC.distinct(767) PC.distinct(77) assms(2) assms(7) insert_iff insert_not_empty insert_subset singleton_insert_inj_eq singleton_insert_inj_eq' subset_singletonD)
                  apply (simp add: TML_Read_response_def)
                 apply (simp add: TML_Write_invocation_def)
                apply (simp add: TML_Write_response_def)
               apply (simp add: TML_Commit_invocation_def)
              apply (simp add: TML_Commit_response_def)
             apply (simp add: TML_Crash_def)
             apply (simp add:  TML_Recover_def)
            apply (simp add: TML_Crash_def)
  using PC.distinct(823) PC.distinct(825) PC.distinct(827) apply presburger
    (***********************)
           apply (rule_tac x="   (TMRead  (inLoc cs t) )  " in exI)
           apply (elim disjE conjE)
                      apply (case_tac " t \<noteq> syst ")
                      apply (simp add: TML_Begin_def)
                      apply (simp add: TML_Begin_def)
                      apply (subgoal_tac " pc cs syst = RecIdle")
                      prefer 2
                      apply (simp add: Read_inv_def TML_Read_def)
                      apply blast
                      apply (simp add:  DTML_total_persistent_invariant_def )
  using  assms(1)
    f_sim_Read3_ReadResponding_LP [where as  = as and cs =cs and cs' =cs' and ta = t ] 
  apply (smt (z3) insertCI insert_commute)
  apply (simp add:  TML_Write_def)
  apply (simp add: TML_Commit_def)
  apply (simp add:  TML_Begin_invocation_def)
  apply (simp add:TML_Begin_response_def)
  apply (simp add: TML_Read_invocation_def)
  apply (simp add: TML_Read_response_def)
  apply (simp add: TML_Write_invocation_def)
  apply (simp add: TML_Write_response_def)
  apply (simp add: TML_Commit_invocation_def)
  apply (simp add: TML_Commit_response_def)
  apply (simp add:  TML_Recover_def)
  apply (simp add: TML_Crash_def)
  using PC.distinct(1129) PC.distinct(1133) PC.distinct(943) apply presburger
    (************)
  apply (rule_tac x="   (TMRead  (inLoc cs t) )  " in exI)
  apply (elim disjE conjE)
  apply (simp add: TML_Begin_def)
  apply (subgoal_tac " pc cs syst = RecIdle")
  prefer 2
  apply (simp add: Read_inv_def TML_Read_def)
  apply blast
  apply (simp add:  DTML_total_persistent_invariant_def )
  using  assms(1)
    f_sim_Read5_ReadResponding_lp [where as  = as and cs =cs and cs' =cs' and ta = t ] 
  apply (smt (z3) insertCI insert_commute)
  apply (simp add:  TML_Write_def)
  apply (simp add: TML_Commit_def)
  apply (simp add:  TML_Begin_invocation_def)
  apply (simp add:TML_Begin_response_def)
  apply (simp add: TML_Read_invocation_def)
  apply (simp add: TML_Read_response_def)
  apply (simp add: TML_Write_invocation_def)
  apply (simp add: TML_Write_response_def)
  apply (simp add: TML_Commit_invocation_def)
  apply (simp add: TML_Commit_response_def)
  apply (simp add:  TML_Recover_def)
  apply (simp add: TML_Crash_def)
  using PC.distinct(1041) PC.distinct(1129) PC.distinct(1133) apply presburger
    (**********************)
  apply (rule_tac x="   TMAbort " in exI)
  apply (elim disjE conjE)
  apply (simp add: TML_Begin_def)
  apply (subgoal_tac " pc cs syst = RecIdle")
  prefer 2
  apply (simp add: Read_inv_def TML_Read_def)
  apply blast
  apply (simp add:  DTML_total_persistent_invariant_def )
  using  assms(1)
    f_sim_read_Read3_abort_lp [where as  = as and cs =cs and cs' =cs' and ta = t ] 
  apply (metis (no_types, lifting) insertCI)
  apply (simp add:  TML_Write_def)
  apply (simp add: TML_Commit_def)
  apply (simp add:  TML_Begin_invocation_def)
  apply (simp add:TML_Begin_response_def)
  apply (simp add: TML_Read_invocation_def)
  apply (simp add: TML_Read_response_def)
  apply (simp add: TML_Write_invocation_def)
  apply (simp add: TML_Write_response_def)
  apply (simp add: TML_Commit_invocation_def)
  apply (simp add: TML_Commit_response_def)
  apply (simp add:  TML_Recover_def)
  apply (simp add: TML_Crash_def)
    (*********************)
  apply (rule_tac x="   TMAbort " in exI)
  apply (elim disjE conjE)
  apply (simp add: TML_Begin_def)
  apply (subgoal_tac " pc cs syst = RecIdle")
  prefer 2
  apply (simp add: Read_inv_def TML_Read_def)
  apply blast
  apply (simp add:  DTML_total_persistent_invariant_def )
  using  assms(1)
    f_sim_read_Read5_aborted_lp [where as  = as and cs =cs and cs' =cs' and ta = t ] 
  apply (smt (verit) insertCI)
  apply (simp add:  TML_Write_def)
  apply (simp add: TML_Commit_def)
  apply (simp add:  TML_Begin_invocation_def)
  apply (simp add:TML_Begin_response_def)
  apply (simp add: TML_Read_invocation_def)
  apply (simp add: TML_Read_response_def)
  apply (simp add: TML_Write_invocation_def)
  apply (simp add: TML_Write_response_def)
  apply (simp add: TML_Commit_invocation_def)
  apply (simp add: TML_Commit_response_def)
  apply (simp add:  TML_Recover_def)
  apply (simp add: TML_Crash_def)
    (**********************)
  apply (rule_tac x="   TMCommit " in exI)
  apply (elim disjE conjE)
  apply (simp add: TML_Begin_def)
  apply (simp add: TML_Read_def)
  apply (simp add:  TML_Write_def)
  apply (simp add: Commit_inv_def)
  apply (simp add:  DTML_total_persistent_invariant_def )
  using   f_sim_commitPending_commitResponding_LP[where as  = as and cs =cs and cs' =cs' and ta = t ]
  apply (smt (z3) DTML_total_program_annotations_def Ready_total_def assms(1) assms(3) insertCI)
  apply (simp add:  TML_Begin_invocation_def)
  apply (simp add:TML_Begin_response_def)
  apply (simp add: TML_Read_invocation_def)
  apply (simp add: TML_Read_response_def)
  apply (simp add: TML_Write_invocation_def)
  apply (simp add: TML_Write_response_def)
  apply (simp add: TML_Commit_invocation_def)
  apply (simp add: TML_Commit_response_def)
  apply (simp add:  TML_Recover_def)
  apply (simp add: TML_Crash_def)                 
  apply (case_tac " t = syst ")
  apply simp
  apply simp
    (*************************************)
  apply (rule_tac x="   TMCommit " in exI)
  apply (elim disjE conjE)
  apply (simp add: TML_Begin_def)
  apply (simp add: TML_Read_def)
  apply (simp add:  TML_Write_def)
  apply (simp add: Commit_inv_def)
  apply (subgoal_tac "
pc cs  syst  = RecIdle \<longrightarrow> (\<forall>t.  (t \<noteq> syst  \<and> ((pc cs) t \<notin> {PC.NotStarted, PC.BeginPending,  PC.Committed,PC.Begin2 ,PC.Aborted  }) \<longrightarrow>   regs (\<tau> cs) t loc \<le> lastVal glb  (\<tau> cs) ))
\<and> (\<forall>t.  (t \<noteq> syst  \<and> ((pc cs) t \<notin> {PC.NotStarted,PC.Aborted, PC.Committed, PC.BeginPending })  \<and> (writeAux cs t \<or> readAux cs t )) \<longrightarrow>  ( regs (\<tau> cs) t loc \<ge>  recoveredGlb cs ))
\<and> ( \<forall>  t.  (   writer cs = Some t \<longrightarrow> odd (lastVal glb  (\<tau> cs)) ))
\<and> ( ( lastVal glb (\<tau> cs)  \<ge>recoveredGlb cs ) )  
\<and> ( pc cs  syst  = RecIdle \<longrightarrow> even (recoveredGlb cs ) )
\<and> ((\<forall>t. ((pc cs) t) \<in> {Commit2, Commit3,Commit4,Write3,Write4, Write5, Write6, Write7,Write8} \<longrightarrow> writer cs  =  Some t ))
\<and> (   (\<forall> n. (0 \<le> n \<and> n  < length (memory (\<tau> cs))  \<and> comploc ((memory (\<tau> cs))!n) glb= glb) \<longrightarrow>  (valOf n glb  (\<tau> cs)) \<le> lastVal glb  (\<tau> cs) ) )
\<and> (\<forall>t. writer cs = Some t \<longrightarrow>
odd (lastVal glb (\<tau> cs))    ) ")
  prefer 2
  using  DTML_total_persistent_invariant_def
  apply (smt (z3) insert_commute)
  using DTML_total_persistent_invariant_def    f_sim_commit3_commit4_LP[where as  = as and cs =cs and cs' =cs' and ta = t ]
  apply (smt (verit) DTML_total_program_annotations_def assms(1) assms(3))
  apply (simp add:  TML_Begin_invocation_def)
  apply (simp add:TML_Begin_response_def)
  apply (simp add: TML_Read_invocation_def)
  apply (simp add: TML_Read_response_def)
  apply (simp add: TML_Write_invocation_def)
  apply (simp add: TML_Write_response_def)
  apply (simp add: TML_Commit_invocation_def)
  apply (simp add: TML_Commit_response_def)
  apply (simp add:  TML_Recover_def)
  apply (simp add: TML_Crash_def)                 
  apply (case_tac " t = syst ")
  apply simp
  apply simp
    (********************)
  apply (rule_tac x="   TMCommitResp " in exI)
  apply (elim disjE conjE)
  apply (simp add: TML_Begin_def)
  apply (simp add: TML_Read_def)
  apply (simp add:  TML_Write_def)
  apply (simp add: TML_Commit_def)
  apply (simp add:  TML_Begin_invocation_def)
  apply (simp add:TML_Begin_response_def)
  apply (simp add: TML_Read_invocation_def)
  apply (simp add: TML_Read_response_def)
  apply (simp add: TML_Write_invocation_def)
  apply (simp add: TML_Write_response_def)
  apply (simp add: TML_Commit_invocation_def)
  apply (subgoal_tac " pc cs syst = RecIdle")
  prefer 2
  apply (simp add: TML_Commit_response_def Commit_Response_inv_def )
  apply (metis fun_upd_def)
  using DTML_total_persistent_invariant_def    f_sim_commit_resp_CommitResponding_lp[where as  = as and cs =cs and cs' =cs' and ta = t ]
  using assms(1) apply blast
  apply (simp add:  TML_Recover_def)
  apply (simp add: TML_Crash_def)  
  using PC.distinct(649) PC.distinct(765) PC.distinct(769) apply presburger
    (***********)
  apply (rule_tac x="  TMWriteInv" in exI)
  apply (elim disjE conjE)
  apply (simp add: TML_Begin_def)
  apply (simp add: TML_Read_def)
  apply (simp add:  TML_Write_def)
  apply (simp add: TML_Commit_def)
  apply (simp add:  TML_Begin_invocation_def)
  apply (simp add:TML_Begin_response_def)
  apply (simp add:  TML_Read_invocation_def)
  apply (simp add: TML_Read_response_def)
  apply (subgoal_tac " pc cs syst = RecIdle")
  prefer 2
  apply (simp add:  TML_Write_invocation_def  Write_invocation_inv_def )
  apply (metis fun_upd_other)
  using  DTML_total_persistent_invariant_def assms(1)  f_sim_write_inv_ready_lp
    [where as  = as and cs =cs and cs' =cs' and ta = t ] 
  apply blast
  apply (simp add: TML_Write_response_def)
  apply (simp add: TML_Commit_invocation_def)
  apply (simp add: TML_Commit_response_def)
  apply (simp add:  TML_Recover_def)
  apply (simp add: TML_Crash_def)              
  using PC.distinct(1173) PC.distinct(1175) PC.distinct(1177) apply presburger
    (*********************)
  apply (rule_tac x="  TMWriteResp" in exI)
  apply (elim disjE conjE)
  apply (simp add: TML_Begin_def)
  apply (simp add: TML_Read_def)
  apply (simp add:  TML_Write_def)
  apply (simp add: TML_Commit_def)
  apply (simp add:  TML_Begin_invocation_def)
  apply (simp add:TML_Begin_response_def)
  apply (simp add: TML_Read_invocation_def)
  apply (simp add: TML_Read_response_def)
  apply (simp add: TML_Write_invocation_def)
  apply (subgoal_tac " pc cs syst = RecIdle")
  prefer 2
  apply (simp add:  TML_Write_response_def  Write_Response_inv_def )
  apply (metis fun_upd_other)
  using   DTML_total_persistent_invariant_def assms(1) 
    f_sim_write_inv_WriteResponding_lp [where as  = as and cs =cs and cs' =cs' and ta = t ] 
  apply blast
  apply (simp add: TML_Commit_invocation_def)
  apply (simp add: TML_Commit_response_def)
  apply (simp add:  TML_Recover_def)
  apply (simp add: TML_Crash_def)              
  using PC.distinct(1481) PC.distinct(1635) PC.distinct(1639) apply presburger
    (***********)
  apply (rule_tac x="  TMWrite   ((inLoc cs) t)  ((inVal cs) t)" in exI)
  apply (elim disjE conjE)
  apply (simp add: TML_Begin_def)
  apply (simp add: TML_Read_def)
  using  f_sim_write_write7_lp Write_inv_def DTML_total_persistent_invariant_def assms(1) 
  apply (smt (verit))
  apply (simp add: TML_Commit_def)
  apply (simp add:  TML_Begin_invocation_def)
  apply (simp add:TML_Begin_response_def)
  apply (simp add:  TML_Read_invocation_def)
  apply (simp add: TML_Read_response_def)
  apply (simp add: TML_Write_invocation_def)
  apply (simp add: TML_Write_response_def)
  apply (simp add: TML_Commit_invocation_def)
  apply (simp add: TML_Commit_response_def)
  apply (simp add: TML_Crash_def)
  apply (simp add:  TML_Recover_def)
  apply (simp add: TML_Crash_def)
  using PC.distinct(1401) PC.distinct(1453) PC.distinct(1457) by presburger


lemma begin_dt:
assumes"  TML_Begin t' \<sigma> \<sigma>'"
and" t \<noteq> t' "
shows  " ((pc \<sigma>') t) = ((pc \<sigma>) t) "
  using assms
  apply (simp add: TML_Begin_def)
  apply (cases "pc \<sigma> t' ";  simp add: split if_splits  )
  using pc_aux 
  by (metis fun_upd_def)

lemma commit_dt:
assumes"  TML_Commit t' \<sigma> \<sigma>'"
and" tb \<noteq> t' "
shows  " ((pc \<sigma>') tb) = ((pc \<sigma>) tb) "
  using assms
  apply (simp add: TML_Commit_def)
  apply (cases "pc \<sigma> t' ";  simp add: split if_splits  )
  using pc_aux 
  by (metis fun_upd_other)

lemma write_dt:
assumes"  TML_Write t' \<sigma> \<sigma>'"
and" tb \<noteq> t' "
shows  "((pc \<sigma>') tb) = ((pc \<sigma>) tb) "
  using assms
  apply (simp add: TML_Write_def)
  apply (cases "pc \<sigma> t' ";  simp add: split if_splits  )
  apply (meson pc_aux)
  apply (metis fun_upd_other gr0I)
  by (metis fun_upd_other)

lemma read_dt:
assumes"  TML_Read t' \<sigma> \<sigma>'"
and" tb \<noteq> t' "
shows  "((pc \<sigma>') tb) = ((pc \<sigma>) tb) "
  using assms
  apply (simp add: TML_Read_def)
  apply (cases "pc \<sigma> t' ";  simp add: split if_splits  )
  apply (meson pc_aux)
  apply (metis fun_upd_other gr0I)
  by (meson pc_aux)

lemma begin_inv_dt:
assumes"   TML_Begin_invocation t' \<sigma> \<sigma>'"
and" tb \<noteq> t' "
shows  "((pc \<sigma>') tb) = ((pc \<sigma>) tb) "
using assms
apply (simp add: TML_Begin_invocation_def)
by (cases "pc \<sigma> t' ";  simp add: split if_splits  )

lemma write_inv_dt:
assumes"   TML_Write_invocation t' \<sigma> \<sigma>'"
and" tb \<noteq> t' "
shows  "((pc \<sigma>') tb) = ((pc \<sigma>) tb) "
  using assms
  apply (simp add: TML_Write_invocation_def)
  by (cases "pc \<sigma> t' ";  simp add: split if_splits  )


lemma read_inv_dt:
assumes"   TML_Read_invocation t' \<sigma> \<sigma>'"
and" tb \<noteq> t' "
shows  "((pc \<sigma>') tb) = ((pc \<sigma>) tb) "
  using assms
  apply (simp add: TML_Read_invocation_def)
  by (cases "pc \<sigma> t' ";  simp add: split if_splits  )

lemma commit_inv_dt:
assumes"   TML_Commit_invocation t' \<sigma> \<sigma>'"
and" tb \<noteq> t' "
shows  "((pc \<sigma>') tb) = ((pc \<sigma>) tb) "
  using assms
  apply (simp add: TML_Commit_invocation_def)
  by (cases "pc \<sigma> t' ";  simp add: split if_splits  )

lemma begin_resp_dt:
assumes"   TML_Begin_response t' \<sigma> \<sigma>'"
and" tb \<noteq> t' "
shows  "((pc \<sigma>') tb) = ((pc \<sigma>) tb) "
  using assms
  apply (simp add: TML_Begin_response_def)
  by (cases "pc \<sigma> t' ";  simp add: split if_splits  )

lemma read_resp_dt:
assumes"   TML_Read_response t' \<sigma> \<sigma>'"
and" tb \<noteq> t' "
shows  "((pc \<sigma>') tb) = ((pc \<sigma>) tb) "
  using assms
  apply (simp add: TML_Read_response_def)
  by (cases "pc \<sigma> t' ";  simp add: split if_splits  )

lemma write_resp_dt:
assumes"   TML_Write_response t' \<sigma> \<sigma>'"
and" tb \<noteq> t' "
shows  "((pc \<sigma>') tb) = ((pc \<sigma>) tb) "
  using assms
  apply (simp add: TML_Write_response_def)
  by (cases "pc \<sigma> t' ";  simp add: split if_splits  )

lemma commit_resp_dt:
assumes"   TML_Commit_response t' \<sigma> \<sigma>'"
and" tb \<noteq> t' "
shows  "((pc \<sigma>') tb) = ((pc \<sigma>) tb) "
  using assms
  apply (simp add: TML_Commit_response_def)
  by (cases "pc \<sigma> t' ";  simp add: split if_splits  )


(*refinement of DTML stuttering steps*)
lemma   f_sim_stuttering_step:
assumes  "thrdsvars"
and "DTML_total_persistent_invariant cs"
and  "  DTML_total_program_annotations t  ((pc cs) t)   cs"
and "stuttering_step  cs cs'  t"
and " dTML  cs cs' t"
and " \<forall>t. tms_inv as  t \<and> tmemory as \<noteq> [] "
and" f_sim  cs as "
shows "f_sim  cs' as "
  using assms
  apply (unfold   DTML_total_program_annotations_def)
  apply (case_tac " t \<noteq> syst")
   apply (simp add:  stuttering_step_def )
   apply (elim disjE)
  apply (simp add: dTML_def)
  apply (elim disjE conjE)
  apply (simp add:  DTML_total_persistent_invariant_def)
  apply (metis assms(1) f_sim_begin_BeginPending)
  apply (simp add: TML_Read_def)
  apply (simp add: TML_Write_def)
  apply (simp add: TML_Commit_def)
  apply (simp add:  TML_Begin_invocation_def)
  apply (simp add:TML_Begin_response_def)
  apply (simp add:  TML_Read_invocation_def)
  apply (simp add: TML_Read_response_def)
  apply (simp add: TML_Write_invocation_def)
  apply (simp add: TML_Write_response_def)
  apply (simp add: TML_Commit_invocation_def)
  apply (simp add: TML_Commit_response_def)
  apply (simp add: TML_Crash_def)
  apply (simp add:  TML_Recover_def)
(************************)
  apply (simp add: dTML_def)
  apply (elim disjE conjE)
  apply (simp add:  DTML_total_persistent_invariant_def)
  apply (metis assms(1) f_sim_begin_Begin2)
  apply (simp add: TML_Read_def)
  apply (simp add: TML_Write_def)
  apply (simp add: TML_Commit_def)
  apply (simp add:  TML_Begin_invocation_def)
  apply (simp add:TML_Begin_response_def)
  apply (simp add:  TML_Read_invocation_def)
  apply (simp add: TML_Read_response_def)
  apply (simp add: TML_Write_invocation_def)
  apply (simp add: TML_Write_response_def)
  apply (simp add: TML_Commit_invocation_def)
  apply (simp add: TML_Commit_response_def)
  apply (simp add: TML_Crash_def)
  apply (simp add:  TML_Recover_def)
(**********************)
  apply (simp add: dTML_def)
  apply (elim disjE conjE)
  apply (simp add:  DTML_total_persistent_invariant_def)
  apply (smt (verit) PC.distinct(247) PC.distinct(307) PC.distinct(5) assms(1) f_sim_begin_begin3_ST)
apply (simp add: TML_Read_def)
  apply (simp add: TML_Write_def)
  apply (simp add: TML_Commit_def)
  apply (simp add:  TML_Begin_invocation_def)
  apply (simp add:TML_Begin_response_def)
  apply (simp add:  TML_Read_invocation_def)
  apply (simp add: TML_Read_response_def)
  apply (simp add: TML_Write_invocation_def)
  apply (simp add: TML_Write_response_def)
  apply (simp add: TML_Commit_invocation_def)
  apply (simp add: TML_Commit_response_def)
  apply (simp add: TML_Crash_def)
  apply (simp add:  TML_Recover_def)
    (************************)
  apply (simp add: dTML_def)
  apply (elim disjE conjE)
  apply (simp add:  DTML_total_persistent_invariant_def)
  apply (simp add: TML_Begin_def)
  apply (simp add: TML_Read_def)
  apply (subgoal_tac "  pc cs syst = RecIdle")
  prefer 2
  apply (simp add: Write_inv_def TML_Write_def  Ready_total_def)
  apply blast
  using  f_sim_write_WritePending DTML_total_persistent_invariant_def
  apply (smt (verit) assms(1))
  apply (simp add: TML_Commit_def)
  apply (simp add:  TML_Begin_invocation_def)
  apply (simp add:TML_Begin_response_def)
  apply (simp add:  TML_Read_invocation_def)
  apply (simp add: TML_Read_response_def)
  apply (simp add: TML_Write_invocation_def)
  apply (simp add: TML_Write_response_def)
  apply (simp add: TML_Commit_invocation_def)
  apply (simp add: TML_Commit_response_def)
  apply (simp add: TML_Crash_def)
  apply (simp add:  TML_Recover_def)
    (****************)
  apply (simp add: dTML_def)
  apply (elim disjE conjE)
  apply (simp add:  DTML_total_persistent_invariant_def)
  apply (simp add: TML_Begin_def)
  apply (simp add: TML_Read_def)
  apply (subgoal_tac "  pc cs syst = RecIdle")
  prefer 2
  apply (simp add: Write_inv_def TML_Write_def  Ready_total_def)
  apply blast
  using  DTML_total_persistent_invariant_def  f_sim_write_write1
  apply (smt (verit) assms(1))
  apply (simp add: TML_Commit_def)
  apply (simp add:  TML_Begin_invocation_def)
  apply (simp add:TML_Begin_response_def)
  apply (simp add:  TML_Read_invocation_def)
  apply (simp add: TML_Read_response_def)
  apply (simp add: TML_Write_invocation_def)
  apply (simp add: TML_Write_response_def)
  apply (simp add: TML_Commit_invocation_def)
  apply (simp add: TML_Commit_response_def)
  apply (simp add: TML_Crash_def)
  apply (simp add:  TML_Recover_def)
    (*******************)
  apply (simp add: dTML_def)
  apply (elim disjE conjE)
  apply (simp add:  DTML_total_persistent_invariant_def)
  apply (simp add: TML_Begin_def)
  apply (simp add: TML_Read_def)
  apply (subgoal_tac "  pc cs syst = RecIdle")
  prefer 2
  apply (simp add: Write_inv_def TML_Write_def  Ready_total_def)
  apply blast
  using  DTML_total_persistent_invariant_def  f_sim_write_write1
  apply (smt (verit) assms(1))
  apply (simp add: TML_Commit_def)
  apply (simp add:  TML_Begin_invocation_def)
  apply (simp add:TML_Begin_response_def)
  apply (simp add:  TML_Read_invocation_def)
  apply (simp add: TML_Read_response_def)
  apply (simp add: TML_Write_invocation_def)
  apply (simp add: TML_Write_response_def)
  apply (simp add: TML_Commit_invocation_def)
  apply (simp add: TML_Commit_response_def)
  apply (simp add: TML_Crash_def)
  apply (simp add:  TML_Recover_def)
    (*******************)
  apply (simp add: dTML_def)
  apply (elim disjE conjE)
  apply (simp add:  DTML_total_persistent_invariant_def)
  apply (simp add: TML_Begin_def)
  apply (simp add: TML_Read_def)
  apply (subgoal_tac "  pc cs syst = RecIdle")
  prefer 2
  apply (simp add: Write_inv_def TML_Write_def  Ready_total_def)
  apply (simp add:  DTML_total_persistent_invariant_def)
  using  f_sim_write_write2_write3_stuttering [where ta = t and cs = cs and as = as and cs' = cs' ] 
  apply (smt (verit) assms(1) insertCI)
  apply (simp add: TML_Commit_def)
  apply (simp add:  TML_Begin_invocation_def)
  apply (simp add:TML_Begin_response_def)
  apply (simp add:  TML_Read_invocation_def)
  apply (simp add: TML_Read_response_def)
  apply (simp add: TML_Write_invocation_def)
  apply (simp add: TML_Write_response_def)
  apply (simp add: TML_Commit_invocation_def)
  apply (simp add: TML_Commit_response_def)
  apply (simp add: TML_Crash_def)
  apply (simp add:  TML_Recover_def)
    (*******************)
  apply (simp add: dTML_def)
  apply (elim disjE conjE)
  apply (simp add: TML_Begin_def)
  apply (simp add:  TML_Read_def)  
  apply (simp add:  DTML_total_persistent_invariant_def)
  using  f_sim_write_write3 [where ta = t and cs = cs and as = as and cs' = cs' ] 
  apply (smt (verit) PC.distinct(1297) PC.distinct(41) PC.distinct(731) assms(1))
  apply (simp add: TML_Commit_def)
  apply (simp add:  TML_Begin_invocation_def)
  apply (simp add:TML_Begin_response_def)
  apply (simp add:  TML_Read_invocation_def)
  apply (simp add: TML_Read_response_def)
  apply (simp add: TML_Write_invocation_def)
  apply (simp add: TML_Write_response_def)
  apply (simp add: TML_Commit_invocation_def)
  apply (simp add: TML_Commit_response_def)
  apply (simp add: TML_Crash_def)
  apply (simp add:  TML_Recover_def)
    (*******************)
  apply (simp add: dTML_def)
  apply (elim disjE conjE)
  apply (simp add: TML_Begin_def)
  apply (simp add:  TML_Read_def)  
  apply (simp add:  DTML_total_persistent_invariant_def)
  using  f_sim_write_write5 [where ta = t and cs = cs and as = as and cs' = cs' ] 
  apply (smt (verit) assms(1) f_sim_write_write4)
  apply (simp add: TML_Commit_def)
  apply (simp add:  TML_Begin_invocation_def)
  apply (simp add:TML_Begin_response_def)
  apply (simp add:  TML_Read_invocation_def)
  apply (simp add: TML_Read_response_def)
  apply (simp add: TML_Write_invocation_def)
  apply (simp add: TML_Write_response_def)
  apply (simp add: TML_Commit_invocation_def)
  apply (simp add: TML_Commit_response_def)
  apply (simp add: TML_Crash_def)
  apply (simp add:  TML_Recover_def)
    (*****************************)
  apply (simp add: dTML_def)
  apply (elim disjE conjE)
  apply (simp add: TML_Begin_def)
  apply (simp add:  TML_Read_def)  
  apply (simp add:  DTML_total_persistent_invariant_def)
  apply (smt (verit) assms(1) f_sim_write_write4)
  apply (simp add: TML_Commit_def)
  apply (simp add:  TML_Begin_invocation_def)
  apply (simp add:TML_Begin_response_def)
  apply (simp add:  TML_Read_invocation_def)
  apply (simp add: TML_Read_response_def)
  apply (simp add: TML_Write_invocation_def)
  apply (simp add: TML_Write_response_def)
  apply (simp add: TML_Commit_invocation_def)
  apply (simp add: TML_Commit_response_def)
  apply (simp add: TML_Crash_def)
  apply (simp add:  TML_Recover_def)
    (**********************)
  apply (simp add: dTML_def)
  apply (elim disjE conjE)
  apply (simp add: TML_Begin_def)
  apply (simp add:  TML_Read_def)  
  apply (simp add:  DTML_total_persistent_invariant_def)
  apply (smt (verit) \<open>\<And>aa. \<lbrakk>thrdsvars; total_wfs (\<tau> cs); TML_Write t cs cs'; Write_inv t (pc cs t) cs; pc cs t = Write5; aa \<noteq> glb; pc cs syst = RecIdle \<longrightarrow> even (recoveredGlb cs); \<forall>t. writer cs = Some t \<longrightarrow> odd (lastVal glb (\<tau> cs)); pc cs syst = RecIdle \<longrightarrow> recoveredGlb cs \<le> lastVal glb (\<tau> cs); f_sim cs as; t \<noteq> syst\<rbrakk> \<Longrightarrow> f_sim cs' as\<close> assms(1))
  apply (simp add: TML_Commit_def)
  apply (simp add:  TML_Begin_invocation_def)
  apply (simp add:TML_Begin_response_def)
  apply (simp add:  TML_Read_invocation_def)
  apply (simp add: TML_Read_response_def)
  apply (simp add: TML_Write_invocation_def)
  apply (simp add: TML_Write_response_def)
  apply (simp add: TML_Commit_invocation_def)
  apply (simp add: TML_Commit_response_def)
  apply (simp add: TML_Crash_def)
  apply (simp add:  TML_Recover_def)
    (**********************)
  apply (simp add: dTML_def)
  apply (elim disjE conjE)
  apply (simp add: TML_Begin_def)
  apply (simp add:  TML_Read_def)  
  apply (simp add:  DTML_total_persistent_invariant_def)
  apply (smt (verit) assms(1) f_sim_write_write6)
  apply (simp add: TML_Commit_def)
  apply (simp add:  TML_Begin_invocation_def)
  apply (simp add:TML_Begin_response_def)
  apply (simp add:  TML_Read_invocation_def)
  apply (simp add: TML_Read_response_def)
  apply (simp add: TML_Write_invocation_def)
  apply (simp add: TML_Write_response_def)
  apply (simp add: TML_Commit_invocation_def)
  apply (simp add: TML_Commit_response_def)
  apply (simp add: TML_Crash_def)
  apply (simp add:  TML_Recover_def)
    (**********************)
  apply (simp add: dTML_def)
  apply (elim disjE conjE)
  apply (simp add: TML_Begin_def)
  apply (simp add:  TML_Read_def)  
  apply (simp add:  DTML_total_persistent_invariant_def)
  apply (smt (verit) assms(1) f_sim_write_write8)
  apply (simp add: TML_Commit_def)
  apply (simp add:  TML_Begin_invocation_def)
  apply (simp add:TML_Begin_response_def)
  apply (simp add:  TML_Read_invocation_def)
  apply (simp add: TML_Read_response_def)
  apply (simp add: TML_Write_invocation_def)
  apply (simp add: TML_Write_response_def)
  apply (simp add: TML_Commit_invocation_def)
  apply (simp add: TML_Commit_response_def)
  apply (simp add: TML_Crash_def)
  apply (simp add:  TML_Recover_def)
    (**********)
  apply (simp add: dTML_def)
  apply (elim disjE conjE)
  apply (simp add: TML_Begin_def)
  apply (simp add:  DTML_total_persistent_invariant_def)
  using  f_sim_read_ready_stuttering
  apply (metis PC.distinct(21) PC.distinct(711) PC.distinct(827) assms(1))
  apply (simp add:  TML_Write_def)
  apply (simp add: TML_Commit_def)
  apply (simp add:  TML_Begin_invocation_def)
  apply (simp add:TML_Begin_response_def)
  apply (simp add:  TML_Read_invocation_def)
  apply (simp add: TML_Read_response_def)
  apply (simp add: TML_Write_invocation_def)
  apply (simp add: TML_Write_response_def)
  apply (simp add: TML_Commit_invocation_def)
  apply (simp add: TML_Commit_response_def)
  apply (simp add: TML_Crash_def)
  apply (simp add:  TML_Recover_def)

(*************************)
  apply (simp add: dTML_def)
  apply (elim disjE conjE)
  apply (simp add: TML_Begin_def)
  apply (simp add:  DTML_total_persistent_invariant_def)
  apply (metis PC.distinct(23) PC.distinct(713) PC.distinct(883) assms(1) f_sim_read_read1_stuttering)
  apply (simp add:  TML_Write_def)
  apply (simp add: TML_Commit_def)
  apply (simp add:  TML_Begin_invocation_def)
  apply (simp add:TML_Begin_response_def)
  apply (simp add:  TML_Read_invocation_def)
  apply (simp add: TML_Read_response_def)
  apply (simp add: TML_Write_invocation_def)
  apply (simp add: TML_Write_response_def)
  apply (simp add: TML_Commit_invocation_def)
  apply (simp add: TML_Commit_response_def)
  apply (simp add: TML_Crash_def)
  apply (simp add:  TML_Recover_def)
    (***************)
  apply (simp add: dTML_def)
  apply (elim disjE conjE)
  apply (simp add: TML_Begin_def)
  apply (simp add:  DTML_total_persistent_invariant_def)
  apply (metis PC.distinct(25) PC.distinct(715) PC.distinct(937) assms(1) f_sim_read_Read2_stuttering)
  apply (simp add:  TML_Write_def)
  apply (simp add: TML_Commit_def)
  apply (simp add:  TML_Begin_invocation_def)
  apply (simp add:TML_Begin_response_def)
  apply (simp add:  TML_Read_invocation_def)
  apply (simp add: TML_Read_response_def)
  apply (simp add: TML_Write_invocation_def)
  apply (simp add: TML_Write_response_def)
  apply (simp add: TML_Commit_invocation_def)
  apply (simp add: TML_Commit_response_def)
  apply (simp add: TML_Crash_def)
  apply (simp add:  TML_Recover_def)
    (***************)
  apply (simp add: dTML_def)
  apply (elim disjE conjE)
  apply (simp add: TML_Begin_def)
  apply (simp add:  DTML_total_persistent_invariant_def)
  apply (metis PC.distinct(25) PC.distinct(715) PC.distinct(937) assms(1) f_sim_read_Read2_stuttering)
  apply (simp add:  TML_Write_def)
  apply (simp add: TML_Commit_def)
  apply (simp add:  TML_Begin_invocation_def)
  apply (simp add:TML_Begin_response_def)
  apply (simp add:  TML_Read_invocation_def)
  apply (simp add: TML_Read_response_def)
  apply (simp add: TML_Write_invocation_def)
  apply (simp add: TML_Write_response_def)
  apply (simp add: TML_Commit_invocation_def)
  apply (simp add: TML_Commit_response_def)
  apply (simp add: TML_Crash_def)
  apply (simp add:  TML_Recover_def)
    (***************)
  apply (simp add: dTML_def)
  apply (elim disjE conjE)
  apply (simp add: TML_Begin_def)
  apply (simp add:  DTML_total_persistent_invariant_def)
  apply (metis assms(1) f_sim_read_Read4_stuttering)
  apply (simp add:  TML_Write_def)
  apply (simp add: TML_Commit_def)
  apply (simp add:  TML_Begin_invocation_def)
  apply (simp add:TML_Begin_response_def)
  apply (simp add:  TML_Read_invocation_def)
  apply (simp add: TML_Read_response_def)
  apply (simp add: TML_Write_invocation_def)
  apply (simp add: TML_Write_response_def)
  apply (simp add: TML_Commit_invocation_def)
  apply (simp add: TML_Commit_response_def)
  apply (simp add: TML_Crash_def)
  apply (simp add:  TML_Recover_def)
    (***************)
  apply (simp add: dTML_def)
  apply (elim disjE conjE)
  apply (simp add: TML_Begin_def)
  apply (simp add:  TML_Read_def)
  apply (simp add:  TML_Write_def)
  apply (simp add:  DTML_total_persistent_invariant_def)
  apply (metis PC.distinct(389) PC.distinct(449) PC.distinct(9) assms(1) f_sim_commit_commitPending_commit2)
  apply (simp add:  TML_Begin_invocation_def)
  apply (simp add:TML_Begin_response_def)
  apply (simp add:  TML_Read_invocation_def)
  apply (simp add: TML_Read_response_def)
  apply (simp add: TML_Write_invocation_def)
  apply (simp add: TML_Write_response_def)
  apply (simp add: TML_Commit_invocation_def)
  apply (simp add: TML_Commit_response_def)
  apply (simp add: TML_Crash_def)
  apply (simp add:  TML_Recover_def)
    (***************)
  apply (simp add: dTML_def)
  apply (elim disjE conjE)
  apply (simp add: TML_Begin_def)
  apply (simp add:  TML_Read_def)
  apply (simp add:  TML_Write_def)
  apply (simp add:  DTML_total_persistent_invariant_def)
  apply (metis PC.distinct(11) PC.distinct(457) PC.distinct(517) assms(1) f_sim_commit_commit2_commit3)
  apply (simp add:  TML_Begin_invocation_def)
  apply (simp add:TML_Begin_response_def)
  apply (simp add:  TML_Read_invocation_def)
  apply (simp add: TML_Read_response_def)
  apply (simp add: TML_Write_invocation_def)
  apply (simp add: TML_Write_response_def)
  apply (simp add: TML_Commit_invocation_def)
  apply (simp add: TML_Commit_response_def)
  apply (simp add: TML_Crash_def)
  apply (simp add:  TML_Recover_def)
    (***************)
  apply (simp add: dTML_def)
  apply (elim disjE conjE)
  apply (simp add: TML_Begin_def)
  apply (simp add:  TML_Read_def)
  apply (simp add:  TML_Write_def)
  apply (simp add:  DTML_total_persistent_invariant_def)
  using  f_sim_commit4_commitResponding[where cs=cs and as=as and cs'=cs' and ta = t]
  apply (smt (verit) DTML_total_persistent_invariant_def assms(1) assms(2) insert_commute)
  apply (simp add:  TML_Begin_invocation_def)
  apply (simp add:TML_Begin_response_def)
  apply (simp add:  TML_Read_invocation_def)
  apply (simp add: TML_Read_response_def)
  apply (simp add: TML_Write_invocation_def)
  apply (simp add: TML_Write_response_def)
  apply (simp add: TML_Commit_invocation_def)
  apply (simp add: TML_Commit_response_def)
  apply (simp add: TML_Crash_def)
    (*********************)
  apply (simp add: dTML_def)
  using pc_aux TML_Crash_def  
  apply (smt (verit) PC.distinct(1605) begin_dt read_inv_dt begin_inv_dt begin_resp_dt commit_dt commit_inv_dt commit_resp_dt read_dt read_resp_dt write_dt write_inv_dt write_resp_dt)
    (*********************)
  apply (simp add: dTML_def)
  using pc_aux TML_Crash_def  
  apply (smt (verit, del_insts) PC.distinct(1525) begin_dt read_inv_dt begin_inv_dt begin_resp_dt commit_dt commit_inv_dt commit_resp_dt read_dt read_resp_dt write_dt write_inv_dt write_resp_dt)
    (*********************)
  apply (simp add: dTML_def)
  using pc_aux TML_Crash_def  
  apply (smt (verit, del_insts) PC.distinct(1509) PC.distinct(1545) begin_dt read_inv_dt begin_inv_dt begin_resp_dt commit_dt commit_inv_dt commit_resp_dt read_dt read_resp_dt write_dt write_inv_dt write_resp_dt)
    (*********************)
  apply (simp add: dTML_def)
  using pc_aux TML_Crash_def  
  apply (smt (verit, del_insts) PC.distinct(1531) PC.distinct(1563) begin_dt read_inv_dt begin_inv_dt begin_resp_dt commit_dt commit_inv_dt commit_resp_dt read_dt read_resp_dt write_dt write_inv_dt write_resp_dt)
    (*********************)
  apply (simp add: dTML_def)
  using pc_aux TML_Crash_def  
  apply (smt (verit) PC.distinct(1551) PC.distinct(1579)begin_dt read_inv_dt begin_inv_dt begin_resp_dt commit_dt commit_inv_dt commit_resp_dt read_dt read_resp_dt write_dt write_inv_dt write_resp_dt)
    (*********************)
  apply (simp add: dTML_def)
  using pc_aux TML_Crash_def  
  apply (smt (verit) PC.distinct(1569) PC.distinct(1593)begin_dt read_inv_dt begin_inv_dt begin_resp_dt commit_dt commit_inv_dt commit_resp_dt read_dt read_resp_dt write_dt write_inv_dt write_resp_dt)
    (*********************)
  apply (simp add: dTML_def)
  using pc_aux TML_Crash_def  
  apply (smt (verit) PC.distinct(1585) PC.distinct(1605)  begin_dt  read_inv_dt begin_inv_dt begin_resp_dt commit_dt commit_inv_dt commit_resp_dt read_dt read_resp_dt write_dt write_inv_dt write_resp_dt)
    (*********************)
  apply (simp add: dTML_def)
  using pc_aux TML_Crash_def  
  apply (smt (verit) PC.distinct(1599) PC.distinct(1615) begin_dt read_inv_dt begin_inv_dt begin_resp_dt commit_dt commit_inv_dt commit_resp_dt read_dt read_resp_dt write_dt write_inv_dt write_resp_dt)
    (*********************)
  apply (simp add: dTML_def)
  using pc_aux TML_Crash_def  
  apply (smt (verit) PC.distinct(1611) PC.distinct(1623) begin_dt read_inv_dt begin_inv_dt begin_resp_dt commit_dt commit_inv_dt commit_resp_dt read_dt read_resp_dt write_dt write_inv_dt write_resp_dt)
    (*********************)
  apply (simp add: dTML_def)
  using pc_aux TML_Crash_def  
  apply (smt (verit) PC.distinct(1613) PC.distinct(1629) begin_dt read_inv_dt begin_inv_dt begin_resp_dt commit_dt commit_inv_dt commit_resp_dt read_dt read_resp_dt write_dt write_inv_dt write_resp_dt)
    (*********************)
  apply (simp add: dTML_def)
  using pc_aux TML_Crash_def  
  apply (smt (verit) PC.distinct(1499) PC.distinct(1503) begin_dt read_inv_dt begin_inv_dt begin_resp_dt commit_dt commit_inv_dt commit_resp_dt read_dt read_resp_dt write_dt write_inv_dt write_resp_dt)
    (*********************)
  apply (simp add: dTML_def)
  using pc_aux TML_Crash_def  
  apply (smt (verit) PC.distinct(1501) PC.distinct(1503) begin_dt read_inv_dt begin_inv_dt begin_resp_dt commit_dt commit_inv_dt commit_resp_dt read_dt read_resp_dt write_dt write_inv_dt write_resp_dt)
    (*********************)
  apply (simp add: dTML_def)
  apply (elim disjE)
  apply(simp add: stuttering_step_def)
  apply (case_tac "   ((pc cs) syst) \<notin> {RecIdle } \<union> recovering" )
  apply (smt (z3) recover_not_pc)
  apply simp
  apply (subgoal_tac "  ((pc cs) syst) \<noteq> RecIdle   \<longrightarrow> (\<forall> t  \<noteq> syst.  ((pc cs) t)   \<in> {PC.NotStarted, PC.Aborted, PC.Committed})")
  prefer 2
  apply (simp add:  DTML_total_persistent_invariant_def)
  apply (case_tac "pc cs syst = ReadyToRecover")
  apply (subgoal_tac "   thrdsvars \<and>
total_wfs (\<tau> cs) \<and>
Recover_inv syst (pc cs syst) cs \<and>
TML_Recover syst cs cs' \<and>
pc cs syst = ReadyToRecover \<and>
(  \<forall>t. tms_inv as t) \<and>
( pc cs syst \<noteq> RecIdle \<longrightarrow>
(\<forall>t. t \<noteq> syst \<longrightarrow>
pc cs t \<in> {PC.NotStarted, PC.Aborted, PC.Committed}))  ")
  prefer 2
  apply (simp add:  DTML_total_persistent_invariant_def)
  using assms(1)  f_sim_recover_readyToRec [where cs =cs and as = as and cs' = cs'] 
  apply fastforce
  apply (case_tac "pc cs syst = Rec1")
  apply (simp add:  DTML_total_persistent_invariant_def)
  using  f_sim_recover_Rec1[where cs=cs and as = as and cs' = cs' ]
  apply (metis assms(1) insertCI)
  apply (case_tac "pc cs syst = Rec2")
  apply (simp add:  DTML_total_persistent_invariant_def)
  using  f_sim_recover_Rec2[where cs=cs and as = as and cs' = cs' ]
  apply (smt(verit) PC.distinct(1487) assms(1) compval_def insertI1 insertI2)
  apply (case_tac "pc cs syst = Rec3")
  apply (simp add:  DTML_total_persistent_invariant_def)
  using DTML_total_persistent_invariant_def   f_sim_recover_Rec3[where cs=cs and as = as and cs' = cs' ]
  apply (smt (verit) assms(1) assms(2))
  apply (case_tac "pc cs syst = Rec4")
  using  DTML_total_persistent_invariant_def   f_sim_recover_Rec4[where cs=cs and as = as and cs' = cs' ]
  apply (smt (z3) assms(1) assms(2))
  apply (case_tac "pc cs syst = Rec5")
  using  DTML_total_persistent_invariant_def  f_sim_recover_Rec5[where cs=cs and as = as and cs' = cs' ]
  apply (smt (verit) assms(1))
  apply (case_tac "pc cs syst = Rec6")
  using  DTML_total_persistent_invariant_def  f_sim_recover_Rec6[where cs=cs and as = as and cs' = cs' ]
  apply (smt (verit) assms(1))
  apply (case_tac "pc cs syst = Rec7")
  using  DTML_total_persistent_invariant_def   f_sim_recover_Rec7[where cs=cs and as = as and cs' = cs' ]
  apply (smt (verit) assms(1))
  apply (case_tac "pc cs syst = Rec8")
  apply (simp add:  DTML_total_persistent_invariant_def)
  using DTML_total_persistent_invariant_def   f_sim_recover_Rec8[where cs=cs and as = as and cs' = cs' ]
  apply (smt (verit) assms(1) assms(2))
  apply (case_tac "pc cs syst = Rec9")
  apply (simp add:  DTML_total_persistent_invariant_def)
  using  DTML_total_persistent_invariant_def  f_sim_recover_Rec9[where cs=cs and as = as and cs' = cs' ]
  apply (smt (verit) assms(1) assms(2))
  apply force
  apply(simp add: TML_Crash_def)
  by (simp add: stuttering_step_def)





end

