theory Recover_Global
imports "../../DTML"
begin

(*Recover annotation is stable against the DTML read operation*)
lemma Read_Recover_global:
assumes "thrdsvars"
and "total_wfs (\<tau> \<sigma>)"
and "pm_inv \<sigma> "
and  " ((pc \<sigma>) syst) \<noteq> RecIdle   \<longrightarrow> (\<forall> t  \<noteq> syst.  ((pc \<sigma>) t)   \<in> {NotStarted, Aborted, Committed})"(*persistent invariant*)
and "  Read_inv  ta   ((pc \<sigma>) ta)  \<sigma>  "
and " Recover_inv   syst  ((pc \<sigma>) syst) \<sigma>  "
and " TML_Read  ta    \<sigma> \<sigma>'"
and "((pc \<sigma>) ta) \<in> {ReadPending, ReadResponding} \<union>  reading \<union> {Aborted} "
and "((pc \<sigma>) syst) \<in> {RecIdle } \<union> recovering" 
and " ta \<noteq> syst"
shows  "  Recover_inv  syst  ((pc \<sigma>') syst) \<sigma>'  " 
  using assms
  apply (unfold thrdsvars_def )
  apply (simp add:TML_Read_def Read_inv_def Recover_inv_def   )
  apply (cases" pc  \<sigma> ta"; simp ; cases "(pc \<sigma>) syst"; simp )
  apply (metis PC.distinct(13) PC.distinct(355) PC.distinct(455))
  apply (metis PC.distinct(13) PC.distinct(355) PC.distinct(455))
  apply (metis PC.distinct(23) PC.distinct(713) PC.distinct(883))
  apply (metis PC.distinct(23) PC.distinct(713) PC.distinct(883))
  apply (metis PC.distinct(23) PC.distinct(713) PC.distinct(883))
  apply (metis PC.distinct(23) PC.distinct(713) PC.distinct(883))
  apply (metis PC.distinct(23) PC.distinct(713) PC.distinct(883))
  apply (metis PC.distinct(23) PC.distinct(713) PC.distinct(883))
  apply (metis PC.distinct(23) PC.distinct(713) PC.distinct(883))
  apply (metis PC.distinct(23) PC.distinct(713) PC.distinct(883))
  apply (metis PC.distinct(23) PC.distinct(713) PC.distinct(883))
  apply (metis PC.distinct(23) PC.distinct(713) PC.distinct(883))
  apply (simp split:if_splits )
  apply (simp split:if_splits )
  apply (simp split:if_splits )
  apply metis
  apply metis
  apply metis
  by metis


(*Read annotation is stable against the DTML recover operation*)
lemma Recover_Read_global:
assumes "thrdsvars"
and "total_wfs (\<tau> \<sigma>)"
and " TML_Recover syst   \<sigma> \<sigma>' "
and  " ((pc \<sigma>) syst) \<noteq> RecIdle   \<longrightarrow> (\<forall> t  \<noteq> syst.  ((pc \<sigma>) t)   \<in> {NotStarted, Aborted, Committed})"(*persistent invariant*)
and "  Read_inv  ta    ((pc \<sigma>) ta)  \<sigma>   "
and "((pc \<sigma>)syst) \<in> {RecIdle} \<union> recovering "
and "((pc \<sigma>)ta) \<in> {Aborted,ReadPending, ReadResponding} \<union> reading "
and " ta \<noteq> syst"
shows "  Read_inv ta   ((pc \<sigma>') ta)  \<sigma>'  "
  using assms
  apply(simp add:TML_Recover_def Recover_inv_def Read_inv_def    )
  apply (cases" pc  \<sigma> syst"; simp ; cases "(pc \<sigma>) ta"; simp )
  apply (unfold Ready_total_def  read_pre_def)
  apply simp+
  apply (simp add: split: if_splits)
  apply simp+
  by (simp split:if_splits )



(*Recover annotation is stable against the DTML begin operation*)
lemma Begin_Recover_global:
assumes "thrdsvars"
and "total_wfs (\<tau> \<sigma>)"
and " Recover_inv   syst  ((pc \<sigma>) syst) \<sigma>  "
and"TML_Begin ta  \<sigma> \<sigma>'"
and  " Begin_inv  ta  ((pc \<sigma>') ta) \<sigma>'  "
and  " ((pc \<sigma>) syst) \<noteq> RecIdle   \<longrightarrow> (\<forall> t  \<noteq> syst.  ((pc \<sigma>) t)   \<in> {NotStarted, Aborted, Committed})"(*persistent invariant*)
and "((pc \<sigma>) ta) \<in> {Aborted,BeginPending, BeginResponding} \<union>  beginning"
and "((pc \<sigma>) syst) \<in> {RecIdle } \<union> recovering" 
and " ta \<noteq> syst"
shows  "  Recover_inv  syst  ((pc \<sigma>') syst) \<sigma>'  " 
  using assms
  apply (unfold thrdsvars_def )
  apply (simp add:TML_Begin_def Begin_inv_def Recover_inv_def)
  apply (cases" pc  \<sigma> syst"; simp ; cases "(pc \<sigma>) ta"; simp )
  apply (simp split:if_splits )
  apply (simp split:if_splits )
  apply (simp split:if_splits )
  apply (simp split:if_splits )
  apply (simp split:if_splits )
  apply (simp split:if_splits )
  apply (simp split:if_splits )
  apply (simp split:if_splits )
  apply (simp split:if_splits )
  apply metis
  apply metis
  apply (simp split:if_splits )
  apply metis
  apply metis
  by (simp split:if_splits )





(*Begin annotation is stable against the DTML recover operation*)
lemma Recover_Begin_global:
assumes "thrdsvars"
and "total_wfs (\<tau> \<sigma>)"
and " TML_Recover syst   \<sigma> \<sigma>' "
and "  Begin_inv  ta    ((pc \<sigma>) ta)  \<sigma>   "
and "((pc \<sigma>)syst) \<in> {RecIdle} \<union> recovering "
and "((pc \<sigma>)ta) \<in> {Aborted,BeginPending, BeginResponding} \<union> beginning "
and  " ((pc \<sigma>) syst) \<noteq> RecIdle   \<longrightarrow> (\<forall> t  \<noteq> syst.  ((pc \<sigma>) t)   \<in> {NotStarted, Aborted, Committed})"(*persistent invariant*)
and " ta \<noteq> syst"
shows "  Begin_inv ta   ((pc \<sigma>') ta)  \<sigma>'  "
  using assms
  apply(simp add:TML_Recover_def Recover_inv_def Begin_inv_def    )
  apply (cases" pc  \<sigma> syst"; simp ; cases "(pc \<sigma>) ta"; simp )
  using reg_coh_ni reg_vrnew_ni apply presburger
  apply (metis PC.distinct(319) PC.distinct(379) PC.distinct(7))
  apply (metis reg_coh_dt_ni st_vrnew_dt_ni)
  apply (metis PC.distinct(319) PC.distinct(379) PC.distinct(7))
  apply (metis flo_coh_ni flo_vrnew_ni)
  apply (metis PC.distinct(319) PC.distinct(379) PC.distinct(7))
  apply (metis sf_coh_ni sf_vrnew_dt_ni)
  apply (simp add: Ready_total_def)
  apply (metis PC.distinct(319) PC.distinct(379) PC.distinct(7))
  apply (metis ld_coh_dt_ni ld_vrnew_dt_ni)
  apply (metis PC.distinct(319) PC.distinct(379) PC.distinct(7))
  apply (metis PC.distinct(1) PC.distinct(157) PC.distinct(97))
  apply (metis PC.distinct(319) PC.distinct(379) PC.distinct(7))
  apply (case_tac " even (regs (\<tau> \<sigma>) syst c1)")
  apply simp
  apply simp
  apply (metis PC.distinct(1) PC.distinct(157) PC.distinct(97))
  apply (metis PC.distinct(319) PC.distinct(379) PC.distinct(7))
  apply (metis reg_coh_dt_ni st_vrnew_dt_ni)
  apply (metis PC.distinct(319) PC.distinct(379) PC.distinct(7))
  apply (simp split:if_splits )
  apply (simp split:if_splits )
  apply (metis PC.distinct(319) PC.distinct(379) PC.distinct(7))
  apply (metis PC.distinct(319) PC.distinct(379) PC.distinct(7))
  by (simp split:if_splits )



(*Write annotation is stable against the  DTML recover operation*)
lemma Recover_Write_global:
assumes "thrdsvars"
and "total_wfs (\<tau> \<sigma>)"
and " TML_Recover syst   \<sigma> \<sigma>' "
and  "  Write_inv  ta   ((pc \<sigma>) ta) \<sigma>  "
and " Recover_inv   syst  ((pc \<sigma>) syst) \<sigma>  "
and "((pc \<sigma>)syst) \<in> {RecIdle} \<union> recovering "
and "((pc \<sigma>)ta) \<in> {Aborted,WritePending, WriteResponding } \<union> writing "
and  " ((pc \<sigma>) syst) \<noteq> RecIdle   \<longrightarrow> (\<forall> t  \<noteq> syst.  ((pc \<sigma>) t)   \<in> {NotStarted, Aborted, Committed})" (*persistent invariant*)
and " ta \<noteq> syst"
shows  "  Write_inv  ta   ((pc \<sigma>') ta) \<sigma>'  "
  using assms
  apply(simp add:TML_Recover_def Recover_inv_def Write_inv_def    )
  apply (cases" pc  \<sigma> syst"; simp ; cases "(pc \<sigma>) ta"; simp )
  apply force
  apply fastforce
  apply metis
  apply auto[1]
  apply metis
  apply (metis PC.distinct(1177) PC.distinct(35) PC.distinct(725))
  apply (simp add: Ready_total_def)+
  apply (simp split:if_splits )
  apply (simp add: Ready_total_def)
  apply (simp add: Ready_total_def)
  apply (simp add: Ready_total_def)
  apply (simp add: Ready_total_def)
  apply (simp add: Ready_total_def)
  apply (simp add: Ready_total_def)
  apply(simp split:if_splits )
  apply (metis PC.distinct(1177) PC.distinct(35) PC.distinct(725))
  apply (metis PC.distinct(1177) PC.distinct(35) PC.distinct(725))
  apply (simp add: Ready_total_def)+
  by (simp split:if_splits )

(*Recover annotation is stable against the DTML write operation*)
lemma Write_Recover_global:
assumes "thrdsvars"
and "total_wfs (\<tau> \<sigma>)"
and "pm_inv \<sigma> "
and  " \<forall>  t.  (   writer \<sigma> = Some t \<longrightarrow> odd (lastVal glb  (\<tau> \<sigma>)) )"
and " \<forall>  t. (  (   writer \<sigma>  = Some t    \<longrightarrow> \<lceil>glb\<rceil>\<^sub>t (\<tau> \<sigma>) ))"
and  " ((pc \<sigma>) syst) \<noteq> RecIdle   \<longrightarrow> (\<forall> t  \<noteq> syst.  ((pc \<sigma>) t)   \<in> {NotStarted, Aborted, Committed})" (*persistent invariant*)
and "glb_monotone_inv (\<tau> \<sigma>) " (*persistent invariant*)
and " Recover_inv   syst  ((pc \<sigma>) syst) \<sigma>  "
and  "  Write_inv  ta ((pc \<sigma>) ta) \<sigma>  "
and "TML_Write  ta    \<sigma> \<sigma>'"
and "((pc \<sigma>) ta) \<in> {WritePending, WriteResponding} \<union>  writing \<union> {Aborted} "
and "((pc \<sigma>) syst) \<in> {RecIdle } \<union> recovering" 
and " ta \<noteq> syst"
shows  "Recover_inv  syst  ((pc \<sigma>') syst) \<sigma>'  " 
  using assms
  apply(simp add:TML_Write_def Recover_inv_def  Write_inv_def  )
  apply (cases" pc  \<sigma> syst"; simp ; cases "(pc \<sigma>) ta"; simp )
  apply(simp add: split: if_splits)
  apply(simp add: split: if_splits)+
  apply metis
  apply (simp add: Ready_total_def)
  apply metis
  apply metis
  apply (simp add: Ready_total_def)+
  apply metis
  by(simp add: split: if_splits)


(* inv(Commit) annotation is stable against the DTML recover operation*)
lemma Recover_Commit_global:
assumes "thrdsvars"
and "total_wfs (\<tau> \<sigma>)"
and " TML_Recover syst   \<sigma> \<sigma>' "
and "  Commit_inv  ta    ((pc \<sigma>) ta)  \<sigma>   "
and " Recover_inv   syst  ((pc \<sigma>) syst) \<sigma>  "
and "((pc \<sigma>)syst) \<in> {RecIdle} \<union> recovering "
and "((pc \<sigma>)ta) \<in> { CommitPending, CommitResponding ,Aborted} \<union> committing "
and  " ((pc \<sigma>) syst) \<noteq> RecIdle   \<longrightarrow> (\<forall> t  \<noteq> syst.  ((pc \<sigma>) t)   \<in> {NotStarted, Aborted, Committed})" (*persistent invariant*)
and " ta \<noteq> syst"
shows "   Commit_inv  ta    ((pc \<sigma>') ta)  \<sigma>'  "
  using assms
  apply(simp add:TML_Recover_def Recover_inv_def Commit_inv_def    )
  apply (cases" pc  \<sigma> syst"; simp ; cases "(pc \<sigma>) ta"; simp )
  apply metis
  apply auto[1]
  apply metis
  apply (metis PC.distinct(389) PC.distinct(449) PC.distinct(9))
  apply (metis PC.distinct(389) PC.distinct(449) PC.distinct(9))
  apply (metis PC.distinct(389) PC.distinct(449) PC.distinct(9))
  apply (metis PC.distinct(389) PC.distinct(449) PC.distinct(9))
  apply (metis PC.distinct(389) PC.distinct(449) PC.distinct(9))
  apply (metis PC.distinct(389) PC.distinct(449) PC.distinct(9))
  apply (metis PC.distinct(389) PC.distinct(449) PC.distinct(9))
  apply(simp add: split: if_splits)
  apply(simp add: split: if_splits)
  apply (metis PC.distinct(389) PC.distinct(449) PC.distinct(9))
  apply (metis PC.distinct(389) PC.distinct(449) PC.distinct(9))
  apply (metis PC.distinct(389) PC.distinct(449) PC.distinct(9))
  apply(simp add: split: if_splits)
  by(simp add: split: if_splits)



(*DTML recover annotation  is stable against the  inv(Commit) annotation*)
lemma Commit_Recover_global:
assumes "thrdsvars"
and "total_wfs (\<tau> \<sigma>)"
and  " \<forall>  t.  (   writer \<sigma> = Some t \<longrightarrow> odd (lastVal glb  (\<tau> \<sigma>)) )"(*persistent invariant*)
and " \<forall>  t. (  (   writer \<sigma>  = Some t    \<longrightarrow> \<lceil>glb\<rceil>\<^sub>t (\<tau> \<sigma>) ))" (*persistent invariant*)
and " Recover_inv   syst  ((pc \<sigma>) syst) \<sigma>  "
and  "  Commit_inv  ta  ((pc \<sigma>) ta) \<sigma>  "
and "TML_Commit  ta   \<sigma> \<sigma>'"
and "((pc \<sigma>) ta) \<in> { CommitPending, CommitResponding } \<union>  committing  \<union> {Aborted} "
and "((pc \<sigma>) syst) \<in> {RecIdle } \<union> recovering" 
and " ta \<noteq> syst"
shows  "  Recover_inv  syst  ((pc \<sigma>') syst) \<sigma>'  " 
  using assms
  apply (unfold thrdsvars_def)
  apply(simp add:TML_Commit_def Recover_inv_def  Commit_inv_def  Ready_total_def )
  apply (cases" pc  \<sigma> syst"; simp ; cases "(pc \<sigma>) ta"; simp )
  apply(simp add: split: if_splits)
  apply (simp add: Ready_total_def)
  apply (simp add: Ready_total_def)
  apply (simp add: Ready_total_def)
  apply (simp add: Ready_total_def)
  apply (simp add: Ready_total_def)
  apply (simp add: Ready_total_def)
  apply (simp add: Ready_total_def)
  apply(simp add: split: if_splits)
  apply metis
  apply metis
  apply (simp add: Ready_total_def)
  apply metis
  apply metis
  by (simp add: Ready_total_def)


(*DTML recover annotation is stable against the inv(Commit) operation*)
lemma Recover_Crash_global:
assumes "thrdsvars"
and "total_wfs (\<tau> \<sigma>)"
and "   Recover_inv syst   ((pc \<sigma>) syst) \<sigma> "
and "  (\<forall>a. a \<in> dom (log \<sigma>) \<longrightarrow> a \<noteq> glb) "
and " TML_Crash  \<sigma> \<sigma>'"
shows " Recover_inv syst   ((pc \<sigma>') syst) \<sigma>'" 
  using assms
  apply (subgoal_tac " length (memory (\<tau> \<sigma>')) = 1 ")
  prefer 2
  apply (simp add: TML_Crash_def crash_step_def crash_trans_def)
  apply (simp add:Recover_inv_def TML_Crash_def  total_wfs_def )
  apply(cases "pc \<sigma> syst"; simp  )
  by (metis gr0I ov_lv_lc)+


(*inv(Begin) annotation is stable against the DTML recover operation*)
lemma Recover_Begin_invocation_global:
assumes"total_wfs (\<tau> \<sigma>) "
and  "Begin_invocation_inv ta  ((pc \<sigma>) ta) \<sigma>"
and "   Recover_inv syst   ((pc \<sigma>) syst) \<sigma> "
and " TML_Recover syst   \<sigma> \<sigma>' "
and "((pc \<sigma>)syst) \<in> {RecIdle} \<union> recovering "
and "((pc \<sigma>)ta) \<in> {NotStarted, BeginPending ,Aborted} "
and  " ((pc \<sigma>) syst) \<noteq> RecIdle   \<longrightarrow> (\<forall> t  \<noteq> syst.  ((pc \<sigma>) t)   \<in> {NotStarted, Aborted, Committed})" (*persistent invariant*)
shows "Begin_invocation_inv ta  ((pc \<sigma>') ta) \<sigma>'" 
  using assms
  apply(simp add: Begin_invocation_inv_def  TML_Recover_def  Recover_inv_def )
  apply (cases" pc  \<sigma> syst"; simp ; cases "(pc \<sigma>) ta"; simp )
  using reg_coh_ni reg_vrnew_ni apply presburger
  apply (metis PC.distinct(1) PC.distinct(157) PC.distinct(97))
  apply (metis reg_coh_dt_ni st_vrnew_dt_ni)
  apply (metis PC.distinct(1) PC.distinct(157) PC.distinct(97))
  apply (metis flo_coh_ni flo_vrnew_ni)
  apply (metis flo_coh_ni flo_vrnew_ni)
  apply (metis sf_coh_ni sf_vrnew_dt_ni)
  apply (metis PC.distinct(1) PC.distinct(157) PC.distinct(97))
  apply (metis ld_coh_dt_ni ld_vrnew_dt_ni)
  apply (metis PC.distinct(1) PC.distinct(157) PC.distinct(97))
  apply(simp add: split: if_splits)+
  apply (metis reg_coh_dt_ni st_vrnew_dt_ni)
  apply (metis PC.distinct(1) PC.distinct(157) PC.distinct(97))
  apply (metis reg_coh_dt_ni st_vrnew_dt_ni)
  apply (metis PC.distinct(1) PC.distinct(157) PC.distinct(97))
  by(simp add: split: if_splits)+

(*DTML recover operation  is stable against the inv(Begin) annotation*)
lemma Begin_invocation_Recover_global:
assumes "thrdsvars"
and "  Recover_inv syst   ((pc \<sigma>) syst)  \<sigma>  "
and "Begin_invocation_inv ta  ((pc \<sigma>) ta) \<sigma>" 
and " TML_Begin_invocation  ta   \<sigma> \<sigma>'"
and "total_wfs (\<tau> \<sigma>) "
and "((pc \<sigma>) ta) \<in> {BeginPending, NotStarted} \<union> {Aborted} "
and "((pc \<sigma>) syst) \<in> {RecIdle } \<union> recovering" 
and  " ((pc \<sigma>) syst) \<noteq> RecIdle   \<longrightarrow> (\<forall> t  \<noteq> syst.  ((pc \<sigma>) t)   \<in> {NotStarted, Aborted, Committed})" (*persistent invariant*)
shows "  Recover_inv syst   ((pc \<sigma>') syst)  \<sigma>' " 
  using assms
  apply(simp add:Begin_invocation_inv_def Recover_inv_def total_wfs_def TML_Begin_invocation_def  )
  apply (cases" pc  \<sigma> syst"; simp ; cases "(pc \<sigma>) ta"; simp )
  by metis+



(*res(Begin) annotation is stable against the DTML recover operation*)
lemma Recover_Begin_response_global:
assumes"total_wfs (\<tau> \<sigma>) "
and  "Begin_Response_inv ta  ((pc \<sigma>) ta) \<sigma>"
and "   Recover_inv syst   ((pc \<sigma>) syst) \<sigma> "
and " TML_Recover syst   \<sigma> \<sigma>' "
and "((pc \<sigma>)syst) \<in> {RecIdle} \<union> recovering "
and "((pc \<sigma>)ta) \<in> { BeginResponding ,Ready, Aborted} "
and  " ((pc \<sigma>) syst) \<noteq> RecIdle   \<longrightarrow> (\<forall> t  \<noteq> syst.  ((pc \<sigma>) t)   \<in> {NotStarted, Aborted, Committed})" (*persistent invariant*)
shows "Begin_Response_inv ta  ((pc \<sigma>') ta) \<sigma>'" 
  using assms
  apply(simp add: Begin_Response_inv_def  TML_Recover_def  Recover_inv_def )
  apply (cases" pc  \<sigma> syst"; simp ; cases "(pc \<sigma>) ta"; simp )
  apply (metis PC.distinct(319) PC.distinct(379) PC.distinct(7))
  apply (metis PC.distinct(1639) PC.distinct(767) PC.distinct(77))
  apply (metis PC.distinct(319) PC.distinct(379) PC.distinct(7))
  apply (metis PC.distinct(1639) PC.distinct(767) PC.distinct(77))
  apply (metis PC.distinct(319) PC.distinct(379) PC.distinct(7))
  apply (metis PC.distinct(1639) PC.distinct(767) PC.distinct(77))
  apply (metis PC.distinct(319) PC.distinct(379) PC.distinct(7))
  apply (metis PC.distinct(1639) PC.distinct(767) PC.distinct(77))
  apply (metis PC.distinct(319) PC.distinct(379) PC.distinct(7))
  apply (metis PC.distinct(1639) PC.distinct(767) PC.distinct(77))
  apply (metis PC.distinct(319) PC.distinct(379) PC.distinct(7))
  apply (metis PC.distinct(1639) PC.distinct(767) PC.distinct(77))
  apply(simp add: split: if_splits)+
  apply (metis PC.distinct(319) PC.distinct(379) PC.distinct(7))
  apply (metis PC.distinct(319) PC.distinct(379) PC.distinct(7))
  apply(simp add: split: if_splits)
  apply (metis PC.distinct(1639) PC.distinct(767) PC.distinct(77))
  apply (metis PC.distinct(1639) PC.distinct(767) PC.distinct(77))
  apply(simp add: split: if_splits)
  apply (metis PC.distinct(319) PC.distinct(379) PC.distinct(7))
  apply (metis PC.distinct(1639) PC.distinct(767) PC.distinct(77))
  apply (metis PC.distinct(319) PC.distinct(379) PC.distinct(7))
  apply (metis PC.distinct(1639) PC.distinct(767) PC.distinct(77))
  apply(simp add: split: if_splits)
  apply (metis PC.distinct(319) PC.distinct(379) PC.distinct(7))
  apply (metis PC.distinct(319) PC.distinct(379) PC.distinct(7))
  apply(simp add: split: if_splits)
  apply (metis PC.distinct(1639) PC.distinct(767) PC.distinct(77))
  apply (metis PC.distinct(1639) PC.distinct(767) PC.distinct(77))
  by(simp add: split: if_splits)

(*DTML recover operation is stable against the res(Begin) annotation*)
lemma Begin_response_Recover_global:
assumes "thrdsvars"
and "  Recover_inv syst   ((pc \<sigma>) syst)  \<sigma>  "
and "Begin_Response_inv ta  ((pc \<sigma>) ta) \<sigma>" 
and " TML_Begin_response  ta   \<sigma> \<sigma>'"
and "total_wfs (\<tau> \<sigma>) "
and "((pc \<sigma>) ta) \<in> {BeginResponding,Ready} \<union> {Aborted} "
and "((pc \<sigma>) syst) \<in> {RecIdle } \<union> recovering" 
and  " ((pc \<sigma>) syst) \<noteq> RecIdle   \<longrightarrow> (\<forall> t  \<noteq> syst.  ((pc \<sigma>) t)   \<in> {NotStarted, Aborted, Committed})" (*persistent invariant*)
shows "  Recover_inv syst   ((pc \<sigma>') syst)  \<sigma>' " 
  using assms
  apply(simp add:Begin_Response_inv_def Recover_inv_def total_wfs_def TML_Begin_response_def  )
  apply (cases" pc  \<sigma> syst"; simp ; cases "(pc \<sigma>) ta"; simp )
  by metis+

(*********************************)

(*inv(Read) annotation is stable against the DTML recover operation*)
lemma Recover_Read_invocation_global:
assumes"total_wfs (\<tau> \<sigma>) "
and  "Read_invocation_inv ta  ((pc \<sigma>) ta) \<sigma>"
and "   Recover_inv syst   ((pc \<sigma>) syst) \<sigma> "
and " TML_Recover syst   \<sigma> \<sigma>' "
and "((pc \<sigma>)syst) \<in> {RecIdle} \<union> recovering "
and "((pc \<sigma>)ta) \<in> {Ready, ReadPending ,Aborted} "
and  " ((pc \<sigma>) syst) \<noteq> RecIdle   \<longrightarrow> (\<forall> t  \<noteq> syst.  ((pc \<sigma>) t)   \<in> {NotStarted, Aborted, Committed})" (*persistent invariant*)
shows "Read_invocation_inv ta  ((pc \<sigma>') ta) \<sigma>'" 
  using assms
  apply(simp add: Read_invocation_inv_def  TML_Recover_def  Recover_inv_def )
  apply (cases" pc  \<sigma> syst"; simp ; cases "(pc \<sigma>) ta"; simp )
  apply (metis PC.distinct(21) PC.distinct(711) PC.distinct(827))
  apply (metis PC.distinct(1639) PC.distinct(767) PC.distinct(77))
  apply (metis PC.distinct(21) PC.distinct(711) PC.distinct(827))
  apply (metis PC.distinct(1639) PC.distinct(767) PC.distinct(77))
  apply (metis PC.distinct(21) PC.distinct(711) PC.distinct(827))
  apply (metis PC.distinct(1639) PC.distinct(767) PC.distinct(77))
  apply (metis PC.distinct(21) PC.distinct(711) PC.distinct(827))
  apply (metis PC.distinct(1639) PC.distinct(767) PC.distinct(77))
  apply (metis PC.distinct(21) PC.distinct(711) PC.distinct(827))
  apply (metis PC.distinct(1639) PC.distinct(767) PC.distinct(77))
  apply (metis PC.distinct(21) PC.distinct(711) PC.distinct(827))
  apply (metis PC.distinct(1639) PC.distinct(767) PC.distinct(77)) 
  apply (metis PC.distinct(21) PC.distinct(711) PC.distinct(817) PC.distinct(827))
  apply (metis PC.distinct(1617) PC.distinct(1639) PC.distinct(767) PC.distinct(77))
  apply (metis PC.distinct(1619) PC.simps(1681) pc_aux)
  apply (metis PC.distinct(21) PC.distinct(711) PC.distinct(827))
  apply (metis PC.distinct(1639) PC.distinct(767) PC.distinct(77))
  apply (metis PC.distinct(21) PC.distinct(711) PC.distinct(827))
  apply (metis PC.distinct(1639) PC.distinct(767) PC.distinct(77))
  apply (metis PC.distinct(21) PC.distinct(711) PC.distinct(823) PC.distinct(827))
  apply (metis PC.distinct(1635) PC.distinct(1639) PC.distinct(767) PC.distinct(77))
  by (metis PC.distinct(1637) PC.simps(1681) pc_aux)


(*DTML recover operation  is stable against the inv(Read) annotation*)
lemma Read_invocation_Recover_global:
assumes "thrdsvars"
and "  Recover_inv syst   ((pc \<sigma>) syst)  \<sigma>  "
and "Read_invocation_inv ta  ((pc \<sigma>) ta) \<sigma>" 
and " TML_Read_invocation  ta   \<sigma> \<sigma>'"
and "total_wfs (\<tau> \<sigma>) "
and "((pc \<sigma>) ta) \<in> {ReadPending,Ready} \<union> {Aborted} "
and "((pc \<sigma>) syst) \<in> {RecIdle } \<union> recovering" 
and  " ((pc \<sigma>) syst) \<noteq> RecIdle   \<longrightarrow> (\<forall> t  \<noteq> syst.  ((pc \<sigma>) t)   \<in> {NotStarted, Aborted, Committed})" (*persistent invariant*)
shows "  Recover_inv syst   ((pc \<sigma>') syst)  \<sigma>' " 
  using assms
  apply(simp add:Read_invocation_inv_def Recover_inv_def total_wfs_def TML_Read_invocation_def  )
  apply (cases" pc  \<sigma> syst"; simp ; cases "(pc \<sigma>) ta"; simp )
  by metis+



(*res(Read) annotation is stable against the DTML recover operation*)
lemma Recover_Read_response_global:
assumes"total_wfs (\<tau> \<sigma>) "
and  "Read_Response_inv ta  ((pc \<sigma>) ta) \<sigma>"
and "   Recover_inv syst   ((pc \<sigma>) syst) \<sigma> "
and " TML_Recover syst   \<sigma> \<sigma>' "
and "((pc \<sigma>)syst) \<in> {RecIdle} \<union> recovering "
and "((pc \<sigma>)ta) \<in> { ReadResponding ,Ready, Aborted} "
and  " ((pc \<sigma>) syst) \<noteq> RecIdle   \<longrightarrow> (\<forall> t  \<noteq> syst.  ((pc \<sigma>) t)   \<in> {NotStarted, Aborted, Committed})" (*persistent invariant*)
and " ta \<noteq> syst"
shows "Read_Response_inv ta  ((pc \<sigma>') ta) \<sigma>'" 
  using assms
  apply(simp add: Read_Response_inv_def  TML_Recover_def  Recover_inv_def )
  apply (cases" pc  \<sigma> syst"; simp ; cases "(pc \<sigma>) ta"; simp )
  apply (metis PC.distinct(1111) PC.distinct(1133) PC.distinct(33) PC.distinct(723))
  apply (metis PC.distinct(1527) PC.distinct(1639) PC.distinct(767) PC.distinct(77))
  apply (metis PC.distinct(1133) PC.distinct(33) PC.distinct(723))
  apply (metis PC.distinct(1639) PC.distinct(767) PC.distinct(77))
  apply (metis PC.distinct(1133) PC.distinct(33) PC.distinct(723))
  apply (metis PC.distinct(1639) PC.distinct(767) PC.distinct(77))
  apply (metis PC.distinct(1133) PC.distinct(33) PC.distinct(723))
  apply (metis PC.distinct(1639) PC.distinct(767) PC.distinct(77))
  apply (metis PC.distinct(1133) PC.distinct(33) PC.distinct(723))
  apply (metis PC.distinct(1639) PC.distinct(767) PC.distinct(77))
  apply (metis PC.distinct(1133) PC.distinct(33) PC.distinct(723))
  apply (metis PC.distinct(1639) PC.distinct(767) PC.distinct(77))
  apply (metis PC.distinct(1133) PC.distinct(33) PC.distinct(723))
  apply (metis PC.distinct(1639) PC.distinct(767) PC.distinct(77))
  apply (metis PC.distinct(1619) PC.simps(1681) pc_aux)
  apply (metis PC.distinct(1133) PC.distinct(33) PC.distinct(723))
  apply (metis PC.distinct(1639) PC.distinct(767) PC.distinct(77))
  apply (metis PC.distinct(1133) PC.distinct(33) PC.distinct(723))
  apply (metis PC.distinct(1639) PC.distinct(767) PC.distinct(77))
  apply(simp add: split: if_splits)+
  apply (metis PC.distinct(1133) PC.distinct(33) PC.distinct(723))
  apply (metis PC.distinct(1133) PC.distinct(33) PC.distinct(723))
  apply (metis PC.distinct(1639) PC.distinct(767) PC.distinct(77))
  by(metis PC.distinct(1619) PC.simps(1681) pc_aux)


(*DTML recover annotation is stable against the res(Read) operation*)
lemma Read_response_Recover_global:
assumes "thrdsvars"
and "  Recover_inv syst   ((pc \<sigma>) syst)  \<sigma>  "
and "Read_Response_inv ta  ((pc \<sigma>) ta) \<sigma>" 
and " TML_Read_response  ta   \<sigma> \<sigma>'"
and "total_wfs (\<tau> \<sigma>) "
and "((pc \<sigma>) ta) \<in> {ReadResponding,Ready} \<union> {Aborted} "
and "((pc \<sigma>) syst) \<in> {RecIdle } \<union> recovering" 
and  " ((pc \<sigma>) syst) \<noteq> RecIdle   \<longrightarrow> (\<forall> t  \<noteq> syst.  ((pc \<sigma>) t)   \<in> {NotStarted, Aborted, Committed})" (*persistent invariant*)
shows "  Recover_inv syst   ((pc \<sigma>') syst)  \<sigma>' " 
  using assms
  apply(simp add:Read_Response_inv_def Recover_inv_def total_wfs_def TML_Read_response_def  )
  apply (cases" pc  \<sigma> syst"; simp ; cases "(pc \<sigma>) ta"; simp )
  by metis+

(*****************************************************)


(*inv(Write) annotation is stable against the DTML recover operation*)
lemma Recover_Write_invocation_global:
assumes"total_wfs (\<tau> \<sigma>) "
and  "Write_invocation_inv ta  ((pc \<sigma>) ta) \<sigma>"
and "   Recover_inv syst   ((pc \<sigma>) syst) \<sigma> "
and " TML_Recover syst   \<sigma> \<sigma>' "
and "((pc \<sigma>)syst) \<in> {RecIdle} \<union> recovering "
and "((pc \<sigma>)ta) \<in> {Ready, WritePending ,Aborted} "
and  " ((pc \<sigma>) syst) \<noteq> RecIdle   \<longrightarrow> (\<forall> t  \<noteq> syst.  ((pc \<sigma>) t)   \<in> {NotStarted, Aborted, Committed})" (*persistent invariant*)
shows "Write_invocation_inv ta  ((pc \<sigma>') ta) \<sigma>'" 
  using assms
  apply(simp add: Write_invocation_inv_def  TML_Recover_def  Recover_inv_def )
  apply (cases" pc  \<sigma> syst"; simp ; cases "(pc \<sigma>) ta"; simp )
  apply (metis PC.distinct(1177) PC.distinct(35) PC.distinct(725))
  apply (metis PC.distinct(1639) PC.distinct(767) PC.distinct(77))
  apply (metis PC.distinct(1177) PC.distinct(35) PC.distinct(725))
  apply (metis PC.distinct(1639) PC.distinct(767) PC.distinct(77))
  apply (metis PC.distinct(1177) PC.distinct(35) PC.distinct(725))
  apply (metis PC.distinct(1639) PC.distinct(767) PC.distinct(77))
  apply (metis PC.distinct(1177) PC.distinct(35) PC.distinct(725))
  apply (metis PC.distinct(1639) PC.distinct(767) PC.distinct(77))
  apply (metis PC.distinct(1177) PC.distinct(35) PC.distinct(725))
  apply (metis PC.distinct(1639) PC.distinct(767) PC.distinct(77))
  apply (metis PC.distinct(1177) PC.distinct(35) PC.distinct(725))
  apply (metis PC.distinct(1639) PC.distinct(767) PC.distinct(77))
  apply (metis PC.distinct(1167) PC.distinct(1177) PC.distinct(35) PC.distinct(725))
  apply (metis PC.distinct(1617) PC.distinct(1639) PC.distinct(767) PC.distinct(77))
  apply (metis PC.distinct(1619) PC.simps(1681) pc_aux)
  apply (metis PC.distinct(1177) PC.distinct(35) PC.distinct(725))
  apply (metis PC.distinct(1639) PC.distinct(767) PC.distinct(77))
  apply (metis PC.distinct(1177) PC.distinct(35) PC.distinct(725))
  apply (metis PC.distinct(1639) PC.distinct(767) PC.distinct(77))
  apply (metis PC.distinct(1173) PC.distinct(1177) PC.distinct(35) PC.distinct(725))
  apply (metis PC.distinct(1635) PC.distinct(1639) PC.distinct(767) PC.distinct(77))
  by (metis PC.distinct(1637) PC.simps(1681) pc_aux)


(*DTML recover annotation is stable against the inv(Write) operation*)
lemma  Write_invocation_Recover_global:
assumes "thrdsvars"
and "  Recover_inv syst   ((pc \<sigma>) syst)  \<sigma>  "
and "Read_invocation_inv ta  ((pc \<sigma>) ta) \<sigma>" 
and " TML_Write_invocation  ta   \<sigma> \<sigma>'"
and "total_wfs (\<tau> \<sigma>) "
and "((pc \<sigma>) ta) \<in> {WritePending,Ready} \<union> {Aborted} "
and "((pc \<sigma>) syst) \<in> {RecIdle } \<union> recovering" 
and  " ((pc \<sigma>) syst) \<noteq> RecIdle   \<longrightarrow> (\<forall> t  \<noteq> syst.  ((pc \<sigma>) t) \<in> {NotStarted, Aborted, Committed})"  (*persistent invariant*)
shows "  Recover_inv syst   ((pc \<sigma>') syst)  \<sigma>' " 
  using assms
  apply(simp add:Read_invocation_inv_def Recover_inv_def total_wfs_def TML_Write_invocation_def  )
  apply (cases" pc  \<sigma> syst"; simp ; cases "(pc \<sigma>) ta"; simp )
  by metis+


(*res(Write) annotation is stable against the DTML recover operation*)
lemma Recover_Write_response_global:
assumes"total_wfs (\<tau> \<sigma>) "
and  "Write_Response_inv ta  ((pc \<sigma>) ta) \<sigma>"
and "   Recover_inv syst   ((pc \<sigma>) syst) \<sigma> "
and " TML_Recover syst   \<sigma> \<sigma>' "
and "((pc \<sigma>)syst) \<in> {RecIdle} \<union> recovering "
and "((pc \<sigma>)ta) \<in> { WriteResponding ,Ready, Aborted} "
and  " ((pc \<sigma>) syst) \<noteq> RecIdle   \<longrightarrow> (\<forall> t  \<noteq> syst.  ((pc \<sigma>) t)   \<in> {NotStarted, Aborted, Committed})"  (*persistent invariant*)
and " ta \<noteq> syst"
shows "Write_Response_inv ta  ((pc \<sigma>') ta) \<sigma>'" 
  using assms
  apply(simp add: Write_Response_inv_def  TML_Recover_def  Recover_inv_def )
  apply (cases" pc  \<sigma> syst"; simp ; cases "(pc \<sigma>) ta"; simp )
  apply (metis PC.distinct(1483) PC.distinct(53) PC.distinct(743))
  apply (metis PC.distinct(1639) PC.distinct(767) PC.distinct(77))
  apply (metis PC.distinct(1483) PC.distinct(53) PC.distinct(743))
  apply (metis PC.distinct(1639) PC.distinct(767) PC.distinct(77))
  apply (metis PC.distinct(1483) PC.distinct(53) PC.distinct(743))
  apply (metis PC.distinct(1639) PC.distinct(767) PC.distinct(77))
  apply (metis PC.distinct(1483) PC.distinct(53) PC.distinct(743))
  apply (metis PC.distinct(1639) PC.distinct(767) PC.distinct(77))
  apply (metis PC.distinct(1483) PC.distinct(53) PC.distinct(743))
  apply (metis PC.distinct(1639) PC.distinct(767) PC.distinct(77))
  apply (metis PC.distinct(1483) PC.distinct(53) PC.distinct(743))
  apply (metis PC.distinct(1639) PC.distinct(767) PC.distinct(77))
  apply (metis PC.distinct(1483) PC.distinct(53) PC.distinct(743))
  apply (metis PC.distinct(1639) PC.distinct(767) PC.distinct(77))
  apply (metis PC.distinct(1619) PC.simps(1681) pc_aux)
  apply (metis PC.distinct(1483) PC.distinct(53) PC.distinct(743))
  apply(metis PC.distinct(1639) PC.distinct(767) PC.distinct(77))
  apply (metis PC.distinct(1483) PC.distinct(53) PC.distinct(743))
  apply (metis PC.distinct(1639) PC.distinct(767) PC.distinct(77))
  apply (metis PC.distinct(1483) PC.distinct(53) PC.distinct(743))
  apply (metis PC.distinct(1639) PC.distinct(767) PC.distinct(77))
  by (metis PC.distinct(1619) PC.simps(1681) pc_aux)


(*DTML recover annotation is stable against the res(Write) operation*)
lemma Write_response_Recover_global:
assumes "thrdsvars"
and "  Recover_inv syst   ((pc \<sigma>) syst)  \<sigma>  "
and "Write_Response_inv ta  ((pc \<sigma>) ta) \<sigma>" 
and " TML_Write_response  ta   \<sigma> \<sigma>'"
and "total_wfs (\<tau> \<sigma>) "
and "((pc \<sigma>) ta) \<in> {WriteResponding,Ready} \<union> {Aborted} "
and "((pc \<sigma>) syst) \<in> {RecIdle } \<union> recovering" 
and  " ((pc \<sigma>) syst) \<noteq> RecIdle   \<longrightarrow> (\<forall> t  \<noteq> syst.  ((pc \<sigma>) t)   \<in> {NotStarted, Aborted, Committed})"  (*persistent invariant*)
shows "  Recover_inv syst   ((pc \<sigma>') syst)  \<sigma>' " 
  using assms
  apply(simp add:Write_Response_inv_def Recover_inv_def total_wfs_def TML_Write_response_def  )
  apply (cases" pc  \<sigma> syst"; simp ; cases "(pc \<sigma>) ta"; simp )
  by metis+

(*inv(Commit) annotation is stable against the DTML recover operation*)
lemma Recover_Commit_invocation_global:
assumes"total_wfs (\<tau> \<sigma>) "
and  "Commit_invocation_inv ta  ((pc \<sigma>) ta) \<sigma>"
and "   Recover_inv syst   ((pc \<sigma>) syst) \<sigma> "
and " TML_Recover syst   \<sigma> \<sigma>' "
and "((pc \<sigma>)syst) \<in> {RecIdle} \<union> recovering "
and "((pc \<sigma>)ta) \<in> {Ready, CommitPending ,Aborted} "
and  " ((pc \<sigma>) syst) \<noteq> RecIdle   \<longrightarrow> (\<forall> t  \<noteq> syst.  ((pc \<sigma>) t)   \<in> {NotStarted, Aborted, Committed})"  (*persistent invariant*)
shows "Commit_invocation_inv ta  ((pc \<sigma>') ta) \<sigma>'" 
  using assms
  apply(simp add: Commit_invocation_inv_def  TML_Recover_def  Recover_inv_def )
  apply (cases" pc  \<sigma> syst"; simp ; cases "(pc \<sigma>) ta"; simp )
  apply (metis PC.distinct(389) PC.distinct(449) PC.distinct(9))
  apply (metis PC.distinct(1639) PC.distinct(767) PC.distinct(77))
  apply (metis PC.distinct(389) PC.distinct(449) PC.distinct(9))
  apply (metis PC.distinct(1639) PC.distinct(767) PC.distinct(77))
  apply (metis PC.distinct(389) PC.distinct(449) PC.distinct(9))
  apply (metis PC.distinct(1639) PC.distinct(767) PC.distinct(77))
  apply (metis PC.distinct(389) PC.distinct(449) PC.distinct(9))
  apply (metis PC.distinct(1639) PC.distinct(767) PC.distinct(77))
  apply (metis PC.distinct(389) PC.distinct(449) PC.distinct(9))
  apply (metis PC.distinct(1639) PC.distinct(767) PC.distinct(77))
  apply (metis PC.distinct(389) PC.distinct(449) PC.distinct(9))
  apply (metis PC.distinct(1639) PC.distinct(767) PC.distinct(77))
  apply (metis PC.distinct(389) PC.distinct(439) PC.distinct(449) PC.distinct(9))
  apply (metis PC.distinct(1617) PC.distinct(1639) PC.distinct(767) PC.distinct(77))
  apply (metis PC.distinct(1619) PC.simps(1681) pc_aux)
  apply (metis PC.distinct(389) PC.distinct(449) PC.distinct(9))
  apply (metis PC.distinct(1639) PC.distinct(767) PC.distinct(77))
  apply (metis PC.distinct(389) PC.distinct(449) PC.distinct(9))
  apply (metis PC.distinct(1639) PC.distinct(767) PC.distinct(77))
  apply (metis PC.distinct(389) PC.distinct(445) PC.distinct(449) PC.distinct(9))
  apply (metis PC.distinct(1635) PC.distinct(1639) PC.distinct(767) PC.distinct(77))
  apply (case_tac "log \<sigma> = Map.empty")
  apply simp
  by simp

(*DTML recover annotation is stable against the inv(Commit) operation*)
lemma Commit_invocation_Recover_global:
assumes "thrdsvars"
and "  Recover_inv syst   ((pc \<sigma>) syst)  \<sigma>  "
and "Commit_invocation_inv ta  ((pc \<sigma>) ta) \<sigma>" 
and " TML_Commit_invocation  ta   \<sigma> \<sigma>'"
and "total_wfs (\<tau> \<sigma>) "
and "((pc \<sigma>) ta) \<in> {CommitPending,Ready} \<union> {Aborted} "
and "((pc \<sigma>) syst) \<in> {RecIdle } \<union> recovering" 
and  " ((pc \<sigma>) syst) \<noteq> RecIdle   \<longrightarrow> (\<forall> t  \<noteq> syst.  ((pc \<sigma>) t)   \<in> {NotStarted, Aborted, Committed})"  (*persistent invariant*)
shows "  Recover_inv syst   ((pc \<sigma>') syst)  \<sigma>' " 
  using assms
  apply(simp add:Commit_invocation_inv_def Recover_inv_def total_wfs_def TML_Commit_invocation_def  )
  apply (cases" pc  \<sigma> syst"; simp ; cases "(pc \<sigma>) ta"; simp )
  by metis+


(*res(Commit) annotation is stable against the DTML Recover operation*)
lemma Recover_Commit_response_global:
assumes"total_wfs (\<tau> \<sigma>) "
and  "Commit_Response_inv ta  ((pc \<sigma>) ta) \<sigma>"
and "   Recover_inv syst   ((pc \<sigma>) syst) \<sigma> "
and " TML_Recover syst   \<sigma> \<sigma>' "
and "((pc \<sigma>)syst) \<in> {RecIdle} \<union> recovering "
and "((pc \<sigma>)ta) \<in> { CommitResponding ,Committed, Aborted} "
and  " ((pc \<sigma>) syst) \<noteq> RecIdle   \<longrightarrow> (\<forall> t  \<noteq> syst.  ((pc \<sigma>) t)   \<in> {NotStarted, Aborted, Committed})"  (*persistent invariant*)
and " ta \<noteq> syst"
shows "Commit_Response_inv ta  ((pc \<sigma>') ta) \<sigma>'" 
  using assms
  by(simp add: Commit_Response_inv_def  TML_Recover_def  Recover_inv_def )


(*DTML recover annotation is stable against the res(Commit) operation*)
lemma Commit_response_Recover_global:
assumes "thrdsvars"
and "  Recover_inv syst   ((pc \<sigma>) syst)  \<sigma>  "
and " Commit_Response_inv ta  ((pc \<sigma>) ta) \<sigma>" 
and " TML_Commit_response  ta   \<sigma> \<sigma>'"
and "total_wfs (\<tau> \<sigma>) "
and "((pc \<sigma>) ta) \<in> {CommitResponding,Committed}  \<union> {Aborted} "
and "((pc \<sigma>) syst) \<in> {RecIdle } \<union> recovering" 
and  " ((pc \<sigma>) syst) \<noteq> RecIdle   \<longrightarrow> (\<forall> t  \<noteq> syst.  ((pc \<sigma>) t)   \<in> {NotStarted, Aborted, Committed})"  (*persistent invariant*)
shows "  Recover_inv syst   ((pc \<sigma>') syst)  \<sigma>' " 
  using assms
  apply(simp add:Commit_Response_inv_def Recover_inv_def total_wfs_def TML_Commit_response_def  )
  apply (cases" pc  \<sigma> syst"; simp ; cases "(pc \<sigma>) ta"; simp )
  by metis+






end
