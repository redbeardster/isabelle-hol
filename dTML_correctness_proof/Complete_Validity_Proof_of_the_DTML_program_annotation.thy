(*Complete proof of the validity of the DTML program annotation*)

theory Complete_Validity_Proof_of_the_DTML_program_annotation
imports  "global_correctness/Begin/Begin_Commit_Global"  "global_correctness/Begin/Begin_Read_Global"   "global_correctness/Begin/Begin_Write_Global"
"global_correctness/Commit/Commit_Begin_Global"  "global_correctness/Commit/Commit_Commit_Global"  "global_correctness/Commit/Commit_Read_Global"  "global_correctness/Commit/Commit_Write_Global" 
"global_correctness/Write/Write_Begin_Global"   "global_correctness/Write/Write_Commit_Global"    "global_correctness/Write/Write_Read_Global"   "global_correctness/Write/Write_Write_Global"  
"global_correctness/Crash_Recover/Crash_Global"  "global_correctness/Crash_Recover/Recover_Global"
"Invocations_LocalGlobal"   "Responses_LocalGlobal" 
"global_correctness/Read/Read_Begin_Global"   "global_correctness/Read/Read_Commit_Global"    "global_correctness/Read/Read_Read_Global"   "global_correctness/Read/Read_Write_Global"  
"global_correctness/Begin/Begin_Begin_Global" "Local_Correctness_Total"

begin 


(*auxiliary lemmas*)

lemma begin_dt:
assumes"  TML_Begin t' \<sigma> \<sigma>'"
and" t \<noteq> t' "
shows  " ((pc \<sigma>') t) = ((pc \<sigma>) t) "
using assms
apply (simp add: TML_Begin_def)
apply (cases "pc \<sigma> t' ";  simp add: split if_splits  )
using pc_aux 
by (metis fun_upd_def)


lemma begin_same_\<sigma>:
assumes "TML_Begin tb  \<sigma> \<sigma>'"
and  "((pc \<sigma>) tb) \<notin> {BeginResponding, BeginPending,  Aborted} \<union>  beginning "
shows " \<sigma> = \<sigma>' "
using assms
apply (simp add: TML_Begin_def)
by  (cases "(pc \<sigma>) tb"; simp) 


lemma commit_dt:
assumes"  TML_Commit t' \<sigma> \<sigma>'"
and" tb \<noteq> t' "
shows  " ((pc \<sigma>') tb) = ((pc \<sigma>) tb) "
using assms
apply (simp add: TML_Commit_def)
apply (cases "pc \<sigma> t' ";  simp add: split if_splits  )
using pc_aux 
by (metis fun_upd_other)


lemma commit_same_\<sigma>:
assumes "TML_Commit tb  \<sigma> \<sigma>'"
and  "((pc \<sigma>) tb) \<notin> {CommitResponding,CommitPending, Aborted} \<union>  committing "
shows " \<sigma> = \<sigma>' "
using assms
apply (simp add: TML_Commit_def)
by  (cases "(pc \<sigma>) tb"; simp) 

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


lemma write_same_\<sigma>:
assumes "TML_Write tb  \<sigma> \<sigma>'"
and  "((pc \<sigma>) tb) \<notin> {WriteResponding,WritePending, Aborted} \<union>  writing "
shows " \<sigma> = \<sigma>' "
using assms
apply (simp add: TML_Write_def)
by  (cases "(pc \<sigma>) tb"; simp) 


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





lemma Read_same_\<sigma>:
assumes "TML_Read tb  \<sigma> \<sigma>'"
and  "((pc \<sigma>) tb) \<notin> {ReadResponding,ReadPending,  Aborted} \<union>  reading "
shows " \<sigma> = \<sigma>' "
using assms
apply (simp add: TML_Read_def)
by  (cases "(pc \<sigma>) tb"; simp) 


lemma begin_inv_dt:
assumes"   TML_Begin_invocation t' \<sigma> \<sigma>'"
and" tb \<noteq> t' "
shows  "((pc \<sigma>') tb) = ((pc \<sigma>) tb) "
using assms
apply (simp add: TML_Begin_invocation_def)
by (cases "pc \<sigma> t' ";  simp add: split if_splits  )


lemma begin_Invocation_\<sigma>:
assumes " TML_Begin_invocation tb  \<sigma> \<sigma>'"
and  "((pc \<sigma>) tb) \<notin> {BeginPending,  NotStarted} "
shows " \<sigma> = \<sigma>' "
using assms
apply (simp add:  TML_Begin_invocation_def)
by  (cases "(pc \<sigma>) tb"; simp) 



lemma write_inv_dt:
assumes"   TML_Write_invocation t' \<sigma> \<sigma>'"
and" tb \<noteq> t' "
shows  "((pc \<sigma>') tb) = ((pc \<sigma>) tb) "
using assms
apply (simp add: TML_Write_invocation_def)
by (cases "pc \<sigma> t' ";  simp add: split if_splits  )




lemma write_Invocation_\<sigma>:
assumes " TML_Write_invocation tb  \<sigma> \<sigma>'"
and  "((pc \<sigma>) tb) \<notin> {WritePending,  Ready} "
shows " \<sigma> = \<sigma>' "
using assms
apply (simp add:  TML_Write_invocation_def)
by  (cases "(pc \<sigma>) tb"; simp) 


lemma read_inv_dt:
assumes"   TML_Read_invocation t' \<sigma> \<sigma>'"
and" tb \<noteq> t' "
shows  "((pc \<sigma>') tb) = ((pc \<sigma>) tb) "
using assms
apply (simp add: TML_Read_invocation_def)
by (cases "pc \<sigma> t' ";  simp add: split if_splits  )


lemma read_Invocation_\<sigma>:
assumes " TML_Read_invocation tb  \<sigma> \<sigma>'"
and  "((pc \<sigma>) tb) \<notin> {ReadPending,  Ready} "
shows " \<sigma> = \<sigma>' "
using assms
apply (simp add:  TML_Read_invocation_def)
by  (cases "(pc \<sigma>) tb"; simp) 


lemma commit_inv_dt:
assumes"   TML_Commit_invocation t' \<sigma> \<sigma>'"
and" tb \<noteq> t' "
shows  "((pc \<sigma>') tb) = ((pc \<sigma>) tb) "
using assms
apply (simp add: TML_Commit_invocation_def)
by (cases "pc \<sigma> t' ";  simp add: split if_splits  )




lemma commit_Invocation_\<sigma>:
assumes " TML_Commit_invocation tb  \<sigma> \<sigma>'"
and  "((pc \<sigma>) tb) \<notin> {CommitPending,  Ready} "
shows " \<sigma> = \<sigma>' "
using assms
apply (simp add:  TML_Commit_invocation_def)
by  (cases "(pc \<sigma>) tb"; simp) 


lemma begin_resp_dt:
assumes"   TML_Begin_response t' \<sigma> \<sigma>'"
and" tb \<noteq> t' "
shows  "((pc \<sigma>') tb) = ((pc \<sigma>) tb) "
using assms
apply (simp add: TML_Begin_response_def)
by (cases "pc \<sigma> t' ";  simp add: split if_splits  )



lemma begin_Response_\<sigma>:
assumes " TML_Begin_response tb  \<sigma> \<sigma>'"
and  "((pc \<sigma>) tb) \<notin> {BeginResponding ,  Ready} "
shows " \<sigma> = \<sigma>' "
using assms
apply (simp add:  TML_Begin_response_def)
by  (cases "(pc \<sigma>) tb"; simp) 


lemma read_resp_dt:
assumes"   TML_Read_response t' \<sigma> \<sigma>'"
and" tb \<noteq> t' "
shows  "((pc \<sigma>') tb) = ((pc \<sigma>) tb) "
using assms
apply (simp add: TML_Read_response_def)
by (cases "pc \<sigma> t' ";  simp add: split if_splits  )





lemma read_Response_\<sigma>:
assumes " TML_Read_response tb  \<sigma> \<sigma>'"
and  "((pc \<sigma>) tb) \<notin> {ReadResponding ,  Ready} "
shows " \<sigma> = \<sigma>' "
using assms
apply (simp add:  TML_Read_response_def)
by  (cases "(pc \<sigma>) tb"; simp) 


lemma write_resp_dt:
assumes"   TML_Write_response t' \<sigma> \<sigma>'"
and" tb \<noteq> t' "
shows  "((pc \<sigma>') tb) = ((pc \<sigma>) tb) "
using assms
apply (simp add: TML_Write_response_def)
by (cases "pc \<sigma> t' ";  simp add: split if_splits  )




lemma write_Response_\<sigma>:
assumes " TML_Write_response tb  \<sigma> \<sigma>'"
and  "((pc \<sigma>) tb) \<notin> {WriteResponding ,  Ready} "
shows " \<sigma> = \<sigma>' "
using assms
apply (simp add:  TML_Write_response_def)
by  (cases "(pc \<sigma>) tb"; simp) 


lemma commit_resp_dt:
assumes"   TML_Commit_response t' \<sigma> \<sigma>'"
and" tb \<noteq> t' "
shows  "((pc \<sigma>') tb) = ((pc \<sigma>) tb) "
using assms
apply (simp add: TML_Commit_response_def)
by (cases "pc \<sigma> t' ";  simp add: split if_splits  )



lemma  commit_Response_\<sigma>:
assumes " TML_Commit_response tb  \<sigma> \<sigma>'"
and  "((pc \<sigma>) tb) \<notin> {CommitResponding ,  Committed} "
shows " \<sigma> = \<sigma>' "
using assms
apply (simp add:  TML_Commit_response_def)
by  (cases "(pc \<sigma>) tb"; simp) 



lemma  ready_same:
shows "  Begin_inv t (BeginResponding) \<sigma> =   Begin_Response_inv  t (BeginResponding) \<sigma> = Begin_Response_inv  t (Ready) \<sigma> =
Read_inv t (ReadResponding) \<sigma>  =  Read_inv t (ReadPending) \<sigma>  =   Read_invocation_inv  t (ReadPending) \<sigma>  =  Read_invocation_inv  t (Ready) \<sigma> 
=  Read_Response_inv  t (Ready) \<sigma> =  Read_Response_inv  t (ReadResponding) \<sigma>  = 
Write_inv t (WriteResponding) \<sigma>  =  Write_inv t (WritePending) \<sigma>  =   Write_invocation_inv  t (WritePending) \<sigma>  = Write_invocation_inv  t (Ready) \<sigma> 
=  Write_Response_inv  t (Ready) \<sigma> =  Write_Response_inv  t (WriteResponding) \<sigma> = 
Commit_inv t ( CommitPending) \<sigma>  =    Commit_invocation_inv  t ( CommitPending) \<sigma>  =  Commit_invocation_inv  t (Ready) \<sigma> 
"
by (simp add:  Begin_inv_def  Begin_Response_inv_def  Read_inv_def
Read_invocation_inv_def  Read_Response_inv_def  Write_inv_def  Write_invocation_inv_def Write_Response_inv_def  Commit_inv_def  Commit_invocation_inv_def)


lemma beginPending_same:
shows "      Begin_invocation_inv t ( BeginPending) \<sigma> =  Begin_inv t ( BeginPending) \<sigma>    "
by (simp add:  Begin_invocation_inv_def Begin_inv_def)

lemma beginPending2_same:
shows " 
Begin_invocation_inv t ( NotStarted) \<sigma> =    Begin_invocation_inv t ( BeginPending) \<sigma> "
by (simp add:  Begin_invocation_inv_def Begin_inv_def)

lemma  commited_true:
shows "  Begin_inv t (Committed) \<sigma> =  Commit_inv t (Committed) \<sigma> =  Read_inv t (Committed) \<sigma> =  Write_inv t (Committed) \<sigma> = True = Recover_inv t (Committed) \<sigma> "
by  (simp add:  Begin_inv_def Commit_inv_def Read_inv_def Write_inv_def Recover_inv_def)

lemma  aborted_true:
shows "  Begin_inv t (Aborted) \<sigma> =  Commit_inv t (Aborted) \<sigma> =  Read_inv t (Aborted) \<sigma> =  Write_inv t (Aborted) \<sigma> = True = Recover_inv t (Aborted) \<sigma> "
by  (simp add:  Begin_inv_def Commit_inv_def Read_inv_def Write_inv_def Recover_inv_def)



lemma begin_invocation_same:
assumes " ((pc \<sigma>) ta) \<notin> {BeginPending,NotStarted }  "
shows "  Begin_invocation_inv  ta  ((pc \<sigma>) ta) \<sigma> "
using assms
apply (unfold   Begin_invocation_inv_def)
by (cases "(pc \<sigma>) ta"; simp) 

lemma begin_inv_same:
assumes " ((pc \<sigma>) ta) \<notin> {BeginResponding, BeginPending, Aborted } \<union> beginning "
shows "  Begin_inv  ta  ((pc \<sigma>) ta) \<sigma> "
using assms
apply (simp add:  Begin_inv_def)
by (cases "(pc \<sigma>) ta"; simp) 

lemma begin_response_same:
assumes " ((pc \<sigma>) ta) \<notin> {BeginResponding,Ready }  "
shows "  Begin_Response_inv  ta  ((pc \<sigma>) ta) \<sigma> "
using assms
apply (simp add:   Begin_Response_inv_def)
by (cases "(pc \<sigma>) ta"; simp) 


lemma write_invocation_same:
assumes " ((pc \<sigma>) ta) \<notin> {WritePending,Ready }  "
shows "  Write_invocation_inv  ta  ((pc \<sigma>) ta) \<sigma> "
using assms
apply (simp add:   Write_invocation_inv_def)
by (cases "(pc \<sigma>) ta"; simp) 

lemma write_inv_same:
assumes " ((pc \<sigma>) ta) \<notin> {WriteResponding,WritePending, Aborted } \<union> writing "
shows "  Write_inv  ta  ((pc \<sigma>) ta) \<sigma> "
using assms
apply (simp add:  Write_inv_def)
by (cases "(pc \<sigma>) ta"; simp) 


lemma write_response_same:
assumes " ((pc \<sigma>) ta) \<notin> {WriteResponding,Ready}  "
shows "  Write_Response_inv  ta  ((pc \<sigma>) ta) \<sigma> "
using assms
apply (simp add:   Write_Response_inv_def)
by (cases "(pc \<sigma>) ta"; simp) 



lemma read_invocation_same:
assumes " ((pc \<sigma>) ta) \<notin> {ReadPending,Ready }  "
shows "  Read_invocation_inv  ta  ((pc \<sigma>) ta) \<sigma> "
using assms
apply (simp add:   Read_invocation_inv_def)
by (cases "(pc \<sigma>) ta"; simp) 



lemma read_inv_same:
assumes " ((pc \<sigma>) ta) \<notin> {ReadResponding,ReadPending ,Aborted } \<union> reading "
shows "  Read_inv  ta  ((pc \<sigma>) ta) \<sigma> "
using assms
apply (simp add:  Read_inv_def)
by (cases "(pc \<sigma>) ta"; simp) 

lemma read_response_same:
assumes " ((pc \<sigma>) ta) \<notin> {ReadResponding,Ready }  "
shows "  Read_Response_inv  ta  ((pc \<sigma>) ta) \<sigma> "
using assms
apply (simp add:   Read_Response_inv_def)
by (cases "(pc \<sigma>) ta"; simp) 


lemma commit_invocation_same:
assumes " ((pc \<sigma>) ta) \<notin> {CommitPending,Ready }  "
shows "  Commit_invocation_inv  ta  ((pc \<sigma>) ta) \<sigma> "
using assms
apply (simp add:   Commit_invocation_inv_def)
by (cases "(pc \<sigma>) ta"; simp) 


lemma commit_inv_same:
assumes " ((pc \<sigma>) ta) \<notin> {CommitResponding,CommitPending, Aborted } \<union> committing "
shows "  Commit_inv  ta  ((pc \<sigma>) ta) \<sigma> "
using assms
apply (simp add:  Commit_inv_def)
by (cases "(pc \<sigma>) ta"; simp) 


lemma commit_response_same:
assumes " ((pc \<sigma>) ta) \<notin> {CommitResponding,Committed }  "
shows "  Commit_Response_inv  ta  ((pc \<sigma>) ta) \<sigma> "
using assms
by(simp add:  Commit_Response_inv_def)


lemma recover_inv_same:
assumes " ((pc \<sigma>) ta) \<notin> {RecIdle } \<union> recovering "
shows "  Recover_inv  ta  ((pc \<sigma>) ta) \<sigma> "
using assms
apply (simp add:  Recover_inv_def)
by (cases "(pc \<sigma>) ta"; simp) 


lemma recover_dt:
assumes   " TML_Recover t'   \<sigma> \<sigma>' "
and" tb \<noteq> t' "
shows  "((pc \<sigma>') tb) = ((pc \<sigma>) tb) "
using assms
apply (simp add:  TML_Recover_def)
apply (cases "pc \<sigma> t' ";  simp add: split if_splits  )
by (meson pc_aux)+



lemma  begin_abort_commit_helping:
assumes  "thrdsvars"
and  "  Begin_inv t (pc \<sigma> t) \<sigma>"
and " total_wfs (\<tau> \<sigma>)"
and " t \<noteq> syst"
and "   pc \<sigma> syst = RecIdle "
and "DTML_total_persistent_invariant \<sigma>"
and "  TML_Begin t \<sigma> \<sigma>'"
and  "((pc \<sigma>) t) \<in>   {BeginPending, Aborted, Committed} "
shows  "Begin_inv t (pc \<sigma>' t) \<sigma>'"
using assms
apply (unfold DTML_total_persistent_invariant_def)
using  Begin_local[where \<sigma> = \<sigma> and \<sigma>' = \<sigma>' and t =t  ]
by presburger


lemma  begin_beginning_helping:
assumes  "thrdsvars"
and  "  Begin_inv t (pc \<sigma> t) \<sigma>"
and " total_wfs (\<tau> \<sigma>)"
and " t \<noteq> syst"
and "DTML_total_persistent_invariant \<sigma>"
and "  TML_Begin t \<sigma> \<sigma>'"
shows  "Begin_inv t (pc \<sigma>' t) \<sigma>'"
using assms
apply (unfold DTML_total_persistent_invariant_def)
using  Begin_local[where \<sigma> = \<sigma> and \<sigma>' = \<sigma>' and t =t  ]
by presburger


lemma  ready_abort_commit_total:
assumes  "thrdsvars"
and  "  DTML_total_program_annotations t  ((pc \<sigma>) t)   \<sigma>"
and " total_wfs (\<tau> \<sigma>)"
and "DTML_total_persistent_invariant \<sigma>"
and " dTML  \<sigma> \<sigma>' t"
and  "((pc \<sigma>) t) \<in>   {Ready, Aborted, Committed} "
shows  "  DTML_total_program_annotations t  ((pc \<sigma>') t)  \<sigma>'"
using assms
apply (simp add: dTML_def)
apply (elim disjE conjE)
apply (unfold  DTML_total_program_annotations_def)
apply (intro conjI impI)
defer
apply (simp add:  Commit_inv_def  TML_Begin_def)
apply (simp add:  Recover_inv_def  TML_Begin_def)
apply (simp add:  Read_inv_def  TML_Begin_def)
apply (simp add:  Write_inv_def  TML_Begin_def)
apply (metis PC.distinct(155) PC.distinct(1639) PC.distinct(231) PC.distinct(305) PC.distinct(377) Un_absorb Un_insert_left Un_insert_right begin_same_\<sigma> ex_in_conv insertE insert_commute insert_iff)
apply (metis PC.distinct(155) PC.distinct(1639) PC.distinct(231) PC.distinct(305) PC.distinct(377) Un_absorb Un_insert_left Un_insert_right begin_same_\<sigma> ex_in_conv insertE insert_commute insert_iff)
apply (smt (verit) PC.distinct(155) PC.distinct(1639) PC.distinct(231) PC.distinct(305) PC.distinct(377) Un_absorb Un_insert_left Un_insert_right begin_same_\<sigma> ex_in_conv insertE insert_commute insert_iff)
apply (metis PC.distinct(155) PC.distinct(1639) PC.distinct(231) PC.distinct(305) PC.distinct(377) Un_absorb Un_insert_left Un_insert_right begin_same_\<sigma> ex_in_conv insertE insert_commute insert_iff)
apply (metis PC.distinct(155) PC.distinct(1639) PC.distinct(231) PC.distinct(305) PC.distinct(377) Un_absorb Un_insert_left Un_insert_right begin_same_\<sigma> ex_in_conv insertE insert_commute insert_iff)
apply (smt (verit) PC.distinct(155) PC.distinct(1639) PC.distinct(231) PC.distinct(305) PC.distinct(377) Un_absorb Un_insert_left Un_insert_right begin_same_\<sigma> ex_in_conv insertE insert_commute insert_iff)
apply (metis PC.distinct(155) PC.distinct(1639) PC.distinct(231) PC.distinct(305) PC.distinct(377) Un_absorb Un_insert_left Un_insert_right begin_same_\<sigma> ex_in_conv insertE insert_commute insert_iff)
using Commit_Response_inv_def apply blast
apply (intro conjI impI)
apply (simp add:  Begin_inv_def  TML_Read_def)
apply (simp add:  Commit_inv_def  TML_Read_def)
apply (simp add:  Recover_inv_def  TML_Begin_def)
defer
apply (simp add:  Write_inv_def  TML_Read_def)
apply (simp add:  Begin_invocation_inv_def TML_Read_def)
apply (simp add:  Read_invocation_inv_def TML_Read_def)
apply (simp add:  Write_invocation_inv_def TML_Read_def)
apply (simp add:  Begin_Response_inv_def TML_Read_def)
apply (simp add:  Commit_Response_inv_def TML_Read_def)
apply (simp add:  Read_Response_inv_def TML_Read_def)
apply (simp add:  Write_Response_inv_def TML_Read_def)
apply (simp add:  Commit_Response_inv_def TML_Read_def)
apply (intro conjI impI)
apply (simp add:  Begin_inv_def  TML_Write_def)
apply (simp add:  Commit_inv_def  TML_Write_def)
apply (simp add:  Recover_inv_def  TML_Write_def)
apply (simp add:  Read_inv_def  TML_Write_def)
apply (simp add:  Begin_invocation_inv_def TML_Write_def)
apply (simp add:  Read_invocation_inv_def  TML_Write_def)
apply (simp add:  Write_invocation_inv_def  TML_Write_def)
apply (simp add:  Begin_Response_inv_def TML_Write_def )
apply (simp add:  Commit_Response_inv_def  TML_Write_def)
apply (simp add:  Read_Response_inv_def  TML_Write_def)
apply (simp add:  Write_Response_inv_def  TML_Write_def)
apply (simp add:  Commit_Response_inv_def  TML_Write_def)
apply (simp add:  Commit_Response_inv_def  TML_Write_def)
apply (intro conjI impI)
apply (simp add:  Begin_inv_def  TML_Commit_def)
apply (simp add: split: if_splits)
defer
apply (simp add:  Recover_inv_def  TML_Write_def)
apply (simp add:  Read_inv_def  TML_Commit_def)
apply (simp add: split: if_splits)
apply (simp add:  Write_inv_def  TML_Commit_def)
apply (simp add:  Begin_inv_def  TML_Commit_def)
apply (simp add:  Commit_inv_def  TML_Commit_def)
apply (simp add:  Recover_inv_def  TML_Commit_def)
apply (simp add:  Read_inv_def  TML_Commit_def)
apply (simp add:  Begin_invocation_inv_def TML_Commit_def)
apply (simp add:  Read_invocation_inv_def  TML_Commit_def)
apply (simp add:  Write_invocation_inv_def  TML_Commit_def)
apply (simp add:  Write_Response_inv_def  TML_Commit_def)
apply (simp add:  TML_Begin_invocation_def)
apply (simp add:  TML_Begin_response_def)
apply (simp add:  TML_Read_invocation_def )
apply (simp add:  Begin_inv_def Commit_inv_def  Recover_inv_def   Read_inv_def  Write_inv_def Begin_invocation_inv_def  
Read_invocation_inv_def   Write_invocation_inv_def Commit_invocation_inv_def Begin_Response_inv_def Read_Response_inv_def 
Write_Response_inv_def Commit_Response_inv_def Ready_total_def)
apply (simp add:  TML_Read_response_def)
apply (simp add:  TML_Write_invocation_def  Begin_inv_def Commit_inv_def  Recover_inv_def   Read_inv_def  Write_inv_def Begin_invocation_inv_def  
Read_invocation_inv_def   Write_invocation_inv_def Commit_invocation_inv_def Begin_Response_inv_def Read_Response_inv_def 
Write_Response_inv_def Commit_Response_inv_def Ready_total_def)
apply (simp add:  TML_Write_response_def)
apply (simp add:  TML_Commit_invocation_def  Begin_inv_def Commit_inv_def  Recover_inv_def   Read_inv_def  Write_inv_def Begin_invocation_inv_def  
Read_invocation_inv_def   Write_invocation_inv_def Commit_invocation_inv_def Begin_Response_inv_def Read_Response_inv_def 
Write_Response_inv_def Commit_Response_inv_def Ready_total_def)
apply (simp add:  TML_Commit_response_def)
apply (simp add:   TML_Begin_def )
apply (simp add:   TML_Read_def )
apply (simp add:   TML_Write_def )
apply (simp add:   TML_Commit_def )
apply (simp add:  TML_Begin_invocation_def)
apply (simp add:  TML_Begin_response_def)
apply (simp add:  TML_Read_invocation_def )
apply (simp add:  TML_Read_response_def )
apply (simp add:  TML_Write_invocation_def )
apply (simp add:  TML_Write_response_def )
apply (simp add:  TML_Commit_invocation_def )
apply (simp add:  TML_Commit_response_def )
apply (simp add:   TML_Begin_def )
apply (simp add:   TML_Read_def )
apply (simp add:   TML_Write_def )
apply (simp add:   TML_Commit_def )
apply (simp add:  TML_Begin_invocation_def)
apply (simp add:  TML_Begin_response_def)
apply (simp add:  TML_Read_invocation_def )
apply (simp add:  TML_Read_response_def )
apply (simp add:  TML_Write_invocation_def )
apply (simp add:  TML_Write_response_def )
apply (simp add:  TML_Commit_invocation_def )
apply (simp add:  TML_Commit_response_def )
apply (simp add:  TML_Recover_def )
apply (simp add:  TML_Crash_def  Begin_inv_def Commit_inv_def   Read_inv_def  Write_inv_def Begin_invocation_inv_def  
Read_invocation_inv_def   Write_invocation_inv_def Commit_invocation_inv_def Begin_Response_inv_def Read_Response_inv_def 
Write_Response_inv_def Commit_Response_inv_def )
apply (intro impI)
apply (case_tac " t \<noteq> syst")
apply simp
apply simp
using  Recover_Crash_global[where \<sigma> = \<sigma> and \<sigma>' = \<sigma>' ]  DTML_total_persistent_invariant_def [where \<sigma> = \<sigma>] 
using TML_Crash_def assms(1) apply presburger
apply (simp add:  TML_Recover_def )+
apply (intro conjI impI)
apply (simp add:Begin_inv_def TML_Crash_def   )
apply (simp add:Commit_inv_def TML_Crash_def   )
(*   apply (case_tac " ((pc \<sigma>) syst) \<in> recovering \<union>{RecIdle} ")*)
apply (subgoal_tac " thrdsvars \<and> total_wfs (\<tau> \<sigma>) \<and> Recover_inv syst (pc \<sigma> syst) \<sigma> \<and> ( \<forall>a. a \<in> dom (log \<sigma>) \<longrightarrow> a \<noteq> glb) \<and> TML_Crash \<sigma> \<sigma>' ")
prefer 2
apply (intro conjI)
using assms(1) apply blast
apply blast
apply blast
using DTML_total_persistent_invariant_def [where \<sigma> = \<sigma>] 
apply presburger
apply blast
using  Recover_Crash_global[where \<sigma> = \<sigma> and \<sigma>' = \<sigma>' ]
apply presburger
using DTML_total_persistent_invariant_def [where \<sigma> = \<sigma>] 
apply (smt (z3) Read_Crash_global assms(1) assms(3) assms(4))
using DTML_total_persistent_invariant_def [where \<sigma> = \<sigma>] 
apply (smt (z3) Write_Crash_global assms(1))
apply (metis Begin_invocation_Crash_global)
apply (metis Read_invocation_Crash_global)
apply (metis Write_invocation_Crash_global)
apply (metis Commit_invocation_Crash_global)
using Begin_response_Crash_global assms(1) apply presburger
apply (metis Read_response_Crash_global)
apply (metis Write_response_Crash_global assms(1))
using Commit_Response_inv_def apply blast
apply (intro conjI impI)
apply (simp add:Begin_inv_def TML_Crash_def   )
apply (simp add:Commit_inv_def TML_Crash_def   )
(*   apply (case_tac " ((pc \<sigma>) syst) \<in> recovering \<union>{RecIdle} ")*)
apply (subgoal_tac " thrdsvars \<and> total_wfs (\<tau> \<sigma>) \<and> Recover_inv syst (pc \<sigma> syst) \<sigma> \<and> ( \<forall>a. a \<in> dom (log \<sigma>) \<longrightarrow> a \<noteq> glb) \<and> TML_Crash \<sigma> \<sigma>' ")
prefer 2
apply (intro conjI)
using assms(1) apply blast
apply blast
apply blast
using DTML_total_persistent_invariant_def [where \<sigma> = \<sigma>] 
apply presburger
apply blast
using  Recover_Crash_global[where \<sigma> = \<sigma> and \<sigma>' = \<sigma>' ]
apply presburger
using DTML_total_persistent_invariant_def [where \<sigma> = \<sigma>] 
apply (smt (z3) Read_Crash_global assms(1) assms(3) assms(4))
using DTML_total_persistent_invariant_def [where \<sigma> = \<sigma>] 
apply (smt (z3) Write_Crash_global assms(1))
apply (metis Begin_invocation_Crash_global)
apply (metis Read_invocation_Crash_global)
apply (metis Write_invocation_Crash_global)
apply (metis Commit_invocation_Crash_global)
using Begin_response_Crash_global assms(1) apply blast
apply (metis Read_response_Crash_global)
apply (metis Write_response_Crash_global assms(1))
using Commit_Response_inv_def apply blast
using assms(1) begin_beginning_helping apply blast
using  Read_local[where \<sigma> = \<sigma> and \<sigma>' = \<sigma>' and t =t  ]DTML_total_persistent_invariant_def [where \<sigma> = \<sigma>]
apply (smt (verit) assms(1))
using Commit_local assms(1) by presburger


lemma begin_commit_inv_same:
assumes " Commit_inv t (pc \<sigma> t) \<sigma> "
and  "thrdsvars"
and "  total_wfs (\<tau> \<sigma>)"
and "t \<noteq> syst"
and "DTML_total_persistent_invariant \<sigma>"
and " Begin_inv t (pc \<sigma> t) \<sigma> "
and "TML_Begin  t   \<sigma> \<sigma>'"
and "((pc \<sigma>) t) \<in>  {PC.BeginPending, BeginResponding} \<union> {Begin2, Begin3} \<union> {PC.Aborted} "
shows " Commit_inv t (pc \<sigma>' t) \<sigma>' "
using assms
apply (subgoal_tac " Begin_inv t (pc \<sigma>' t) \<sigma>'  ")
prefer 2
using  begin_beginning_helping[where \<sigma> = \<sigma> and \<sigma>' = \<sigma>' and t = t] 
apply blast
apply (simp add:  Commit_inv_def)
apply (cases "(pc \<sigma>') t"; simp) 
apply (smt (z3) Begin_pcs PC.distinct(163) PC.distinct(237) PC.distinct(309) PC.distinct(449) PC.distinct(87) Un_empty_right Un_insert_right assms(7) assms(8) insertE insert_absorb insert_absorb2 insert_def insert_not_empty)
apply (smt (z3) Begin_pcs PC.distinct(165) PC.distinct(239) PC.distinct(311) PC.distinct(517) PC.distinct(89) Un_empty_right Un_insert_right assms(7) assms(8) insertE insert_absorb insert_absorb2 insert_def insert_not_empty)
apply (smt (z3) Begin_pcs PC.distinct(167) PC.distinct(241) PC.distinct(313) PC.distinct(583) PC.distinct(91) Un_empty_right Un_insert_right assms(7) assms(8) insertE insert_absorb insert_absorb2 insert_def insert_not_empty)
by (smt (z3) Begin_pcs PC.distinct(169) PC.distinct(243) PC.distinct(315) PC.distinct(647) PC.distinct(93) Un_empty_right Un_insert_right assms(7) assms(8) insertE insert_absorb insert_absorb2 insert_def insert_not_empty)


lemma begin_Read_inv_same:
assumes " Read_inv t (pc \<sigma> t) \<sigma> "
and  "thrdsvars"
and "t \<noteq> syst"
and "  total_wfs (\<tau> \<sigma>)"
and "DTML_total_persistent_invariant \<sigma>"
and " Begin_inv t (pc \<sigma> t) \<sigma> "
and "TML_Begin  t   \<sigma> \<sigma>'"
and "((pc \<sigma>) t) \<in> {PC.BeginPending, BeginResponding} \<union> {Begin2, Begin3} \<union> {PC.Aborted}" 
shows " Write_inv t (pc \<sigma>' t) \<sigma>' "
using assms
apply (subgoal_tac " Begin_inv t (pc \<sigma>' t) \<sigma>'  ")
prefer 2
using  begin_beginning_helping[where \<sigma> = \<sigma> and \<sigma>' = \<sigma>' and t = t] 
apply blast
apply (subgoal_tac "((pc \<sigma>') t) \<in> {PC.BeginPending, BeginResponding} \<union> {Begin2, Begin3} \<union> {PC.Aborted}")
prefer 2
using Begin_pcs[where \<sigma> = \<sigma> and \<sigma>' = \<sigma>' and t =t]  
apply fastforce
apply (simp add:  Write_inv_def)
by  (cases "(pc \<sigma>') t"; simp) 


lemma begin_Write_inv_same:
assumes " Read_inv t (pc \<sigma> t) \<sigma> "
and  "thrdsvars"
and "t \<noteq> syst"
and "  total_wfs (\<tau> \<sigma>)"
and "DTML_total_persistent_invariant \<sigma>"
and " Begin_inv t (pc \<sigma> t) \<sigma> "
and "TML_Begin  t   \<sigma> \<sigma>'"
and "((pc \<sigma>) t) \<in> {PC.BeginPending, BeginResponding} \<union> {Begin2, Begin3} \<union> {PC.Aborted} "
shows " Read_inv t (pc \<sigma>' t) \<sigma>' "
using assms
apply (subgoal_tac " Begin_inv t (pc \<sigma>' t) \<sigma>'  ")
prefer 2
using  begin_beginning_helping[where \<sigma> = \<sigma> and \<sigma>' = \<sigma>' and t = t] 
apply blast
apply (subgoal_tac "((pc \<sigma>') t) \<in> {PC.BeginPending, BeginResponding} \<union> {Begin2, Begin3} \<union> {PC.Aborted}")
prefer 2
using Begin_pcs[where \<sigma> = \<sigma> and \<sigma>' = \<sigma>' and t =t]  
apply fastforce

apply (simp add:  Read_inv_def)
by (cases "(pc \<sigma>') t"; simp) 



lemma read_commit_inv_same:
assumes " Commit_inv t (pc \<sigma> t) \<sigma> "
and  "thrdsvars"
and "t \<noteq> syst"
and "DTML_total_persistent_invariant \<sigma>"
and " Read_inv t (pc \<sigma> t) \<sigma> "
and "TML_Read  t   \<sigma> \<sigma>'"
and "((pc \<sigma>) t) \<in>  {PC.ReadPending, ReadResponding} \<union> reading \<union> {PC.Aborted}"
and "  total_wfs (\<tau> \<sigma>)"
shows " Commit_inv t (pc \<sigma>' t) \<sigma>' "
using assms
apply (subgoal_tac " Read_inv t (pc \<sigma>' t) \<sigma>'  ")
prefer 2
using DTML_total_persistent_invariant_def [where \<sigma> = \<sigma>]  Read_local[where \<sigma> = \<sigma> and \<sigma>' = \<sigma>'  and t = t]
apply presburger
apply (subgoal_tac "((pc \<sigma>') t) \<in> {PC.ReadPending, ReadResponding} \<union> reading \<union> {PC.Aborted}")
prefer 2
using Read_pcs apply blast
apply (simp add:  Commit_inv_def)
by  (cases "(pc \<sigma>') t"; simp) 



lemma read_write_inv_same:
assumes " Write_inv t (pc \<sigma> t) \<sigma> "
and  "thrdsvars"
and "t \<noteq> syst"
and "DTML_total_persistent_invariant \<sigma>"
and " Read_inv t (pc \<sigma> t) \<sigma> "
and "TML_Read  t   \<sigma> \<sigma>'"
and "((pc \<sigma>) t) \<in>  {PC.ReadPending, ReadResponding} \<union> reading \<union> {PC.Aborted}"
and "  total_wfs (\<tau> \<sigma>)"
shows " Write_inv t (pc \<sigma>' t) \<sigma>' "
using assms
apply (subgoal_tac " Read_inv t (pc \<sigma>' t) \<sigma>'  ")
prefer 2
using DTML_total_persistent_invariant_def [where \<sigma> = \<sigma>]  Read_local[where \<sigma> = \<sigma> and \<sigma>' = \<sigma>'  and t = t]
apply presburger
apply (subgoal_tac "((pc \<sigma>') t) \<in> {ReadPending, ReadResponding} \<union> reading \<union> {PC.Aborted}")
prefer 2
using Read_pcs apply blast
apply (simp add:  Write_inv_def)
by  (cases "(pc \<sigma>') t"; simp) 

lemma read_begin_inv_same:
assumes " Begin_inv t (pc \<sigma> t) \<sigma> "
and  "thrdsvars"
and "t \<noteq> syst"
and "DTML_total_persistent_invariant \<sigma>"
and " Read_inv t (pc \<sigma> t) \<sigma> "
and "TML_Read  t   \<sigma> \<sigma>'"
and "((pc \<sigma>) t) \<in>  {PC.ReadPending, ReadResponding} \<union> reading \<union> {PC.Aborted} "
and "  total_wfs (\<tau> \<sigma>)"
shows " Begin_inv t (pc \<sigma>' t) \<sigma>' "
using assms
apply (subgoal_tac " Read_inv t (pc \<sigma>' t) \<sigma>'  ")
prefer 2
using DTML_total_persistent_invariant_def [where \<sigma> = \<sigma>]  Read_local[where \<sigma> = \<sigma> and \<sigma>' = \<sigma>'  and t = t]
apply presburger
apply (subgoal_tac "((pc \<sigma>') t) \<in> {ReadPending, ReadResponding} \<union> reading \<union> {PC.Aborted}")
prefer 2
using Read_pcs apply blast
apply (simp add: Begin_inv_def)
by  (cases "(pc \<sigma>') t"; simp) 


lemma read_read_inv_same:
assumes " Read_inv t (pc \<sigma> t) \<sigma> "
and  "thrdsvars"
and "t \<noteq> syst"
and "DTML_total_persistent_invariant \<sigma>"
and " Read_inv t (pc \<sigma> t) \<sigma> "
and "TML_Read  t   \<sigma> \<sigma>'"
and "((pc \<sigma>) t) \<in>  {PC.ReadPending, ReadResponding} \<union> reading \<union> {PC.Aborted} "
and "  total_wfs (\<tau> \<sigma>)"
shows " Read_inv t (pc \<sigma>' t) \<sigma>' "
using assms
apply (subgoal_tac " Read_inv t (pc \<sigma>' t) \<sigma>'  ")
prefer 2
using DTML_total_persistent_invariant_def [where \<sigma> = \<sigma>]  Read_local[where \<sigma> = \<sigma> and \<sigma>' = \<sigma>'  and t = t]
apply presburger
apply (subgoal_tac "((pc \<sigma>') t) \<in> {ReadPending, ReadResponding} \<union> reading \<union> {PC.Aborted}")
prefer 2
using Read_pcs apply blast
by (simp add: Read_inv_def)


lemma write_commit_inv_same:
assumes " Commit_inv t (pc \<sigma> t) \<sigma> "
and  "thrdsvars"
and "t \<noteq> syst"
and "DTML_total_persistent_invariant \<sigma>"
and " Write_inv t (pc \<sigma> t) \<sigma> "
and "TML_Write  t   \<sigma> \<sigma>'"
and "((pc \<sigma>) t) \<in>  {PC.WritePending, WriteResponding} \<union> writing \<union> {PC.Aborted} "
and "  total_wfs (\<tau> \<sigma>)"
shows " Commit_inv t (pc \<sigma>' t) \<sigma>' "
using assms
apply (subgoal_tac " Write_inv t (pc \<sigma>' t) \<sigma>'  ")
prefer 2
using DTML_total_persistent_invariant_def [where \<sigma> = \<sigma>]  Write_local[where \<sigma> = \<sigma> and \<sigma>' = \<sigma>'  and t = t]
apply presburger
apply (subgoal_tac "((pc \<sigma>') t) \<in> {WritePending, WriteResponding} \<union> writing \<union> {PC.Aborted}")
prefer 2
using  Write_pcs 
apply (meson UnI1 UnI2)
apply (simp add:  Commit_inv_def)
by  (cases "(pc \<sigma>') t"; simp) 


lemma write_write_inv_same:
assumes " Write_inv t (pc \<sigma> t) \<sigma> "
and  "thrdsvars"
and "t \<noteq> syst"
and "DTML_total_persistent_invariant \<sigma>"
and " Write_inv t (pc \<sigma> t) \<sigma> "
and "TML_Write  t   \<sigma> \<sigma>'"
and "((pc \<sigma>) t) \<in>  {PC.WritePending, WriteResponding} \<union> writing \<union> {PC.Aborted} "
and "  total_wfs (\<tau> \<sigma>)"
shows " Write_inv t (pc \<sigma>' t) \<sigma>' "
using assms
apply (subgoal_tac " Write_inv t (pc \<sigma>' t) \<sigma>'  ")
prefer 2
using DTML_total_persistent_invariant_def [where \<sigma> = \<sigma>]  Write_local[where \<sigma> = \<sigma> and \<sigma>' = \<sigma>'  and t = t]
apply presburger

apply (subgoal_tac "((pc \<sigma>') t) \<in> {WritePending, WriteResponding} \<union> writing \<union> {PC.Aborted}")
prefer 2
using  Write_pcs 
apply (meson UnI1 UnI2)
by (simp add:  Commit_inv_def)


lemma write_read_inv_same:
assumes " Read_inv t (pc \<sigma> t) \<sigma> "
and  "thrdsvars"
and "t \<noteq> syst"
and "DTML_total_persistent_invariant \<sigma>"
and " Write_inv t (pc \<sigma> t) \<sigma> "
and "TML_Write  t   \<sigma> \<sigma>'"
and "((pc \<sigma>) t) \<in>  {PC.WritePending, WriteResponding} \<union> writing \<union> {PC.Aborted} "
and "  total_wfs (\<tau> \<sigma>)"
shows " Read_inv t (pc \<sigma>' t) \<sigma>' "
using assms
apply (subgoal_tac " Write_inv t (pc \<sigma>' t) \<sigma>'  ")
prefer 2
using DTML_total_persistent_invariant_def [where \<sigma> = \<sigma>]  Write_local[where \<sigma> = \<sigma> and \<sigma>' = \<sigma>'  and t = t]
apply presburger
apply (subgoal_tac "((pc \<sigma>') t) \<in> {WritePending, WriteResponding} \<union> writing \<union> {PC.Aborted}")
prefer 2
using  Write_pcs 
apply (meson UnI1 UnI2)
apply (simp add:  Read_inv_def)
by  (cases "(pc \<sigma>') t"; simp) 

lemma write_begin_inv_same:
assumes " Begin_inv t (pc \<sigma> t) \<sigma> "
and  "thrdsvars"
and "t \<noteq> syst"
and "DTML_total_persistent_invariant \<sigma>"
and " Write_inv t (pc \<sigma> t) \<sigma> "
and "TML_Write  t   \<sigma> \<sigma>'"
and "((pc \<sigma>) t) \<in>  {PC.WritePending, WriteResponding} \<union> writing \<union> {PC.Aborted} "
and "  total_wfs (\<tau> \<sigma>)"
shows " Begin_inv t (pc \<sigma>' t) \<sigma>' "
using assms
apply (subgoal_tac " Write_inv t (pc \<sigma>' t) \<sigma>'  ")
prefer 2
using DTML_total_persistent_invariant_def [where \<sigma> = \<sigma>]  Write_local[where \<sigma> = \<sigma> and \<sigma>' = \<sigma>'  and t = t]
apply presburger

apply (subgoal_tac "((pc \<sigma>') t) \<in> {WritePending, WriteResponding} \<union> writing \<union> {PC.Aborted}")
prefer 2
using  Write_pcs 
apply (meson UnI1 UnI2)
apply (simp add:  Begin_inv_def)
by  (cases "(pc \<sigma>') t"; simp) 

lemma commit_write_inv_same:
assumes " Commit_inv t (pc \<sigma> t) \<sigma> "
and  "thrdsvars"
and "t \<noteq> syst"
and "DTML_total_persistent_invariant \<sigma>"
and " Write_inv t (pc \<sigma> t) \<sigma> "
and "TML_Commit  t   \<sigma> \<sigma>'"
and "((pc \<sigma>) t) \<in>  {PC.CommitPending, CommitResponding} \<union> committing \<union> {PC.Aborted} "
and "  total_wfs (\<tau> \<sigma>)"
shows " Write_inv t (pc \<sigma>' t) \<sigma>' "
using assms
apply (subgoal_tac " Commit_inv t (pc \<sigma>' t) \<sigma>'  ")
prefer 2
using DTML_total_persistent_invariant_def [where \<sigma> = \<sigma>]  Commit_local[where \<sigma> = \<sigma> and \<sigma>' = \<sigma>'  and t = t]
apply fastforce

apply (subgoal_tac "((pc \<sigma>') t) \<in> {CommitPending, CommitResponding} \<union> committing  \<union> {PC.Aborted}")
prefer 2
using  Commit_pcs 
apply (meson UnI1 UnI2)
apply (simp add:  Commit_inv_def)
apply  (cases "(pc \<sigma>') t"; simp) 
apply  (cases "(pc \<sigma>) t"; simp) 
by (simp add: Write_inv_def)+


lemma commit_read_inv_same:
assumes " Commit_inv t (pc \<sigma> t) \<sigma> "
and  "thrdsvars"
and "t \<noteq> syst"
and "DTML_total_persistent_invariant \<sigma>"
and " Read_inv t (pc \<sigma> t) \<sigma> "
and "TML_Commit  t   \<sigma> \<sigma>'"
and "((pc \<sigma>) t) \<in>  {PC.CommitPending, CommitResponding} \<union> committing \<union> {PC.Aborted} "
and "  total_wfs (\<tau> \<sigma>)"
shows " Read_inv t (pc \<sigma>' t) \<sigma>' "
using assms
apply (subgoal_tac " Commit_inv t (pc \<sigma>' t) \<sigma>'  ")
prefer 2
using DTML_total_persistent_invariant_def [where \<sigma> = \<sigma>]  Commit_local[where \<sigma> = \<sigma> and \<sigma>' = \<sigma>'  and t = t]
apply fastforce
apply (subgoal_tac "((pc \<sigma>') t) \<in> {CommitPending, CommitResponding} \<union> committing  \<union> {PC.Aborted}")
prefer 2
using  Commit_pcs 
apply (meson UnI1 UnI2)
apply (simp add:  Commit_inv_def)
apply  (cases "(pc \<sigma>') t"; simp) 
apply  (cases "(pc \<sigma>) t"; simp) 
by (simp add: Read_inv_def)+


lemma commit_begin_inv_same:
assumes " Begin_inv t (pc \<sigma> t) \<sigma> "
and  "thrdsvars"
and "t \<noteq> syst"
and "DTML_total_persistent_invariant \<sigma>"
and " Commit_inv t (pc \<sigma> t) \<sigma> "
and "TML_Commit  t   \<sigma> \<sigma>'"
and "((pc \<sigma>) t) \<in>  {PC.CommitPending, CommitResponding} \<union> committing \<union> {PC.Aborted} "
and "  total_wfs (\<tau> \<sigma>)"
shows " Begin_inv t (pc \<sigma>' t) \<sigma>' "
using assms
apply (subgoal_tac " Commit_inv t (pc \<sigma>' t) \<sigma>'  ")
prefer 2
using DTML_total_persistent_invariant_def [where \<sigma> = \<sigma>]  Commit_local[where \<sigma> = \<sigma> and \<sigma>' = \<sigma>'  and t = t]
apply fastforce

apply (subgoal_tac "((pc \<sigma>') t) \<in> {CommitPending, CommitResponding} \<union> committing  \<union> {PC.Aborted}")
prefer 2
using  Commit_pcs 
apply (meson UnI1 UnI2)
apply (simp add:  Commit_inv_def)
apply  (cases "(pc \<sigma>') t"; simp) 
apply  (cases "(pc \<sigma>) t"; simp) 
by (simp add: Begin_inv_def)+


(***************************************************************************************************************)

(*Lemma that establishes local correnctness of DTML*)
lemma local_correnctness_total :
assumes  "thrdsvars"
and  "  DTML_total_program_annotations t ((pc \<sigma>) t) \<sigma>"
and "DTML_total_persistent_invariant \<sigma>"
and " dTML  \<sigma> \<sigma>' t"
and "  total_wfs (\<tau> \<sigma>)"
shows  "  DTML_total_program_annotations t ((pc \<sigma>') t) \<sigma>'"
  using assms 
  apply (simp add: dTML_def)
  apply (elim disjE conjE)
               apply (unfold  DTML_total_program_annotations_def)
               apply (intro conjI impI)
  using DTML_total_persistent_invariant_def [where  \<sigma> = \<sigma>]  Begin_local [where  \<sigma> = \<sigma>  and  \<sigma>' = \<sigma>'  and t = t]
  using assms(1) apply presburger
                      apply (smt (verit) Un_insert_right assms(1) assms(3) assms(5) begin_commit_inv_same begin_same_\<sigma> insertI1 insert_commute insert_iff singleton_iff sup_bot.right_neutral)
                      apply auto[1]
                      apply (smt (verit) Un_insert_right assms(1) assms(3) assms(5) begin_Write_inv_same begin_same_\<sigma> insertE insertI1 insert_commute insert_iff singleton_iff sup_bot.right_neutral)
                      apply (smt (verit) Un_insert_right assms(1) assms(3) assms(5) begin_Read_inv_same begin_same_\<sigma> insertE insertI1 insert_commute insert_iff singleton_iff sup_bot.right_neutral)
                      apply (elim conjE )
                      apply (case_tac " ((pc \<sigma>) t) \<notin>  {PC.BeginPending, PC.BeginResponding } \<union> beginning \<union> {PC.Aborted}  ")
                      apply (smt (verit) Un_insert_left assms(1) assms(2) assms(3) assms(4) assms(5) begin_same_\<sigma> DTML_total_program_annotations_def insertE insertI1 insert_absorb2 insert_commute ready_abort_commit_total sup_bot_left)          
                      apply (case_tac " (pc \<sigma>) t = BeginPending  ") 
                      apply (simp add:   Begin_invocation_inv_def Begin_inv_def)
                      apply (cases "(pc \<sigma>') t" ;simp)
                      apply (metis (no_types, opaque_lifting) Begin_not_pcs Begin_pcs PC.distinct(1) PC.distinct(3) PC.distinct(5) PC.distinct(7) PC.distinct(79) Un_iff ex_in_conv insertE)
                      apply (smt (z3) Begin_invocation_inv_def PC.simps(1642) assms(1) beginPending_same begin_beginning_helping)
                      apply (simp add: Begin_invocation_inv_def)
                      apply (cases "(pc \<sigma>') t" ;simp)
                      apply (smt (z3)Begin_not_pcs Begin_pcs PC.distinct(1) PC.distinct(3) PC.distinct(5) PC.distinct(7) PC.distinct(79) Un_insert_left Un_insert_right emptyE insertE insertI1 insert_absorb2 insert_commute insert_iff sup_bot_left sup_bot_right)
                      apply (smt (z3) Begin_invocation_inv_def PC.simps(1642) assms(1) assms(2) assms(3) assms(4) assms(5) beginPending_same begin_beginning_helping bot_nat_def DTML_total_program_annotations_def insertI1 insert_commute ready_abort_commit_total)
                     apply (case_tac " ((pc \<sigma>) t) \<notin>  {PC.BeginPending, PC.BeginResponding } \<union> beginning \<union> {PC.Aborted}  ")
  using Begin_not_pcs apply blast
                     apply (simp add:   Read_invocation_inv_def)
                     apply (cases "(pc \<sigma>') t" ;simp)
                      apply (smt (z3) Begin_not_pcs Begin_pcs PC.distinct(175) PC.distinct(249) PC.distinct(321) PC.distinct(827) PC.distinct(99) Un_insert_left emptyE insertE insertI1 insert_absorb2 insert_commute insert_iff sup_assoc sup_bot_left)
                     apply (smt (z3)  Begin_not_pcs Begin_pcs PC.distinct(155) PC.distinct(1639) PC.distinct(231) PC.distinct(305) PC.distinct(377) Un_insert_right begin_same_\<sigma> ex_in_conv insertE insertI1 insert_absorb2 insert_commute insert_iff sup_bot.right_neutral)
                    apply (case_tac " ((pc \<sigma>) t) \<notin>  {PC.BeginPending, PC.BeginResponding } \<union> beginning \<union> {PC.Aborted}  ")
  using Begin_not_pcs apply blast
                    apply (simp add:   Write_invocation_inv_def)
                    apply (cases "(pc \<sigma>') t" ;simp)
                     apply (smt (z3) Begin_not_pcs Begin_pcs PC.distinct(113) PC.distinct(1177) PC.distinct(189) PC.distinct(263) PC.distinct(335) Un_insert_left emptyE insertE insertI1 insert_absorb2 insert_commute insert_iff sup_assoc sup_bot_left)
                    apply (smt (z3) Begin_not_pcs Begin_pcs PC.distinct(155) PC.distinct(1639) PC.distinct(231) PC.distinct(305) PC.distinct(377) Un_insert_right begin_same_\<sigma> ex_in_conv insertE insertI1 insert_absorb2 insert_commute insert_iff sup_bot.right_neutral)
                   apply (case_tac " ((pc \<sigma>) t) \<notin>  {PC.BeginPending, PC.BeginResponding } \<union> beginning \<union> {PC.Aborted}  ")
  using Begin_not_pcs apply blast
                   apply (simp add:   Commit_invocation_inv_def)
                   apply (cases "(pc \<sigma>') t" ;simp)
                    apply (smt (z3) Begin_not_pcs Begin_pcs PC.distinct(163) PC.distinct(237) PC.distinct(309) PC.distinct(449) PC.distinct(87) Un_insert_left emptyE insertE insertI1 insert_absorb2 insert_commute insert_iff sup_assoc sup_bot_left)
  apply (smt (z3) Begin_not_pcs Begin_pcs PC.distinct(155) PC.distinct(1639) PC.distinct(231) PC.distinct(305) PC.distinct(377) Un_insert_right begin_same_\<sigma> ex_in_conv insertE insertI1 insert_absorb2 insert_commute sup_bot.right_neutral)
  apply (case_tac " ((pc \<sigma>) t) \<notin>  {PC.BeginPending, PC.BeginResponding } \<union> beginning \<union> {PC.Aborted}  ")
  using Begin_not_pcs apply blast
  apply (subgoal_tac "  pc \<sigma>' t \<in> {BeginPending, BeginResponding} \<union> {Begin2, Begin3} \<union> {Aborted}")
  prefer 2
  using Begin_pcs apply presburger
  apply (case_tac " (pc \<sigma>') t = BeginResponding  ") 
  apply (simp add:  TML_Begin_def  Begin_Response_inv_def  Begin_inv_def)
  apply (cases "(pc \<sigma>) t" ;simp)
  apply (simp add: Ready_total_def)
  apply (simp add: split if_splits)
  apply (smt (verit) Begin_inv_def PC.distinct(161) PC.simps(1644) fun_upd_other fun_upd_same)
  apply (metis (no_types, opaque_lifting) PC.distinct(155) PC.distinct(1639) PC.distinct(231) PC.distinct(305) Un_insert_left begin_response_same emptyE insert_iff sup_bot_left)
  apply (case_tac " ((pc \<sigma>) t) \<notin>  {PC.BeginPending, PC.BeginResponding } \<union> beginning \<union> {PC.Aborted}  ")
  using Begin_not_pcs apply blast
  apply (metis (no_types, opaque_lifting) Begin_pcs PC.distinct(111) PC.distinct(1133) PC.distinct(155) PC.distinct(1639) PC.distinct(187) PC.distinct(231) PC.distinct(261) PC.distinct(305) PC.distinct(333) PC.distinct(377) Un_insert_left empty_iff insert_iff read_response_same sup_bot_left)
  apply (case_tac " ((pc \<sigma>) t) \<notin>  {PC.BeginPending, PC.BeginResponding } \<union> beginning \<union> {PC.Aborted}  ")
  using Begin_not_pcs apply blast
  apply (metis (no_types, opaque_lifting) Begin_pcs PC.distinct(131) PC.distinct(1483) PC.distinct(155) PC.distinct(1639) PC.distinct(207) PC.distinct(231) PC.distinct(281) PC.distinct(305) PC.distinct(353) PC.distinct(377) Un_insert_left empty_iff insert_iff sup_bot_left write_response_same)
  apply (case_tac " ((pc \<sigma>) t) \<notin>  {PC.BeginPending, PC.BeginResponding } \<union> beginning \<union> {PC.Aborted}  ")
  using Begin_not_pcs apply blast
  using Commit_Response_inv_def apply blast
    (*************************)
  apply (case_tac " ((pc \<sigma>) t) \<notin>  {PC.ReadPending, PC.ReadResponding } \<union> reading \<union> {PC.Aborted}  ")
  using Read_not_pcs apply blast  
  apply (intro conjI impI)
  using assms(1) read_begin_inv_same apply blast
  using assms(1) read_commit_inv_same apply blast
  apply simp
  using assms(1) read_read_inv_same apply blast
  using assms(1) read_write_inv_same apply blast
  apply (simp add:  Begin_invocation_inv_def)
  apply (cases "(pc \<sigma>') t" ;simp)
  apply (metis (no_types, opaque_lifting) PC.distinct(21) PC.distinct(23) PC.distinct(25) PC.distinct(27) PC.distinct(29) PC.distinct(31) PC.distinct(33) PC.distinct(79) Read_not_pcs Read_pcs UnE emptyE insertE)
  apply (metis (no_types, opaque_lifting) PC.distinct(101) PC.distinct(103) PC.distinct(105) PC.distinct(107) PC.distinct(109) PC.distinct(111) PC.distinct(157) PC.distinct(99) Read_not_pcs Read_pcs UnE emptyE insertE)
  apply (case_tac " (pc \<sigma>') t = ReadPending  ") 
  apply (simp add:  Read_invocation_inv_def Read_inv_def)
  apply (cases "(pc \<sigma>) t" ;simp)
  apply (cases "(pc \<sigma>') t" ;simp )
  apply (simp add:  TML_Read_def)
  apply (simp add:  TML_Read_def)
  apply (simp add:  TML_Read_def)
  apply (case_tac "  even (regs (\<tau> \<sigma>) t DTML.loc) \<and> \<not> readAux \<sigma> t ")
  apply simp
  apply simp
  apply (simp add:  TML_Read_def)
  apply (case_tac "  regs (\<tau> \<sigma>') t c1 = Suc 0 ")
  apply simp
  apply simp
  apply (simp add:  TML_Read_def)
  apply (simp add:  TML_Read_def)
  apply (case_tac " regs (\<tau> \<sigma>) t r3 = regs (\<tau> \<sigma>) t DTML.loc")
  apply simp
  apply simp
  apply (simp add:  TML_Read_def)
  apply (simp add:  TML_Read_def)
  apply (metis (no_types, opaque_lifting) PC.distinct(1037) PC.distinct(1085) PC.distinct(1131) PC.distinct(1639) PC.distinct(881) PC.distinct(935) PC.distinct(987) Read_pcs Un_insert_left empty_iff insert_iff read_invocation_same sup_bot_left)
  using Write_invocation_inv_def
  apply (smt (z3) PC.simps(1652) PC.simps(1653) PC.simps(1654) PC.simps(1655) PC.simps(1656) PC.simps(1657) PC.simps(1658) PC.simps(1681) Read_pcs Un_iff empty_iff insert_iff)
  using Commit_invocation_inv_def
  apply (smt (z3) PC.simps(1652) PC.simps(1653) PC.simps(1654) PC.simps(1655) PC.simps(1656) PC.simps(1657) PC.simps(1658) PC.simps(1681) Read_pcs Un_iff empty_iff insert_iff)
  using Begin_Response_inv_def
  apply (smt (z3) PC.simps(1652) PC.simps(1653) PC.simps(1654) PC.simps(1655) PC.simps(1656) PC.simps(1657) PC.simps(1658) PC.simps(1681) Read_pcs Un_iff empty_iff insert_iff)
  apply (subgoal_tac" Read_Response_inv t ( ReadResponding) \<sigma>' = Read_inv t (ReadResponding) \<sigma>' ")
  prefer 2
  apply (simp add:  Read_Response_inv_def Read_inv_def)
  apply (metis (no_types, opaque_lifting) PC.distinct(1037) PC.distinct(1085) PC.distinct(1639) PC.distinct(825) PC.distinct(881) PC.distinct(935) PC.distinct(987) Read_pcs Un_insert_left assms(1) empty_iff insert_iff read_read_inv_same read_response_same sup_bot_left)
  using Write_Response_inv_def
  apply (smt (z3) PC.simps(1652) PC.simps(1653) PC.simps(1654) PC.simps(1655) PC.simps(1656) PC.simps(1657) PC.simps(1658) PC.simps(1681) Read_pcs Un_iff empty_iff insert_iff)
  using Commit_Response_inv_def
  apply (smt (z3) PC.simps(1652) PC.simps(1653) PC.simps(1654) PC.simps(1655) PC.simps(1656) PC.simps(1657) PC.simps(1658) PC.simps(1681) Read_pcs Un_iff empty_iff insert_iff)
    (**************************************)
  apply (case_tac " ((pc \<sigma>) t) \<notin>  {PC.WritePending, PC.WriteResponding } \<union> writing  \<union> {PC.Aborted}  ")
  using Write_not_pcs apply blast  
  apply (subgoal_tac "  ((pc \<sigma>') t) \<in> {PC.WritePending, PC.WriteResponding } \<union> writing  \<union> {PC.Aborted} ")
  prefer 2
  using Write_pcs apply presburger
  apply (intro conjI impI)
  using assms(1) write_begin_inv_same apply blast
  using assms(1) write_commit_inv_same apply blast
  apply blast
  using assms(1) write_read_inv_same apply blast
  using assms(1) write_write_inv_same apply blast
  apply (metis (no_types, opaque_lifting) PC.distinct(113) PC.distinct(115) PC.distinct(117) PC.distinct(119) PC.distinct(121) PC.distinct(123) PC.distinct(125) PC.distinct(127) PC.distinct(129) PC.distinct(131) PC.distinct(157) PC.distinct(35) PC.distinct(37) PC.distinct(39) PC.distinct(41) PC.distinct(43) PC.distinct(45) PC.distinct(47) PC.distinct(49) PC.distinct(51) PC.distinct(53) PC.distinct(79) UnE begin_invocation_same insertE singletonD)
  using  read_invocation_same[where \<sigma> = \<sigma>' and ta = t]
  apply (metis (no_types, opaque_lifting) PC.distinct(1175) PC.distinct(1217) PC.distinct(1257) PC.distinct(1295) PC.distinct(1331) PC.distinct(1365) PC.distinct(1397) PC.distinct(1427) PC.distinct(1455) PC.distinct(1481) PC.distinct(1639) PC.distinct(783) PC.distinct(785) PC.distinct(787) PC.distinct(789) PC.distinct(791) PC.distinct(793) PC.distinct(795) PC.distinct(797) PC.distinct(799) PC.distinct(801) PC.distinct(827) Un_iff insertE singletonD)
  apply (subgoal_tac" Write_invocation_inv t ( WritePending) \<sigma>' = Write_inv t (WritePending) \<sigma>' ")
  prefer 2
  apply (simp add:  Write_invocation_inv_def Write_inv_def)
  apply simp
  apply (case_tac " (pc \<sigma>') t = WritePending  ") 
  apply (simp add:  Write_invocation_inv_def Write_inv_def  TML_Write_def)
  apply (cases "(pc \<sigma>) t" ;simp add: split if_splits)
  apply (cases "(pc \<sigma>') t" ;simp )
  apply (case_tac "  even (regs (\<tau> \<sigma>) t DTML.loc)")
  apply simp
  apply simp
  apply (case_tac " regs (\<tau> \<sigma>') t c1 = 0")
  apply simp
  apply simp
  apply (case_tac "  inLoc \<sigma> t \<notin> dom (log \<sigma>)")
  apply simp
  apply simp
  apply (metis PC.distinct(1217) PC.distinct(1257) PC.distinct(1295) PC.distinct(1331) PC.distinct(1365) PC.distinct(1397) PC.distinct(1427) PC.distinct(1455) PC.distinct(1481) PC.distinct(1639) emptyE insertE write_invocation_same)
  apply (simp add: Commit_invocation_inv_def)
  apply (smt(z3) PC.simps(1659) PC.simps(1660) PC.simps(1661) PC.simps(1662) PC.simps(1663) PC.simps(1664) PC.simps(1665) PC.simps(1666) PC.simps(1667) PC.simps(1668) PC.simps(1681))
  apply (simp add: Begin_Response_inv_def)
  apply (smt(z3) PC.simps(1659) PC.simps(1660) PC.simps(1661) PC.simps(1662) PC.simps(1663) PC.simps(1664) PC.simps(1665) PC.simps(1666) PC.simps(1667) PC.simps(1668) PC.simps(1681))
  apply (simp add: Read_Response_inv_def)
  apply (smt(z3) PC.simps(1659) PC.simps(1660) PC.simps(1661) PC.simps(1662) PC.simps(1663) PC.simps(1664) PC.simps(1665) PC.simps(1666) PC.simps(1667) PC.simps(1668) PC.simps(1681))
  apply (subgoal_tac" Write_Response_inv t ( WriteResponding) \<sigma>' = Write_inv t ( WriteResponding) \<sigma>' ")
  prefer 2
  apply (simp add: Write_Response_inv_def Write_inv_def)
  apply simp
  using  Write_local[where \<sigma> = \<sigma> and \<sigma>' = \<sigma>' and t =t  ]
    DTML_total_persistent_invariant_def [where \<sigma> = \<sigma>] 
  apply (smt (verit) PC.distinct(1175) PC.distinct(1217) PC.distinct(1257) PC.distinct(1295) PC.distinct(1331) PC.distinct(1365) PC.distinct(1397) PC.distinct(1427) PC.distinct(1455) PC.distinct(1639) assms(1) insert_iff singleton_iff write_response_same)
  using Commit_Response_inv_def apply presburger
    (**********************)
  apply (case_tac " ((pc \<sigma>) t) \<notin>  {PC.CommitPending, PC.CommitResponding } \<union> committing  \<union> {PC.Aborted}  ")
  using Commit_not_pcs apply blast  
  apply (subgoal_tac "  ((pc \<sigma>') t) \<in> {PC.CommitPending, PC.CommitResponding } \<union>  committing  \<union> {PC.Aborted} ")
  prefer 2
  using Commit_pcs apply presburger
  apply (intro conjI impI)
  apply (metis assms(1) commit_begin_inv_same)
  apply (metis Commit_local assms(1))
  apply blast
  apply (metis assms(1) commit_read_inv_same)
  apply (metis assms(1) commit_write_inv_same)
  apply (smt(z3) PC.distinct(11) PC.distinct(13) PC.distinct(15) PC.distinct(157) PC.distinct(17) PC.distinct(79) PC.distinct(87) PC.distinct(89) PC.distinct(9) PC.distinct(91) PC.distinct(93) PC.distinct(95) Un_insert_left begin_invocation_same emptyE insertE insert_commute insert_iff singletonD sup_assoc sup_bot_left)
  apply (smt (verit) PC.distinct(1639) PC.distinct(391) PC.distinct(447) PC.distinct(459) PC.distinct(515) PC.distinct(525) PC.distinct(581) PC.distinct(589) PC.distinct(645) PC.distinct(651) PC.distinct(707) PC.distinct(827) Un_insert_left emptyE insertE insert_commute insert_iff read_invocation_same singletonD sup_assoc sup_bot_left)
  apply (smt (verit) PC.distinct(1177) PC.distinct(1639) PC.distinct(405) PC.distinct(447) PC.distinct(473) PC.distinct(515) PC.distinct(539) PC.distinct(581) PC.distinct(603) PC.distinct(645) PC.distinct(665) PC.distinct(707) Un_insert_left emptyE insertE insert_commute insert_iff singletonD sup_assoc sup_bot_left write_invocation_same)
  apply (subgoal_tac" Commit_invocation_inv t (CommitPending) \<sigma>' = Commit_inv t (CommitPending) \<sigma>' ")
  prefer 2
  apply (simp add:   Commit_invocation_inv_def Commit_inv_def)
  apply (metis (no_types, opaque_lifting) Commit_local PC.distinct(1639) PC.distinct(447) PC.distinct(515) PC.distinct(581) PC.distinct(645) PC.distinct(707) Un_insert_left assms(1) commit_invocation_same emptyE insertE sup_bot_left)
  apply (metis (no_types, opaque_lifting) PC.distinct(1639) PC.distinct(309) PC.distinct(311) PC.distinct(313) PC.distinct(315) PC.distinct(317) PC.distinct(379) PC.distinct(447) PC.distinct(515) PC.distinct(581) PC.distinct(645) PC.distinct(707) Un_insert_right begin_response_same empty_iff insert_iff sup_bot_right)
  apply (metis (no_types, opaque_lifting) PC.distinct(1133) PC.distinct(1639) PC.distinct(403) PC.distinct(447) PC.distinct(471) PC.distinct(515) PC.distinct(537) PC.distinct(581) PC.distinct(601) PC.distinct(645) PC.distinct(663) PC.distinct(707) Un_insert_right empty_iff insert_iff read_response_same sup_bot_right)
  apply (metis (no_types, opaque_lifting) PC.distinct(1483) PC.distinct(1639) PC.distinct(423) PC.distinct(447) PC.distinct(491) PC.distinct(515) PC.distinct(557) PC.distinct(581) PC.distinct(621) PC.distinct(645) PC.distinct(683) PC.distinct(707) Un_insert_right empty_iff insert_iff sup_bot_right write_response_same)
  using Commit_Response_inv_def apply presburger
    (**************************)
  apply (case_tac " ((pc \<sigma>) t) \<notin>  {PC.NotStarted, PC.BeginPending }   ")
  using begin_Invocation_\<sigma> apply auto[1]
  apply (subgoal_tac "  ((pc \<sigma>') t) \<in> { PC.BeginPending } ")
  prefer 2
  apply (simp add:  TML_Begin_invocation_def)
  apply (cases "(pc \<sigma>) t" ;simp)

  apply (intro conjI impI)
  apply (subgoal_tac" Begin_invocation_inv t (BeginPending) \<sigma>' = Begin_inv t (BeginPending) \<sigma>' ")
  prefer 2
  using beginPending_same apply presburger
  using TML_Begin_invocation_def
  apply (metis Begin_invocation_local assms(1) singletonD)
  apply (metis PC.distinct(157) PC.distinct(87) PC.distinct(89) PC.distinct(91) PC.distinct(93) PC.distinct(95) Un_absorb Un_commute Un_insert_right commit_inv_same insertE singletonD)
  apply linarith
  apply (smt(verit) PC.distinct(101) PC.distinct(103) PC.distinct(105) PC.distinct(107) PC.distinct(109) PC.distinct(111) PC.distinct(157) PC.distinct(99) Un_insert_left Un_insert_right insert_commute insert_iff insert_is_Un read_inv_same singleton_iff)
  using Write_inv_def apply force
  using Begin_invocation_local assms(1) apply blast
  apply (metis PC.distinct(155) PC.distinct(99) insertE read_invocation_same singletonD)
  apply (metis PC.distinct(113) PC.distinct(155) insertE singletonD write_invocation_same)
  apply (metis PC.distinct(155) PC.distinct(87) commit_invocation_same insertE singletonD)
  apply (metis PC.distinct(155) PC.distinct(85) begin_response_same insertE singletonD)
  apply (metis PC.distinct(111) PC.distinct(155) insertE read_response_same singletonD)
  apply (metis PC.distinct(131) PC.distinct(155) insert_iff singleton_iff write_response_same)
  using Commit_Response_inv_def apply blast
    (****************************************)
  apply (case_tac " ((pc \<sigma>) t) \<notin>  {PC.BeginResponding, PC.Ready }   ")
  using begin_Response_\<sigma> apply auto[1]
  apply (subgoal_tac "  ((pc \<sigma>') t) \<in> { PC.Ready } ")
  prefer 2
  apply (simp add:  TML_Begin_response_def)
  apply (cases "(pc \<sigma>) t" ;simp)

  apply (intro conjI impI)
  apply (metis PC.distinct(155) PC.distinct(1639) PC.distinct(231) PC.distinct(305) PC.distinct(377) Un_absorb Un_commute Un_insert_right begin_inv_same insertE singletonD)
  using Commit_inv_def apply force
  apply blast
  apply (smt(verit) PC.distinct(1037) PC.distinct(1085) PC.distinct(1131) PC.distinct(1639) PC.distinct(825) PC.distinct(881) PC.distinct(935) PC.distinct(987) Un_insert_left Un_insert_right insert_commute insert_iff insert_is_Un read_inv_same singleton_iff)
  using Write_inv_def apply force
  apply (metis PC.distinct(155) PC.distinct(77) begin_invocation_same insertE singletonD)
  apply (metis Begin_Response_inv_def Begin_response_local PC.simps(1680) Read_invocation_inv_def assms(1) singletonD)
  apply (metis Begin_Response_inv_def Begin_response_local PC.simps(1680) Write_invocation_inv_def assms(1) singletonD)
  apply (metis Begin_Response_inv_def Begin_response_local Commit_invocation_inv_def PC.simps(1680) assms(1) singletonD)
  using Begin_response_local assms(1) apply blast
  apply (metis Begin_Response_inv_def Begin_response_local PC.simps(1680) Read_Response_inv_def assms(1) singletonD)
  apply (metis Begin_Response_inv_def Begin_response_local PC.simps(1680) Write_Response_inv_def assms(1) singletonD)
  using Commit_Response_inv_def apply blast
    (*****************************************)
  apply (case_tac " ((pc \<sigma>) t) \<notin>  {PC.ReadPending, PC.Ready }   ")
  using read_Invocation_\<sigma> apply auto[1]
  apply (subgoal_tac "  ((pc \<sigma>') t) \<in> { PC.ReadPending } ")
  prefer 2
  apply (simp add: TML_Read_invocation_def)
  apply (cases "(pc \<sigma>) t" ;simp)
  apply (intro conjI impI)
  apply (metis PC.distinct(175) PC.distinct(249) PC.distinct(321) PC.distinct(827) PC.distinct(99) Un_absorb Un_commute Un_insert_right begin_inv_same insertE singletonD)
  using Commit_inv_def apply force
  apply blast
  apply (smt (z3) PC.simps(1652) TML_Read_invocation_def assms(1) assms(4) DTML_total_program_annotations_def insert_iff ready_abort_commit_total)
  using Write_inv_def apply force
  apply (metis PC.distinct(21) PC.distinct(99) begin_invocation_same insertE singletonD)
  using Read_invocation_local assms(1) apply blast
  apply (metis PC.distinct(783) PC.distinct(825) insertE singletonD write_invocation_same)
  apply (metis PC.distinct(391) PC.distinct(825) commit_invocation_same insertE singletonD)
  apply (metis PC.distinct(321) PC.distinct(825) begin_response_same insertE singletonD)
  apply (metis PC.distinct(781) PC.distinct(825) insertE read_response_same singletonD)
  apply (metis PC.distinct(801) PC.distinct(825) insertE singletonD write_response_same)
  using Commit_Response_inv_def apply blast
    (**************************************)
  apply (case_tac " ((pc \<sigma>) t) \<notin>  {PC.ReadResponding, PC.Ready }   ")
  using read_Response_\<sigma> apply auto[1]
  apply (subgoal_tac "  ((pc \<sigma>') t) \<in> { PC.Ready} ")
  prefer 2
  apply (simp add: TML_Read_response_def)
  apply (cases "(pc \<sigma>) t" ;simp)
  apply (intro conjI impI)
  apply (metis PC.distinct(155) PC.distinct(1639) PC.distinct(231) PC.distinct(305) PC.distinct(377) Un_absorb Un_commute Un_insert_right begin_inv_same insertE singletonD)
  using Commit_inv_def apply force
  apply blast
  apply (smt(verit) PC.distinct(1037) PC.distinct(1085) PC.distinct(1131) PC.distinct(1639) PC.distinct(825) PC.distinct(881) PC.distinct(935) PC.distinct(987) Un_insert_left Un_insert_right insert_commute insert_iff insert_is_Un read_inv_same singleton_iff)
  using Write_inv_def apply force
  apply (metis PC.distinct(155) PC.distinct(77) begin_invocation_same insertE singletonD)
  apply (smt (z3) PC.simps(1680) Read_Response_inv_def Read_invocation_inv_def Read_response_local assms(1) mem_Collect_eq singleton_conv2)
  apply (metis PC.simps(1680) Read_Response_inv_def Read_response_local Write_invocation_inv_def assms(1) singletonD)
  apply (metis Commit_invocation_inv_def PC.simps(1680) Read_Response_inv_def Read_response_local assms(1) singletonD)
  apply (smt (z3) Begin_Response_inv_def PC.simps(1680) Read_Response_inv_def Read_response_local assms(1) mem_Collect_eq singleton_conv2)
  using Read_response_local assms(1) apply blast
  apply (metis PC.simps(1680) Read_Response_inv_def Read_response_local Write_Response_inv_def assms(1) singletonD)
  using Commit_Response_inv_def apply presburger
    (**************************************)
  apply (case_tac " ((pc \<sigma>) t) \<notin>  {PC.WritePending, PC.Ready }   ")
  using write_Invocation_\<sigma> apply auto[1]
  apply (subgoal_tac "  ((pc \<sigma>') t) \<in> { PC.WritePending } ")
  prefer 2
  apply (simp add: TML_Write_invocation_def)
  apply (cases "(pc \<sigma>) t" ;simp)
  apply (intro conjI impI)
  apply (metis PC.distinct(113) PC.distinct(1177) PC.distinct(189) PC.distinct(263) PC.distinct(335) Un_absorb Un_commute Un_insert_right begin_inv_same insertE singletonD)
  apply (metis PC.distinct(1177) PC.distinct(405) PC.distinct(473) PC.distinct(539) PC.distinct(603) PC.distinct(665) Un_absorb Un_commute Un_insert_right commit_inv_same insertE singletonD)
  apply blast
  apply (smt(verit) PC.distinct(1043) PC.distinct(1089) PC.distinct(1177) PC.distinct(783) PC.distinct(839) PC.distinct(893) PC.distinct(945) PC.distinct(995) Un_insert_left Un_insert_right insert_commute insert_iff insert_is_Un read_inv_same singleton_iff)
  using  Write_inv_def Write_invocation_inv_def
  apply (smt (z3) PC.simps(1659) TML_Write_invocation_def assms(1) assms(4) DTML_total_program_annotations_def insert_iff ready_abort_commit_total singletonD)
  apply (metis PC.distinct(113) PC.distinct(35) begin_invocation_same insertE singletonD)
  apply (metis PC.distinct(1175) PC.distinct(783) insertE read_invocation_same singletonD)
  using Write_invocation_local assms(1) apply blast
  apply (metis PC.distinct(1175) PC.distinct(405) commit_invocation_same insertE singletonD)
  apply (metis PC.distinct(1175) PC.distinct(335) begin_response_same insertE singletonD)
  apply (metis PC.distinct(1089) PC.distinct(1175) insertE read_response_same singletonD)
  apply (metis PC.distinct(1151) PC.distinct(1175) insertE singletonD write_response_same)
  using Commit_Response_inv_def apply blast
    (*************************************)
  apply (case_tac " ((pc \<sigma>) t) \<notin>  {PC.WriteResponding, PC.Ready }   ")
  using write_Response_\<sigma> apply auto[1]
  apply (subgoal_tac "  ((pc \<sigma>') t) \<in> { PC.Ready } ")
  prefer 2
  apply (simp add: TML_Write_response_def)
  apply (cases "(pc \<sigma>) t" ;simp)
  apply (intro conjI impI)
  apply (metis PC.distinct(155) PC.distinct(1639) PC.distinct(231) PC.distinct(305) PC.distinct(377) Un_absorb Un_commute Un_insert_right begin_inv_same insertE singletonD)
  using Commit_inv_def apply force
  apply linarith
  apply (metis PC.distinct(1037) PC.distinct(1085) PC.distinct(1131) PC.distinct(1639) PC.distinct(825) PC.distinct(881) PC.distinct(935) PC.distinct(987) Un_empty_left Un_insert_left insertE read_inv_same singletonD)
  using Write_inv_def apply force
  apply (metis PC.distinct(155) PC.distinct(77) begin_invocation_same insertE singletonD)
  apply (metis PC.simps(1680) Read_invocation_inv_def Write_Response_inv_def Write_response_local assms(1) singletonD)
  apply (metis PC.simps(1680) Write_Response_inv_def Write_invocation_inv_def Write_response_local assms(1) singletonD)
  apply (metis Commit_invocation_inv_def PC.simps(1680) Write_Response_inv_def Write_response_local assms(1) singletonD)
  apply (metis Begin_Response_inv_def PC.simps(1680) Write_Response_inv_def Write_response_local assms(1) singletonD)
  apply (metis PC.simps(1680) Read_Response_inv_def Write_Response_inv_def Write_response_local assms(1) singletonD)
  using Write_response_local assms(1) apply blast
  using Commit_Response_inv_def apply blast
    (****************************)
  apply (case_tac " ((pc \<sigma>) t) \<notin>  {PC.CommitPending, PC.Ready }   ")
  using commit_Invocation_\<sigma> apply auto[1]
  using TML_Commit_invocation_def 
  apply (smt (z3) PC.simps(1646) assms(1) assms(4) DTML_total_program_annotations_def insert_iff ready_abort_commit_total)
    (******************************)
  apply (case_tac " ((pc \<sigma>) t) \<notin>  {PC.CommitResponding, PC.Committed }   ")
  using commit_Response_\<sigma> apply auto[1]
  apply (subgoal_tac "  ((pc \<sigma>') t) \<in> { PC.Committed } ")
  prefer 2
  apply (simp add: TML_Commit_response_def)
  apply (cases "(pc \<sigma>) t" ;simp)
  apply (intro conjI impI)
  apply (metis PC.distinct(173) PC.distinct(247) PC.distinct(319) PC.distinct(769) PC.distinct(97) Un_absorb Un_commute Un_insert_right begin_inv_same insertE singletonD)
  apply (metis PC.distinct(389) PC.distinct(457) PC.distinct(523) PC.distinct(587) PC.distinct(649) PC.distinct(769) Un_absorb Un_commute Un_insert_right commit_inv_same insertE singletonD)
  apply linarith
  apply (smt(verit) PC.distinct(711) PC.distinct(713) PC.distinct(715) PC.distinct(717) PC.distinct(719) PC.distinct(721) PC.distinct(723) PC.distinct(769) Un_insert_left insert_commute insert_iff insert_is_Un read_inv_same singleton_iff)
  using Write_inv_def apply force
  apply (metis PC.distinct(19) PC.distinct(97) begin_invocation_same insertE singletonD)
  apply (metis PC.distinct(711) PC.distinct(767) insertE read_invocation_same singletonD)
  apply (metis PC.distinct(725) PC.distinct(767) insertE singletonD write_invocation_same)
  apply (metis PC.distinct(389) PC.distinct(767) commit_invocation_same insertE singletonD)
  apply (metis PC.distinct(319) PC.distinct(767) begin_response_same insertE singletonD)
  apply (metis PC.distinct(723) PC.distinct(767) insertE read_response_same singletonD)
  apply (metis PC.distinct(743) PC.distinct(767) insertE singletonD write_response_same)
  using Commit_Response_inv_def apply presburger
  apply (metis Recover_local assms(1))
  apply (intro conjI impI)
  using DTML_total_persistent_invariant_def [where \<sigma> = \<sigma>]  Begin_Crash_global[where \<sigma> = \<sigma> and \<sigma>' = \<sigma>'  and t = t]
  using assms(1) apply fastforce
  using DTML_total_persistent_invariant_def [where \<sigma> = \<sigma>]  Commit_Crash_global[where \<sigma> = \<sigma> and \<sigma>' = \<sigma>'  and t = t]
  using assms(1) apply presburger
  using DTML_total_persistent_invariant_def [where \<sigma> = \<sigma>]  Recover_Crash_global[where \<sigma> = \<sigma> and \<sigma>' = \<sigma>'  ]
  apply (smt (z3) assms(1))
  using DTML_total_persistent_invariant_def [where \<sigma> = \<sigma>]  Read_Crash_global[where \<sigma> = \<sigma> and \<sigma>' = \<sigma>'  ]
  using assms(1) apply presburger
  using DTML_total_persistent_invariant_def [where \<sigma> = \<sigma>]  Write_Crash_global[where \<sigma> = \<sigma> and \<sigma>' = \<sigma>'  ]
  using assms(1) apply  presburger
  using Begin_invocation_Crash_global apply blast
  using Read_invocation_Crash_global apply blast
  using Write_invocation_Crash_global apply blast
  using Commit_invocation_Crash_global apply blast
  using Begin_response_Crash_global assms(1) apply presburger
  using Read_response_Crash_global apply blast
  using Write_response_Crash_global assms(1) apply blast
  using Commit_Response_inv_def by presburger






(*Lemma that establishes global correnctness of DTML*)
lemma global_correnctness_total :
assumes  "thrdsvars"
and  "  DTML_total_program_annotations t  ((pc \<sigma>) t)   \<sigma>"
and  "  DTML_total_program_annotations t'  ((pc \<sigma>) t')   \<sigma>"
and "DTML_total_persistent_invariant \<sigma>"
and " dTML  \<sigma> \<sigma>' t'"
and " t \<noteq> t' "
and "  total_wfs (\<tau> \<sigma>)"
shows  "  DTML_total_program_annotations  t ((pc \<sigma>') t) \<sigma>'"
  using assms 
  apply (simp add: dTML_def)
  apply (subgoal_tac "  pc \<sigma> syst \<noteq> RecIdle \<longrightarrow> (\<forall>t. t \<noteq> syst \<longrightarrow> pc \<sigma> t \<in> {NotStarted, Aborted, Committed})")
   prefer 2
  using DTML_total_persistent_invariant_def [where \<sigma> = \<sigma>]
   apply presburger
  apply (elim disjE conjE)
               apply (unfold  DTML_total_program_annotations_def)
               apply (intro conjI impI)
                      apply (case_tac "((pc \<sigma>) t') \<in>    {BeginPending,BeginResponding, Aborted} \<union> beginning
\<and>  pc \<sigma> t \<in> {BeginPending, BeginResponding, Aborted} \<union> beginning")
  using  Begin_Begin_global[where \<sigma> = \<sigma> and \<sigma>' = \<sigma>' and ta = t and tb = t' ]
                      apply (metis Un_insert_left assms(1) begin_same_\<sigma> insert_iff)
                      apply (smt (verit, best) begin_dt begin_inv_same begin_same_\<sigma> insert_commute)  
    (**************************)
                      apply (case_tac " pc \<sigma> t' \<in> {BeginPending, BeginResponding, Aborted} \<union> beginning \<and>
pc \<sigma> t \<in> {CommitPending, CommitResponding, Aborted} \<union> committing")

  using  Begin_Commit_global[where \<sigma> = \<sigma> and \<sigma>' = \<sigma>' and ta = t and tb = t' ]
  using assms(1) apply fastforce
                      apply (smt (verit) begin_dt begin_same_\<sigma> commit_inv_same insert_commute)
    (*************************)
                      apply (case_tac " ((pc \<sigma>) syst) \<in> {RecIdle } \<union> recovering \<and>
((pc \<sigma>) t') \<in> {BeginPending, BeginResponding,Aborted} \<union>  beginning   ")
                      apply (subgoal_tac "   pc \<sigma> syst \<noteq> RecIdle \<longrightarrow>
(\<forall>t. t \<noteq> syst \<longrightarrow> pc \<sigma> t \<in> {NotStarted, Aborted, Committed})")
                      prefer 2
                      apply (simp add: DTML_total_persistent_invariant_def)
  using Begin_Recover_global[where \<sigma> = \<sigma> and \<sigma>' = \<sigma>' and ta = t' ] 
                      apply (smt (z3) assms(1) begin_beginning_helping insert_commute)
                      apply (smt (verit, ccfv_threshold) begin_dt begin_same_\<sigma> insert_commute recover_inv_same)
    (*************************)
                      apply (case_tac "((pc \<sigma>) t) \<in> {ReadPending,ReadResponding, Aborted} \<union>  reading  \<and>
((pc \<sigma>) t') \<in> {BeginPending,BeginResponding, Aborted} \<union>  beginning   ")
  using Begin_Read_global[where \<sigma> = \<sigma> and \<sigma>' = \<sigma>' and tb = t' and ta = t  ]
  using assms(1) apply fastforce
                      apply (smt (verit, ccfv_SIG) begin_dt begin_same_\<sigma> insert_commute read_inv_same)
    (*************************)
                      apply (case_tac "((pc \<sigma>) t) \<in> {WritePending,WriteResponding, Aborted} \<union>  writing  \<and>
((pc \<sigma>) t') \<in> {BeginPending,BeginResponding,Aborted} \<union>  beginning   ")
  using Begin_Write_global[where \<sigma> = \<sigma> and \<sigma>' = \<sigma>' and tb = t' and ta = t  ]
  using assms(1) apply blast
  apply (smt (verit, ccfv_threshold) begin_dt begin_same_\<sigma> insert_commute write_inv_same)
  apply (smt (z3) Begin_Begin_invocation_global UnCI assms(1) begin_dt begin_invocation_same begin_same_\<sigma> insert_commute)
  apply (smt (z3) Begin_Read_invocation_global UnCI assms(1) begin_dt begin_same_\<sigma> insert_commute read_invocation_same)
  apply (smt (z3) Begin_Write_invocation_global UnCI assms(1) begin_dt begin_same_\<sigma> insert_commute write_invocation_same)
  apply (smt (verit) Begin_Commit_invocation_global UnCI assms(1) begin_dt begin_same_\<sigma> commit_invocation_same insert_commute)
  apply (smt (verit) Begin_Begin_response_global UnCI assms(1) assms(6) begin_dt begin_response_same begin_same_\<sigma> insert_commute)
  apply (smt (z3) Begin_Read_response_global UnCI assms(1) begin_dt begin_same_\<sigma> insert_commute read_response_same)
  apply (smt (verit) Begin_Write_response_global UnCI assms(1) begin_dt begin_same_\<sigma> insert_commute write_response_same)
  using Commit_Response_inv_def apply presburger
    (*************************)
  apply (subgoal_tac " total_wfs (\<tau> \<sigma>) \<and>
pm_inv \<sigma> \<and>
( \<forall>t. writer \<sigma> = Some t \<longrightarrow> odd (lastVal glb (\<tau> \<sigma>))) \<and>
( \<forall>t. writer \<sigma> = Some t \<longrightarrow> \<lceil>glb\<rceil>\<^sub>t \<tau> \<sigma> ) \<and>
glb_monotone_inv (\<tau> \<sigma>) \<and>
mem_tml_prop3 (\<tau> \<sigma>) \<and>
( ((pc \<sigma>) syst) \<noteq> RecIdle   \<longrightarrow> (\<forall> t  \<noteq> syst.  ((pc \<sigma>) t)   \<in> {NotStarted, Aborted, Committed})) \<and>
( \<forall>b. mem_tml_prop glb b (\<tau> \<sigma>))\<and>
(  pc \<sigma>  syst  = RecIdle \<longrightarrow> (\<forall>t. t \<noteq> syst \<and> pc \<sigma> t \<notin> {NotStarted, Aborted, Committed, Begin2, BeginPending} \<longrightarrow>
regs (\<tau> \<sigma>) t DTML.loc \<le> lastVal glb (\<tau> \<sigma>)))
")
  prefer 2
  using DTML_total_persistent_invariant_def [where \<sigma> = \<sigma>]
  apply presburger
    (*************************)
  apply (intro conjI impI)
  apply (case_tac "((pc \<sigma>) t) \<in> {BeginPending,BeginResponding, Aborted} \<union>  beginning  \<and>
((pc \<sigma>) t') \<in> {ReadPending,ReadResponding, Aborted} \<union> reading  ")      
  using  Read_Begin_global[where \<sigma> = \<sigma> and \<sigma>' = \<sigma>' and tb = t' and ta = t  ] 
  apply (simp add: Un_empty_right Un_insert_right assms(1) insert_commute)
  apply (smt (z3) Read_same_\<sigma> begin_inv_same insert_commute read_dt)
    (*************************)
  apply (case_tac "((pc \<sigma>) t) \<in> {CommitPending,CommitResponding, Aborted} \<union> committing  \<and>
((pc \<sigma>) t') \<in> {ReadPending,ReadResponding, Aborted} \<union> reading  ")
  using  Read_Commit_global[where \<sigma> = \<sigma> and \<sigma>' = \<sigma>' and tb = t' and ta = t  ]
  apply (metis Read_not_pcs assms(1))
  apply (smt (z3) Read_same_\<sigma> commit_inv_same insert_commute read_dt)
    (*************************)
  apply (case_tac "((pc \<sigma>) t) \<in> {RecIdle} \<union> recovering  \<and>
((pc \<sigma>) t') \<in> {ReadPending,ReadResponding, Aborted} \<union> reading  ")
  using   Read_Recover_global[where \<sigma> = \<sigma> and \<sigma>' = \<sigma>' and  ta = t'  ]
                      apply (metis Read_not_pcs assms(1))
  apply (smt (verit) Read_same_\<sigma> insert_commute read_dt recover_inv_same)
    (*************************)
  apply (case_tac "((pc \<sigma>) t) \<in> {ReadPending,ReadResponding, Aborted} \<union> reading  \<and>
((pc \<sigma>) t') \<in>  {ReadPending,ReadResponding, Aborted} \<union> reading    ")

  using  Read_Read_global[where \<sigma> = \<sigma> and \<sigma>' = \<sigma>' and tb = t' and ta = t  ]
  apply (simp add: insert_commute)
  apply (smt (z3) Read_same_\<sigma> insert_commute read_dt read_inv_same)
    (*************************)
  apply (case_tac "((pc \<sigma>) t) \<in>  {WritePending,WriteResponding,  Aborted} \<union> writing \<and>
((pc \<sigma>) t') \<in> {ReadPending,ReadResponding, Aborted} \<union> reading  ")
  using   Read_Write_global[where \<sigma> = \<sigma> and \<sigma>' = \<sigma>' and  ta = t  and tb = t' ]
  apply (smt (verit) Read_not_pcs Un_empty_right Un_insert_left Un_insert_right assms(1))
  apply (smt (z3) Read_same_\<sigma> insert_commute read_dt write_inv_same)
  using  Read_Begin_invocation_global
  apply (smt (verit) Read_same_\<sigma> UnCI begin_invocation_same insert_commute read_dt thrdsvars_def)
  using  Read_Begin_invocation_global
  apply (smt (z3) Read_Read_invocation_global Read_same_\<sigma> UnCI insert_commute read_dt read_invocation_same thrdsvars_def)
  using  Read_Write_invocation_global
  apply (smt (z3) Read_same_\<sigma> UnCI insert_commute read_dt thrdsvars_def write_invocation_same)
  using  Read_Commit_invocation_global 
  apply (smt (verit) Read_same_\<sigma> UnCI commit_invocation_same insert_commute read_dt thrdsvars_def)
  using  Read_Begin_response_global 
  apply (smt (z3) Read_same_\<sigma> UnCI begin_response_same insert_commute read_dt thrdsvars_def)
  using  Read_Read_response_global 
  apply (smt (verit) Read_same_\<sigma> UnCI insert_commute read_dt read_response_same thrdsvars_def)
  using  Read_Read_response_global
  apply (smt (verit) Read_Write_response_global Read_same_\<sigma> UnCI insert_commute read_dt thrdsvars_def write_response_same)
  using  Read_Write_response_global
  using Commit_Response_inv_def apply presburger
    (*************************)
  apply (subgoal_tac " total_wfs (\<tau> \<sigma>) \<and>
pm_inv \<sigma> \<and>
( \<forall>t. writer \<sigma> = Some t \<longrightarrow> odd (lastVal glb (\<tau> \<sigma>))) \<and>
( \<forall>t. writer \<sigma> = Some t \<longrightarrow> \<lceil>glb\<rceil>\<^sub>t \<tau> \<sigma> ) \<and>
glb_monotone_inv (\<tau> \<sigma>) \<and>
mem_tml_prop3 (\<tau> \<sigma>) \<and>
( ((pc \<sigma>) syst) \<noteq> RecIdle   \<longrightarrow> (\<forall> t  \<noteq> syst.  ((pc \<sigma>) t)   \<in> {NotStarted, Aborted, Committed})) \<and>
( \<forall>b. mem_tml_prop glb b (\<tau> \<sigma>))")
  prefer 2
  using DTML_total_persistent_invariant_def [where \<sigma> = \<sigma>]
  apply presburger
(**************************write*****************)
  apply (intro conjI impI)
  apply (case_tac "((pc \<sigma>) t) \<in>  {BeginPending,BeginResponding, Aborted} \<union> beginning   \<and>
((pc \<sigma>) t') \<in> {WritePending,WriteResponding, Aborted} \<union> writing ")
  using  Write_Begin_global[where \<sigma> = \<sigma> and \<sigma>' = \<sigma>' and tb = t' and ta = t  ]
  apply (metis UnE UnI1 UnI2 assms(1) insert_is_Un)
  apply (smt (verit, ccfv_SIG) begin_inv_same insert_commute write_dt write_same_\<sigma>)
    (************************************************)
  apply (case_tac "((pc \<sigma>) t) \<in>  {CommitPending,CommitResponding, Aborted} \<union> committing   \<and>
((pc \<sigma>) t') \<in> {WritePending,WriteResponding, Aborted} \<union> writing ")
  using  Write_Commit_global[where \<sigma> = \<sigma> and \<sigma>' = \<sigma>' and tb = t' and ta = t  ]
  apply (metis (no_types, lifting) Write_not_pcs assms(1))
  apply (smt (z3) commit_inv_same insert_commute write_dt write_same_\<sigma>)
    (************************************************)
  apply (case_tac "((pc \<sigma>) t) \<in>  {RecIdle} \<union> recovering  \<and>
((pc \<sigma>) t') \<in> {WritePending,WriteResponding, Aborted} \<union> writing ")
  using  Write_Recover_global[where \<sigma> = \<sigma> and \<sigma>' = \<sigma>' and ta = t'  ]
  apply (simp add: insert_commute)
  apply (smt (verit) Write_not_pcs \<open>\<lbrakk>thrdsvars; total_wfs (\<tau> \<sigma>); pm_inv \<sigma>; \<forall>t. writer \<sigma> = Some t \<longrightarrow> odd (lastVal glb (\<tau> \<sigma>)); \<forall>t. writer \<sigma> = Some t \<longrightarrow> \<lceil>glb\<rceil>\<^sub>t \<tau> \<sigma>; pc \<sigma> syst \<noteq> RecIdle \<longrightarrow> (\<forall>t. t \<noteq> syst \<longrightarrow> pc \<sigma> t \<in> {NotStarted, Aborted, Committed}); glb_monotone_inv (\<tau> \<sigma>); Recover_inv syst (pc \<sigma> syst) \<sigma>; Write_inv t' (pc \<sigma> t') \<sigma>; TML_Write t' \<sigma> \<sigma>'; pc \<sigma> t' \<in> {WritePending, WriteResponding} \<union> writing \<union> {Aborted}; pc \<sigma> syst \<in> {RecIdle} \<union> recovering; t' \<noteq> syst\<rbrakk> \<Longrightarrow> Recover_inv syst (pc \<sigma>' syst) \<sigma>'\<close> assms(1) recover_inv_same write_dt)
    (************************************************)
  apply (case_tac "((pc \<sigma>) t) \<in>  {Aborted,ReadPending,ReadResponding} \<union> reading  \<and>
((pc \<sigma>) t') \<in> {WritePending,WriteResponding, Aborted} \<union> writing ")
  using  Write_Read_global[where \<sigma> = \<sigma> and \<sigma>' = \<sigma>' and tb = t' and ta = t  ]
  apply (simp add: insert_commute)
  apply (smt (verit) Un_insert_right Write_not_pcs boolean_algebra.disj_zero_right inf_sup_aci(5) insert_commute read_inv_same write_dt)
    (************************************************)
  apply (case_tac "((pc \<sigma>) t) \<in>  {Aborted,WritePending,WriteResponding} \<union> writing  \<and>
((pc \<sigma>) t') \<in> {WritePending,WriteResponding, Aborted} \<union> writing ")
  using  Write_Write_global[where \<sigma> = \<sigma> and \<sigma>' = \<sigma>' and tb = t' and ta = t  ]
  apply (simp add: insert_commute)
  apply (smt (verit) insert_commute write_dt write_inv_same write_same_\<sigma>)
  using assms(1)  Write_Begin_invocation_global[where ta = t and tb = t' and \<sigma> = \<sigma>
      and \<sigma>' = \<sigma>']
  apply (metis (no_types, lifting) UnI1 Write_not_pcs begin_invocation_same write_dt)
  apply (case_tac "    pc \<sigma> t \<in> {ReadPending, Ready} \<union> {Aborted} \<and>
pc \<sigma> t' \<in> {Aborted, WritePending, WriteResponding} \<union> writing ")
  using assms(1)  Write_Read_invocation_global[where ta = t and tb = t' and \<sigma> = \<sigma>
      and \<sigma>' = \<sigma>']            
  apply (smt (verit) Write_not_pcs Un_empty_right Un_insert_left Un_insert_right assms(1))
  using  Write_Read_invocation_global write_same_\<sigma>
  apply (smt (z3) UnI1 Un_insert_left Un_insert_right read_invocation_same write_dt)
  using assms(1)  Write_Write_invocation_global[where ta = t and tb = t' and \<sigma> = \<sigma>
      and \<sigma>' = \<sigma>']    
  apply (smt (z3) Un_commute insert_commute insert_iff insert_is_Un write_dt write_invocation_same write_same_\<sigma>)
  using assms(1)  Write_Commit_invocation_global[where ta = t and tb = t' and \<sigma> = \<sigma>
      and \<sigma>' = \<sigma>']  
  apply (smt (verit) UnI1 Un_empty_right Un_insert_left Un_insert_right Write_not_pcs commit_invocation_same write_dt)
  using assms(1)  Write_Begin_response_global[where ta = t and tb = t' and \<sigma> = \<sigma>
      and \<sigma>' = \<sigma>']  
  apply (metis (no_types, lifting) UnI1 Write_not_pcs begin_response_same write_dt)
  using assms(1)  Write_Read_response_global[where ta = t and tb = t' and \<sigma> = \<sigma>
      and \<sigma>' = \<sigma>']  
  using  Write_not_pcs read_response_same
  apply (smt (verit) UnI1 Un_empty_right Un_insert_left Un_insert_right write_dt)
  using assms(1)   Write_Write_reponse_global[where ta = t and tb = t' and \<sigma> = \<sigma>
      and \<sigma>' = \<sigma>']  
  apply (smt (z3) Un_commute insertCI insert_commute insert_is_Un write_dt write_response_same write_same_\<sigma>)
  using Commit_Response_inv_def apply presburger
    (************************commit******************************)
  apply (subgoal_tac " total_wfs (\<tau> \<sigma>) \<and>
pm_inv \<sigma> \<and>
( \<forall>t. writer \<sigma> = Some t \<longrightarrow> odd (lastVal glb (\<tau> \<sigma>))) \<and>
( \<forall>t. writer \<sigma> = Some t \<longrightarrow> \<lceil>glb\<rceil>\<^sub>t \<tau> \<sigma> ) \<and>
glb_monotone_inv (\<tau> \<sigma>) \<and>
mem_tml_prop3 (\<tau> \<sigma>) \<and>
( ((pc \<sigma>) syst) \<noteq> RecIdle   \<longrightarrow> (\<forall> t  \<noteq> syst.  ((pc \<sigma>) t)   \<in> {NotStarted, Aborted, Committed})) \<and>
( \<forall>b. mem_tml_prop glb b (\<tau> \<sigma>))\<and>
(  pc \<sigma>  syst  = RecIdle \<longrightarrow> (\<forall>t. t \<noteq> syst \<and> pc \<sigma> t \<notin> {NotStarted, BeginPending,Aborted, Committed, Begin2} \<longrightarrow>
regs (\<tau> \<sigma>) t DTML.loc \<le> lastVal glb (\<tau> \<sigma>)))
")
  prefer 2
  using DTML_total_persistent_invariant_def [where \<sigma> = \<sigma>]
  apply (smt (verit) assms(4) insert_commute)
    (************************************************)
  apply (intro conjI impI)
  apply (case_tac "((pc \<sigma>) t) \<in>  {Ready, Aborted} \<union> beginning   \<and>
((pc \<sigma>) t') \<in> {Ready, Aborted} \<union> committing ")
  using  Commit_Begin_global[where \<sigma> = \<sigma> and \<sigma>' = \<sigma>' and tb = t' and ta = t  ]
  using assms(1)
  apply (smt (verit) begin_inv_same commit_dt commit_same_\<sigma> insert_commute)
  apply (smt (verit) \<open>\<lbrakk>thrdsvars; total_wfs (\<tau> \<sigma>); pm_inv \<sigma>; t \<noteq> t'; Begin_inv t (pc \<sigma> t) \<sigma>; Commit_inv t' (pc \<sigma> t') \<sigma>; TML_Commit t' \<sigma> \<sigma>'; pc \<sigma> t' \<in> {CommitPending, CommitResponding, Aborted} \<union> committing; pc \<sigma> t \<in> {BeginPending, BeginResponding, Aborted} \<union> beginning; t \<noteq> syst; t' \<noteq> syst; t \<noteq> t'\<rbrakk> \<Longrightarrow> Begin_inv t (pc \<sigma>' t) \<sigma>'\<close> assms(1) begin_inv_same commit_dt commit_same_\<sigma> insert_commute)
    (************************************************)
  apply (case_tac "((pc \<sigma>) t) \<in>  {BeginPending,BeginResponding, Aborted} \<union> committing   \<and>
((pc \<sigma>) t') \<in> {CommitPending,CommitResponding, Aborted} \<union> committing ")
  using  Commit_Commit_global[where \<sigma> = \<sigma> and \<sigma>' = \<sigma>' and tb = t' and ta = t  ]
  using assms(1)
  apply (metis (no_types, lifting) commit_dt commit_inv_same insert_commute)
  apply (smt (z3) \<open>\<lbrakk>thrdsvars; total_wfs (\<tau> \<sigma>); pm_inv \<sigma>; t \<noteq> t'; Commit_inv t (pc \<sigma> t) \<sigma>; Commit_inv t' (pc \<sigma> t') \<sigma>; TML_Commit t' \<sigma> \<sigma>'; pc \<sigma> t' \<in> {CommitPending, CommitResponding, Aborted} \<union> committing; pc \<sigma> t \<in> {CommitPending, CommitResponding, Aborted} \<union> committing; t \<noteq> syst; t' \<noteq> syst; t \<noteq> t'\<rbrakk> \<Longrightarrow> Commit_inv t (pc \<sigma>' t) \<sigma>'\<close> assms(1) commit_dt commit_inv_same commit_same_\<sigma> insert_commute)
    (************************************************)
  apply (case_tac "((pc \<sigma>) t) \<in>  {RecIdle} \<union> recovering   \<and>
((pc \<sigma>) t') \<in> {CommitPending,CommitResponding,  Aborted} \<union> committing ")
  using  Commit_Recover_global[where \<sigma> = \<sigma> and \<sigma>' = \<sigma>' ]
  apply (smt (z3) Un_assoc Un_commute assms(1) insert_is_Un)
  apply (smt (verit) Commit_Recover_global Commit_not_pcs assms(1) commit_dt recover_inv_same)
    (************************************************)
  apply (case_tac "((pc \<sigma>) t) \<in>  {ReadPending,ReadResponding, Aborted} \<union> reading   \<and>
((pc \<sigma>) t') \<in> {CommitPending,CommitResponding,  Aborted} \<union> committing ")
  using  Commit_Read_global[where \<sigma> = \<sigma> and \<sigma>' = \<sigma>' and tb = t' and ta = t  ]
  apply (smt(z3) Un_commute Un_empty_right Un_insert_right assms(1) insert_iff)
  apply (smt (z3) commit_dt commit_same_\<sigma> insert_commute read_inv_same)
    (************************************************)
  apply (case_tac "((pc \<sigma>) t) \<in>  {WritePending,WriteResponding,  Aborted} \<union> writing   \<and>
((pc \<sigma>) t') \<in> {CommitPending,CommitResponding, Aborted} \<union> committing ")
  using  Commit_Write_global[where \<sigma> = \<sigma> and \<sigma>' = \<sigma>' and tb = t' and ta = t  ]
  apply force
  apply (smt (verit) commit_dt commit_same_\<sigma> insert_commute write_inv_same)
  using assms(1)  Commit_Begin_invocation_global[where ta = t and tb = t' and \<sigma> = \<sigma>
      and \<sigma>' = \<sigma>']
  apply (metis (no_types, lifting) Commit_not_pcs UnCI begin_invocation_same commit_dt)
  using assms(1)  Commit_Read_invocation_global[where ta = t and tb = t' and \<sigma> = \<sigma>
      and \<sigma>' = \<sigma>']                       
  apply (smt (verit) Commit_not_pcs Un_empty_right Un_insert_right commit_dt in_mono insert_commute read_invocation_same sup.cobounded1)
  using assms(1)  Commit_Write_invocation_global[where ta = t and tb = t' and \<sigma> = \<sigma>
      and \<sigma>' = \<sigma>'] 
  apply (metis Commit_not_pcs UnI1 Un_empty_right Un_insert_left Un_insert_right commit_dt write_invocation_same)
  apply (smt (verit) Commit_Commit_invocation_global Commit_not_pcs UnI1 Un_empty_right Un_insert_left Un_insert_right assms(1) commit_dt commit_invocation_same)
  apply (smt (verit, ccfv_SIG) Commit_Begin_response_global Commit_not_pcs UnI1 assms(1) begin_response_same commit_dt)
  using  Commit_Read_response_global[where ta = t and tb = t' and \<sigma> = \<sigma>
      and \<sigma>' = \<sigma>'] 
  apply (smt (verit) Commit_not_pcs Un_empty_right Un_insert_right assms(1) commit_dt inf_sup_ord(3) insert_commute read_response_same subset_iff)
  apply (smt (verit) Commit_Write_response_global Commit_not_pcs UnI1 Un_empty_right Un_insert_left Un_insert_right assms(1) commit_dt write_response_same)
  using Commit_Response_inv_def apply presburger
(**********************TML_BeginInvocation***************************)
  apply (intro conjI impI)
  apply (case_tac "  pc \<sigma> t'
\<in> {BeginPending, NotStarted} \<union> {Aborted} \<and>
pc \<sigma> t
\<in> {Aborted, BeginPending, BeginResponding} \<union>
beginning")
  using  Begin_invocation_Begin_global[where ta = t' and tb = t and \<sigma> = \<sigma>]
  using assms(1) apply presburger
  apply (smt (verit, ccfv_SIG) Begin_Invocation_not_pcs begin_inv_dt begin_inv_same insert_commute)
  apply (smt (z3) Begin_Invocation_not_pcs Begin_invocation_Commit_global Un_empty_right Un_insert_left Un_insert_right assms(1) begin_inv_dt commit_inv_same)
  apply (case_tac "   pc \<sigma> t' \<in> {BeginPending, NotStarted} \<union> {Aborted} \<and>
pc \<sigma> syst \<in> {RecIdle} \<union> recovering")
  using Begin_invocation_Recover_global[where ta = t'  and \<sigma> = \<sigma>] 
  using assms(1) apply presburger
  apply (smt (verit, ccfv_SIG) Begin_Invocation_not_pcs begin_inv_dt recover_inv_same)
  using  Begin_invocation_Read_global 
  apply (smt (verit) Begin_Invocation_not_pcs begin_inv_dt insert_commute read_inv_same thrdsvars_def)
  using Begin_invocation_Write_global[where ta = t'  and \<sigma> = \<sigma>] 
  apply (smt (verit) Begin_Invocation_not_pcs Un_insert_left Un_insert_right assms(1) assms(6) assms(7) begin_inv_dt sup_bot.right_neutral write_inv_same)
  apply (smt (z3) Begin_invocation_Begin_invocation_global assms(1) begin_Invocation_\<sigma> begin_inv_dt begin_invocation_same insertCI)
  apply (smt (verit, ccfv_threshold) Begin_Invocation_not_pcs Begin_invocation_Read_invocation_global UnI1 Un_empty_right Un_insert_right assms(1) begin_inv_dt read_invocation_same)
  apply (smt (verit, best) Begin_invocation_Write_invocation_global assms(1) begin_Invocation_\<sigma> begin_inv_dt insertCI write_invocation_same)
  apply (smt (verit, ccfv_threshold) Begin_Invocation_not_pcs Begin_invocation_Commit_invocation_global UnI1 Un_empty_right Un_insert_right assms(1) begin_inv_dt commit_invocation_same)
  apply (smt (verit, ccfv_threshold) Begin_Invocation_not_pcs Begin_invocation_Begin_response_global UnI1 Un_empty_right Un_insert_right assms(1) begin_inv_dt begin_response_same)
  apply (smt (z3) Begin_invocation_Read_response_global assms(1) begin_Invocation_\<sigma> begin_inv_dt insertCI read_response_same)
  apply (smt (verit, ccfv_threshold) Begin_Invocation_not_pcs Begin_invocation_Write_response_global UnI1 Un_empty_right Un_insert_right assms(1) begin_inv_dt write_response_same)
  using Commit_Response_inv_def apply presburger
    (**********************TML_BeginResponse***************************)
  apply (intro conjI impI)
  apply (smt (verit) Begin_response_Begin_global UnCI assms(1) begin_Response_\<sigma> begin_inv_same begin_resp_dt insert_commute)
  apply (smt (z3) Begin_response_Commit_global UnCI Un_insert_left Un_insert_right assms(1) begin_Response_\<sigma> begin_resp_dt commit_inv_same)
  using  Begin_response_Recover_global[where ta = t' and \<sigma> = \<sigma> and \<sigma>' = \<sigma>']
  apply (smt (z3) UnI1 assms(1) begin_Response_\<sigma> begin_resp_dt recover_inv_same)
  using Begin_response_Read_global  
  apply (smt (z3) Un_iff begin_Response_\<sigma> begin_resp_dt insert_commute read_inv_same thrdsvars_def)
  using  Begin_Response_Write_global
  apply (smt (verit) Un_commute Un_left_commute begin_Response_\<sigma> begin_resp_dt insert_iff insert_is_Un thrdsvars_def write_inv_same)
  apply (smt (verit) Begin_response_Begin_invocation_global assms(1) assms(6) assms(7) begin_Response_\<sigma> begin_invocation_same begin_resp_dt insertCI)
  apply (smt (verit) Begin_response_Read_invocation_global assms(1) begin_Response_\<sigma> begin_resp_dt insertCI read_invocation_same)
  apply (smt (verit, ccfv_SIG) Begin_response_Write_invocation_global assms(1) begin_Response_\<sigma> begin_resp_dt insertCI write_invocation_same)
  apply (smt (verit) Begin_response_Commit_invocation_global assms(1) begin_Response_\<sigma> begin_resp_dt commit_invocation_same insertCI)
  apply (smt (verit) Begin_response_Begin_response_global assms(1) begin_Response_\<sigma> begin_resp_dt begin_response_same insertCI)
  apply (smt (verit) Begin_response_Read_response_global assms(1) assms(6) begin_Response_\<sigma> begin_resp_dt insertCI read_response_same)
  apply (smt (verit) Begin_response_Write_response_global assms(1) begin_Response_\<sigma> begin_resp_dt insertCI write_response_same)
  using Commit_Response_inv_def apply presburger
    (**********************TML_Readinvocation***************************)
  apply (intro conjI impI)
  apply (case_tac "   pc \<sigma> t' \<in> {ReadPending, Ready} \<union> {Aborted} \<and>
pc \<sigma> t \<in> {Aborted, BeginPending, BeginResponding} \<union> beginning ")
  using  Read_invocation_Begin_global[where ta = t' and tb  = t and  \<sigma> = \<sigma> and \<sigma>' = \<sigma>']
  using assms(1) apply presburger
  using  read_Invocation_\<sigma>  read_inv_dt  read_invocation_same 
  apply (smt (verit) Un_iff begin_inv_same insert_iff)
  using  Read_invocation_Commit_global[where ta = t' and tb  = t and  \<sigma> = \<sigma> and \<sigma>' = \<sigma>']
  apply (smt (verit) Read_Invocation_not_pcs Un_insert_right assms(1) assms(6) commit_inv_same insert_commute read_inv_dt sup_bot.right_neutral)
  using  Read_invocation_Recover_global[where ta = t' and \<sigma> = \<sigma> and \<sigma>' = \<sigma>']
  apply (smt (z3) Read_Invocation_not_pcs assms(1) read_inv_dt recover_inv_same)
  using  Read_invocation_Read_global[where ta = t' and tb  = t and  \<sigma> = \<sigma> and \<sigma>' = \<sigma>']
  apply (smt (verit, ccfv_SIG) assms(1) inf_sup_aci(5) insertI1 insert_absorb insert_commute insert_is_Un read_Invocation_\<sigma> read_inv_same  read_inv_dt)
  using  Read_invocation_Write_global[where ta = t' and tb  = t and  \<sigma> = \<sigma> and \<sigma>' = \<sigma>']
  apply (smt (verit) Read_Invocation_not_pcs assms(1) insert_commute  read_inv_dt write_inv_same)
  apply (smt (z3) Read_Invocation_not_pcs Read_invocation_Begin_invocation_global Un_empty_right Un_insert_right assms(1) begin_invocation_same insertCI  read_inv_dt)
  apply (smt (verit, del_insts) Read_invocation_Read_invocation_global assms(1) insertI2 read_Invocation_\<sigma> read_inv_dt read_invocation_same singletonD)
  apply (smt (verit) Read_Invocation_not_pcs Read_invocation_Write_invocation_global Un_empty_right Un_insert_right assms(1) insertCI  read_inv_dt write_invocation_same)
  apply (smt (verit) Read_Invocation_not_pcs Read_invocation_Commit_invocation_global Un_empty_right Un_insert_right assms(1) commit_invocation_same insertCI  read_inv_dt)
  apply (smt (verit) Read_Invocation_not_pcs Read_invocation_Begin_response_global Un_empty_right Un_insert_right assms(1) begin_response_same insertCI  read_inv_dt)
  apply (smt (verit, ccfv_threshold) Read_Invocation_not_pcs Read_invocation_Read_response_global UnI1 Un_empty_right Un_insert_right assms(1)  read_inv_dt read_response_same)
  apply (smt (z3) Read_Invocation_not_pcs Read_invocation_Write_response_global UnI1 Un_empty_right Un_insert_right assms(1) assms(7)  read_inv_dt write_response_same)
  using Commit_Response_inv_def apply presburger
    (*******************TML_Read_Response******************)
  apply (intro conjI impI)
  apply (smt (z3) Read_response_Begin_global Un_empty_right Un_insert_left Un_insert_right assms(1) begin_inv_same insertCI read_Response_\<sigma>  read_resp_dt )
  using Read_response_Commit_global 
  apply (smt (z3) Un_commute Un_insert_right assms(1) commit_inv_same insert_iff read_Response_\<sigma> read_resp_dt singleton_iff)
  using Read_response_Recover_global 
  apply (smt (verit, ccfv_SIG) Un_iff read_Response_\<sigma>  read_resp_dt  recover_inv_same thrdsvars_def)
  apply (smt (verit, ccfv_threshold) Read_response_Read_global Un_empty_right Un_insert_right assms(1) insertCI insert_commute read_Response_\<sigma> read_inv_same  read_resp_dt )
  using  Read_response_Write_global 
  apply (smt (verit) Un_insert_left Un_insert_right insertCI insert_is_Un read_Response_\<sigma>  read_resp_dt  thrdsvars_def write_inv_same)
  apply (smt (verit, ccfv_SIG) Read_response_Begin_invocation_global assms(1) begin_invocation_same insertCI read_Response_\<sigma>  read_resp_dt )
  using Read_response_Read_invocation_global
  apply (smt (z3) insert_iff read_Response_\<sigma> read_invocation_same  read_resp_dt  thrdsvars_def)
  apply (smt (verit, del_insts) Read_response_Write_invocation_global assms(1) insertCI read_Response_\<sigma>  read_resp_dt write_invocation_same)
  apply (smt (verit) Read_response_Commit_invocation_global assms(1) commit_invocation_same insertCI read_Response_\<sigma>  read_resp_dt )
  apply (smt (verit, best) Read_response_Begin_response_global assms(1) begin_response_same insertCI read_Response_\<sigma>  read_resp_dt )
  apply (smt (z3) Read_response_Read_response_global assms(1) insertCI read_Response_\<sigma>  read_resp_dt  read_response_same)
  apply (smt (verit, best) Read_reasponse_Write_response_global assms(1) insertCI read_Response_\<sigma>  read_resp_dt  write_response_same)
  using Commit_Response_inv_def apply presburger
    (*********** TML_Write_invocation****************)
  apply (intro conjI impI)
  apply (smt (z3) Un_insert_left Write_Invocation_not_pcs Write_invocation_Begin_global assms(1) begin_inv_same insertCI insert_commute write_inv_dt)
  apply (smt (verit) Write_Invocation_not_pcs Write_invocation_Commit_global assms(1) commit_inv_same insert_commute write_inv_dt)
  using Write_invocation_Recover_global
  apply (smt (verit, best) Write_Invocation_not_pcs recover_inv_same thrdsvars_def write_inv_dt)
  apply (smt (verit, best) Write_Invocation_not_pcs Write_invocation_Read_global assms(1) insert_commute read_inv_same write_inv_dt)
  using  Write_invocation_Write_global
  apply (smt (verit) Write_Invocation_not_pcs insert_commute thrdsvars_def write_inv_same write_inv_dt)
  apply (smt (z3) UnI1 Un_empty_right Un_insert_right Write_Invocation_not_pcs Write_invocation_Begin_invocation_global assms(1) begin_invocation_same write_inv_dt)
  apply (smt (verit, ccfv_threshold) Write_invocation_Read_invocation_global assms(1) insertCI read_invocation_same write_Invocation_\<sigma> write_inv_dt)
  apply (smt (verit, ccfv_threshold) Write_invocation_Write_invocation_global assms(1) insertCI write_Invocation_\<sigma> write_inv_dt write_invocation_same)
  apply (smt (verit, ccfv_threshold) Write_invocation_Commit_invocation_global assms(1) commit_invocation_same insertCI write_Invocation_\<sigma> write_inv_dt)
  apply (smt (z3) Write_invocation_Begin_response_global assms(1) begin_response_same insertCI write_Invocation_\<sigma> write_inv_dt)
  using  Write_invocation_Read_response_global
  apply (smt (z3) UnI1 Un_empty_right Un_insert_right Write_Invocation_not_pcs read_response_same thrdsvars_def write_inv_dt)
  apply (smt (z3) UnI1 Un_empty_right Un_insert_right Write_Invocation_not_pcs Write_invocation_Write_response_global assms(1) assms(6) assms(7) write_inv_dt write_response_same)
  using Commit_Response_inv_def apply blast
    (******************TML_WriteResponse************)
  apply (intro conjI impI)
  apply (smt (z3) Un_empty_right Un_insert_left Un_insert_right Write_response_Begin_global assms(1) begin_inv_same insertCI write_Response_\<sigma> write_resp_dt)
  apply (smt (z3) Un_empty_right Un_insert_right Write_response_Commit_global assms(1) commit_inv_same insertCI insert_commute write_Response_\<sigma> write_resp_dt)
  using Write_response_Recover_global
  apply (smt (verit) Un_iff recover_inv_same thrdsvars_def write_Response_\<sigma> write_resp_dt)
  apply (smt (verit, ccfv_threshold) Un_empty_right Un_insert_right Write_response_Read_global assms(1) insertCI insert_commute read_inv_same write_Response_\<sigma> write_resp_dt)
  using Write_response_Write_global
  apply (smt (verit) Un_commute Un_empty_right Un_insert_right assms(7) insertCI insert_commute thrdsvars_def write_Response_\<sigma> write_inv_same write_resp_dt)
  apply (smt (z3) Write_response_Begin_invocation_global assms(1) begin_invocation_same insertCI write_Response_\<sigma> write_resp_dt)
  apply (smt (verit, best) Write_response_Read_invocation_global assms(1) insertI2 read_invocation_same singletonD write_Response_\<sigma> write_resp_dt)
  apply (smt (z3) Write_response_Write_invocation_global assms(1) insertCI write_Response_\<sigma> write_invocation_same write_resp_dt)
  apply (smt (z3) Write_response_Commit_invocation_global assms(1) commit_invocation_same insertCI write_Response_\<sigma> write_resp_dt)
  apply (smt (verit, best) Write_response_Begin_response_global assms(1) begin_response_same insertCI write_Response_\<sigma> write_resp_dt)
  using  Write_response_Read_response_global
  apply (smt (verit, best) insert_iff read_response_same thrdsvars_def write_Response_\<sigma> write_resp_dt)
  apply (smt (verit) Write_response_Write_response_global assms(1) insertCI write_Response_\<sigma> write_resp_dt write_response_same)
  using Commit_Response_inv_def apply presburger
    (*********** TML_Commit_invocation****************)
  apply (intro conjI impI)
  apply (smt (z3) Commit_Invocation_not_pcs Commit_invocation_Begin_global Un_insert_left assms(1) begin_inv_same commit_inv_dt  insertCI insert_commute)
  using Commit_invocation_Commit_global
  apply (smt (z3) Commit_Invocation_not_pcs commit_inv_same  commit_inv_dt insert_commute thrdsvars_def)
  using Commit_invocation_Recover_global
  apply (smt (verit) Commit_Invocation_not_pcs commit_inv_dt recover_inv_same thrdsvars_def)
  apply (smt (z3) Commit_Invocation_not_pcs Commit_invocation_Read_global assms(1)  commit_inv_dt insert_commute read_inv_same)
  using Commit_invocation_Write_global
  apply (smt (verit) Commit_Invocation_not_pcs  commit_inv_dt insert_commute thrdsvars_def write_inv_same)
  apply (smt (verit) Commit_invocation_Begin_invocation_global assms(1) begin_invocation_same commit_Invocation_\<sigma>  commit_inv_dt insertCI)
  apply (smt (z3) Commit_invocation_Read_invocation_global assms(1) commit_Invocation_\<sigma>  commit_inv_dt insertCI read_invocation_same)
  apply (smt (z3) Commit_invocation_Write_invocation_global assms(1) commit_Invocation_\<sigma>  commit_inv_dt insertCI write_invocation_same)
  apply (smt (z3) Commit_Invocation_not_pcs Commit_invocation_Commit_invocation_global UnI1 Un_insert_right assms(1) assms(7) boolean_algebra.disj_zero_right  commit_inv_dt  commit_invocation_same)
  apply (smt (z3) Commit_invocation_Begin_response_global assms(1) begin_response_same commit_Invocation_\<sigma>  commit_inv_dt insertCI)
  apply (smt (verit, ccfv_threshold) Commit_Invocation_not_pcs Commit_invocation_Read_response_global UnI1 Un_empty_right Un_insert_right assms(1)  commit_inv_dt read_response_same)
  apply (smt (verit, ccfv_threshold) Commit_Invocation_not_pcs Commit_invocation_Write_response_global UnI1 Un_empty_right Un_insert_right assms(1)  commit_inv_dt write_response_same)
  using Commit_Response_inv_def apply presburger
    (*********** TML_Commit_response****************)
  apply (intro conjI impI)
  apply (smt (z3) Commit_response_Begin_global UnCI Un_insert_left assms(1) begin_inv_same commit_Response_\<sigma>  commit_resp_dt insertCI insert_commute)
  using Commit_response_Commit_global
  apply (smt (z3) UnCI commit_Response_\<sigma> commit_inv_same commit_resp_dt insert_commute thrdsvars_def)
  using Commit_response_Recover_global
  apply (smt (verit) Un_iff commit_Response_\<sigma> commit_resp_dt recover_inv_same thrdsvars_def)
  apply (smt (verit, ccfv_SIG) Commit_response_Read_global assms(1)commit_resp_dt insert_commute read_inv_same)
  using Commit_response_Write_global
  apply (smt(z3) Un_commute assms(1) commit_Response_\<sigma> commit_resp_dt insertI2 insert_commute insert_is_Un write_inv_same)
  apply (smt (verit, ccfv_SIG) Commit_response_Begin_invocation_global assms(1) begin_invocation_same commit_Response_\<sigma> commit_resp_dt insertCI)
  apply (smt (z3) Commit_response_Read_invocation_global assms(1) commit_Response_\<sigma>  commit_resp_dt  insertCI read_invocation_same)
  apply (smt (verit, ccfv_SIG) Commit_response_Write_invocation_global assms(1) commit_Response_\<sigma>  commit_resp_dt  insertCI write_invocation_same)
  apply (smt (z3) Commit_response_Commit_invocation_global assms(1) commit_Response_\<sigma> commit_invocation_same  commit_resp_dt  insertCI)
  apply (smt (verit, ccfv_threshold) Commit_response_Begin_response_global assms(1) begin_response_same commit_Response_\<sigma>  commit_resp_dt  insertCI)
  apply (smt (verit, best) Commit_response_Read_response_global assms(1) commit_Response_\<sigma>  commit_resp_dt  insertCI read_response_same)
  apply (smt (verit, ccfv_threshold) Commit_response_Write_response_global assms(1) commit_Response_\<sigma>  commit_resp_dt  insertCI write_response_same)
  using Commit_Response_inv_def apply presburger
    (***************Recover*********************************)
  apply (subgoal_tac " total_wfs (\<tau> \<sigma>) \<and>
pm_inv \<sigma> \<and>
( \<forall>t. writer \<sigma> = Some t \<longrightarrow> odd (lastVal glb (\<tau> \<sigma>))) \<and>
( \<forall>t. writer \<sigma> = Some t \<longrightarrow> \<lceil>glb\<rceil>\<^sub>t \<tau> \<sigma> ) \<and>
glb_monotone_inv (\<tau> \<sigma>) \<and>
mem_tml_prop3 (\<tau> \<sigma>) \<and>
( ((pc \<sigma>) syst) \<noteq> RecIdle   \<longrightarrow> (\<forall> t  \<noteq> syst.  ((pc \<sigma>) t)   \<in> {NotStarted, Aborted, Committed})) \<and>
( \<forall>b. mem_tml_prop glb b (\<tau> \<sigma>))\<and>
(  pc \<sigma>  syst  = RecIdle \<longrightarrow> (\<forall>t. t \<noteq> syst \<and> pc \<sigma> t \<notin> {NotStarted, Aborted, Committed, Begin2, BeginPending} \<longrightarrow>
regs (\<tau> \<sigma>) t DTML.loc \<le> lastVal glb (\<tau> \<sigma>)))
")
  prefer 2
  using DTML_total_persistent_invariant_def [where \<sigma> = \<sigma>]
  apply presburger
    (************************************************)
  apply (intro conjI impI)
  apply (case_tac "((pc \<sigma>) t) \<in>    {BeginPending, BeginResponding, Aborted} \<union> beginning \<and>
((pc \<sigma>) t') \<in> {RecIdle} \<union> recovering ")
  using  Recover_Begin_global[where \<sigma> = \<sigma> and \<sigma>' = \<sigma>' ]
  apply (simp add: insert_commute)
  apply (smt (verit) begin_inv_same insert_commute recover_dt recover_not_pc)
    (************************************************)
  apply (case_tac "((pc \<sigma>) t) \<in>    {CommitPending,CommitResponding, Aborted} \<union> committing \<and>
((pc \<sigma>) t') \<in> {RecIdle} \<union> recovering ")
  using  Recover_Commit_global[where \<sigma> = \<sigma> and \<sigma>' = \<sigma>' ]
               apply (simp add: insert_commute)
              apply (smt (z3) commit_inv_same insert_commute recover_not_pc  recover_dt)
           (*  apply (subgoal_tac "False")
  prefer 2
  sledgehammer
  apply fastforce
  apply (metis Recover_not_pcs commit_inv_same insert_commute  recover_dt)*)
  
  apply meson
    (************************************************)
  apply (case_tac "((pc \<sigma>) t) \<in>    {ReadPending,ReadResponding, Aborted} \<union> reading \<and>
((pc \<sigma>) t') \<in> {RecIdle} \<union> recovering ")
  using  Recover_Read_global[where \<sigma> = \<sigma> and \<sigma>' = \<sigma>' ]
  apply (simp add: insert_commute)
  apply (smt (z3) insert_commute read_inv_same recover_not_pc  recover_dt)
    (************************************************)
  apply (case_tac "((pc \<sigma>) t) \<in>    {WritePending,WriteResponding, Aborted} \<union> writing \<and>
((pc \<sigma>) t') \<in> {RecIdle} \<union> recovering ")
  using  Recover_Write_global[where \<sigma> = \<sigma> and \<sigma>' = \<sigma>' ]
  apply (smt (z3) assms(1) insert_commute)
  apply (smt (z3) insert_commute recover_not_pc  recover_dt write_inv_same) 
    (************************************************)
  using   Recover_Begin_invocation_global[where \<sigma> = \<sigma> and \<sigma>' = \<sigma>' ]
  apply (smt (verit) begin_invocation_same insert_iff recover_not_pc  recover_dt)
  using   Recover_Read_invocation_global[where \<sigma> = \<sigma> and \<sigma>' = \<sigma>' ]
  apply (smt (verit) insert_iff read_invocation_same recover_not_pc  recover_dt)
  using   Recover_Write_invocation_global[where \<sigma> = \<sigma> and \<sigma>' = \<sigma>' ]
  apply (smt (verit) insert_iff recover_not_pc  recover_dt  write_invocation_same)
  using   Recover_Commit_invocation_global[where \<sigma> = \<sigma> and \<sigma>' = \<sigma>' ]
  apply (smt (verit) commit_invocation_same insert_iff recover_not_pc  recover_dt)
  using    Recover_Begin_response_global[where \<sigma> = \<sigma> and \<sigma>' = \<sigma>' ]
  apply (smt (verit) Un_insert_right begin_response_same insertCI insert_is_Un recover_not_pc  recover_dt)
  using    Recover_Read_response_global[where \<sigma> = \<sigma> and \<sigma>' = \<sigma>' ]
  apply (smt (verit) Un_insert_right read_response_same insertCI insert_is_Un recover_not_pc  recover_dt)
  using    Recover_Write_response_global[where \<sigma> = \<sigma> and \<sigma>' = \<sigma>' ]
  apply (smt (verit) Un_insert_right write_response_same insertCI insert_is_Un recover_not_pc  recover_dt)
  using    Recover_Commit_response_global[where \<sigma> = \<sigma> and \<sigma>' = \<sigma>' ]
  apply (smt (verit) Un_insert_right commit_response_same insertCI insert_is_Un recover_not_pc  recover_dt)
    (************************************************)
  by (smt(z3) Begin_Crash_global Begin_invocation_Crash_global Begin_response_Crash_global Commit_Response_inv_def Commit_invocation_Crash_global Read_invocation_Crash_global assms(1) assms(2) assms(4) assms(7) dTML_def DTML_total_program_annotations_def empty_iff insert_iff local_correnctness_total read_invocation_same)













end

