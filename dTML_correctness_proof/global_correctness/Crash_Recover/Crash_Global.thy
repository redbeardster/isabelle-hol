theory Crash_Global
imports "../../DTML"
begin

(*Commit annotation is stable against a crash*)
lemma Commit_Crash_global:
assumes "thrdsvars"
and "total_wfs (\<tau> \<sigma>)"
and "  Commit_inv  t   ((pc \<sigma>) t) \<sigma>  "
and " TML_Crash  \<sigma> \<sigma>'"
shows "  Commit_inv  t   ((pc \<sigma>') t) \<sigma>' "
  using assms
  apply (unfold thrdsvars_def )
  by (simp add:TML_Crash_def Commit_inv_def  )


(*Read annotation is stable against a crash*)
lemma Read_Crash_global:
assumes "thrdsvars"
and "total_wfs (\<tau> \<sigma>)"
and "Read_inv t  ((pc \<sigma>) t) \<sigma>" 
and " TML_Crash  \<sigma> \<sigma>'"
shows "Read_inv t  ((pc \<sigma>') t) \<sigma>'" 
  using assms
  apply (unfold thrdsvars_def )
  by (simp add:TML_Crash_def Read_inv_def )

(*Write annotation is stable against a crash*)
lemma Write_Crash_global:
assumes "thrdsvars"
and "total_wfs (\<tau> \<sigma>)"
and "  Write_inv  t  ((pc \<sigma>) t) \<sigma>  "
and " TML_Crash  \<sigma> \<sigma>'"
shows "Write_inv t  ((pc \<sigma>') t) \<sigma>'" 
  using assms
  by (simp add:Write_inv_def TML_Crash_def)

(*Begin annotation is stable against a crash*)
lemma Begin_Crash_global:
assumes "thrdsvars"
and "total_wfs (\<tau> \<sigma>)"
and "   Begin_inv  t   ((pc \<sigma>) t) \<sigma> "
and " TML_Crash  \<sigma> \<sigma>'"
shows "  Begin_inv  t   ((pc \<sigma>') t) \<sigma>'" 
  using assms
  by (simp add:Begin_inv_def TML_Crash_def)

(*inv(Begin) annotation is stable against a crash*)
lemma Begin_invocation_Crash_global:
assumes "Begin_invocation_inv ta  ((pc \<sigma>) ta) \<sigma>" 
and " TML_Crash   \<sigma> \<sigma>'"
and "total_wfs (\<tau> \<sigma>) "
shows "Begin_invocation_inv ta  ((pc \<sigma>') ta) \<sigma>'" 
  using assms
  apply(simp add: Begin_invocation_inv_def  TML_Crash_def)
  by (simp add:  crash_step_def  crash_trans_def)

(*res(Begin) annotation is stable against a crash*)
lemma Begin_response_Crash_global:
assumes "thrdsvars"
and "total_wfs (\<tau> \<sigma>)"
and "  Begin_Response_inv t   ((pc \<sigma>) t) \<sigma>  "
and " TML_Crash  \<sigma> \<sigma>'"
shows "  Begin_Response_inv t   ((pc \<sigma>') t) \<sigma>' "
  using assms
  apply (unfold thrdsvars_def )
  by (simp add:TML_Crash_def Begin_Response_inv_def)


(*inv(Write) annotation is stable against a crash*)
lemma Write_invocation_Crash_global:
assumes "Write_invocation_inv ta  ((pc \<sigma>) ta) \<sigma>" 
and " TML_Crash   \<sigma> \<sigma>'"
and "total_wfs (\<tau> \<sigma>) "
shows "Write_invocation_inv ta  ((pc \<sigma>') ta) \<sigma>'" 
  using assms
  by(simp add: Write_invocation_inv_def  TML_Crash_def)

(*res(Write) annotation is stable against a crash*)
lemma Write_response_Crash_global:
assumes "thrdsvars"
and "total_wfs (\<tau> \<sigma>)"
and "  Write_Response_inv t   ((pc \<sigma>) t) \<sigma>  "
and " TML_Crash  \<sigma> \<sigma>'"
shows "  Write_Response_inv t   ((pc \<sigma>') t) \<sigma>' "
  using assms
  apply (unfold thrdsvars_def )
  by (simp add:TML_Crash_def Write_Response_inv_def)

(*inv(Read) annotation is stable against a crash*)
lemma Read_invocation_Crash_global:
assumes "Read_invocation_inv ta  ((pc \<sigma>) ta) \<sigma>" 
and " TML_Crash   \<sigma> \<sigma>'"
and "total_wfs (\<tau> \<sigma>) "
shows "Read_invocation_inv ta  ((pc \<sigma>') ta) \<sigma>'" 
  using assms
  by(simp add: Read_invocation_inv_def  TML_Crash_def)


(*res(Read) annotation is stable against a crash*)
lemma Read_response_Crash_global:
assumes "Read_Response_inv ta  ((pc \<sigma>) ta) \<sigma>" 
and " TML_Crash   \<sigma> \<sigma>'"
and "total_wfs (\<tau> \<sigma>) "
shows "Read_Response_inv ta  ((pc \<sigma>') ta) \<sigma>'" 
  using assms
  by(simp add: Read_Response_inv_def  TML_Crash_def)


(*inv(Commit) annotation is stable against a crash*)
lemma Commit_invocation_Crash_global:
assumes "Commit_invocation_inv ta  ((pc \<sigma>) ta) \<sigma>" 
and " TML_Crash   \<sigma> \<sigma>'"
and "total_wfs (\<tau> \<sigma>) "
shows "Commit_invocation_inv ta  ((pc \<sigma>') ta) \<sigma>'" 
  using assms
  by(simp add: Commit_invocation_inv_def  TML_Crash_def   )


(*res(Commit) annotation is stable against a crash*)
lemma Commit_response_Crash_global:
assumes "Commit_Response_inv ta  ((pc \<sigma>) ta) \<sigma>" 
and " TML_Crash   \<sigma> \<sigma>'"
and "total_wfs (\<tau> \<sigma>) "
shows "Commit_Response_inv ta  ((pc \<sigma>') ta) \<sigma>'" 
  using assms
  by(simp add: Commit_Response_inv_def  TML_Crash_def   )





end
