(*Showing that all the invocations  events' annotations are locally correct and stable with respect to all the DTML operations*)
theory Invocations_LocalGlobal
imports  DTML
begin




lemma Begin_invocation_Begin_invocation_global:
  assumes "thrdsvars"
and "  Begin_invocation_inv  tb   ((pc \<sigma>) tb)  \<sigma>  "
and "Begin_invocation_inv ta  ((pc \<sigma>) ta) \<sigma>" 
   and " TML_Begin_invocation  tb    \<sigma> \<sigma>'"
and "total_wfs (\<tau> \<sigma>) "
  and "((pc \<sigma>) ta) \<in>  {Aborted,BeginPending,NotStarted} "
  and " ((pc \<sigma>)tb) \<in> {Aborted,BeginPending,NotStarted}  " 
and " ta \<noteq> tb"
shows "Begin_invocation_inv ta  ((pc \<sigma>') ta) \<sigma>'" 
  using assms
  apply(simp add:Begin_invocation_inv_def  TML_Begin_invocation_def total_wfs_def  )
  by (cases" pc  \<sigma> tb"; simp ; cases "(pc \<sigma>) ta"; simp )


lemma Begin_invocation_Begin_response_global:
  assumes "thrdsvars"
and "  Begin_invocation_inv  tb   ((pc \<sigma>) tb)  \<sigma>  "
and "Begin_Response_inv ta  ((pc \<sigma>) ta) \<sigma>" 
   and " TML_Begin_invocation  tb    \<sigma> \<sigma>'"
and "total_wfs (\<tau> \<sigma>) "
  and "((pc \<sigma>) ta) \<in>  {Aborted,BeginResponding,Ready} "
  and " ((pc \<sigma>)tb) \<in> {Aborted,BeginPending,NotStarted}  " 
and " ta \<noteq> tb"
shows "Begin_Response_inv ta  ((pc \<sigma>') ta) \<sigma>'" 
  using assms
  apply(simp add:Begin_invocation_inv_def Begin_Response_inv_def TML_Begin_invocation_def total_wfs_def  )
  apply (cases" pc  \<sigma> tb"; simp ; cases "(pc \<sigma>) ta"; simp )
  apply (unfold Ready_total_def)
  by metis+






lemma Begin_invocation_Read_invocation_global:
  assumes "thrdsvars"
and "  Begin_invocation_inv  tb   ((pc \<sigma>) tb)  \<sigma>  "
and "Read_invocation_inv ta  ((pc \<sigma>) ta) \<sigma>" 
   and " TML_Begin_invocation  tb    \<sigma> \<sigma>'"
and "total_wfs (\<tau> \<sigma>) "
  and "((pc \<sigma>) ta) \<in>  {Aborted,ReadPending,Ready} "
  and " ((pc \<sigma>)tb) \<in>  {Aborted,BeginPending,NotStarted} " 
and " ta \<noteq> tb"
shows "Read_invocation_inv ta  ((pc \<sigma>') ta) \<sigma>'" 
  using assms
  apply(simp add:Begin_invocation_inv_def  TML_Begin_invocation_def  Read_invocation_inv_def  total_wfs_def  )
  apply   (cases" pc  \<sigma> tb"; simp ; cases "(pc \<sigma>) ta"; simp )

  apply (unfold Ready_total_def)
  by  metis+



lemma Begin_invocation_Read_response_global:
  assumes "thrdsvars"
and "  Begin_invocation_inv  tb   ((pc \<sigma>) tb)  \<sigma>  "
and "Read_Response_inv ta  ((pc \<sigma>) ta) \<sigma>" 
   and " TML_Begin_invocation  tb    \<sigma> \<sigma>'"
and "total_wfs (\<tau> \<sigma>) "
  and "((pc \<sigma>) ta) \<in>  {Aborted,ReadResponding,Ready} "
  and " ((pc \<sigma>)tb) \<in>  {Aborted,BeginPending,NotStarted} " 
and " ta \<noteq> tb"
shows "Read_Response_inv ta  ((pc \<sigma>') ta) \<sigma>'" 
  using assms
  apply(simp add:Begin_invocation_inv_def  TML_Begin_invocation_def  Read_Response_inv_def  total_wfs_def  )
  apply   (cases" pc  \<sigma> tb"; simp ; cases "(pc \<sigma>) ta"; simp )

  apply (unfold Ready_total_def)
  by  metis+






lemma Begin_invocation_Write_invocation_global:
  assumes "thrdsvars"
and "  Begin_invocation_inv  tb   ((pc \<sigma>) tb)  \<sigma>  "
and "Write_invocation_inv ta  ((pc \<sigma>) ta) \<sigma>" 
   and " TML_Begin_invocation  tb    \<sigma> \<sigma>'"
and "total_wfs (\<tau> \<sigma>) "
  and "((pc \<sigma>) ta) \<in>  {Aborted,WritePending,Ready} "
  and " ((pc \<sigma>)tb) \<in>  {Aborted,BeginPending,NotStarted} " 
and " ta \<noteq> tb"
shows "Write_invocation_inv ta  ((pc \<sigma>') ta) \<sigma>'" 
  using assms
  apply(simp add:Begin_invocation_inv_def  TML_Begin_invocation_def  Write_invocation_inv_def  total_wfs_def  )
  apply   (cases" pc  \<sigma> tb"; simp ; cases "(pc \<sigma>) ta"; simp )

  apply (unfold Ready_total_def)
  by  metis+



lemma Begin_invocation_Write_response_global:
  assumes "thrdsvars"
and "  Begin_invocation_inv  tb   ((pc \<sigma>) tb)  \<sigma>  "
and "Write_Response_inv ta  ((pc \<sigma>) ta) \<sigma>" 
   and " TML_Begin_invocation  tb    \<sigma> \<sigma>'"
and "total_wfs (\<tau> \<sigma>) "
  and "((pc \<sigma>) ta) \<in>  {Aborted,WriteResponding,Ready} "
  and " ((pc \<sigma>)tb) \<in>  {Aborted,BeginPending,NotStarted} " 
and " ta \<noteq> tb"
shows "Write_Response_inv ta  ((pc \<sigma>') ta) \<sigma>'" 
  using assms
  apply(simp add:Begin_invocation_inv_def  TML_Begin_invocation_def  Write_Response_inv_def  total_wfs_def  )
  apply   (cases" pc  \<sigma> tb"; simp ; cases "(pc \<sigma>) ta"; simp )

  apply (unfold Ready_total_def)
  by  metis+








lemma Begin_invocation_Commit_invocation_global:
  assumes "thrdsvars"
and "  Begin_invocation_inv  tb   ((pc \<sigma>) tb)  \<sigma>  "
and "Commit_invocation_inv ta  ((pc \<sigma>) ta) \<sigma>" 
   and " TML_Begin_invocation  tb    \<sigma> \<sigma>'"
and "total_wfs (\<tau> \<sigma>) "
  and "((pc \<sigma>) ta) \<in>  {Aborted,CommitPending,Ready} "
  and " ((pc \<sigma>)tb) \<in>  {Aborted,BeginPending,NotStarted} " 
and " ta \<noteq> tb"
shows "Commit_invocation_inv ta  ((pc \<sigma>') ta) \<sigma>'" 
  using assms
  apply(simp add:Begin_invocation_inv_def  TML_Begin_invocation_def  Commit_invocation_inv_def  total_wfs_def  )
  apply   (cases" pc  \<sigma> tb"; simp ; cases "(pc \<sigma>) ta"; simp )
  apply (unfold Ready_total_def)
  by  metis+






lemma Begin_invocation_Commit_response_global:
  assumes "thrdsvars"
and "  Begin_invocation_inv  tb   ((pc \<sigma>) tb)  \<sigma>  "
and "Commit_Response_inv ta  ((pc \<sigma>) ta) \<sigma>" 
   and " TML_Begin_invocation  tb    \<sigma> \<sigma>'"
and "total_wfs (\<tau> \<sigma>) "
  and "((pc \<sigma>) ta) \<in>  {Aborted,CommitResponding,Committed} "
  and " ((pc \<sigma>)tb) \<in>  {Aborted,BeginPending,NotStarted} " 
and " ta \<noteq> tb"
shows "Commit_Response_inv ta  ((pc \<sigma>') ta) \<sigma>'" 
  using assms
  by(simp add:Begin_invocation_inv_def  TML_Begin_invocation_def  Commit_Response_inv_def  total_wfs_def  )

(***********************************)


lemma Read_invocation_Begin_invocation_global:
  assumes "thrdsvars"
and "  Read_invocation_inv  tb   ((pc \<sigma>) tb)  \<sigma>  "
and "Begin_invocation_inv ta  ((pc \<sigma>) ta) \<sigma>" 
   and " TML_Read_invocation  tb    \<sigma> \<sigma>'"
and "total_wfs (\<tau> \<sigma>) "
  and " ((pc \<sigma>)ta) \<in> {Aborted,BeginPending,NotStarted}  " 
  and "((pc \<sigma>) tb) \<in>  {Aborted,ReadPending, Ready} "
and " ta \<noteq> tb"
shows "Begin_invocation_inv ta  ((pc \<sigma>') ta) \<sigma>'" 
  using assms
  apply(simp add:Begin_invocation_inv_def Read_invocation_inv_def   TML_Read_invocation_def total_wfs_def  )
  by(cases" pc  \<sigma> tb"; simp ; cases "(pc \<sigma>) ta"; simp )



lemma Read_invocation_Begin_response_global:
  assumes "thrdsvars"
and "  Read_invocation_inv  tb   ((pc \<sigma>) tb)  \<sigma>  "
and "Begin_Response_inv ta  ((pc \<sigma>) ta) \<sigma>" 
   and " TML_Read_invocation  tb    \<sigma> \<sigma>'"
and "total_wfs (\<tau> \<sigma>) "
  and " ((pc \<sigma>)ta) \<in> {Aborted,BeginResponding,Ready}  " 
  and "((pc \<sigma>) tb) \<in>  {Aborted,ReadPending, Ready} "
and " ta \<noteq> tb"
shows "Begin_Response_inv ta  ((pc \<sigma>') ta) \<sigma>'" 
  using assms
  apply(simp add:Begin_Response_inv_def Read_invocation_inv_def   TML_Read_invocation_def total_wfs_def  )
apply(cases" pc  \<sigma> tb"; simp ; cases "(pc \<sigma>) ta"; simp )
  apply (unfold Ready_total_def)
  by metis+



lemma Read_invocation_Read_invocation_global:
  assumes "thrdsvars"
and "  Read_invocation_inv  tb   ((pc \<sigma>) tb)  \<sigma>  "
and "Read_invocation_inv ta  ((pc \<sigma>) ta) \<sigma>" 
   and " TML_Read_invocation  tb    \<sigma> \<sigma>'"
and "total_wfs (\<tau> \<sigma>) "
  and "((pc \<sigma>) ta) \<in>  {Aborted,ReadPending,Ready} "
  and " ((pc \<sigma>)tb) \<in>   {Aborted,ReadPending,Ready} " 
and " ta \<noteq> tb"
shows "Read_invocation_inv ta  ((pc \<sigma>') ta) \<sigma>'" 
  using assms
  apply(simp add:Read_invocation_inv_def  TML_Read_invocation_def  Read_invocation_inv_def  total_wfs_def  )

  apply   (cases" pc  \<sigma> tb"; simp ; cases "(pc \<sigma>) ta"; simp )

  apply (unfold Ready_total_def)
  by  metis+


lemma Read_invocation_Read_response_global:
  assumes "thrdsvars"
and "  Read_invocation_inv  tb   ((pc \<sigma>) tb)  \<sigma>  "
and "Read_Response_inv ta  ((pc \<sigma>) ta) \<sigma>" 
   and " TML_Read_invocation  tb    \<sigma> \<sigma>'"
and "total_wfs (\<tau> \<sigma>) "
  and "((pc \<sigma>) ta) \<in>  {Aborted,ReadResponding,Ready} "
  and " ((pc \<sigma>)tb) \<in>   {Aborted,ReadPending,Ready} " 
and " ta \<noteq> tb"
shows "Read_Response_inv ta  ((pc \<sigma>') ta) \<sigma>'" 
  using assms
  apply(simp add:Read_invocation_inv_def  TML_Read_invocation_def  Read_Response_inv_def  total_wfs_def  )

  apply   (cases" pc  \<sigma> tb"; simp ; cases "(pc \<sigma>) ta"; simp )

  apply (unfold Ready_total_def)
  by  metis+




lemma Read_invocation_Write_invocation_global:
  assumes "thrdsvars"
and "  Read_invocation_inv  tb   ((pc \<sigma>) tb)  \<sigma>  "
and "Write_invocation_inv ta  ((pc \<sigma>) ta) \<sigma>" 
   and " TML_Read_invocation  tb    \<sigma> \<sigma>'"
and "total_wfs (\<tau> \<sigma>) "
  and "((pc \<sigma>) ta) \<in>  {Aborted, WritePending,Ready} "
  and " ((pc \<sigma>)tb) \<in>   {Aborted,ReadPending,Ready} " 
and " ta \<noteq> tb"
shows "Write_invocation_inv ta  ((pc \<sigma>') ta) \<sigma>'" 
  using assms
  apply(simp add:Read_invocation_inv_def  TML_Read_invocation_def  _Write_invocation_inv_def  total_wfs_def  )

  apply   (cases" pc  \<sigma> tb"; simp ; cases "(pc \<sigma>) ta"; simp )

  apply (unfold Ready_total_def)
  by  metis+



lemma Read_invocation_Write_response_global:
  assumes "thrdsvars"
and "  Read_invocation_inv  tb   ((pc \<sigma>) tb)  \<sigma>  "
and "Write_Response_inv ta  ((pc \<sigma>) ta) \<sigma>" 
   and " TML_Read_invocation  tb    \<sigma> \<sigma>'"
and "total_wfs (\<tau> \<sigma>) "
  and "((pc \<sigma>) ta) \<in>  {Aborted, WriteResponding,Ready} "
  and " ((pc \<sigma>)tb) \<in>   {Aborted,ReadPending,Ready} " 
and " ta \<noteq> tb"
shows "Write_Response_inv ta  ((pc \<sigma>') ta) \<sigma>'" 
  using assms
  apply(simp add:Read_invocation_inv_def  TML_Read_invocation_def  _Write_Response_inv_def  total_wfs_def  )

  apply   (cases" pc  \<sigma> tb"; simp ; cases "(pc \<sigma>) ta"; simp )

  apply (unfold Ready_total_def)
  by  metis+







lemma Read_invocation_Commit_invocation_global:
  assumes "thrdsvars"
and "  Read_invocation_inv  tb   ((pc \<sigma>) tb)  \<sigma>  "
and "Commit_invocation_inv ta  ((pc \<sigma>) ta) \<sigma>" 
   and " TML_Read_invocation  tb    \<sigma> \<sigma>'"
and "total_wfs (\<tau> \<sigma>) "
  and "((pc \<sigma>) ta) \<in>  {Aborted, CommitPending,Ready} "
  and " ((pc \<sigma>)tb) \<in>   {Aborted,ReadPending,Ready} " 
and " ta \<noteq> tb"
shows "Commit_invocation_inv ta  ((pc \<sigma>') ta) \<sigma>'" 
  using assms
  apply(simp add:Read_invocation_inv_def  TML_Read_invocation_def  Commit_invocation_inv_def  total_wfs_def  )

  apply   (cases" pc  \<sigma> tb"; simp ; cases "(pc \<sigma>) ta"; simp )

  apply (unfold Ready_total_def)
  by  metis+


lemma Read_invocation_Commit_response_global:
  assumes "thrdsvars"
and "  Read_invocation_inv  tb   ((pc \<sigma>) tb)  \<sigma>  "
and "Commit_Response_inv ta  ((pc \<sigma>) ta) \<sigma>" 
   and " TML_Read_invocation  tb    \<sigma> \<sigma>'"
and "total_wfs (\<tau> \<sigma>) "
  and "((pc \<sigma>) ta) \<in>  {Aborted, CommitResponding,Committed} "
  and " ((pc \<sigma>)tb) \<in>   {Aborted,ReadPending,Ready} " 
and " ta \<noteq> tb"
shows "Commit_Response_inv ta  ((pc \<sigma>') ta) \<sigma>'" 
  using assms
by(simp add:Read_invocation_inv_def  TML_Read_invocation_def  Commit_Response_inv_def  total_wfs_def  )


(**************************************************)


lemma Write_invocation_Begin_invocation_global:
  assumes "thrdsvars"
and "  Write_invocation_inv  tb   ((pc \<sigma>) tb)  \<sigma>  "
and "Begin_invocation_inv ta  ((pc \<sigma>) ta) \<sigma>" 
   and " TML_Write_invocation  tb    \<sigma> \<sigma>'"
and "total_wfs (\<tau> \<sigma>) "
  and " ((pc \<sigma>)ta) \<in> {Aborted,BeginPending,NotStarted}  " 
  and "((pc \<sigma>) tb) \<in>  {Aborted,WritePending, Ready} "
and " ta \<noteq> tb"
shows "Begin_invocation_inv ta  ((pc \<sigma>') ta) \<sigma>'" 
  using assms
  apply(simp add:Begin_invocation_inv_def Write_invocation_inv_def   TML_Write_invocation_def total_wfs_def  )

  by (cases" pc  \<sigma> tb"; simp ; cases "(pc \<sigma>) ta"; simp )



lemma Write_invocation_Begin_response_global:
  assumes "thrdsvars"
and "  Write_invocation_inv  tb   ((pc \<sigma>) tb)  \<sigma>  "
and "Begin_Response_inv ta  ((pc \<sigma>) ta) \<sigma>" 
   and " TML_Write_invocation  tb    \<sigma> \<sigma>'"
and "total_wfs (\<tau> \<sigma>) "
  and " ((pc \<sigma>)ta) \<in> {Aborted,BeginResponding,Ready}  " 
  and "((pc \<sigma>) tb) \<in>  {Aborted,WritePending, Ready} "
and " ta \<noteq> tb"
shows "Begin_Response_inv ta  ((pc \<sigma>') ta) \<sigma>'" 
  using assms
  apply(simp add:Begin_Response_inv_def Write_invocation_inv_def   TML_Write_invocation_def total_wfs_def  )

  apply (cases" pc  \<sigma> tb"; simp ; cases "(pc \<sigma>) ta"; simp )
  apply (unfold Ready_total_def)
  by metis+






lemma  Write_invocation_Read_invocation_global:
  assumes "thrdsvars"
and "  Write_invocation_inv  tb   ((pc \<sigma>) tb)  \<sigma>  "
and "Read_invocation_inv ta  ((pc \<sigma>) ta) \<sigma>" 
   and " TML_Write_invocation  tb    \<sigma> \<sigma>'"
and "total_wfs (\<tau> \<sigma>) "
  and "((pc \<sigma>) ta) \<in>  {Aborted,ReadPending,Ready} "
  and " ((pc \<sigma>)tb) \<in>   {Aborted,WritePending,Ready} " 
and " ta \<noteq> tb"
shows "Read_invocation_inv ta  ((pc \<sigma>') ta) \<sigma>'" 
  using assms
  apply(simp add:Read_invocation_inv_def  TML_Write_invocation_def  Write_invocation_inv_def  total_wfs_def  )

  apply   (cases" pc  \<sigma> tb"; simp ; cases "(pc \<sigma>) ta"; simp )

  apply (unfold Ready_total_def)
  by  metis+



lemma  Write_invocation_Read_response_global:
  assumes "thrdsvars"
and "  Write_invocation_inv  tb   ((pc \<sigma>) tb)  \<sigma>  "
and "Read_Response_inv ta  ((pc \<sigma>) ta) \<sigma>" 
   and " TML_Write_invocation  tb    \<sigma> \<sigma>'"
and "total_wfs (\<tau> \<sigma>) "
  and "((pc \<sigma>) ta) \<in>  {Aborted,ReadResponding,Ready} "
  and " ((pc \<sigma>)tb) \<in>   {Aborted,WritePending,Ready} " 
and " ta \<noteq> tb"
shows "Read_Response_inv ta  ((pc \<sigma>') ta) \<sigma>'" 
  using assms
  apply(simp add:Read_Response_inv_def  TML_Write_invocation_def  Write_invocation_inv_def  total_wfs_def  )

  apply   (cases" pc  \<sigma> tb"; simp ; cases "(pc \<sigma>) ta"; simp )

  apply (unfold Ready_total_def)
  by  metis+



lemma Write_invocation_Write_invocation_global:
  assumes "thrdsvars"
and "  Write_invocation_inv  tb   ((pc \<sigma>) tb)  \<sigma>  "
and "Write_invocation_inv ta  ((pc \<sigma>) ta) \<sigma>" 
   and " TML_Write_invocation  tb    \<sigma> \<sigma>'"
and "total_wfs (\<tau> \<sigma>) "
  and "((pc \<sigma>) ta) \<in>  {Aborted, WritePending,Ready} "
  and " ((pc \<sigma>)tb) \<in>   {Aborted, WritePending,Ready}  " 
and " ta \<noteq> tb"
shows "Write_invocation_inv ta  ((pc \<sigma>') ta) \<sigma>'" 
  using assms
  apply(simp add:  TML_Write_invocation_def  _Write_invocation_inv_def  total_wfs_def  )

  apply   (cases" pc  \<sigma> tb"; simp ; cases "(pc \<sigma>) ta"; simp )

  apply (unfold Ready_total_def)
  by  metis+



lemma Write_invocation_Write_response_global:
  assumes "thrdsvars"
and "  Write_invocation_inv  tb   ((pc \<sigma>) tb)  \<sigma>  "
and "Write_Response_inv ta  ((pc \<sigma>) ta) \<sigma>" 
   and " TML_Write_invocation  tb    \<sigma> \<sigma>'"
and "total_wfs (\<tau> \<sigma>) "
  and "((pc \<sigma>) ta) \<in>  {Aborted, WriteResponding,Ready} "
  and " ((pc \<sigma>)tb) \<in>   {Aborted, WritePending,Ready}  " 
and " ta \<noteq> tb"
shows "Write_Response_inv ta  ((pc \<sigma>') ta) \<sigma>'" 
  using assms
  apply(simp add:  TML_Write_invocation_def  _Write_invocation_inv_def _Write_Response_inv_def  total_wfs_def  )

  apply   (cases" pc  \<sigma> tb"; simp ; cases "(pc \<sigma>) ta"; simp )

  apply (unfold Ready_total_def)
  by  metis+




lemma Write_invocation_Commit_invocation_global:
  assumes "thrdsvars"
and "  Write_invocation_inv  tb   ((pc \<sigma>) tb)  \<sigma>  "
and "Commit_invocation_inv ta  ((pc \<sigma>) ta) \<sigma>" 
   and " TML_Write_invocation  tb    \<sigma> \<sigma>'"
and "total_wfs (\<tau> \<sigma>) "
  and "((pc \<sigma>) ta) \<in>  {Aborted, CommitPending,Ready} "
  and " ((pc \<sigma>)tb) \<in>   {Aborted,WritePending,Ready} " 
and " ta \<noteq> tb"
shows "Commit_invocation_inv ta  ((pc \<sigma>') ta) \<sigma>'" 
  using assms
  apply(simp add:Write_invocation_inv_def  TML_Write_invocation_def  Commit_invocation_inv_def  total_wfs_def  )

  apply   (cases" pc  \<sigma> tb"; simp ; cases "(pc \<sigma>) ta"; simp )

  apply (unfold Ready_total_def)
  by  metis+



lemma Write_invocation_Commit_response_global:
  assumes "thrdsvars"
and "  Write_invocation_inv  tb   ((pc \<sigma>) tb)  \<sigma>  "
and "Commit_Response_inv ta  ((pc \<sigma>) ta) \<sigma>" 
   and " TML_Write_invocation  tb    \<sigma> \<sigma>'"
and "total_wfs (\<tau> \<sigma>) "
  and "((pc \<sigma>) ta) \<in>  {Aborted, CommitResponding,Committed} "
  and " ((pc \<sigma>)tb) \<in>   {Aborted,WritePending,Ready} " 
and " ta \<noteq> tb"
shows "Commit_Response_inv ta  ((pc \<sigma>') ta) \<sigma>'" 
  using assms
  by(simp add:Write_invocation_inv_def  TML_Write_invocation_def  Commit_Response_inv_def  total_wfs_def  )



(********************************)




lemma Commit_invocation_Begin_invocation_global:
  assumes "thrdsvars"
and "  Commit_invocation_inv  tb   ((pc \<sigma>) tb)  \<sigma>  "
and "Begin_invocation_inv ta  ((pc \<sigma>) ta) \<sigma>" 
   and " TML_Commit_invocation  tb    \<sigma> \<sigma>'"
and "total_wfs (\<tau> \<sigma>) "
  and " ((pc \<sigma>)ta) \<in> {Aborted,BeginPending,NotStarted}  " 
  and "((pc \<sigma>) tb) \<in>  {Aborted,CommitPending, Ready} "
and " ta \<noteq> tb"
shows "Begin_invocation_inv ta  ((pc \<sigma>') ta) \<sigma>'" 
  using assms
  apply(simp add:Begin_invocation_inv_def Commit_invocation_inv_def   TML_Commit_invocation_def total_wfs_def  )
  by (cases" pc  \<sigma> tb"; simp ; cases "(pc \<sigma>) ta"; simp )



lemma Commit_invocation_Begin_response_global:
  assumes "thrdsvars"
and "  Commit_invocation_inv  tb   ((pc \<sigma>) tb)  \<sigma>  "
and "Begin_Response_inv ta  ((pc \<sigma>) ta) \<sigma>" 
   and " TML_Commit_invocation  tb    \<sigma> \<sigma>'"
and "total_wfs (\<tau> \<sigma>) "
  and " ((pc \<sigma>)ta) \<in> {Aborted,BeginResponding,Ready}  " 
  and "((pc \<sigma>) tb) \<in>  {Aborted,CommitPending, Ready} "
and " ta \<noteq> tb"
shows "Begin_Response_inv ta  ((pc \<sigma>') ta) \<sigma>'" 
  using assms
  apply(simp add:Begin_Response_inv_def Commit_invocation_inv_def   TML_Commit_invocation_def total_wfs_def  )
  apply (cases" pc  \<sigma> tb"; simp ; cases "(pc \<sigma>) ta"; simp )
  apply (unfold Ready_total_def)
  apply metis
  by metis







lemma Commit_invocation_Read_invocation_global:
  assumes "thrdsvars"
and "  Commit_invocation_inv  tb   ((pc \<sigma>) tb)  \<sigma>  "
and "Read_invocation_inv ta  ((pc \<sigma>) ta) \<sigma>" 
   and " TML_Commit_invocation  tb    \<sigma> \<sigma>'"
and "total_wfs (\<tau> \<sigma>) "
  and " ((pc \<sigma>)ta) \<in> {Aborted,ReadPending,Ready}  " 
  and "((pc \<sigma>) tb) \<in>  {Aborted,CommitPending, Ready} "
and " ta \<noteq> tb"
shows "Read_invocation_inv ta  ((pc \<sigma>') ta) \<sigma>'" 
  using assms
  apply(simp add:Read_invocation_inv_def Commit_invocation_inv_def   TML_Commit_invocation_def total_wfs_def  )
  apply  (cases" pc  \<sigma> tb"; simp ; cases "(pc \<sigma>) ta"; simp )
  apply (unfold Ready_total_def)
  by metis+




lemma Commit_invocation_Read_response_global:
  assumes "thrdsvars"
and "  Commit_invocation_inv  tb   ((pc \<sigma>) tb)  \<sigma>  "
and "Read_Response_inv ta  ((pc \<sigma>) ta) \<sigma>" 
   and " TML_Commit_invocation  tb    \<sigma> \<sigma>'"
and "total_wfs (\<tau> \<sigma>) "
  and " ((pc \<sigma>)ta) \<in> {Aborted,ReadResponding,Ready}  " 
  and "((pc \<sigma>) tb) \<in>  {Aborted,CommitPending, Ready} "
and " ta \<noteq> tb"
shows "Read_Response_inv ta  ((pc \<sigma>') ta) \<sigma>'" 
  using assms
  apply(simp add:Read_Response_inv_def Commit_invocation_inv_def   TML_Commit_invocation_def total_wfs_def  )

  apply  (cases" pc  \<sigma> tb"; simp ; cases "(pc \<sigma>) ta"; simp )
  apply (unfold Ready_total_def)
  by metis+







lemma Commit_invocation_Write_invocation_global:
  assumes "thrdsvars"
and "  Commit_invocation_inv  tb   ((pc \<sigma>) tb)  \<sigma>  "
and "Write_invocation_inv ta  ((pc \<sigma>) ta) \<sigma>" 
   and " TML_Commit_invocation  tb    \<sigma> \<sigma>'"
and "total_wfs (\<tau> \<sigma>) "
  and " ((pc \<sigma>)ta) \<in> {Aborted, WritePending,Ready}  " 
  and "((pc \<sigma>) tb) \<in>  {Aborted,CommitPending, Ready} "
and " ta \<noteq> tb"
shows "Write_invocation_inv ta  ((pc \<sigma>') ta) \<sigma>'" 
  using assms
  apply(simp add:Write_invocation_inv_def Commit_invocation_inv_def   TML_Commit_invocation_def total_wfs_def  )

  apply  (cases" pc  \<sigma> tb"; simp ; cases "(pc \<sigma>) ta"; simp )
  apply (unfold Ready_total_def)
  apply (metis (no_types, opaque_lifting))
  by metis



lemma Commit_invocation_Write_response_global:
  assumes "thrdsvars"
and "  Commit_invocation_inv  tb   ((pc \<sigma>) tb)  \<sigma>  "
and "Write_Response_inv ta  ((pc \<sigma>) ta) \<sigma>" 
   and " TML_Commit_invocation  tb    \<sigma> \<sigma>'"
and "total_wfs (\<tau> \<sigma>) "
  and " ((pc \<sigma>)ta) \<in> {Aborted, WriteResponding,Ready}  " 
  and "((pc \<sigma>) tb) \<in>  {Aborted,CommitPending, Ready} "
and " ta \<noteq> tb"
shows "Write_Response_inv ta  ((pc \<sigma>') ta) \<sigma>'" 
  using assms
  apply(simp add:Write_Response_inv_def Commit_invocation_inv_def   TML_Commit_invocation_def total_wfs_def  )

  apply  (cases" pc  \<sigma> tb"; simp ; cases "(pc \<sigma>) ta"; simp )
  apply (unfold Ready_total_def)
  by metis+






lemma Commit_invocation_Commit_invocation_global:
  assumes "thrdsvars"
and "  Commit_invocation_inv  tb   ((pc \<sigma>) tb)  \<sigma>  "
and "Commit_invocation_inv ta  ((pc \<sigma>) ta) \<sigma>" 
   and " TML_Commit_invocation  tb    \<sigma> \<sigma>'"
and "total_wfs (\<tau> \<sigma>) "
  and "((pc \<sigma>) ta) \<in>  {Aborted, CommitPending,Ready} "
  and " ((pc \<sigma>)tb) \<in>   {Aborted, CommitPending,Ready} " 
and " ta \<noteq> tb"
shows "Commit_invocation_inv ta  ((pc \<sigma>') ta) \<sigma>'" 
  using assms
  apply(simp add: Commit_invocation_inv_def  TML_Commit_invocation_def  Commit_invocation_inv_def  total_wfs_def  )

  apply   (cases" pc  \<sigma> tb"; simp ; cases "(pc \<sigma>) ta"; simp )

  apply (unfold Ready_total_def)
  by  metis+




lemma Commit_invocation_Commit_response_global:
  assumes "thrdsvars"
and "  Commit_invocation_inv  tb   ((pc \<sigma>) tb)  \<sigma>  "
and "Commit_Response_inv ta  ((pc \<sigma>) ta) \<sigma>" 
   and " TML_Commit_invocation  tb    \<sigma> \<sigma>'"
and "total_wfs (\<tau> \<sigma>) "
  and "((pc \<sigma>) ta) \<in>  {Aborted, CommitResponding,Committed} "
  and " ((pc \<sigma>)tb) \<in>   {Aborted, CommitPending,Ready} " 
and " ta \<noteq> tb"
shows "Commit_Response_inv ta  ((pc \<sigma>') ta) \<sigma>'" 
  using assms
  by(simp add: Commit_Response_inv_def  TML_Commit_invocation_def  Commit_invocation_inv_def  total_wfs_def  )





(***********************)

























lemma Begin_invocation_local:
  assumes "thrdsvars"
and "total_wfs (\<tau> \<sigma>) "
and "Begin_invocation_inv t  ((pc \<sigma>) t) \<sigma>" 
 and " TML_Begin_invocation  t   \<sigma> \<sigma>'"
shows "Begin_invocation_inv t  ((pc \<sigma>') t) \<sigma>'"  
  using assms
  apply (simp add: TML_Begin_invocation_def Begin_invocation_inv_def   total_wfs_def   )

  by (cases "pc \<sigma> t";simp  )



lemma Begin_Begin_invocation_global:
  assumes "thrdsvars"
and "  Read_inv  tb   ((pc \<sigma>) tb)  \<sigma>  "
and "Begin_invocation_inv ta  ((pc \<sigma>) ta) \<sigma>" 
   and " TML_Begin  tb    \<sigma> \<sigma>'"
and "total_wfs (\<tau> \<sigma>) "
  and "((pc \<sigma>) ta) \<in> {BeginPending, NotStarted} \<union> {Aborted} "
  and " ((pc \<sigma>)tb) \<in> {Aborted,BeginPending,BeginResponding} \<union> beginning  " 
and " ta \<noteq> tb"
shows "Begin_invocation_inv ta  ((pc \<sigma>') ta) \<sigma>'" 
  using assms
  apply(simp add:Begin_invocation_inv_def Begin_inv_def TML_Begin_def total_wfs_def  )

  apply (cases" pc  \<sigma> tb"; simp ; cases "(pc \<sigma>) ta"; simp )
  apply (metis assms(5) ld_coh_dt_ni ld_vrnew_dt_ni)  
  apply ( simp add: split: if_split_asm)+
     apply (metis assms(5) ld_coh_dt_ni ld_vrnew_dt_ni)
  apply (smt (z3) PC.simps(1641) pc_aux)
  by ( simp add: split: if_split_asm)+






lemma Begin_invocation_Begin_global:
  assumes "thrdsvars"
and "  Begin_inv  tb   ((pc \<sigma>) tb)  \<sigma>  "
and "Begin_invocation_inv ta  ((pc \<sigma>) ta) \<sigma>" 
 and " TML_Begin_invocation  ta   \<sigma> \<sigma>'"
and "total_wfs (\<tau> \<sigma>) "
   and "((pc \<sigma>) ta) \<in> {BeginPending, NotStarted} \<union> {Aborted} "
   and " ((pc \<sigma>)tb) \<in> {Aborted,BeginPending,BeginResponding} \<union> beginning  " 
and " ta \<noteq> tb"
shows "  Begin_inv  tb   ((pc \<sigma>') tb)  \<sigma>'" 
  using assms
  apply(simp add:Begin_invocation_inv_def Begin_inv_def total_wfs_def TML_Begin_invocation_def Ready_total_def )
  apply  (cases" pc  \<sigma> tb"; simp ; cases "(pc \<sigma>) ta"; simp )
  apply (metis PC.distinct(55))
   apply (metis PC.distinct(55))
  apply (unfold Ready_total_def read_pre_def)
  by (smt (verit))





lemma Read_Begin_invocation_global:
  assumes "thrdsvars"
and "  Read_inv  tb   ((pc \<sigma>) tb)  \<sigma>  "
and "Begin_invocation_inv ta  ((pc \<sigma>) ta) \<sigma>" 
   and " TML_Read  tb    \<sigma> \<sigma>'"
and "total_wfs (\<tau> \<sigma>) "
   and "((pc \<sigma>) ta) \<in> {BeginPending, NotStarted} \<union> {Aborted} "
  and " ((pc \<sigma>)tb) \<in> {Aborted,ReadPending, ReadResponding} \<union> reading  " 
and " ta \<noteq> tb"
shows "Begin_invocation_inv ta  ((pc \<sigma>') ta) \<sigma>'" 
  using assms
  apply(simp add:Begin_invocation_inv_def Read_inv_def TML_Read_def total_wfs_def  )
  apply (cases" pc  \<sigma> tb"; simp ; cases "(pc \<sigma>) ta"; simp )
  apply (metis assms(5) ld_coh_dt_ni ld_vrnew_dt_ni)  
             apply ( simp add: split: if_split_asm)+
  apply (metis assms(5) ld_coh_dt_ni ld_vrnew_dt_ni)
             apply ( simp add: split: if_split_asm)+
         apply (metis assms(5) cas_coh_dt_ni cas_vrnew_dt_ni)
  apply (metis (no_types, opaque_lifting) assms(5) cas_coh_dt_ni cas_vrnew_dt_ni)
        apply ( simp add: split: if_split_asm)+
  apply (metis assms(5) cas_coh_dt_ni cas_vrnew_dt_ni)
  apply (metis assms(5) cas_coh_dt_ni cas_vrnew_dt_ni)
  apply ( simp add: split: if_split_asm)+
  apply (metis assms(5) ld_coh_dt_ni ld_vrnew_dt_ni)
  apply (metis assms(5) ld_coh_dt_ni ld_vrnew_dt_ni)
  by ( simp add: split: if_split_asm)+




lemma Begin_invocation_Read_global:
  assumes "thrdsvars"
and "  Read_inv  tb   ((pc \<sigma>) tb)  \<sigma>  "
and "Begin_invocation_inv ta  ((pc \<sigma>) ta) \<sigma>" 
 and " TML_Begin_invocation  ta   \<sigma> \<sigma>'"
and "total_wfs (\<tau> \<sigma>) "
  and "((pc \<sigma>) ta) \<in> {BeginPending, NotStarted} \<union> {Aborted} "
  and " ((pc \<sigma>)tb) \<in> {Aborted,ReadPending, ReadResponding} \<union> reading  " 
and " ta \<noteq> tb"
shows "  Read_inv  tb   ((pc \<sigma>') tb)  \<sigma>'" 
  using assms
  apply(simp add:Begin_invocation_inv_def Read_inv_def total_wfs_def TML_Begin_invocation_def Ready_total_def )
  apply  (cases" pc  \<sigma> tb"; simp ; cases "(pc \<sigma>) ta"; simp )
  apply (unfold Ready_total_def read_pre_def)
  apply (smt (verit))
  apply metis
  apply (metis PC.distinct(55))
  apply (metis PC.distinct(55))
    apply (metis PC.distinct(55))
  apply (metis PC.distinct(55))
  by (smt (verit))



lemma Write_Begin_invocation_global:
  assumes "thrdsvars"
and "  Write_inv  tb   ((pc \<sigma>) tb)  \<sigma>  "
and "Begin_invocation_inv ta  ((pc \<sigma>) ta) \<sigma>" 
    and "TML_Write  tb   \<sigma> \<sigma>'"
and "total_wfs (\<tau> \<sigma>) "
  and "((pc \<sigma>) ta) \<in> {BeginPending, NotStarted} \<union> {Aborted} "
 and "((pc \<sigma>) tb) \<in> {WritePending, WriteResponding } \<union> writing  \<union> {Aborted}"
and " ta \<noteq> tb"
shows "Begin_invocation_inv ta  ((pc \<sigma>') ta) \<sigma>'" 
  using assms
  apply(simp add:Begin_invocation_inv_def Write_inv_def TML_Write_def total_wfs_def  )

  apply (cases" pc  \<sigma> tb"; simp ; cases "(pc \<sigma>) ta"; simp )
  apply ( simp add: split: if_split_asm)+
  apply (metis assms(5) cas_coh_dt_ni cas_vrnew_dt_ni)
  apply (metis assms(5) cas_coh_dt_ni cas_vrnew_dt_ni)
              apply ( simp add: split: if_split_asm)+
  apply (metis assms(5) cas_coh_dt_ni cas_vrnew_dt_ni)
  apply (metis assms(5) cas_coh_dt_ni cas_vrnew_dt_ni)
             apply ( simp add: split: if_split_asm)+
  apply (metis assms(5) reg_coh_ni reg_vrnew_ni)
  using assms(5) reg_coh_ni reg_vrnew_ni apply presburger
             apply ( simp add: split: if_split_asm)+
  apply (metis assms(5) ld_coh_dt_ni ld_vrnew_dt_ni)
  apply (metis assms(5) ld_coh_dt_ni ld_vrnew_dt_ni)
  apply (metis assms(5) reg_coh_dt_ni st_vrnew_dt_ni)
  apply (metis assms(5) reg_coh_dt_ni st_vrnew_dt_ni)
  apply (metis assms(5) flo_coh_ni flo_vrnew_ni)
  by (metis assms(5) flo_coh_ni flo_vrnew_ni)






lemma Begin_invocation_Write_global:
  assumes "thrdsvars"
and "  Write_inv  tb   ((pc \<sigma>) tb)  \<sigma>  "
and "Begin_invocation_inv ta  ((pc \<sigma>) ta) \<sigma>" 
 and " TML_Begin_invocation  ta   \<sigma> \<sigma>'"
and "total_wfs (\<tau> \<sigma>) "
  and "((pc \<sigma>) ta) \<in> {BeginPending, NotStarted} \<union> {Aborted} "
  and "((pc \<sigma>) tb) \<in> {WritePending, WriteResponding } \<union> writing  \<union> {Aborted}"
and " ta \<noteq> tb"
shows "  Write_inv  tb   ((pc \<sigma>') tb)  \<sigma>'" 
  using assms
  apply(simp add:Begin_invocation_inv_def Write_inv_def total_wfs_def TML_Begin_invocation_def Ready_total_def )

  apply  (cases" pc  \<sigma> tb"; simp ; cases "(pc \<sigma>) ta"; simp )
  apply (unfold Ready_total_def read_pre_def)
  apply (smt (verit))
  apply metis
  apply (metis PC.distinct(55))
  apply (metis PC.distinct(55))
  apply (metis PC.distinct(55))
  apply metis
  apply metis
  apply (metis PC.distinct(55))
  apply metis
  apply metis
  apply (metis PC.distinct(55))
  apply metis
  apply metis
  apply (metis PC.distinct(55))
  apply metis
  apply metis
  apply (metis PC.distinct(55))
  apply metis
   apply metis
  by (smt (verit))





lemma Commit_Begin_invocation_global:
  assumes "thrdsvars"
and "  Commit_inv  tb   ((pc \<sigma>) tb)  \<sigma>  "
and "Begin_invocation_inv ta  ((pc \<sigma>) ta) \<sigma>" 
    and "TML_Commit  tb   \<sigma> \<sigma>'"
and "total_wfs (\<tau> \<sigma>) "
  and "((pc \<sigma>) ta) \<in> {BeginPending, NotStarted} \<union> {Aborted} "
 and "((pc \<sigma>) tb) \<in> {CommitPending,CommitResponding} \<union> committing  \<union> {Aborted}"
and " ta \<noteq> tb"
shows "Begin_invocation_inv ta  ((pc \<sigma>') ta) \<sigma>'" 
  using assms
  apply(simp add:Begin_invocation_inv_def Commit_inv_def TML_Commit_def total_wfs_def  )

  apply (cases" pc  \<sigma> tb"; simp ; cases "(pc \<sigma>) ta"; simp )
  apply ( simp add: split: if_split_asm)+
     apply (metis assms(5) sf_coh_ni sf_vrnew_dt_ni)
  apply (metis assms(5) sf_coh_ni sf_vrnew_dt_ni)
  apply (metis assms(5) reg_coh_dt_ni st_vrnew_dt_ni)
  by (metis assms(5) reg_coh_dt_ni st_vrnew_dt_ni)




lemma Begin_invocation_Commit_global:
  assumes "thrdsvars"
and "  Commit_inv  tb   ((pc \<sigma>) tb)  \<sigma>  "
and "Begin_invocation_inv ta  ((pc \<sigma>) ta) \<sigma>" 
 and " TML_Begin_invocation  ta   \<sigma> \<sigma>'"
and "total_wfs (\<tau> \<sigma>) "
  and "((pc \<sigma>) ta) \<in> {BeginPending, NotStarted} \<union> {Aborted} "
 and "((pc \<sigma>) tb) \<in> {CommitPending,CommitResponding} \<union> committing  \<union> {Aborted}"
and " ta \<noteq> tb"
shows "  Commit_inv  tb   ((pc \<sigma>') tb)  \<sigma>'" 
  using assms
  apply(simp add:Begin_invocation_inv_def Commit_inv_def total_wfs_def TML_Begin_invocation_def Ready_total_def )

  apply  (cases" pc  \<sigma> tb"; simp ; cases "(pc \<sigma>) ta"; simp )
  apply (unfold Ready_total_def read_pre_def)
  apply (smt (verit))
  apply (metis PC.distinct(55))
  apply metis
  apply metis
  apply (metis PC.distinct(55))
  apply metis
  apply metis
  apply (metis PC.distinct(55))
  by metis+


(***************************************)


lemma Read_invocation_local:
  assumes "thrdsvars"
and "total_wfs (\<tau> \<sigma>) "
and "Read_invocation_inv t  ((pc \<sigma>) t) \<sigma>" 
 and " TML_Read_invocation  t   \<sigma> \<sigma>'"
shows " Read_invocation_inv t  ((pc \<sigma>') t) \<sigma>'"  
  using assms
  apply (simp add: TML_Read_invocation_def Read_invocation_inv_def Ready_total_def   total_wfs_def   )
  apply (cases "pc \<sigma> t";simp  )
  apply (simp add: Ready_total_def)
  by (metis PC.distinct(1505))




(*****************************************************)

lemma cas_read_pre_ni:
assumes  "read_pre (\<tau> \<sigma>) ta b "
and "\<tau> \<sigma> [CAS glb regs (\<tau> \<sigma>) tb DTML.loc regs (\<tau> \<sigma>) tb DTML.loc c1]\<^sub>tb \<tau> \<sigma>'"
and "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
and " ta \<noteq> syst"
and "tb \<noteq> syst"
and "ta \<noteq> tb"
shows   "read_pre (\<tau> \<sigma>') ta b "
  using assms
  apply (unfold total_wfs_def read_pre_def)
 apply (subgoal_tac " ta \<noteq> tb ")
          prefer 2
  using thrdsvars_def apply linarith
  apply (subgoal_tac " (regs (\<tau> \<sigma>) ta DTML.loc) = (regs (\<tau> \<sigma>') ta DTML.loc)")
         prefer 2
  using reg_same_CAS_dt
   apply presburger
  apply (subgoal_tac "  valOf ( last_entry_lim (\<tau> \<sigma>') b (coh (\<tau> \<sigma>') ta  glb)) b (\<tau> \<sigma>) = valOf(  last_entry_lim (\<tau> \<sigma>) b (coh (\<tau> \<sigma>) ta glb)) b (\<tau> \<sigma>) ")
   prefer 2
  using assms(4) cas_le_lim_dt_ni apply presburger
  by (metis assms(4) cas_coh_dt_ni cas_coh_valof_dt_ni cas_le_lim_dt_ni cas_vrnew_dt_ni)



(* \<tau> \<sigma> [r3 \<leftarrow> glb]\<^sub>tb \<tau> \<sigma>'*)
lemma read_read_pre_ni:
assumes  "read_pre (\<tau> \<sigma>) ta g "
and "( \<tau> \<sigma>) [f \<leftarrow> v]\<^sub>tb ( \<tau> \<sigma>')"
and "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
and " ta \<noteq> syst"
and "tb \<noteq> syst"
and "ta \<noteq> tb"
shows   "read_pre (\<tau> \<sigma>') ta g "
  using assms
apply (subgoal_tac " ta \<noteq> tb ")
          prefer 2
  using thrdsvars_def apply linarith
  apply (unfold total_wfs_def read_pre_def)
  apply (intro conjI)
      apply (metis reg_same_ld_dr)
  using assms(4) ld_coh_dt_ni apply presburger
  apply (subgoal_tac " regs (\<tau> \<sigma>) ta DTML.loc = regs (\<tau> \<sigma>') ta DTML.loc")
     prefer 2
  using reg_same_ld_dr apply presburger
    apply (subgoal_tac " (coh (\<tau> \<sigma>') ta glb) = (coh (\<tau> \<sigma>) ta glb)")
     prefer 2
  using assms(4) ld_coh_dt_ni apply presburger
  apply (simp add: valOf_def)
    apply (metis ld_step_mem survived_val_preserved_load)
   apply (metis assms(4) ld_le_coh_ni ld_vrnew_dt_ni)
  by (metis assms(4) ld_coh_dt_ni ld_vrnew_dt_ni)


lemma read_cas_lv_ni:
assumes "(\<forall>l. [l]\<^sub>ta \<tau> \<sigma> = {lastVal l (\<tau> \<sigma>)})"
and " \<tau> \<sigma> [CAS glb regs (\<tau> \<sigma>) tb DTML.loc regs (\<tau> \<sigma>) tb DTML.loc c1]\<^sub>tb \<tau> \<sigma>' "
and "regs (\<tau> \<sigma>') tb  c1 = 1"
and "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
and " ta \<noteq> syst"
and "tb \<noteq> syst"
and "ta \<noteq> tb"
shows "\<forall>l. [l]\<^sub>ta \<tau> \<sigma>' = {lastVal l (\<tau> \<sigma>')}"
  using assms
  apply (unfold  total_wfs_def)
  apply clarify
  apply (case_tac " l \<noteq> glb ")

  apply (smt (verit, ccfv_SIG) cas_le_daddr cas_ov_daddr_ni_s ex_in_conv)
  apply (subgoal_tac " lastVal l (\<tau> \<sigma>) = regs (\<tau> \<sigma>) tb DTML.loc ")
   prefer 2
   apply(simp add: step_def)
  apply clarify
   apply (subgoal_tac " \<tau> \<sigma>' = cas_succ_trans tb ind glb (regs (\<tau> \<sigma>) tb DTML.loc) (regs (\<tau> \<sigma>) tb DTML.loc) c1 nv
        mnv (\<tau> \<sigma>)")
  prefer 2
  apply (metis Zero_neq_Suc cas_fail_reg)
  apply (metis Zero_neq_Suc assms(2) cas_fail_diff_lv)
  apply (subgoal_tac " lastVal l (\<tau> \<sigma>') = regs (\<tau> \<sigma>) tb DTML.loc ")
 prefer 2
   apply(simp add: step_def)
  apply clarify
   apply (subgoal_tac " \<tau> \<sigma>' = cas_succ_trans tb ind glb (regs (\<tau> \<sigma>) tb DTML.loc) (regs (\<tau> \<sigma>) tb DTML.loc) c1 nv
        mnv (\<tau> \<sigma>)")
    prefer 2
  apply (metis Zero_neq_Suc cas_fail_reg)
   apply (metis assms(2) assms(3) cas_succ_lv_lc lastVal_def)
  apply (subgoal_tac " lastVal l (\<tau> \<sigma>')  \<in>  [l]\<^sub>ta  (\<tau> \<sigma>')")
   prefer 2

  using lev_in_ov apply blast

  by (smt (z3) Set.set_insert cas_nov_lc lev_in_ov singleton_insert_inj_eq subset_iff subset_insertI)



lemma Begin_Read_invocation_global:
  assumes "thrdsvars"
and "  Begin_inv  tb   ((pc \<sigma>) tb)  \<sigma>  "
and "Read_invocation_inv ta  ((pc \<sigma>) ta) \<sigma>" 
   and " TML_Begin  tb    \<sigma> \<sigma>'"
and "total_wfs (\<tau> \<sigma>) "
  and "((pc \<sigma>) ta) \<in> {ReadPending, Ready} \<union> {Aborted} "
  and " ((pc \<sigma>)tb) \<in> {Aborted, BeginPending, BeginResponding} \<union> beginning  " 
and " ta \<noteq> tb"
shows "Read_invocation_inv ta  ((pc \<sigma>') ta) \<sigma>'" 
  using assms
 apply (unfold thrdsvars_def )
  apply (simp add:TML_Begin_def Begin_inv_def Read_invocation_inv_def total_wfs_def  )
  apply (cases "(pc \<sigma>) ta";simp; cases "(pc \<sigma>) tb" ;simp)
  apply (unfold Ready_total_def read_pre_def)
  apply (smt (verit))
 apply (case_tac " \<not> readAux \<sigma>' ta \<and>  \<not> writeAux \<sigma>' ta ")
             apply simp
        apply (smt (z3) PC.distinct(209) assms(5) lastVal_ni ld_ov_ni reg_same_ld_dr)
       apply (case_tac "  readAux \<sigma>' ta \<and>  \<not> writeAux \<sigma>' ta ")
       apply simp
  apply (smt (z3) PC.distinct(209) assms(5) ld_coh_dt_ni ld_crash ld_le_lim_ni ld_step_mem ld_vrnew_dt_ni reg_same_ld_dr valOf_def)
  apply simp
  apply (smt (verit) PC.distinct(209) assms(5) lastVal_ni ld_oav_ni ld_ov_ni reg_same_ld_dr)

  apply ( simp add: split: if_split_asm)
  apply (metis PC.distinct(283))
      apply (metis PC.distinct(283))

     apply (smt (verit))
apply (case_tac " \<not> readAux \<sigma>' ta \<and>  \<not> writeAux \<sigma>' ta ")
             apply simp
        apply (smt (z3) PC.distinct(209) assms(5) lastVal_ni ld_ov_ni reg_same_ld_dr)
       apply (case_tac "  readAux \<sigma>' ta \<and>  \<not> writeAux \<sigma>' ta ")
       apply simp
  apply (smt (z3) PC.distinct(209) assms(5) ld_coh_dt_ni ld_crash ld_le_lim_ni ld_step_mem ld_vrnew_dt_ni reg_same_ld_dr valOf_def)
  apply simp
  apply (smt (verit) PC.distinct(209) assms(5) lastVal_ni ld_oav_ni ld_ov_ni reg_same_ld_dr)
  apply ( simp add: split: if_split_asm)
  apply (metis PC.distinct(283))
  apply (metis PC.distinct(283))
  by ( simp add: split: if_split_asm)




lemma Read_invocation_Begin_global:
  assumes "thrdsvars"
and "  Begin_inv  tb   ((pc \<sigma>) tb)  \<sigma>  "
and "Read_invocation_inv ta  ((pc \<sigma>) ta) \<sigma>" 
 and " TML_Read_invocation  ta   \<sigma> \<sigma>'"
and "total_wfs (\<tau> \<sigma>) "
  and "((pc \<sigma>) ta) \<in> {ReadPending, Ready} \<union> {Aborted} "
  and " ((pc \<sigma>)tb) \<in> {Aborted,BeginPending, BeginResponding} \<union> beginning " 
and " ta \<noteq> tb"
shows "  Begin_inv  tb   ((pc \<sigma>') tb)  \<sigma>'" 
  using assms
  apply(simp add:Read_invocation_inv_def Begin_inv_def total_wfs_def TML_Read_invocation_def Ready_total_def )

  apply  (cases" pc  \<sigma> tb"; simp ; cases "(pc \<sigma>) ta"; simp )
  apply (metis PC.distinct(1505))
  apply (metis PC.distinct(1505))
  apply (unfold Ready_total_def read_pre_def)
  by (smt (verit))





lemma Read_Read_invocation_global:
  assumes "thrdsvars"
and "  Read_inv  tb   ((pc \<sigma>) tb)  \<sigma>  "
and "Read_invocation_inv ta  ((pc \<sigma>) ta) \<sigma>" 
   and " TML_Read  tb    \<sigma> \<sigma>'"
and "total_wfs (\<tau> \<sigma>) "
  and "((pc \<sigma>) ta) \<in> {ReadPending, Ready} \<union> {Aborted} "
  and " ((pc \<sigma>)tb) \<in> {Aborted,ReadPending, ReadResponding} \<union> reading  " 
and " ta \<noteq> tb"
shows "Read_invocation_inv ta  ((pc \<sigma>') ta) \<sigma>'" 
  using assms
 apply (unfold thrdsvars_def )
  apply (simp add:TML_Read_def Read_inv_def Read_invocation_inv_def  )
  apply (cases "(pc \<sigma>) ta";simp; cases "(pc \<sigma>) tb" ;simp)
  apply (unfold total_wfs_def Ready_total_def)
  apply (smt (verit) PC.distinct(803) fun_upd_other)

  apply (unfold read_pre_def)
 apply (case_tac " \<not> readAux \<sigma>' ta \<and>  \<not> writeAux \<sigma>' ta ")
             apply simp
             apply (smt (verit) PC.distinct(859) assms(5) lastVal_ni ld_ov_ni reg_same_ld_dt)
  apply (case_tac " odd (regs (\<tau> \<sigma>') ta DTML.loc) " )
            apply simp
  apply (smt (verit) PC.distinct(859) assms(5) lastVal_ni ld_oav_ni ld_ov_ni reg_same_ld_dt)
            apply simp
  apply (case_tac " readAux \<sigma>' ta \<and>  \<not> writeAux \<sigma>' ta ")
  apply simp
  apply (intro conjI impI)
  apply (metis PC.distinct(859))
  apply clarify
  apply (intro conjI)
  apply (metis assms(5) ld_coh_dt_ni)
  apply (metis assms(5) ld_coh_valof_dt_ni reg_same_ld_dr)
  apply (metis assms(5) ld_coh_dt_ni ld_le_lim_ni ld_vrnew_dt_ni)
  apply (metis assms(5) ld_coh_dt_ni ld_vrnew_dt_ni)
  apply (metis reg_same_ld_dr)
   apply ( simp add: split: if_split_asm)
  apply (metis PC.distinct(913))
  apply (metis PC.distinct(913))
   apply ( simp add: split: if_split_asm)+
  apply (smt (verit) PC.distinct(965) assms(5) cas_coh_dt_ni cas_coh_valof_dt_ni cas_fail_diff_lv cas_lc cas_le_daddr cas_le_lim_dt_ni cas_ov_daddr_dt_sx_ni cas_vrnew_dt_ni lastVal_def numeral_1_eq_Suc_0 numerals(1) reg_same_CAS_dt zero_neq_one)
apply (subgoal_tac " \<forall> a. [a]\<^sub>ta \<tau> \<sigma>' = [a]\<^sub>ta \<tau> \<sigma>   ")
  prefer 2
         apply (simp add: step_def)
         apply clarify
  apply (case_tac "  \<tau> \<sigma>' =
       cas_fail_trans tb ind glb (regs (\<tau> \<sigma>) tb DTML.loc)
        (regs (\<tau> \<sigma>) tb DTML.loc) c1 (\<tau> \<sigma>)")
  prefer 2
  apply (metis One_nat_def cas_suc_reg)
  apply (metis cas_fail_ov_ni)

        apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc)")
                     apply simp
  apply (smt (verit) PC.distinct(965) assms(5) cas_fail_diff_lv cas_fail_lastVal_same cas_fail_oav_ni cas_le_daddr reg_same_CAS_dt)
  apply (case_tac " \<not> readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
  apply simp
  apply (metis (no_types, lifting) PC.distinct(965) assms(5) cas_fail_lastVal_same cas_le_daddr cas_sv_lc numeral_1_eq_Suc_0 numerals(1) reg_same_CAS_dt)
  apply simp
          apply clarify
  apply (intro conjI impI)
  apply (metis PC.distinct(965))
  apply (metis reg_same_CAS_dt)
  apply (metis PC.distinct(803) assms(1) assms(5) cas_read_pre_ni read_pre_def)
  apply (metis reg_same_CAS_dt)
            apply (intro conjI)
  apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc)")
                     apply simp
  apply (metis (no_types, lifting) PC.distinct(1015) assms(5) lastVal_ni ld_ov_ni reg_same_ld_dt)
         apply simp
  apply (case_tac " \<not> readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
  apply simp
   apply (metis PC.distinct(1015) reg_same_ld_dt)

              apply simp
   apply (metis PC.distinct(1015) reg_same_ld_dt)
 apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc)")
                     apply simp
  apply (metis (no_types, lifting) PC.distinct(1015) assms(5) lastVal_ni ld_ov_ni reg_same_ld_dt)
         apply simp
  apply (case_tac " \<not> readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
              apply simp

  apply (smt (verit) PC.distinct(1015) assms(5) lastVal_ni ld_ov_ni reg_same_ld_dt)

             apply simp
  apply (smt (verit) PC.distinct(1015) assms(5) ld_coh_dt_ni ld_coh_valof_dt_ni ld_le_coh_ni ld_vrnew_dt_ni reg_same_ld_dt)
  apply simp
            apply (smt (verit) PC.distinct(1015) assms(5) even_add lastVal_ni ld_oav_ni ld_ov_ni reg_same_ld_dt)
           apply (simp add: split if_splits)
  apply (case_tac " regs (\<tau> \<sigma>) tb r3 = regs (\<tau> \<sigma>) tb DTML.loc")
  apply simp
            apply (smt (verit) PC.distinct(1063) PC.simps(1652) pc_aux)
  apply simp
  apply (metis PC.distinct(1063))
  

 apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc)")
                     apply simp
  apply (metis PC.distinct(803))

         apply simp
  apply (case_tac " \<not> readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
  apply simp
   
   apply (metis PC.distinct(803))

         apply simp
  apply (metis PC.distinct(803))






 apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc)")
                     apply simp
  apply (smt (verit) PC.distinct(859) assms(5) lastVal_ni ld_oav_ni ld_ov_ni reg_same_ld_dt)
         apply simp
  apply (case_tac " \<not> readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
  apply simp
  apply (smt (verit) PC.distinct(859) assms(5) lastVal_ni ld_ov_ni reg_same_ld_dt)
         apply simp
  apply (smt (z3) PC.distinct(1505) PC.distinct(859) assms(1) assms(5) ld_coh_dt_ni read_pre_def read_read_pre_ni)
  apply ( simp add: split: if_split_asm)
  apply (metis PC.distinct(913))
        apply (metis PC.distinct(913))
  apply ( simp add: split: if_split_asm)


apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc)")
         apply simp
  apply (metis One_nat_def cas_nlv_lc lastVal_def zero_neq_one)
  apply (case_tac " \<not> readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
         apply simp
  apply (subgoal_tac "  lastVal glb (\<tau> \<sigma>') =  lastVal glb (\<tau> \<sigma>) ")
  prefer 2
  apply (metis One_nat_def cas_fail_diff_lv cas_lc lastVal_def zero_neq_one)
  using  reg_same_CAS_dt 
         apply (metis (no_types, lifting) PC.distinct(965) assms(5) cas_le_daddr cas_ov_daddr_dt_sx_ni)
  apply simp
  apply (smt (verit) PC.distinct(965) assms(5) cas_coh_dt_ni cas_coh_valof_dt_ni cas_le_lim_dt_ni cas_vrnew_dt_ni reg_same_CAS_dt)

apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc)")
        apply simp
  apply (subgoal_tac " syst \<noteq> tb ")
  prefer 2
  apply (metis PC.distinct(965))
        apply simp
        apply (intro conjI)
  apply (metis reg_same_CAS_dt)
  apply (metis cas_fail_diff_lv cas_fail_lastVal_dt_ni)
  apply (metis cas_fail_lv_ni lastVal_def reg_same_CAS_dt)
  apply (metis reg_same_CAS_dt)
  apply (metis cas_fail_lv_ni lastVal_def reg_same_CAS_dt)
  apply (metis cas_fail_diff_lv cas_fail_lastVal_dt_ni)
  apply (metis reg_same_CAS_dt)
  apply (metis cas_fail_diff_lv cas_fail_lastVal_dt_ni)
  apply (metis assms(5) cas_fail_diff_lv cas_fail_lastVal_same cas_fail_oav_ni cas_le_daddr)
  apply (metis cas_fail_lv_ni lastVal_def reg_same_CAS_dt) 

  apply (case_tac " \<not> readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
         apply simp
    apply (subgoal_tac " syst \<noteq> tb ")
  prefer 2
  apply (metis PC.distinct(965))
        apply simp
  apply (subgoal_tac " lastVal glb (\<tau> \<sigma>') = lastVal glb (\<tau> \<sigma>) ")
  prefer 2
         apply (smt (verit) One_nat_def assms(5) cas_fail_lastVal_same cas_sv_lc)
  apply (subgoal_tac " regs (\<tau> \<sigma>') ta DTML.loc  = regs (\<tau> \<sigma>) ta DTML.loc ")
         prefer 2
  using reg_same_CAS_dt apply presburger
  apply (metis assms(5) cas_le_daddr cas_ov_daddr_dt_sx_ni)
  apply simp
  apply (smt (z3) PC.distinct(965) assms(5) cas_coh_dt_ni cas_coh_valof_dt_ni cas_le_lim_dt_ni cas_vrnew_dt_ni reg_same_CAS_dt)
 apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc)")
        apply simp
       apply (smt (verit) PC.distinct(1015) assms(5) lastVal_ni ld_oav_ni ld_ov_ni reg_same_ld_dt)
  apply simp

apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc)")
         apply simp
  apply (case_tac " \<not> readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
       apply simp
       apply (smt (verit) PC.distinct(1015) assms(5) lastVal_ni ld_ov_ni reg_same_ld_dt)
  apply simp
  apply (smt (verit) PC.distinct(1015) assms(5) ld_coh_dt_ni ld_coh_valof_dt_ni ld_le_coh_ni ld_vrnew_dt_ni reg_same_ld_dt)
  apply( simp add: split: if_split_asm)+
  apply (metis PC.distinct(1063))
  apply (metis PC.distinct(1063))
  by( simp add: split: if_split_asm)+





lemma Read_invocation_Read_global:
  assumes "thrdsvars"
and "  Read_inv  tb   ((pc \<sigma>) tb)  \<sigma>  "
and "Read_invocation_inv ta  ((pc \<sigma>) ta) \<sigma>" 
 and " TML_Read_invocation  ta   \<sigma> \<sigma>'"
and "total_wfs (\<tau> \<sigma>) "
  and "((pc \<sigma>) ta) \<in> {ReadPending, Ready} \<union> {Aborted} "
  and " ((pc \<sigma>)tb) \<in> {Aborted,ReadPending, ReadResponding} \<union> reading  " 
and " ta \<noteq> tb"
shows "  Read_inv  tb   ((pc \<sigma>') tb)  \<sigma>'" 
  using assms
  apply(simp add:Read_invocation_inv_def Read_inv_def total_wfs_def TML_Read_invocation_def Ready_total_def )
  apply  (cases" pc  \<sigma> tb"; simp ; cases "(pc \<sigma>) ta"; simp )
  apply (unfold Ready_total_def read_pre_def)
  apply (smt (verit))
  apply metis
  apply (metis PC.distinct(1505))
  apply (metis PC.distinct(1505))
  apply (metis PC.distinct(1505))
  apply (metis PC.distinct(1505))
  by (smt (verit))


lemma upreg_read_pre_ni:
assumes  "read_pre (\<tau> \<sigma>) ta b "
and " \<tau> \<sigma>' = (update_reg tb DTML.loc (lastVal glb (\<tau> \<sigma>)) (\<tau> \<sigma>)) "
and "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
and " ta \<noteq> syst"
and "tb \<noteq> syst"
and "ta \<noteq> tb"
shows   "read_pre (\<tau> \<sigma>') ta b "
 using assms
  apply (unfold total_wfs_def read_pre_def thrdsvars_def)
  apply (intro conjI)
     apply (metis reg_dt_ni)
    apply (metis (mono_tags, lifting) assms(4) reg_coh_ni)
   apply (unfold valOf_def)
  apply (metis (mono_tags, lifting) assms(4) reg_coh_ni reg_dt_ni reg_write__crash reg_write_mem)
  apply (subgoal_tac "vrnew (\<tau> \<sigma>') ta = vrnew (\<tau> \<sigma>) ta ")
   prefer 2
   apply (simp add: update_reg_def)
  using assms(4) reg_coh_lim_dt_ni apply presburger
 apply (subgoal_tac "vrnew (\<tau> \<sigma>') ta = vrnew (\<tau> \<sigma>) ta ")
   prefer 2
   apply (simp add: update_reg_def)
  using assms(4) reg_coh_ni by presburger

lemma Write_Read_invocation_global:
  assumes "thrdsvars"
and "  Write_inv  tb   ((pc \<sigma>) tb)  \<sigma>  "
and "Read_invocation_inv ta  ((pc \<sigma>) ta) \<sigma>" 
   and " TML_Write  tb    \<sigma> \<sigma>'"
and "total_wfs (\<tau> \<sigma>) "
  and "((pc \<sigma>) ta) \<in> {ReadPending, Ready} \<union> {Aborted} "
  and " ((pc \<sigma>)tb) \<in> {Aborted,WritePending, WriteResponding} \<union> writing  " 
and " ta \<noteq> tb"
shows "Read_invocation_inv ta  ((pc \<sigma>') ta) \<sigma>'" 
  using assms
 apply (unfold thrdsvars_def )
  apply (simp add:TML_Write_def Write_inv_def Read_invocation_inv_def read_pre_def Ready_total_def  )
  apply   (cases "(pc \<sigma>) ta";simp; cases "(pc \<sigma>) tb" ;simp)
  apply (simp add: Ready_total_def)
  apply (metis PC.distinct(1153))
                     apply ( simp add: split: if_split_asm)
  apply (simp add: Ready_total_def)
                      apply (metis PC.distinct(1195))
  apply (simp add: Ready_total_def)
  apply (metis PC.distinct(1195))
                     apply ( simp add: split: if_split_asm)
  apply (simp add: Ready_total_def)
 apply (case_tac "  (odd (regs (\<tau> \<sigma>) ta DTML.loc)) ")
  apply simp
                      apply (intro conjI impI)
  apply (metis PC.distinct(1235))
  apply (metis reg_same_CAS_dt)
  using  total_wfs_def 
  apply (meson cas_fail_lastVal_dt_ni)
  apply (metis cas_fail_lastVal_same reg_same_CAS_dt)
  apply (metis reg_same_CAS_dt)
  apply (metis cas_fail_lastVal_same reg_same_CAS_dt)
  using  total_wfs_def 
  apply (meson cas_fail_lastVal_dt_ni)
  apply (metis reg_same_CAS_dt)
  using  total_wfs_def 
  apply (meson cas_fail_lastVal_dt_ni)
  using  total_wfs_def   
  apply (metis cas_fail_lastVal_same cas_fail_oav_ni cas_le_daddr)
                      apply (metis cas_fail_lastVal_same reg_same_CAS_dt)
                     apply (unfold total_wfs_def)
 apply (case_tac "  (odd (regs (\<tau> \<sigma>) ta DTML.loc)) ")
  apply meson
apply (case_tac "   \<not> readAux \<sigma> ta \<and>
      \<not> writeAux \<sigma>  ta ")
                      apply simp
                      apply (intro conjI impI)
  apply (metis PC.distinct(1235))
  apply (metis reg_same_CAS_dt)
  apply (elim disjE conjE)
  apply (subgoal_tac " even (regs (\<tau> \<sigma>') ta DTML.loc) \<and>
    regs (\<tau> \<sigma>') ta DTML.loc = lastVal glb (\<tau> \<sigma>') \<and>
    (\<forall>l. [l]\<^sub>ta \<tau> \<sigma>' = {lastVal l (\<tau> \<sigma>')})")
                      prefer 2
  apply (intro conjI)
  apply (metis reg_same_CAS_dt)
  apply (metis assms(5) cas_fail_lastVal_same reg_same_CAS_dt)
  apply (metis cas_fail_lastVal_dt_ni)
  apply blast
  apply (metis assms(5) cas_fail_lastVal_same reg_same_CAS_dt)
  apply (metis reg_same_CAS_dt)
 apply (case_tac "  (odd (regs (\<tau> \<sigma>) ta DTML.loc)) ")
  apply meson

apply (case_tac "   \<not> readAux \<sigma> ta \<and>
      \<not> writeAux \<sigma>  ta ")
                      apply simp
                      apply (intro conjI impI)
  apply (metis PC.distinct(1235))
                      apply (metis reg_same_CAS_dt)
                      apply (unfold read_pre_def)
  apply simp
  apply (smt (z3) assms(5) cas_coh_dt_ni cas_coh_valof_dt_ni cas_le_lim_dt_ni cas_vrnew_dt_ni reg_same_CAS_dt)
                     apply (metis reg_same_CAS_dt)
  apply (unfold Ready_total_def)
 apply (case_tac "  (odd (regs (\<tau> \<sigma>) ta DTML.loc)) ")
  apply (metis cas_nlv_lc gr0_conv_Suc lastVal_def nat.distinct(1))


apply (case_tac "   \<not> readAux \<sigma> ta \<and>
      \<not> writeAux \<sigma>  ta ")
                      apply simp
                      apply (intro conjI impI)
  apply (metis PC.distinct(1235))
                      apply (metis reg_same_CAS_dt)
                      apply (unfold read_pre_def)
  apply (smt (verit) cas_lc cas_nlv_lc lastVal_def less_Suc_eq not_less_iff_gr_or_eq reg_same_CAS_dt)
  apply (metis reg_same_CAS_dt)
  apply simp
  apply (smt (z3) PC.distinct(1235) assms(5) cas_coh_dt_ni cas_coh_valof_dt_ni cas_le_lim_dt_ni cas_vrnew_dt_ni reg_same_CAS_dt)
  apply (case_tac "  (odd (regs (\<tau> \<sigma>) ta DTML.loc)) ")
  apply simp
apply (case_tac "   \<not> readAux \<sigma> ta \<and>
      \<not> writeAux \<sigma>  ta ")
  apply simp
  apply (metis PC.distinct(1273) even_Suc reg_dt_ni reg_write_lastVal_ni)

  apply simp
  using  upreg_read_pre_ni 
  apply (smt (z3) PC.distinct(1273) PC.distinct(803) assms(5) read_pre_def reg_dt_ni thrdsvars_def)
                  apply (simp add: split if_splits)
  apply (case_tac " inLoc \<sigma> tb \<in> dom (log \<sigma>) ")
                   apply simp
  apply (metis PC.distinct(1309))
                  apply simp
                  apply (metis PC.distinct(1309))
                 apply simp
  using
 lastVal_ni ld_coh_dt_ni ld_coh_valof_dt_ni ld_le_lim_ni ld_oav_ni ld_ov_ni ld_vrnew_dt_ni reg_same_ld_dt
  apply (smt (verit) PC.distinct(1343) assms(5))






  apply (case_tac "  (odd (regs (\<tau> \<sigma>) ta DTML.loc)) ")
  apply simp
apply (case_tac "   \<not> readAux \<sigma> ta \<and>
      \<not> writeAux \<sigma>  ta ")
  apply simp
                 apply (metis PC.distinct(1375))
  apply simp
  apply (metis PC.distinct(1375))


 apply (case_tac "  (odd (regs (\<tau> \<sigma>) ta DTML.loc)) ")
  apply simp
apply (case_tac "   \<not> readAux \<sigma> ta \<and>
      \<not> writeAux \<sigma>  ta ")
  apply simp
  apply (metis PC.distinct(1405) assms(5) reg_same_st st_lv__daddr_ni)
 apply (case_tac "  (odd (regs (\<tau> \<sigma>) ta DTML.loc)) ")
  apply simp
apply (case_tac "   \<not> readAux \<sigma> ta \<and>
      \<not> writeAux \<sigma>  ta ")
                apply simp
  using  reg_coh_dt_ni reg_same_st st_coh_valof_dt_ni st_le_lim_dt_ni st_vrnew_dt_ni
(*hereeeeeee*)
apply (case_tac "  (odd (regs (\<tau> \<sigma>) ta DTML.loc)) ")
  apply simp
apply (case_tac "   \<not> readAux \<sigma> ta \<and>
      \<not> writeAux \<sigma>  ta ")
                apply simp
                apply simp

  apply (metis (no_types, lifting) PC.distinct(1405) assms(5))

 apply (case_tac "  (odd (regs (\<tau> \<sigma>) ta DTML.loc)) ")
  apply simp
apply (case_tac "   \<not> readAux \<sigma> ta \<and>
      \<not> writeAux \<sigma>  ta ")
                apply simp
  using  reg_coh_dt_ni reg_same_st st_coh_valof_dt_ni st_le_lim_dt_ni st_vrnew_dt_ni


  apply (metis PC.distinct(1433) assms(5) flo_lastVal_ni reg_same_flo)

apply (case_tac "  (odd (regs (\<tau> \<sigma>) ta DTML.loc)) ")
               apply simp
apply (case_tac "   \<not> readAux \<sigma> ta \<and>
      \<not> writeAux \<sigma>  ta ")
                apply simp
              apply simp
  apply (smt (verit) PC.distinct(1433) assms(5) flo_coh_ni flo_coh_valof_dt_ni flo_le_lim_dt_ni flo_vrnew_ni reg_same_flo)

apply (case_tac "  (odd (regs (\<tau> \<sigma>) ta DTML.loc)) ")
               apply simp
apply (case_tac "   \<not> readAux \<sigma> ta \<and>
      \<not> writeAux \<sigma>  ta ")
                apply simp
  apply simp           
  apply (metis PC.distinct(1153))

apply (case_tac "  (odd (regs (\<tau> \<sigma>) ta DTML.loc)) ")
               apply simp
apply (case_tac "   \<not> readAux \<sigma> ta \<and>
      \<not> writeAux \<sigma>  ta ")
                apply simp
              apply (metis PC.distinct(1153))
  apply simp
  apply (metis PC.distinct(1153))



                     apply ( simp add: split: if_split_asm)
  apply (metis PC.distinct(1195))
            apply (metis PC.distinct(1195))
                     apply ( simp add: split: if_split_asm)
apply (case_tac "  (odd (regs (\<tau> \<sigma>) ta DTML.loc)) ")
  apply simp
                      apply (intro conjI impI)
  apply (metis PC.distinct(1235))
  apply (metis reg_same_CAS_dt)
  using  total_wfs_def 
                     apply (meson cas_fail_lastVal_dt_ni)
  apply (metis assms(5) cas_fail_lastVal_same reg_same_CAS_dt)
  apply (metis reg_same_CAS_dt)
  apply (metis cas_fail_lv_ni lastVal_def reg_same_CAS_dt)
  apply (meson cas_fail_lastVal_dt_ni)
  apply (metis reg_same_CAS_dt)
  apply (meson cas_fail_lastVal_dt_ni)
  apply (metis assms(5) cas_fail_lastVal_same cas_fail_oav_ni cas_le_daddr)
  apply (metis cas_fail_lv_ni lastVal_def reg_same_CAS_dt)

apply (case_tac "   \<not> readAux \<sigma> ta \<and>
      \<not> writeAux \<sigma>  ta ")
                      apply simp
                      apply (intro conjI impI)
  apply (metis PC.distinct(1235))
  apply (metis reg_same_CAS_dt)
  apply (elim disjE conjE)
  apply (subgoal_tac " even (regs (\<tau> \<sigma>') ta DTML.loc) \<and>
    regs (\<tau> \<sigma>') ta DTML.loc = lastVal glb (\<tau> \<sigma>') \<and>
    (\<forall>l. [l]\<^sub>ta \<tau> \<sigma>' = {lastVal l (\<tau> \<sigma>')})")
                      prefer 2
  apply (intro conjI)
  apply (metis reg_same_CAS_dt)
  apply (metis assms(5) cas_fail_lastVal_same reg_same_CAS_dt)
  apply (metis cas_fail_lastVal_dt_ni)
  apply blast
  apply (metis assms(5) cas_fail_lastVal_same reg_same_CAS_dt)
  apply (metis reg_same_CAS_dt)
 apply (case_tac "  (odd (regs (\<tau> \<sigma>) ta DTML.loc)) ")
  apply meson

apply (case_tac "   \<not> readAux \<sigma> ta \<and>
      \<not> writeAux \<sigma>  ta ")
                      apply simp
                      apply (intro conjI impI)
  apply (metis PC.distinct(1235))
                      apply (metis reg_same_CAS_dt)
  apply simp
  apply (smt (z3) assms(5) cas_coh_dt_ni cas_coh_valof_dt_ni cas_le_lim_dt_ni cas_vrnew_dt_ni reg_same_CAS_dt)
                     apply (metis reg_same_CAS_dt)
 apply (case_tac "  (odd (regs (\<tau> \<sigma>) ta DTML.loc)) ")
  apply (metis cas_nlv_lc gr0_conv_Suc lastVal_def nat.distinct(1))


apply (case_tac "   \<not> readAux \<sigma> ta \<and>
      \<not> writeAux \<sigma>  ta ")
                      apply simp
                      apply (intro conjI impI)
  apply (metis PC.distinct(1235))
                      apply (metis reg_same_CAS_dt)
  apply (smt (verit) cas_lc cas_nlv_lc lastVal_def less_Suc_eq not_less_iff_gr_or_eq reg_same_CAS_dt)
  apply (metis reg_same_CAS_dt)
  apply simp
  apply (smt (z3) PC.distinct(1235) assms(5) cas_coh_dt_ni cas_coh_valof_dt_ni cas_le_lim_dt_ni cas_vrnew_dt_ni reg_same_CAS_dt)
  apply (case_tac "  (odd (regs (\<tau> \<sigma>) ta DTML.loc)) ")
  apply simp
apply (case_tac "   \<not> readAux \<sigma> ta \<and>
      \<not> writeAux \<sigma>  ta ")
  apply simp
  apply (metis PC.distinct(1273) even_Suc reg_dt_ni reg_write_lastVal_ni)


  apply simp
  using  upreg_read_pre_ni 
  apply (metis PC.distinct(1273) PC.distinct(1505) assms(5) read_pre_def reg_coh_ni thrdsvars_def)

                  apply (simp add: split if_splits)
  apply (case_tac " inLoc \<sigma> tb \<in> dom (log \<sigma>) ")
                   apply simp
  apply (metis PC.distinct(1309))
                  apply simp
         apply (metis PC.distinct(1309))

  apply (case_tac "  (odd (regs (\<tau> \<sigma>) ta DTML.loc)) ")
  apply simp
apply (case_tac "   \<not> readAux \<sigma> ta \<and>
      \<not> writeAux \<sigma>  ta ")
         apply simp
         apply (metis PC.distinct(1343) assms(5) lastVal_ni reg_same_ld_dt)
  apply simp
  apply (metis PC.distinct(1343) PC.distinct(1505) assms(1) assms(5) read_pre_def read_read_pre_ni)






  apply (case_tac "  (odd (regs (\<tau> \<sigma>) ta DTML.loc)) ")
  apply simp
apply (case_tac "   \<not> readAux \<sigma> ta \<and>
      \<not> writeAux \<sigma>  ta ")
  apply simp
  apply (metis PC.distinct(1375))
apply (case_tac "   \<not> readAux \<sigma> ta \<and>
       writeAux \<sigma>  ta ")
  apply meson
  apply simp
  apply (metis PC.distinct(1375))


 apply (case_tac "  (odd (regs (\<tau> \<sigma>) ta DTML.loc)) ")
  apply simp
apply (case_tac "   \<not> readAux \<sigma> ta \<and>
      \<not> writeAux \<sigma>  ta ")
       apply simp
  apply (metis PC.distinct(1405) assms(5) reg_same_st st_lv__daddr_ni)
      apply simp
  apply (metis (no_types, lifting) PC.distinct(1405) assms(5) reg_coh_dt_ni reg_same_st st_coh_valof_dt_ni st_le_lim_dt_ni st_vrnew_dt_ni)

  apply simp

 apply (case_tac "  (odd (regs (\<tau> \<sigma>) ta DTML.loc)) ")
  apply simp
apply (case_tac "   \<not> readAux \<sigma> ta \<and>
      \<not> writeAux \<sigma>  ta ")
      apply simp
  apply (metis PC.distinct(1433) assms(5) flo_lastVal_ni reg_same_flo)
      apply simp
  apply (smt (z3) PC.distinct(1433) assms(5) assms(8) flo_coh_ni flo_coh_valof_dt_ni flo_le_lim_dt_ni flo_vrnew_ni reg_same_flo)
  apply simp
    apply ( simp add: split: if_split_asm)
                     apply ( simp add: split: if_split_asm)
  by ( simp add: split: if_split_asm)



lemma Read_invocation_Write_global:
  assumes "thrdsvars"
and "  Write_inv  tb   ((pc \<sigma>) tb)  \<sigma>  "
and "Read_invocation_inv ta  ((pc \<sigma>) ta) \<sigma>" 
 and " TML_Read_invocation  ta   \<sigma> \<sigma>'"
and "total_wfs (\<tau> \<sigma>) "
  and "((pc \<sigma>) ta) \<in> {ReadPending, Ready} \<union> {Aborted} "
  and " ((pc \<sigma>)tb) \<in> {Aborted,WritePending, WriteResponding} \<union> writing  " 
and " ta \<noteq> tb"
shows "  Write_inv  tb   ((pc \<sigma>') tb)  \<sigma>'" 
  using assms
  apply(simp add:Read_invocation_inv_def Write_inv_def total_wfs_def TML_Read_invocation_def Ready_total_def read_pre_def )
  apply  (cases" pc  \<sigma> tb"; simp ; cases "(pc \<sigma>) ta"; simp )
  apply (unfold Ready_total_def read_pre_def )
  apply (smt (verit))
  apply metis
  apply (metis PC.distinct(1505))
  apply (metis PC.distinct(1505))
  apply metis
  apply (metis PC.distinct(1505))
  apply metis
  apply metis
  apply (metis PC.distinct(1505))
  apply metis
  apply metis
  apply (metis PC.distinct(1505))
  apply metis
  apply metis
  apply (metis PC.distinct(1505))
  apply metis
  apply metis
  apply (metis PC.distinct(1505))
  apply metis
  by (smt (verit))




lemma sf_read_pre_ni:
assumes  "read_pre (\<tau> \<sigma>) ta z "
and " (\<tau> \<sigma>) [sfence ]\<^sub>tb (\<tau> \<sigma>')" 
and "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
and " ta \<noteq> syst"
and "tb \<noteq> syst"
and "ta \<noteq> tb"
shows   "read_pre (\<tau> \<sigma>') ta z "
  using assms
  apply (unfold read_pre_def total_wfs_def thrdsvars_def)
  by (metis (no_types, opaque_lifting) assms(4) reg_same_sfence sf_coh_ni sf_coh_valof_dt_ni sf_le_lim_ni sf_vrnew_dt_ni)

lemma wr_glb_read_pre_ni:
assumes  "read_pre (\<tau> \<sigma>) ta b "
and "  (\<tau> \<sigma>) [glb := Suc (lastVal glb (\<tau> \<sigma>))]\<^sub>tb (\<tau> \<sigma>')" 
and "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
and " ta \<noteq> syst"
and "tb \<noteq> syst"
and "ta \<noteq> tb"
shows   "read_pre (\<tau> \<sigma>') ta b "
 using assms
  apply (unfold read_pre_def total_wfs_def thrdsvars_def)
  by (metis (no_types, lifting) assms(4) reg_coh_dt_ni reg_same_st st_coh_valof_dt_ni st_le_lim_dt_ni st_vrnew_dt_ni)




lemma Commit_Read_invocation_global:
  assumes "thrdsvars"
and "  Commit_inv  tb   ((pc \<sigma>) tb)  \<sigma>  "
and "Read_invocation_inv ta  ((pc \<sigma>) ta) \<sigma>" 
   and " TML_Commit  tb    \<sigma> \<sigma>'"
and "total_wfs (\<tau> \<sigma>) "
 and  " pc \<sigma>  syst  = RecIdle \<longrightarrow> (\<forall>t.  (t \<noteq> syst  \<and> ((pc \<sigma>) t \<notin> {PC.NotStarted,PC.Aborted, PC.Committed,PC.Begin2,PC.BeginPending   }) \<longrightarrow>   regs (\<tau> \<sigma>) t loc \<le> lastVal glb  (\<tau> \<sigma>) ))"
  and "((pc \<sigma>) ta) \<in> {ReadPending, Ready} \<union> {Aborted} "
  and " ((pc \<sigma>)tb) \<in> {Aborted,CommitPending, CommitResponding} \<union> committing  " 
and " ta \<noteq> tb"
shows "Read_invocation_inv ta  ((pc \<sigma>') ta) \<sigma>'" 
  using assms
 apply (unfold thrdsvars_def )
  apply (simp add:TML_Commit_def Commit_inv_def Read_invocation_inv_def total_wfs_def )

  apply (cases "(pc \<sigma>) ta";simp; cases "(pc \<sigma>) tb" ;simp)

  apply (unfold Ready_total_def)
       apply (simp add:  read_pre_def)
       apply ( simp add: split: if_split_asm)
       apply (simp add:  read_pre_def)
        apply (metis PC.distinct(425))
       apply (simp add:  read_pre_def)

  apply (metis PC.distinct(425))
  apply (intro conjI impI)
  apply (metis PC.distinct(493) fun_upd_def option.inject reg_same_sfence)
        apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc)")
        apply simp
  apply (case_tac " \<not> readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
        apply simp
           apply (metis PC.distinct(493) reg_same_sfence sfence_lastVal_ni)
        apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc)")
        apply simp
  apply (case_tac " \<not> readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
        apply simp
  apply simp
  apply (metis PC.distinct(493) PC.distinct(803) assms(1) assms(5) reg_same_sfence sf_read_pre_ni)

  apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc)")
        apply simp
apply (case_tac " \<not> readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
        apply simp
  apply (metis PC.distinct(493) reg_same_sfence)
apply (case_tac " \<not> readAux \<sigma> ta \<and>   writeAux \<sigma> ta ")
  apply simp
         apply simp
  apply (metis PC.distinct(493) reg_same_sfence)


  apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc)")
        apply simp
apply (case_tac " \<not> readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
          apply simp
apply (case_tac " \<not> readAux \<sigma> ta \<and>   writeAux \<sigma> ta ")
  apply simp
  apply (metis PC.distinct(559))


  apply simp
  apply (metis PC.distinct(559))

  apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc)")
        apply simp
apply (case_tac " \<not> readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
        apply simp
  apply (metis PC.distinct(623) less_SucI reg_same_st st_lastVal_lc)

apply (case_tac " \<not> readAux \<sigma> ta \<and>   writeAux \<sigma> ta ")
        apply simp
       apply simp
  apply (unfold read_pre_def)
  using  reg_coh_dt_ni reg_same_st st_coh_valof_dt_ni st_le_lim_dt_ni st_vrnew_dt_ni
  apply (smt (verit) PC.distinct(623) assms(5))





  apply ( simp add: split: if_split_asm)
  apply (metis PC.distinct(425))
      apply (metis PC.distinct(425))

  apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc)")
      apply simp
apply (case_tac " \<not> readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
        apply simp
  apply (metis PC.distinct(493) reg_same_sfence sfence_lastVal_ni)
apply (case_tac "  readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
      apply simp
  apply (smt (verit) PC.distinct(493) assms(5) reg_same_sfence sf_coh_ni sf_coh_valof_dt_ni sf_le_lim_ni sf_vrnew_dt_ni)


  apply fastforce
  apply (smt (verit) PC.distinct(559) fun_upd_other option.inject)

  apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc)")
    apply simp
  apply (case_tac " \<not> readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
  apply simp
    apply (metis PC.distinct(623) less_SucI reg_same_st st_lastVal_lc)
  apply simp
  apply (smt (verit) PC.distinct(623) assms(5) assms(9) reg_coh_dt_ni reg_same_st st_coh_valof_dt_ni st_le_lim_dt_ni st_vrnew_dt_ni)
  by ( simp add: split: if_split_asm)




lemma Read_invocation_Commit_global:
  assumes "thrdsvars"
and "  Commit_inv  tb   ((pc \<sigma>) tb)  \<sigma>  "
and "Read_invocation_inv ta  ((pc \<sigma>) ta) \<sigma>" 
 and " TML_Read_invocation  ta   \<sigma> \<sigma>'"
and "total_wfs (\<tau> \<sigma>) "
  and "((pc \<sigma>) ta) \<in> {ReadPending, Ready} \<union> {Aborted} "
  and " ((pc \<sigma>)tb) \<in>  {CommitPending,CommitResponding} \<union> committing \<union> {Aborted} " 
and " ta \<noteq> tb"
shows "  Commit_inv  tb   ((pc \<sigma>') tb)  \<sigma>'" 
  using assms
  apply(simp add:Read_invocation_inv_def Commit_inv_def total_wfs_def TML_Read_invocation_def Ready_total_def read_pre_def )

  apply (cases "(pc \<sigma>) ta";simp; cases "(pc \<sigma>) tb" ;simp)
  apply metis
  apply metis
  apply (unfold Ready_total_def)
  apply metis
  apply metis
  apply (metis PC.distinct(1505))
  apply (metis PC.distinct(1505))
  apply (metis PC.distinct(1505))
  apply metis
  apply metis
  by metis




(***************************************************************************)



lemma Begin_Write_invocation_global:
  assumes "thrdsvars"
and "  Begin_inv  tb   ((pc \<sigma>) tb)  \<sigma>  "
and "Write_invocation_inv ta  ((pc \<sigma>) ta) \<sigma>" 
   and " TML_Begin  tb    \<sigma> \<sigma>'"
and "total_wfs (\<tau> \<sigma>) "
  and "((pc \<sigma>) ta) \<in> {WritePending, Ready} \<union> {Aborted} "
  and " ((pc \<sigma>)tb) \<in> {Aborted,BeginPending, BeginResponding} \<union> beginning "  
and " ta \<noteq> tb"
shows "Write_invocation_inv ta  ((pc \<sigma>') ta) \<sigma>'" 
  using assms
 apply (unfold thrdsvars_def )
  apply (simp add:TML_Begin_def Begin_inv_def Write_invocation_inv_def  )
  apply  (cases "(pc \<sigma>) ta";simp; cases "(pc \<sigma>) tb" ;simp)
        apply (unfold total_wfs_def read_pre_def Ready_total_def)
  apply (smt (verit))
 apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc)")
        apply simp
        apply (smt (verit) PC.distinct(209) assms(5) lastVal_ni ld_oav_ni ld_ov_ni reg_same_ld_dr)

 apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc)")
      apply simp
apply (case_tac " \<not> readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
        apply simp
  apply (smt (verit) PC.distinct(209) assms(5) lastVal_ni ld_ov_ni reg_same_ld_dr)
apply (case_tac "  readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
        apply simp
  apply (smt (verit) PC.distinct(209) assms(5) ld_coh_dt_ni ld_coh_valof_dt_ni ld_le_lim_ni ld_vrnew_dt_ni reg_same_ld_dr)
  apply meson

  apply ( simp add: split: if_split_asm)
  apply (metis (no_types, opaque_lifting) PC.distinct(283))
  apply (metis PC.distinct(283))
     apply (smt (verit))
apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc)")
     apply simp
  apply (smt (verit) PC.distinct(209) assms(5) lastVal_ni ld_oav_ni ld_ov_ni reg_same_ld_dr)

apply (case_tac " \<not> readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
      apply simp


  apply (smt (verit) PC.distinct(209) assms(5) lastVal_ni ld_ov_ni reg_same_ld_dr)
apply (case_tac "  readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
        apply simp
  apply (smt (verit) PC.distinct(209) assms(5) ld_coh_dt_ni ld_coh_valof_dt_ni ld_le_lim_ni ld_vrnew_dt_ni reg_same_ld_dr)
  apply meson


        apply ( simp add: split: if_split_asm)
  apply (metis PC.distinct(283))
  apply (metis PC.distinct(283))
  by ( simp add: split: if_split_asm)




lemma Write_invocation_Begin_global:
  assumes "thrdsvars"
and "  Begin_inv  tb   ((pc \<sigma>) tb)  \<sigma>  "
and "Write_invocation_inv ta  ((pc \<sigma>) ta) \<sigma>" 
 and " TML_Write_invocation  ta   \<sigma> \<sigma>'"
and "total_wfs (\<tau> \<sigma>) "
  and "((pc \<sigma>) ta) \<in> {WritePending, Ready} \<union> {Aborted} "
  and " ((pc \<sigma>)tb) \<in> {Aborted,BeginPending, BeginResponding} \<union> beginning " 
and " ta \<noteq> tb"
shows "  Begin_inv  tb   ((pc \<sigma>') tb)  \<sigma>'" 
  using assms
  apply(simp add:Write_invocation_inv_def Begin_inv_def total_wfs_def TML_Write_invocation_def  )
  apply  (cases" pc  \<sigma> tb"; simp ; cases "(pc \<sigma>) ta"; simp )
  apply (metis PC.distinct(1505))
  apply (metis PC.distinct(1505))
  apply (unfold Ready_total_def read_pre_def)
  by (smt (verit))




lemma Read_Write_invocation_global:
  assumes "thrdsvars"
and "  Read_inv  tb   ((pc \<sigma>) tb)  \<sigma>  "
and "Write_invocation_inv ta  ((pc \<sigma>) ta) \<sigma>" 
   and " TML_Read  tb    \<sigma> \<sigma>'"
and "total_wfs (\<tau> \<sigma>) "
  and "((pc \<sigma>) ta) \<in> {WritePending, Ready} \<union> {Aborted} "
  and " ((pc \<sigma>)tb) \<in> {Aborted,ReadPending, ReadResponding} \<union> reading "  
and " ta \<noteq> tb"
shows "Write_invocation_inv ta  ((pc \<sigma>') ta) \<sigma>'" 
  using assms
 apply (unfold thrdsvars_def )
  apply (simp add:TML_Read_def Read_inv_def Write_invocation_inv_def  )
  apply  (cases "(pc \<sigma>) ta";simp; cases "(pc \<sigma>) tb" ;simp)
                apply (unfold total_wfs_def read_pre_def Ready_total_def)

apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc)")
     apply simp
  apply (metis PC.distinct(803))

apply (case_tac " \<not> readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
      apply simp
  apply (metis PC.distinct(803))

                apply simp
  apply (metis PC.distinct(803))



apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc)")
        apply simp
                apply (smt (verit) PC.distinct(859) assms(5) lastVal_ni ld_oav_ni ld_ov_ni reg_same_ld_dt)
apply (case_tac " \<not> readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
      apply simp
  apply (smt (verit) PC.distinct(859) assms(5) lastVal_ni ld_ov_ni reg_same_ld_dr)
                apply simp
  apply (metis PC.distinct(1153) PC.distinct(859) assms(1) assms(5) read_pre_def read_read_pre_ni)




        apply ( simp add: split: if_split_asm)
  apply (metis PC.distinct(913))
  apply (metis PC.distinct(913))
         apply ( simp add: split: if_split_asm)
apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc)")
        apply simp
  apply (metis One_nat_def cas_nlv_lc lastVal_def zero_neq_one)
apply (case_tac " \<not> readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
        apply simp
  apply (elim disjE)
  apply (smt (verit) One_nat_def PC.distinct(965) assms(5) cas_le_daddr cas_ov_daddr_dt_sx_ni cas_succ_lv_lc lastVal_def reg_same_CAS_dt)
         apply simp
  apply (metis One_nat_def PC.distinct(965) cas_lc lastVal_def reg_same_CAS_dt zero_neq_one)
  apply (metis One_nat_def cas_fail_diff_lv less_irrefl_nat zero_neq_one)
  apply (metis One_nat_def cas_fail_diff_lv less_irrefl_nat zero_neq_one)
apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc)")
        apply simp
apply (case_tac " \<not> readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
  apply fastforce
 apply simp
  apply (metis (no_types, lifting) PC.distinct(965) assms(5) cas_coh_dt_ni cas_coh_valof_dt_ni cas_le_lim_dt_ni cas_vrnew_dt_ni reg_same_CAS_dt)
apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc)")
        apply simp
  apply (intro conjI)
  apply (metis PC.distinct(965))
  apply (intro impI conjI)
  apply (metis reg_same_CAS_dt)
  apply (metis cas_fail_diff_lv cas_fail_lastVal_dt_ni)
  apply (metis cas_fail_lv_ni lastVal_def reg_same_CAS_dt)
  apply (metis reg_same_CAS_dt)
  apply (metis cas_fail_lv_ni lastVal_def reg_same_CAS_dt)
  apply (metis cas_fail_diff_lv cas_fail_lastVal_dt_ni)
  apply (metis reg_same_CAS_dt)
  apply (metis cas_fail_diff_lv cas_fail_lastVal_dt_ni)
  apply (metis (no_types, lifting) assms(5) cas_fail_diff_lv cas_fail_lastVal_same cas_fail_oav_ni cas_le_daddr)
  apply (metis cas_fail_lv_ni lastVal_def reg_same_CAS_dt)

apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc)")
        apply simp
apply (case_tac " \<not> readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
  apply simp
              apply (subgoal_tac " syst \<noteq> tb ")
  prefer 2
  apply (metis PC.distinct(965))
  apply simp
  apply (intro conjI)
  apply (metis reg_same_CAS_dt)
  apply (elim disjE)
  apply (subgoal_tac "  even (regs (\<tau> \<sigma>') ta DTML.loc) \<and>
    regs (\<tau> \<sigma>') ta DTML.loc = lastVal glb (\<tau> \<sigma>') \<and>
    (\<forall>l. [l]\<^sub>ta \<tau> \<sigma>' = {lastVal l (\<tau> \<sigma>')}) ")
  prefer 2
  apply (intro  conjI)
  apply (metis reg_same_CAS_dt)
  apply (metis cas_possible_lv_lc lastVal_def reg_same_CAS_dt)
  apply (metis One_nat_def assms(5) cas_fail_lastVal_dt_ni cas_lastEntry total_wfs_def)
  apply blast
  apply (metis cas_possible_lv_lc lastVal_def reg_same_CAS_dt)
  apply (subgoal_tac "    even (regs (\<tau> \<sigma>') ta DTML.loc) \<and>
    regs (\<tau> \<sigma>') ta DTML.loc = lastVal glb (\<tau> \<sigma>') \<and>
    (\<forall>l. [l]\<^sub>ta \<tau> \<sigma>' = {lastVal l (\<tau> \<sigma>')})")
  prefer 2
  apply (intro conjI)
  apply (metis reg_same_CAS_dt)
  apply (metis cas_fail_lv_ni lastVal_def less_irrefl_nat reg_same_CAS_dt)
  apply (metis cas_fail_diff_lv cas_fail_lastVal_dt_ni nat_neq_iff)
  apply blast
  apply (metis cas_fail_lv_ni lastVal_def less_irrefl_nat reg_same_CAS_dt)
  apply (metis reg_same_CAS_dt)
apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc)")
        apply simp
apply (case_tac " \<not> readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
  apply simp
  apply simp
  apply (intro conjI impI)
  apply (metis PC.distinct(965))
  apply (metis reg_same_CAS_dt)
  apply clarify
  apply (metis PC.distinct(1153) assms(1) assms(5) cas_read_pre_ni read_pre_def)
             apply (metis reg_same_CAS_dt)


apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc)")
        apply simp
  apply (smt (verit) PC.distinct(1015) assms(5) lastVal_ni ld_oav_ni ld_ov_ni reg_same_ld_dt)
apply (case_tac " \<not> readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
  apply simp
             apply (smt (verit) PC.distinct(1015) assms(5) lastVal_ni ld_ov_ni reg_same_ld_dt)
apply (case_tac " \<not> readAux \<sigma> ta \<and>    writeAux \<sigma> ta ")
  apply simp
            apply simp
  apply (smt (verit) PC.distinct(1015) assms(5) ld_coh_dt_ni ld_coh_valof_dt_ni ld_le_coh_ni ld_vrnew_dt_ni reg_same_ld_dt)



       apply ( simp add: split: if_split_asm)
  apply (metis PC.distinct(1063))
           apply (metis PC.distinct(1063))

apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc)")
           apply simp
  apply (metis PC.distinct(803))

apply (case_tac " \<not> readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
           apply simp
  apply (metis PC.distinct(803))

apply (case_tac " readAux \<sigma> ta \<and>   \<not>  writeAux \<sigma> ta ")
           apply simp
  apply (metis PC.distinct(803))
            apply simp



apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc)")
  apply simp
          apply (smt (verit) PC.distinct(859) assms(5) lastVal_ni ld_oav_ni ld_ov_ni reg_same_ld_dt)
apply (case_tac " \<not> readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
           apply simp
  apply (smt (verit) PC.distinct(859) assms(5) lastVal_ni ld_ov_ni reg_same_ld_dr)

apply (case_tac " readAux \<sigma> ta \<and>   \<not>  writeAux \<sigma> ta ")
          apply simp
  apply (smt (verit) PC.distinct(1505) PC.distinct(859) assms(1) assms(5) ld_coh_dt_ni ld_le_lim_ni ld_vrnew_dt_ni read_pre_def read_read_pre_ni)

  apply metis

         apply ( simp add: split: if_split_asm)
  apply (metis PC.distinct(913))
  apply (metis PC.distinct(913))
          apply ( simp add: split: if_split_asm)
 apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc)")
        apply simp
  apply (metis One_nat_def cas_nlv_lc lastVal_def zero_neq_one)
apply (case_tac " \<not> readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
  apply simp
  apply (elim disjE)
  apply (smt (verit) One_nat_def PC.distinct(965) assms(5) cas_le_daddr cas_ov_daddr_dt_sx_ni cas_succ_lv_lc lastVal_def reg_same_CAS_dt)
  apply (metis One_nat_def PC.distinct(965) cas_lc lastVal_def reg_same_CAS_dt zero_neq_one)
  apply (metis One_nat_def cas_fail_diff_lv less_irrefl_nat zero_neq_one)
  apply (metis One_nat_def cas_fail_diff_lv less_irrefl_nat zero_neq_one)
 apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc)")
        apply simp
apply (case_tac " \<not> readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
  apply simp
  apply simp
  apply (smt (verit) PC.distinct(965) assms(5) cas_coh_dt_ni cas_coh_valof_dt_ni cas_le_lim_dt_ni cas_vrnew_dt_ni reg_same_CAS_dt)
 apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc)")
        apply simp
  apply (intro conjI)
  apply (metis PC.distinct(965))
  apply (intro conjI impI)
  apply (metis reg_same_CAS_dt)
  apply (metis cas_fail_diff_lv cas_fail_lastVal_dt_ni)
  apply (metis cas_fail_lv_ni lastVal_def reg_same_CAS_dt)
  apply (metis reg_same_CAS_dt)
  apply (metis cas_fail_lv_ni lastVal_def reg_same_CAS_dt)
  apply (metis cas_fail_diff_lv cas_fail_lastVal_dt_ni)
  apply (metis reg_same_CAS_dt)
  apply (metis cas_fail_diff_lv cas_fail_lastVal_dt_ni)
  apply (metis assms(5) cas_fail_diff_lv cas_fail_lastVal_same cas_fail_oav_ni cas_le_daddr)
  apply (metis cas_fail_lv_ni lastVal_def reg_same_CAS_dt)
  apply simp
  apply (subgoal_tac " memory (\<tau> \<sigma>) = memory( \<tau> \<sigma>') ")
  prefer 2
  apply (metis One_nat_def cas_fail_mem_same cas_lc)
  apply (case_tac "  readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
  apply simp
  apply (intro conjI impI)
  apply (metis PC.distinct(965))
  apply (metis reg_same_CAS_dt)
  apply (metis PC.distinct(1505) assms(1) assms(5) cas_read_pre_ni read_pre_def)
  apply (metis reg_same_CAS_dt)
  apply (intro conjI impI)
  apply (metis PC.distinct(965))
  apply (metis reg_same_CAS_dt)
  apply simp
  apply (elim disjE)
  apply (subgoal_tac " even (regs (\<tau> \<sigma>') ta DTML.loc) \<and>
    regs (\<tau> \<sigma>') ta DTML.loc = lastVal glb (\<tau> \<sigma>') \<and> (\<forall>l. [l]\<^sub>ta \<tau> \<sigma>' = {lastVal l (\<tau> \<sigma>')})")
  prefer 2
            apply (intro conjI)
  apply (metis reg_same_CAS_dt)
  apply (metis cas_possible_lv_lc lastVal_def reg_same_CAS_dt)
  apply (metis (no_types, opaque_lifting) One_nat_def assms(5) cas_fail_lastVal_dt_ni cas_lastEntry total_wfs_def)
  apply blast
  apply (metis cas_possible_lv_lc lastVal_def reg_same_CAS_dt)
  apply (metis (no_types, lifting) assms(5) cas_dt_ov_ni cas_fail_diff_lv cas_fail_lastVal_same cas_le_daddr less_irrefl_nat reg_same_CAS_dt)
  apply (metis cas_fail_lv_ni lastVal_def less_irrefl_nat reg_same_CAS_dt)
  apply (metis reg_same_CAS_dt)
apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc)")
       apply simp
  apply (smt (verit) PC.distinct(1015) assms(5) lastVal_ni ld_oav_ni ld_ov_ni reg_same_ld_dt)
apply (case_tac " \<not> readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
       apply simp
  apply (smt (verit) PC.distinct(1015) assms(5) lastVal_ni ld_ov_ni reg_same_ld_dr)

  apply simp
  apply (smt (z3) PC.distinct(1015) assms(5) ld_coh_dt_ni ld_coh_valof_dt_ni ld_le_coh_ni ld_vrnew_dt_ni reg_same_ld_dt)

  apply ( simp add: split: if_split_asm)
  apply (metis PC.distinct(1063))
  apply (metis PC.distinct(1063))

  apply ( simp add: split: if_split_asm)
  apply ( simp add: split: if_split_asm)
  by( simp add: split: if_split_asm)








lemma Write_invocation_Read_global:
  assumes "thrdsvars"
and "  Read_inv  tb   ((pc \<sigma>) tb)  \<sigma>  "
and "Write_invocation_inv ta  ((pc \<sigma>) ta) \<sigma>" 
 and " TML_Write_invocation  ta   \<sigma> \<sigma>'"
and "total_wfs (\<tau> \<sigma>) "
  and "((pc \<sigma>) ta) \<in> {WritePending, Ready} \<union> {Aborted} "
  and " ((pc \<sigma>)tb) \<in> {Aborted,ReadPending, ReadResponding} \<union> reading " 
and " ta \<noteq> tb"
shows "  Read_inv  tb   ((pc \<sigma>') tb)  \<sigma>'" 
  using assms
  apply(simp add:Write_invocation_inv_def Read_inv_def total_wfs_def TML_Write_invocation_def  )
  apply  (cases" pc  \<sigma> tb"; simp ; cases "(pc \<sigma>) ta"; simp )

  apply (unfold total_wfs_def read_pre_def Ready_total_def)
  apply (smt (verit))
  apply metis
  apply (metis PC.distinct(1505))
  apply (metis PC.distinct(1505))
  apply (metis PC.distinct(1505))
  apply (metis PC.distinct(1505))
  by (smt (verit))








lemma flo_read_pre_ni:
assumes  "read_pre (\<tau> \<sigma>) ta b "
and " (\<tau> \<sigma>) [flush\<^sub>o a]\<^sub>tb (\<tau> \<sigma>')"
and "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
and " ta \<noteq> syst"
and "tb \<noteq> syst"
and "ta \<noteq> tb"
shows   "read_pre (\<tau> \<sigma>') ta b "
 using assms
  apply (unfold total_wfs_def read_pre_def thrdsvars_def)
apply (subgoal_tac "vrnew (\<tau> \<sigma>') ta = vrnew (\<tau> \<sigma>) ta ")
   prefer 2
  apply (simp add: step_def flush_opt_trans_def)
  by (metis (no_types, lifting) assms(4) flo_coh_ni flo_coh_valof_dt_ni flo_le_lim_dt_ni reg_same_flo)







lemma Write_Write_invocation_global:
  assumes "thrdsvars"
and "  Write_inv  tb   ((pc \<sigma>) tb)  \<sigma>  "
and "Write_invocation_inv ta  ((pc \<sigma>) ta) \<sigma>" 
   and " TML_Write  tb    \<sigma> \<sigma>'"
and "total_wfs (\<tau> \<sigma>) "
  and "((pc \<sigma>) ta) \<in> {WritePending, Ready} \<union> {Aborted} "
  and " ((pc \<sigma>)tb) \<in> {Aborted,WritePending,WriteResponding} \<union> writing "  
and " ta \<noteq> tb"
shows "Write_invocation_inv ta  ((pc \<sigma>') ta) \<sigma>'" 
  using assms
  apply(simp add:Write_invocation_inv_def Write_inv_def total_wfs_def TML_Write_def  )
  apply  (cases" pc  \<sigma> tb"; simp ; cases "(pc \<sigma>) ta"; simp )
  apply (unfold total_wfs_def read_pre_def Ready_total_def)
  apply (smt (verit) PC.distinct(1153) fun_upd_other)
  apply (smt (verit) PC.distinct(1153) fun_upd_other)
  apply ( simp add: split: if_splits)
  apply (metis PC.distinct(1195))
  apply (metis PC.distinct(1195))
   apply ( simp add: split: if_splits)
  apply (metis PC.distinct(1195))
  apply (metis PC.distinct(1195))
    apply ( simp add: split: if_splits)
    apply ( simp add: split: if_splits)
 apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc)")
                   apply simp
  apply (intro conjI impI)
  apply (metis PC.distinct(1235))
  apply (metis reg_same_CAS_dt)
  apply (meson cas_fail_lastVal_dt_ni)
  apply (metis cas_fail_lv_ni lastVal_def reg_same_CAS_dt)
  apply (metis reg_same_CAS_dt)
  apply (metis cas_fail_lv_ni lastVal_def reg_same_CAS_dt)
  apply (meson cas_fail_lastVal_dt_ni)
  apply (metis reg_same_CAS_dt)
  apply (meson cas_fail_lastVal_dt_ni)
  apply (metis assms(5) cas_fail_lastVal_same cas_fail_oav_ni cas_le_daddr)
  apply (metis cas_fail_lv_ni lastVal_def reg_same_CAS_dt)
apply (case_tac " \<not> readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
  apply simp
  apply (subgoal_tac "  (\<forall>l. lastVal l (\<tau> \<sigma>')  =  lastVal l (\<tau> \<sigma>)  ) ")
  prefer 2
  apply (metis assms(5) cas_fail_lastVal_same cas_le_daddr)
                   apply (smt (verit) PC.distinct(1235) cas_dt_ov_ni less_add_eq_less reg_same_CAS_dt)
  apply simp
  apply (intro conjI)
   apply (metis PC.distinct(1235))
  apply (intro conjI impI)
                    apply clarify
  apply (metis reg_same_CAS_dt)
  apply clarify
  apply (smt (verit) assms(5) cas_coh_dt_ni cas_coh_valof_dt_ni cas_le_lim_dt_ni cas_vrnew_dt_ni reg_same_CAS_dt)
   apply (metis reg_same_CAS_dt)
  apply (intro conjI impI)
  apply (metis PC.distinct(1235))
  apply (metis cas_fail_diff_lv less_numeral_extra(3) reg_same_CAS_dt)
  apply (metis Zero_not_Suc cas_fail_diff_lv gr0_implies_Suc)


 apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc)")
  apply simp
  apply (metis cas_fail_diff_lv less_numeral_extra(3))
apply (case_tac " \<not> readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
  apply simp
  apply (smt (verit) cas_lc cas_nlv_lc lastVal_def less_Suc_eq not_less_iff_gr_or_eq reg_same_CAS_dt)
  apply simp
apply (intro conjI)
  apply (metis reg_same_CAS_dt)
 apply clarify
  apply (smt (verit) assms(5) cas_coh_dt_ni cas_coh_valof_dt_ni cas_le_lim_dt_ni cas_vrnew_dt_ni reg_same_CAS_dt)
  apply (metis Zero_not_Suc cas_nlv_lc gr0_implies_Suc lastVal_def reg_same_CAS_dt)
  apply (metis cas_fail_diff_lv less_numeral_extra(3))
  apply ( simp add: split: if_splits)

 apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc)")
  apply simp
  apply (intro conjI impI)
  apply (metis PC.distinct(1235))
  apply (metis reg_same_CAS_dt)
  apply (meson cas_fail_lastVal_dt_ni)
  apply (metis cas_fail_lv_ni lastVal_def reg_same_CAS_dt)
  apply (metis reg_same_CAS_dt)
  apply (metis cas_fail_lv_ni lastVal_def reg_same_CAS_dt)
  apply (meson cas_fail_lastVal_dt_ni)
  apply (metis reg_same_CAS_dt)
  apply (meson cas_fail_lastVal_dt_ni)
  apply (metis assms(5) cas_fail_lastVal_same cas_fail_oav_ni cas_le_daddr)
  apply (metis cas_fail_lv_ni lastVal_def reg_same_CAS_dt)
apply (case_tac " \<not> readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
  apply simp
  apply (elim disjE)
  apply simp
  apply (subgoal_tac " regs (\<tau> \<sigma>') ta DTML.loc = lastVal glb (\<tau> \<sigma>') \<and> (\<forall>l. [l]\<^sub>ta \<tau> \<sigma>' = {lastVal l (\<tau> \<sigma>')})")
                    prefer 2
 apply (intro conjI)
  apply (metis assms(5) cas_fail_lastVal_same reg_same_CAS_dt)
  apply (meson cas_fail_lastVal_dt_ni)
  apply (metis PC.distinct(1235) assms(5) cas_fail_lastVal_same)
  apply (metis PC.distinct(1235) assms(5) cas_fail_lastVal_same reg_same_CAS_dt)
  apply simp
  apply(intro conjI impI)
  apply (metis PC.distinct(1235))
  apply (metis reg_same_CAS_dt)
  apply clarify
  apply (smt (verit) assms(5) cas_coh_dt_ni cas_coh_valof_dt_ni cas_le_lim_dt_ni cas_vrnew_dt_ni reg_same_CAS_dt)
  apply (metis reg_same_CAS_dt)


 apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc)")
  apply simp
                 apply (metis cas_fail_diff_lv less_numeral_extra(3))
apply (case_tac " \<not> readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
  apply simp
  apply (smt (verit) PC.distinct(1235) cas_lc cas_nlv_lc lastVal_def less_Suc_eq not_less_iff_gr_or_eq reg_same_CAS_dt)
  apply simp
  apply (intro conjI impI)
  apply (metis PC.distinct(1235))
  apply (metis reg_same_CAS_dt)
  apply clarify
  apply (smt (verit) assms(5) cas_coh_dt_ni cas_coh_valof_dt_ni cas_le_lim_dt_ni cas_vrnew_dt_ni reg_same_CAS_dt)
  apply (metis reg_same_CAS_dt)
  apply ( simp add: split: if_splits)
 apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc)")
  apply simp
              apply (case_tac " \<not> readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
  apply (metis PC.distinct(1273) even_Suc fun_upd_other reg_dt_ni reg_write_lastVal_ni)

  apply simp
  apply (intro conjI impI)
                 apply clarify
  using  upreg_read_pre_ni
  using PC.distinct(1273) apply presburger
  using reg_dt_ni apply presburger
  apply clarify
  using  upreg_read_pre_ni
  apply (metis (no_types, lifting) PC.distinct(1153) assms(5) read_pre_def thrdsvars_def)
  using reg_dt_ni apply presburger

 apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc)")
  apply simp
             apply (case_tac " \<not> readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
  apply simp

  apply (metis PC.distinct(1273) even_Suc reg_dt_ni reg_write_lastVal_ni)

             apply simp
  apply (intro impI conjI)
  using  upreg_read_pre_ni read_pre_def
  apply (metis PC.distinct(1273))
  using reg_dt_ni apply presburger
  apply (subgoal_tac " ta \<noteq> syst")
  prefer 2
  apply (metis PC.distinct(1505))

 apply (subgoal_tac " tb \<noteq> syst")
  prefer 2
  apply (metis PC.distinct(1505))
  using  upreg_read_pre_ni read_pre_def
              apply (metis (no_types, lifting) assms(5) thrdsvars_def) 

  using reg_dt_ni apply presburger
   apply ( simp add: split: if_splits)
  apply (metis PC.distinct(1309))
  apply (metis PC.distinct(1309))
   apply ( simp add: split: if_splits)
  apply (metis PC.distinct(1309))
  apply (metis PC.distinct(1309))
  apply ( simp add: split: if_splits)

  
apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc)")
          apply simp
             apply (case_tac " \<not> readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
  apply simp
  apply (metis PC.distinct(1343) assms(5) lastVal_ni reg_same_ld_dt)
         apply simp 
             apply (case_tac "  readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
  apply simp
  apply (smt (z3) PC.distinct(1343) assms(5) ld_coh_dt_ni ld_coh_valof_dt_ni ld_le_lim_ni ld_vrnew_dt_ni reg_same_ld_dr)

apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc)")
          apply simp
             apply (case_tac " \<not> readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
  apply simp
  apply (metis PC.distinct(1343) assms(5) lastVal_ni reg_same_ld_dt)
         apply simp 
             apply (case_tac "  readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
  apply simp
  apply (smt (z3) PC.distinct(1343) assms(5) ld_coh_dt_ni ld_coh_valof_dt_ni ld_le_lim_ni ld_vrnew_dt_ni reg_same_ld_dr)

apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc)")
          apply simp
             apply (case_tac " \<not> readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
  apply simp
  apply (metis PC.distinct(1343) assms(5) lastVal_ni reg_same_ld_dt)
         apply simp 
             apply (case_tac "  readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
  apply simp
  apply (metis PC.distinct(1375))

  apply (metis PC.distinct(1375) fun_upd_other map_upd_eqD1)

apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc)")
          apply simp
             apply (case_tac " \<not> readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
       apply simp
  apply (metis PC.distinct(1375))
         apply simp 
             apply (case_tac "  readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
  apply simp
  apply (metis PC.distinct(1375))
  apply presburger

apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc)")
          apply simp
             apply (case_tac " \<not> readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
       apply simp
  apply (metis PC.distinct(1405) assms(5) reg_same_st st_lv__daddr_ni)
         apply simp 
             apply (case_tac "  readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
  apply simp
  apply (subgoal_tac " syst \<noteq> tb ")
  prefer 2
       apply (metis PC.distinct(1405))
  apply simp
      apply (intro conjI)
  apply (metis reg_same_st)
  apply (smt (z3) assms(5) reg_coh_dt_ni reg_same_st st_coh_valof_dt_ni st_le_lim_dt_ni st_vrnew_dt_ni)
  apply (metis reg_same_st)
  apply metis


apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc)")
          apply simp
             apply (case_tac " \<not> readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
       apply simp
  apply (metis PC.distinct(1405) assms(5) reg_same_st st_lv__daddr_ni)
         apply simp 
             apply (case_tac "  readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
 apply simp
  apply (subgoal_tac " syst \<noteq> tb ")
  prefer 2
       apply (metis PC.distinct(1405))
  apply simp
      apply (intro conjI)
  apply (metis reg_same_st)
  apply (smt (z3) assms(5) reg_coh_dt_ni reg_same_st st_coh_valof_dt_ni st_le_lim_dt_ni st_vrnew_dt_ni)
  apply (metis reg_same_st)
  apply metis

  apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc)")
          apply simp
             apply (case_tac " \<not> readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
    apply simp
  apply (metis PC.distinct(1433) assms(5) flo_lastVal_ni reg_same_flo)
         apply simp 
             apply (case_tac "  readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
 apply simp
  apply (subgoal_tac " syst \<noteq> tb ")
     prefer 2
  apply (metis PC.distinct(1433))

    apply simp

    apply (intro conjI)
  apply (metis reg_same_flo)
  apply (metis PC.distinct(1153) assms(1) assms(5) flo_read_pre_ni read_pre_def)
  apply (metis reg_same_flo)
  apply presburger


  apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc)")
          apply simp
             apply (case_tac " \<not> readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
    apply simp
  apply (metis PC.distinct(1433) assms(5) flo_lastVal_ni reg_same_flo)
         apply simp 
             apply (case_tac "  readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
   apply simp
  apply (smt(z3) PC.distinct(1433) PC.distinct(1505) assms(1) assms(5) flo_coh_valof_dt_ni flo_read_pre_ni flo_vrnew_ni read_pre_def)
  by presburger


 
lemma Write_invocation_Write_global:
  assumes "thrdsvars"
and "  Write_inv  tb   ((pc \<sigma>) tb)  \<sigma>  "
and "Write_invocation_inv ta  ((pc \<sigma>) ta) \<sigma>" 
 and " TML_Write_invocation  ta   \<sigma> \<sigma>'"
and "total_wfs (\<tau> \<sigma>) "
  and "((pc \<sigma>) ta) \<in> {WritePending, Ready} \<union> {Aborted} "
  and " ((pc \<sigma>)tb) \<in> {Aborted,WritePending, WriteResponding} \<union> writing " 
and " ta \<noteq> tb"
shows "  Write_inv  tb   ((pc \<sigma>') tb)  \<sigma>'" 
  using assms
  apply(simp add:Write_invocation_inv_def Write_inv_def total_wfs_def  TML_Write_invocation_def  )
  apply  (cases" pc  \<sigma> tb"; simp ; cases "(pc \<sigma>) ta"; simp )
  apply (unfold total_wfs_def read_pre_def Ready_total_def)
  apply (smt (verit))
  apply metis
  apply (metis PC.distinct(1505))
  apply (metis PC.distinct(1505))
  apply metis
  apply (metis PC.distinct(1505))
  apply metis
  apply metis
  apply (metis PC.distinct(1505))
  apply metis
  apply metis
  apply (metis PC.distinct(1505))
  apply metis
  apply metis
  apply (metis PC.distinct(1505))
  apply metis
  apply metis
  apply (metis PC.distinct(1505))
  apply metis
  by (smt (verit))

(*
lemma wr_glb_read_pre_ni:
assumes  "read_pre (\<tau> \<sigma>) ta b "
and "  (\<tau> \<sigma>) [glb := Suc (lastVal glb (\<tau> \<sigma>))]\<^sub>tb (\<tau> \<sigma>')" 
and "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
and " ta \<noteq> syst"
and "tb \<noteq> syst"
and "ta \<noteq> tb"
shows   "read_pre (\<tau> \<sigma>') ta b "
 using assms
  apply (unfold read_pre_def total_wfs_def thrdsvars_def)
  by (metis (no_types, lifting) assms(4) reg_coh_dt_ni reg_same_st st_coh_valof_dt_ni st_le_lim_dt_ni st_vrnew_dt_ni)

*)


lemma Commit_Write_invocation_global:
  assumes "thrdsvars"
and "  Commit_inv  tb   ((pc \<sigma>) tb)  \<sigma>  "
and "Write_invocation_inv ta  ((pc \<sigma>) ta) \<sigma>" 
   and " TML_Commit  tb    \<sigma> \<sigma>'"
and "total_wfs (\<tau> \<sigma>) "
  and "((pc \<sigma>) ta) \<in> {WritePending, Ready} \<union> {Aborted} "
  and " ((pc \<sigma>)tb) \<in> {Aborted,CommitPending,CommitResponding} \<union> committing "  
and " ta \<noteq> tb"
shows "Write_invocation_inv ta  ((pc \<sigma>') ta) \<sigma>'" 
  using assms
  apply(simp add:Write_invocation_inv_def Commit_inv_def total_wfs_def TML_Commit_def  )
  apply  (cases" pc  \<sigma> ta"; simp ; cases "(pc \<sigma>) tb"; simp )

  apply (simp add: split if_splits)
  apply (  cases" pc \<sigma>' ta ";simp)
           apply (simp add: Ready_total_def)
  apply (smt (verit) PC.distinct(425) fun_upd_other)

          apply (metis PC.distinct(1175) fun_upd_def)
         apply (simp add:  Ready_total_def)

  apply (smt (verit) PC.distinct(1153) PC.distinct(493) Ready_total_def assms(1) assms(5) empty_iff fun_upd_apply insert_iff reg_same_sfence sf_oav_ni sf_ov_ni sf_read_pre_ni sf_wfs_preserved total_wfs_def)
        apply (simp add:  Ready_total_def)
  apply (metis PC.distinct(559))

          apply (simp add:  Ready_total_def)

apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc)")
        apply simp
 apply (case_tac " \<not> readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
        apply simp
  apply (metis PC.distinct(623) less_SucI reg_same_st st_lastVal_lc)
  apply simp
  using  wr_glb_read_pre_ni read_pre_def
  apply (metis PC.distinct(1153) PC.distinct(623) assms(1) assms(5))
  apply (  cases" pc \<sigma>' ta ";simp)
         apply (simp add:  Ready_total_def)
  apply (metis PC.distinct(1175) pc_aux)
      apply (simp add: split if_splits)
      apply (simp add:  Ready_total_def)
  apply (smt (verit) PC.distinct(425) fun_upd_other)

         apply (simp add:  Ready_total_def)



  apply (smt(verit) PC.distinct(1505) PC.distinct(493) assms(1) assms(5) assms(8) empty_iff insert_iff reg_same_sfence sf_oav_ni sf_ots_ni sf_ov_ni sf_read_pre_ni sf_wfs_preserved step_mem_sfence total_wfs_def)
  apply (smt (z3) PC.distinct(559) Ready_total_def fun_upd_other option.inject)


         apply (simp add:  Ready_total_def)

apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc)")
        apply simp
 apply (case_tac " \<not> readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
        apply simp
  apply (metis PC.distinct(623) less_SucI reg_same_st st_lastVal_lc)
  apply simp
  using  wr_glb_read_pre_ni read_pre_def
  apply (metis PC.distinct(1505) PC.distinct(623) assms(1) assms(5))

  apply (  cases" pc \<sigma>' ta ";simp)
   apply (simp add:  Ready_total_def)
  apply (metis PC.distinct(1177) pc_aux)
  by (metis PC.distinct(1639) pc_aux)






lemma Write_invocation_Commit_global:
  assumes "thrdsvars"
and "  Commit_inv  tb   ((pc \<sigma>) tb)  \<sigma>  "
and "Write_invocation_inv ta  ((pc \<sigma>) ta) \<sigma>" 
 and " TML_Write_invocation  ta   \<sigma> \<sigma>'"
and "total_wfs (\<tau> \<sigma>) "
  and "((pc \<sigma>) ta) \<in> {WritePending, Ready} \<union> {Aborted} "
  and " ((pc \<sigma>)tb) \<in> {Aborted,CommitPending, CommitResponding} \<union> committing " 
and " ta \<noteq> tb"
shows "  Commit_inv  tb   ((pc \<sigma>') tb)  \<sigma>'" 
  using assms
  apply(simp add:Write_invocation_inv_def Commit_inv_def total_wfs_def  TML_Write_invocation_def  )

   apply  (cases" pc  \<sigma> ta"; simp ; cases "(pc \<sigma>) tb"; simp )
  apply metis
  apply metis
  apply metis
  apply (unfold Ready_total_def)
  apply metis
  apply (metis PC.distinct(1505))
  apply (metis PC.distinct(1505))
  apply (metis PC.distinct(1505))
  apply metis
  apply metis
  by metis










(******************************************************)



lemma Begin_Commit_invocation_global:
  assumes "thrdsvars"
and "  Begin_inv  tb   ((pc \<sigma>) tb)  \<sigma>  "
and "Commit_invocation_inv ta  ((pc \<sigma>) ta) \<sigma>" 
   and " TML_Begin  tb    \<sigma> \<sigma>'"
and "total_wfs (\<tau> \<sigma>) "
  and "((pc \<sigma>) ta) \<in> {CommitPending, Ready} \<union> {Aborted} "
  and " ((pc \<sigma>)tb) \<in> {Aborted,BeginPending, BeginResponding} \<union> beginning "  
and " ta \<noteq> tb"
shows "Commit_invocation_inv ta  ((pc \<sigma>') ta) \<sigma>'" 
  using assms
 apply (unfold thrdsvars_def )
  apply (simp add:TML_Begin_def Begin_inv_def Commit_invocation_inv_def  )
  apply  (cases "(pc \<sigma>) ta";simp; cases "(pc \<sigma>) tb" ;simp)
        apply (unfold total_wfs_def read_pre_def Ready_total_def)
        apply (smt (verit))


apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc)")
          apply simp
             apply (case_tac " \<not> readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
         apply simp
  apply (smt (verit) PC.distinct(209) assms(5) lastVal_ni ld_oav_ni ld_ov_ni reg_same_ld_dr)
         apply simp 
             apply (case_tac "  readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
  apply simp
  apply (smt (z3) PC.distinct(209) assms(5) ld_coh_dt_ni ld_coh_valof_dt_ni ld_le_lim_ni ld_vrnew_dt_ni reg_same_ld_dr)
  apply (metis PC.distinct(209) assms(5) lastVal_ni ld_ov_ni reg_same_ld_dr)
  apply (case_tac " even (regs (\<tau> \<sigma>) tb DTML.loc)")
       apply simp
       apply (metis PC.distinct(283))
  apply simp
  apply (metis PC.distinct(283))
  apply (smt (verit))

apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc)")
          apply simp
             apply (case_tac " \<not> readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
         apply simp
  apply (smt (verit) PC.distinct(209) assms(5) lastVal_ni ld_oav_ni ld_ov_ni reg_same_ld_dr)
         apply simp 
             apply (case_tac "  readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
  apply simp
     apply (smt (z3) PC.distinct(209) assms(5) ld_coh_dt_ni ld_coh_valof_dt_ni ld_le_lim_ni ld_vrnew_dt_ni reg_same_ld_dr)
    apply (metis PC.distinct(209) assms(5) lastVal_ni ld_ov_ni ld_step_mem reg_same_ld_dr)
  apply (case_tac " even (regs (\<tau> \<sigma>) tb DTML.loc)")
     apply simp
       apply (metis PC.distinct(283))
  apply simp
  apply (metis PC.distinct(283))
  apply (case_tac " even (regs (\<tau> \<sigma>) tb DTML.loc)")
   apply simp
  by simp




lemma Commit_invocation_Begin_global:
  assumes "thrdsvars"
and "  Begin_inv  tb   ((pc \<sigma>) tb)  \<sigma>  "
and "Commit_invocation_inv ta  ((pc \<sigma>) ta) \<sigma>" 
 and " TML_Commit_invocation  ta   \<sigma> \<sigma>'"
and "total_wfs (\<tau> \<sigma>) "
  and "((pc \<sigma>) ta) \<in> {CommitPending, Ready} \<union> {Aborted} "
  and " ((pc \<sigma>)tb) \<in> {Aborted,BeginPending, BeginResponding} \<union> beginning " 
and " ta \<noteq> tb"
shows "  Begin_inv  tb   ((pc \<sigma>') tb)  \<sigma>'" 
  using assms
  apply(simp add:Commit_invocation_inv_def Begin_inv_def total_wfs_def TML_Commit_invocation_def  )
  apply  (cases" pc  \<sigma> tb"; simp ; cases "(pc \<sigma>) ta"; simp )
  apply (metis PC.distinct(1505))
  apply (metis PC.distinct(1505))
  apply (unfold Ready_total_def read_pre_def)
  by (smt (verit))


lemma Read_Commit_invocation_global:
  assumes "thrdsvars"
and "  Read_inv  tb   ((pc \<sigma>) tb)  \<sigma>  "
and "Commit_invocation_inv ta  ((pc \<sigma>) ta) \<sigma>" 
   and " TML_Read  tb    \<sigma> \<sigma>'"
and "total_wfs (\<tau> \<sigma>) "
  and "((pc \<sigma>) ta) \<in> {CommitPending, Ready} \<union> {Aborted} "
  and " ((pc \<sigma>)tb) \<in> {Aborted,ReadPending, ReadResponding} \<union> reading "  
and " ta \<noteq> tb"
and  " \<forall>  t.  (   writer \<sigma> = Some t \<longrightarrow> odd (lastVal glb  (\<tau> \<sigma>)) )"
 and " \<forall>  t. (  (   writer \<sigma>  = Some t    \<longrightarrow> \<lceil>glb\<rceil>\<^sub>t (\<tau> \<sigma>) ))"
and " ta \<noteq> syst"
and "tb \<noteq> syst"
shows "Commit_invocation_inv ta  ((pc \<sigma>') ta) \<sigma>'" 
  using assms
 apply (unfold thrdsvars_def )
  apply (simp add:TML_Read_def Read_inv_def Commit_invocation_inv_def  )
  apply  (cases "(pc \<sigma>) ta";simp; cases "(pc \<sigma>) tb" ;simp)
                apply (unfold total_wfs_def read_pre_def Ready_total_def)


apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc)")
          apply simp
             apply (case_tac " \<not> readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
         apply simp
  apply (smt (verit) PC.distinct(209) assms(5) lastVal_ni ld_oav_ni ld_ov_ni reg_same_ld_dr)
                apply simp 


apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc)")
                      apply simp
 using  reg_same_st  
  apply (smt (verit) PC.distinct(859) assms(5) lastVal_ni ld_oav_ni ld_ov_ni reg_same_ld_dt)
 
  apply (case_tac " \<not> readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
                     apply simp
  using  reg_same_st   
  apply (smt (verit) PC.distinct(859) assms(5) lastVal_ni ld_ov_ni reg_same_ld_dt)



apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc)")
          apply simp
             apply (case_tac " \<not> readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
                apply simp
   apply (case_tac "  readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
  apply simp
     apply (smt (z3) PC.distinct(209) assms(5) ld_coh_dt_ni ld_coh_valof_dt_ni ld_le_lim_ni ld_vrnew_dt_ni reg_same_ld_dr)
    apply (metis PC.distinct(209) assms(5) lastVal_ni ld_ov_ni ld_step_mem reg_same_ld_dr)





   apply ( simp add: split: if_splits)
   apply ( simp add: split: if_splits)
  apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc)")
  apply (subgoal_tac "  odd (lastVal glb  (\<tau> \<sigma>)) ")
                     prefer 2
  apply presburger
  apply (metis cas_nlv_lc lastVal_def numeral_1_eq_Suc_0 numeral_eq_one_iff zero_neq_one)
  apply (case_tac "  \<not> readAux \<sigma> ta \<and>    \<not> writeAux \<sigma> ta  ")
                     apply simp
apply (subgoal_tac " lastVal glb (\<tau> \<sigma>') = lastVal glb (\<tau> \<sigma>) ")
  prefer 2
  apply (metis One_nat_def cas_lc cas_nlv_lc lastVal_def zero_neq_one)
  using  reg_same_CAS_dt 
               apply (metis (no_types, lifting) PC.distinct(965) assms(5) cas_le_daddr cas_ov_daddr_dt_sx_ni)
  apply simp
              apply (intro conjI)
  apply (metis reg_same_CAS_dt)
  apply clarify
  apply (intro conjI)
                apply (metis reg_same_CAS_dt)


  apply (metis cas_coh_dt_ni)
  using cas_coh_dt_ni  reg_same_CAS_dt
  apply (metis assms(5) cas_coh_valof_dt_ni)
  apply (metis assms(5) cas_le_lim_dt_ni cas_vrnew_dt_ni)
  apply (metis assms(5) cas_coh_dt_ni cas_vrnew_dt_ni)



  apply (metis reg_same_CAS_dt)


apply (subgoal_tac " \<forall> a. [a]\<^sub>ta \<tau> \<sigma>' = [a]\<^sub>ta \<tau> \<sigma>   ")
  prefer 2
         apply (simp add: step_def)
         apply clarify
  apply (case_tac "  \<tau> \<sigma>' =
       cas_fail_trans tb ind glb (regs (\<tau> \<sigma>) tb DTML.loc)
        (regs (\<tau> \<sigma>) tb DTML.loc) c1 (\<tau> \<sigma>)")
  prefer 2
  apply (metis One_nat_def cas_suc_reg)
  apply (metis cas_fail_ov_ni)

        apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc)")
                     apply simp
  apply (smt (verit) PC.distinct(965) assms(5) cas_fail_diff_lv cas_fail_lastVal_same cas_fail_oav_ni cas_le_daddr reg_same_CAS_dt)

  apply (case_tac " \<not> readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
              apply simp
  apply (metis (no_types, lifting) One_nat_def PC.distinct(965) assms(5) cas_fail_lastVal_same cas_le_daddr cas_sv_lc reg_same_CAS_dt)
  apply simp
  apply (metis assms(1) assms(5) cas_read_pre_ni read_pre_def)
  apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc)")
             apply simp
  apply (smt (verit) assms(5) lastVal_ni ld_oav_ni ld_ov_ni reg_same_ld_dt)
  apply simp
   apply (case_tac " \<not> readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
             apply simp
  apply (smt (verit) assms(5) lastVal_ni ld_ov_ni reg_same_ld_dr)
  apply (metis assms(1) assms(5) read_pre_def read_read_pre_ni)
           apply ( simp add: split: if_splits)
 apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc)")
                     apply simp

  apply (case_tac " \<not> readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
              apply simp
  apply (metis (no_types, lifting) One_nat_def PC.distinct(965) assms(5) cas_fail_lastVal_same cas_le_daddr cas_sv_lc reg_same_CAS_dt)
  apply simp


  apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc)")
             apply simp
          apply (smt (verit) assms(5) lastVal_ni ld_oav_ni ld_ov_ni reg_same_ld_dt)

apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc)")
                     apply simp

  apply (case_tac " \<not> readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
              apply simp
  apply (smt (verit) assms(5) lastVal_ni ld_ov_ni reg_same_ld_dt)

  apply simp
  apply (smt (verit) assms(1) assms(5) ld_coh_dt_ni ld_le_lim_ni ld_vrnew_dt_ni read_pre_def read_read_pre_ni)




  apply ( simp add: split: if_splits)
       apply ( simp add: split: if_splits)
 apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc)")
             apply simp
  apply (metis One_nat_def assms(5) cas_succ_eq)
 apply (case_tac " \<not> readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
             apply simp
  apply (elim disjE)
  apply (smt (verit) One_nat_def assms(5) cas_le_daddr cas_ov_daddr_dt_sx_ni cas_succ_lv_lc lastVal_def reg_same_CAS_dt)
  apply (metis One_nat_def cas_lc lastVal_def reg_same_CAS_dt zero_neq_one)
  apply (metis One_nat_def cas_fail_diff_lv less_irrefl_nat zero_neq_one)
  apply (metis One_nat_def cas_fail_diff_lv less_irrefl_nat zero_neq_one)
  apply simp
  apply (intro conjI)
  apply (metis reg_same_CAS_dt)
  using cas_read_pre_ni read_pre_def 
  apply (metis assms(1) assms(5) assms(8))
        apply (metis reg_same_CAS_dt)
 apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc)")
        apply simp
  apply (intro conjI)
  apply (metis reg_same_CAS_dt)
  apply (metis cas_fail_diff_lv cas_fail_lastVal_dt_ni)
  apply (metis cas_fail_lv_ni lastVal_def reg_same_CAS_dt)
  apply (metis reg_same_CAS_dt)
  apply (metis cas_fail_lv_ni lastVal_def reg_same_CAS_dt)
  apply (metis cas_fail_diff_lv cas_fail_lastVal_dt_ni)
  apply (metis reg_same_CAS_dt)
  apply (metis cas_fail_diff_lv cas_fail_lastVal_dt_ni)
  apply (metis assms(5) cas_fail_diff_lv cas_fail_lastVal_same cas_fail_oav_ni cas_le_daddr)
  apply (metis cas_fail_lv_ni lastVal_def reg_same_CAS_dt)
  apply simp
 apply (case_tac " \<not> readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
  apply simp
  apply (intro conjI)
  apply (metis reg_same_CAS_dt)
  apply (elim disjE)
  apply (subgoal_tac " lastVal glb (\<tau> \<sigma>') = lastVal glb (\<tau> \<sigma>)")
  prefer 2
  apply (metis cas_possible_lv_lc lastVal_def)
  apply (subgoal_tac "  regs (\<tau> \<sigma>') ta DTML.loc = lastVal glb (\<tau> \<sigma>') \<and> (\<forall>l. [l]\<^sub>ta \<tau> \<sigma>' = {lastVal l (\<tau> \<sigma>')}) ")
  prefer 2
  apply (intro conjI)
  apply (metis reg_same_CAS_dt)
  apply (metis assms(5) cas_le_daddr cas_ov_daddr_dt_sx_ni)
  apply metis
           apply (metis cas_possible_lv_lc lastVal_def reg_same_CAS_dt)
  apply (subgoal_tac "  even (regs (\<tau> \<sigma>') ta DTML.loc) \<and>
    regs (\<tau> \<sigma>') ta DTML.loc = lastVal glb (\<tau> \<sigma>') \<and>
    (\<forall>l. [l]\<^sub>ta \<tau> \<sigma>' = {lastVal l (\<tau> \<sigma>')})")
  prefer 2
           apply (intro conjI)
  apply (metis reg_same_CAS_dt)
  apply (metis cas_fail_lv_ni lastVal_def less_irrefl_nat reg_same_CAS_dt)
  apply (metis cas_fail_diff_lv cas_fail_lastVal_dt_ni nat_neq_iff)
  apply blast
  apply (metis cas_fail_lv_ni lastVal_def less_irrefl_nat reg_same_CAS_dt)
  apply (metis reg_same_CAS_dt)
  apply simp
  using read_pre_def cas_read_pre_ni
  apply (metis assms(1) assms(5))

 apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc)")
        apply simp
       apply (smt (z3) assms(5) lastVal_ni ld_oav_ni ld_ov_ni reg_same_ld_dr)

apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc)")
                     apply simp

  apply (case_tac " \<not> readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
              apply simp
       apply (smt (verit) assms(5) lastVal_ni ld_ov_ni reg_same_ld_dt)
  apply simp
  apply (smt (verit) assms(5) ld_coh_dt_ni ld_coh_valof_dt_ni ld_le_coh_ni ld_vrnew_dt_ni reg_same_ld_dt)

  by ( simp add: split: if_splits)+



lemma Commit_invocation_Read_global:
  assumes "thrdsvars"
and "  Read_inv  tb   ((pc \<sigma>) tb)  \<sigma>  "
and "Commit_invocation_inv ta  ((pc \<sigma>) ta) \<sigma>" 
 and " TML_Commit_invocation  ta   \<sigma> \<sigma>'"
and "total_wfs (\<tau> \<sigma>) "
  and "((pc \<sigma>) ta) \<in> {CommitPending, Ready} \<union> {Aborted} "
  and " ((pc \<sigma>)tb) \<in> {Aborted,ReadPending, ReadResponding} \<union> reading " 
and " ta \<noteq> tb"
and " ta \<noteq> syst"
and "tb \<noteq> syst"
shows "  Read_inv  tb   ((pc \<sigma>') tb)  \<sigma>'" 
  using assms
  apply(simp add:Commit_invocation_inv_def Read_inv_def total_wfs_def TML_Commit_invocation_def  )
  apply  (cases" pc  \<sigma> tb"; simp ; cases "(pc \<sigma>) ta"; simp )
    apply (unfold total_wfs_def read_pre_def Ready_total_def)
  apply (smt (verit))
  apply metis
  by metis





lemma Write_Commit_invocation_global:
  assumes "thrdsvars"
and "  Write_inv  tb   ((pc \<sigma>) tb)  \<sigma>  "
and "Commit_invocation_inv ta  ((pc \<sigma>) ta) \<sigma>" 
   and " TML_Write  tb    \<sigma> \<sigma>'"
and "total_wfs (\<tau> \<sigma>) "
  and "((pc \<sigma>) ta) \<in> {CommitPending, Ready} \<union> {Aborted} "
  and " ((pc \<sigma>)tb) \<in> {Aborted,WritePending, WriteResponding} \<union> writing "  
and " ta \<noteq> tb"
and  " \<forall>  t.  (   writer \<sigma> = Some t \<longrightarrow> odd (lastVal glb  (\<tau> \<sigma>)) )"
 and " \<forall>  t. (  (   writer \<sigma>  = Some t    \<longrightarrow> \<lceil>glb\<rceil>\<^sub>t (\<tau> \<sigma>) ))"
and " ta \<noteq> syst"
and "tb \<noteq> syst"
shows "Commit_invocation_inv ta  ((pc \<sigma>') ta) \<sigma>'" 
  using assms
 apply (unfold thrdsvars_def )
  apply (simp add:TML_Write_def Write_inv_def Commit_invocation_inv_def  )
  apply  (cases "(pc \<sigma>) ta";simp; cases "(pc \<sigma>) tb" ;simp)
                      apply (unfold total_wfs_def read_pre_def Ready_total_def)


apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc)")
                     apply simp

  apply (case_tac " \<not> readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
              apply simp
  apply (smt (verit) assms(5) lastVal_ni ld_ov_ni reg_same_ld_dt)

  apply simp

  apply ( simp add: split: if_splits)
  apply ( simp add: split: if_splits)
        apply (case_tac "   odd (regs (\<tau> \<sigma>) ta DTML.loc)")
                      apply simp
                      apply (intro conjI)
  apply (metis reg_same_CAS_dt)
  apply (meson cas_fail_lastVal_dt_ni)
  apply (metis cas_fail_lv_ni lastVal_def reg_same_CAS_dt)
                      apply (metis reg_same_CAS_dt)
  apply (metis cas_fail_lv_ni lastVal_def reg_same_CAS_dt)

  apply (meson cas_fail_lastVal_dt_ni)
  apply (metis reg_same_CAS_dt)
                      apply (meson cas_fail_lastVal_dt_ni)
  apply (metis assms(5) cas_fail_lastVal_same cas_fail_oav_ni cas_le_daddr)

                      apply (metis assms(5) cas_fail_lastVal_same reg_same_CAS_dt)
  apply (case_tac " \<not> readAux \<sigma>' ta \<and>  \<not> writeAux \<sigma>' ta ")
                      apply simp
                      apply (elim disjE)
  apply (subgoal_tac "      regs (\<tau> \<sigma>') ta DTML.loc = lastVal glb (\<tau> \<sigma>') \<or>
     regs (\<tau> \<sigma>') ta DTML.loc < lastVal glb (\<tau> \<sigma>') ")
                      prefer 2
  apply (metis cas_fail_lv_ni cas_possible_lv_lc lastVal_def less_Suc_eq reg_same_CAS_dt)

  apply (subgoal_tac " \<forall> l. [l]\<^sub>ta  (\<tau> \<sigma>') = [l]\<^sub>ta  (\<tau> \<sigma>) ")
  prefer 2
  apply (metis (no_types, lifting) cas_dt_ni cas_fail_lastVal_dt_ni singletonD)
  apply (metis cas_le_daddr reg_same_CAS_dt)
                      apply (metis assms(5) cas_fail_lastVal_same reg_same_CAS_dt)
                     apply (intro conjI)
                      apply (metis reg_same_CAS_dt)
                      apply simp
                      apply (intro conjI)
  apply (metis reg_same_CAS_dt)
  using  cas_read_pre_ni read_pre_def 
  apply (smt (verit) assms(5) cas_coh_dt_ni cas_coh_valof_dt_ni cas_le_lim_dt_ni cas_vrnew_dt_ni reg_same_CAS_dt)
  apply (metis reg_same_CAS_dt)
 apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc)")
        apply simp
  apply (metis cas_fail_diff_lv less_numeral_extra(3))
 apply (case_tac " \<not> readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
  apply (smt (verit) cas_lc cas_nlv_lc lastVal_def less_Suc_eq not_less_iff_gr_or_eq reg_same_CAS_dt)
                    apply simp
  using  cas_read_pre_ni read_pre_def 
  apply (smt (verit) assms(5) cas_coh_dt_ni cas_coh_valof_dt_ni cas_le_lim_dt_ni cas_vrnew_dt_ni reg_same_CAS_dt)
        apply (case_tac "   odd (regs (\<tau> \<sigma>) ta DTML.loc)")
  apply simp
   apply (case_tac " \<not> readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
  apply simp
                    apply (metis reg_dt_ni reg_write_lastVal_ni)
  apply simp
  apply (metis (no_types, lifting) assms(1) assms(5) read_pre_def upreg_read_pre_ni)

                  apply ( simp add: split: if_splits)


apply (case_tac "  odd (regs (\<tau> \<sigma>) ta DTML.loc)")
                     apply simp

  apply (case_tac " \<not> readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
              apply simp
  apply (smt (verit) assms(5) lastVal_ni ld_ov_ni reg_same_ld_dt)
  apply simp
  apply (metis assms(1) assms(5) read_pre_def read_read_pre_ni)




        apply (case_tac "   odd (regs (\<tau> \<sigma>) ta DTML.loc)")
  apply simp
                apply (case_tac " \<not> readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
                 apply simp
  apply simp
 

     apply (case_tac "   odd (regs (\<tau> \<sigma>) ta DTML.loc)")
  apply simp
                apply (case_tac " \<not> readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
                 apply simp
  apply (metis assms(5) reg_same_st st_lv__daddr_ni)
               apply simp
  using  reg_coh_dt_ni reg_same_st st_coh_valof_dt_ni st_le_lim_dt_ni st_vrnew_dt_ni
  apply (metis (no_types, lifting) assms(5))



        apply (case_tac "   odd (regs (\<tau> \<sigma>) ta DTML.loc)")
  apply simp
 apply (case_tac " \<not> readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
  apply simp
               apply (metis assms(5) flo_lastVal_ni reg_same_flo)
  apply simp
              apply (intro conjI)
  apply (metis reg_same_flo)
  apply clarify
  apply (metis assms(1) assms(5) flo_read_pre_ni read_pre_def)
              apply (metis reg_same_flo)

 apply (case_tac "   odd (regs (\<tau> \<sigma>) ta DTML.loc)")
  apply simp
 apply (case_tac " \<not> readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
  apply simp
               apply (metis assms(5) flo_lastVal_ni reg_same_flo)
  apply simp


    apply ( simp add: split: if_splits)
      apply ( simp add: split: if_splits)
        apply (case_tac "   odd (regs (\<tau> \<sigma>) ta DTML.loc)")
  apply  simp
  apply (intro conjI)
  apply (metis reg_same_CAS_dt)
  apply (meson cas_fail_lastVal_dt_ni)
  apply (metis cas_fail_lv_ni lastVal_def reg_same_CAS_dt)
  apply (metis reg_same_CAS_dt)
  apply (metis cas_fail_lv_ni lastVal_def reg_same_CAS_dt)
  apply (meson cas_fail_lastVal_dt_ni)
  apply (metis reg_same_CAS_dt)
  apply (meson cas_fail_lastVal_dt_ni)
  apply (metis assms(5) cas_fail_lastVal_same cas_fail_oav_ni cas_le_daddr)
  apply (metis cas_fail_lv_ni lastVal_def reg_same_CAS_dt)

 apply (case_tac " \<not> readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
             apply simp
  apply (elim disjE)
  apply (subgoal_tac "  even (regs (\<tau> \<sigma>') ta DTML.loc) \<and>
     regs (\<tau> \<sigma>') ta DTML.loc = lastVal glb (\<tau> \<sigma>') \<and> (\<forall>l. [l]\<^sub>ta \<tau> \<sigma>' = {lastVal l (\<tau> \<sigma>')})")
  prefer 2
  apply (intro conjI)
  apply (metis reg_same_CAS_dt)
  apply (metis assms(5) cas_fail_lastVal_same reg_same_CAS_dt)
  apply (meson cas_fail_lastVal_dt_ni)
  apply blast
  apply (metis assms(5) cas_fail_lastVal_same reg_same_CAS_dt)
  apply simp
  apply (intro conjI)
  apply (metis reg_same_CAS_dt)
  apply clarify
  apply (smt (verit) assms(5) cas_coh_dt_ni cas_coh_valof_dt_ni cas_le_lim_dt_ni cas_vrnew_dt_ni reg_same_CAS_dt)
  apply (metis reg_same_CAS_dt)

        apply (case_tac "   odd (regs (\<tau> \<sigma>) ta DTML.loc)")
  apply simp
  apply (metis Zero_not_Suc cas_nlv_lc gr0_implies_Suc lastVal_def)

 apply (case_tac " \<not> readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
  apply simp
  apply (metis cas_fail_diff_lv cas_lc lastVal_def less_Suc_eq neq0_conv reg_same_CAS_dt)

  apply simp
           apply (intro conjI)
  apply (metis reg_same_CAS_dt)
  apply clarify
  apply (smt (verit) assms(5) cas_coh_dt_ni cas_coh_valof_dt_ni cas_le_lim_dt_ni cas_vrnew_dt_ni reg_same_CAS_dt)
  apply (metis reg_same_CAS_dt)
  apply simp
          apply (elim disjE conjE)
  apply (metis map_upd_eqD1)
  apply meson
  apply meson
  apply fastforce
  apply meson
  apply fastforce
  apply linarith
  apply fastforce
  apply meson
  apply meson
               apply meson 
  apply linarith
  apply fastforce
  apply metis
  apply (metis reg_dt_ni reg_write_lastVal_ni)
  apply (metis (no_types, lifting) assms(1) assms(5) read_pre_def upreg_read_pre_ni)
         apply ( simp add: split: if_splits)
  apply (case_tac "   odd (regs (\<tau> \<sigma>) ta DTML.loc)")
      apply simp
apply (case_tac " \<not> readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
  apply simp
  apply (metis assms(5) lastVal_ni reg_same_ld_dt)
        apply simp
  apply (smt (z3) assms(1) assms(5) ld_coh_dt_ni ld_le_lim_ni ld_vrnew_dt_ni read_pre_def read_read_pre_ni)

  apply (case_tac "   odd (regs (\<tau> \<sigma>) ta DTML.loc)")
      apply simp
apply (case_tac " \<not> readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
  apply simp
        apply simp



        apply (case_tac "   odd (regs (\<tau> \<sigma>) ta DTML.loc)")
       apply simp
  apply (case_tac " \<not> readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
  apply simp
  apply (metis assms(5) reg_same_st st_lv__daddr_ni)
      apply simp
  using  reg_coh_dt_ni reg_same_st st_coh_valof_dt_ni st_le_lim_dt_ni st_lv__daddr_ni st_vrnew_dt_ni
  apply (smt (verit) assms(5))


         apply (case_tac "   odd (regs (\<tau> \<sigma>) ta DTML.loc)")
      apply simp
apply (case_tac " \<not> readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
  apply simp
  apply (metis assms(5) flo_lastVal_ni reg_same_flo)
      apply simp
  apply (metis assms(1) assms(5) flo_read_pre_ni read_pre_def)

  by  ( simp add: split: if_splits)+

lemma Commit_invocation_Write_global:
  assumes "thrdsvars"
and "  Write_inv  tb   ((pc \<sigma>) tb)  \<sigma>  "
and "Commit_invocation_inv ta  ((pc \<sigma>) ta) \<sigma>" 
 and " TML_Commit_invocation  ta   \<sigma> \<sigma>'"
and "total_wfs (\<tau> \<sigma>) "
  and "((pc \<sigma>) ta) \<in> {CommitPending, Ready} \<union> {Aborted} "
  and " ((pc \<sigma>)tb) \<in> {Aborted,WritePending, WriteResponding} \<union> writing " 
and " ta \<noteq> tb"
and " ta \<noteq> syst"
and "tb \<noteq> syst"
shows "  Write_inv  tb   ((pc \<sigma>') tb)  \<sigma>'" 
  using assms
  apply(simp add:Commit_invocation_inv_def Write_inv_def total_wfs_def TML_Commit_invocation_def  )
  apply  (cases" pc  \<sigma> tb"; simp ; cases "(pc \<sigma>) ta"; simp )
   apply (unfold total_wfs_def read_pre_def Ready_total_def)
  by metis+



lemma Commit_Commit_invocation_global:
  assumes "thrdsvars"
and "  Commit_inv  tb   ((pc \<sigma>) tb)  \<sigma>  "
and "Commit_invocation_inv ta  ((pc \<sigma>) ta) \<sigma>" 
   and " TML_Commit  tb    \<sigma> \<sigma>'"
and "total_wfs (\<tau> \<sigma>) "
  and "((pc \<sigma>) ta) \<in> {CommitPending, Ready} \<union> {Aborted} "
  and " ((pc \<sigma>)tb) \<in> {Aborted,CommitPending, CommitResponding} \<union> committing "  
and " ta \<noteq> tb"
and " ta \<noteq> syst"
and "tb \<noteq> syst"
shows "Commit_invocation_inv ta  ((pc \<sigma>') ta) \<sigma>'" 
  using assms
 apply (unfold thrdsvars_def )
  apply (simp add:TML_Commit_def Commit_inv_def Commit_invocation_inv_def  )
  apply  (cases "(pc \<sigma>) ta";simp; cases "(pc \<sigma>) tb" ;simp)
   apply (unfold total_wfs_def read_pre_def Ready_total_def)
  apply ( simp add: split: if_splits)+
apply (case_tac "   odd (regs (\<tau> \<sigma>) ta DTML.loc)")
  apply simp
 apply (case_tac " \<not> readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
  apply simp
  apply (metis lastVal_def reg_same_sfence sf_nlv_ni)
  apply (smt (verit) assms(1) assms(5) read_pre_def sf_read_pre_ni)
  apply auto[1]
 apply (case_tac "   odd (regs (\<tau> \<sigma>) ta DTML.loc)")
        apply simp 
 apply (case_tac " \<not> readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
  apply simp
  apply (metis less_SucI reg_same_st st_lastVal_lc)
   apply simp
  apply (intro conjI)
  apply (metis reg_same_st)
  apply (metis assms(1) assms(5) read_pre_def wr_glb_read_pre_ni)
  apply (metis reg_same_st)
      apply ( simp add: split: if_splits)
 apply (case_tac "   odd (regs (\<tau> \<sigma>) ta DTML.loc)")
  apply simp
 apply (case_tac " \<not> readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
  apply simp
      apply (metis lastVal_def reg_same_sfence sf_nlv_ni)
     apply simp
  apply (smt (verit) assms(5) reg_same_sfence sf_coh_ni sf_coh_valof_dt_ni sf_le_lim_ni sf_vrnew_dt_ni)


  apply auto[1]
  apply (case_tac "   odd (regs (\<tau> \<sigma>) ta DTML.loc)")
  apply simp
 apply (case_tac " \<not> readAux \<sigma> ta \<and>   \<not> writeAux \<sigma> ta ")
    apply simp
    apply (metis less_SucI reg_same_st st_lastVal_lc)
  apply simp
 apply (intro conjI)
  apply (metis reg_same_st)
  apply clarify
  apply (intro conjI)
  apply (metis reg_same_st)
  apply (metis assms(5) reg_coh_dt_ni)
  apply (metis assms(5) reg_same_st st_coh_valof_dt_ni)
  apply (metis assms(5) st_le_lim_dt_ni st_vrnew_dt_ni)
  apply (metis assms(5) reg_coh_dt_ni st_vrnew_dt_ni)
  apply (metis reg_same_st)
  by ( simp add: split: if_splits)



lemma Commit_invocation_Commit_global:
  assumes "thrdsvars"
and "  Commit_inv  tb   ((pc \<sigma>) tb)  \<sigma>  "
and "Commit_invocation_inv ta  ((pc \<sigma>) ta) \<sigma>" 
 and " TML_Commit_invocation  ta   \<sigma> \<sigma>'"
and "total_wfs (\<tau> \<sigma>) "
  and "((pc \<sigma>) ta) \<in> {CommitPending, Ready} \<union> {Aborted} "
  and " ((pc \<sigma>)tb) \<in> {Aborted,CommitPending, CommitResponding} \<union> committing " 
and " ta \<noteq> tb"
and " ta \<noteq> syst"
and "tb \<noteq> syst"
shows "  Commit_inv  tb   ((pc \<sigma>') tb)  \<sigma>'" 
  using assms
  apply(simp add:Commit_invocation_inv_def Commit_inv_def total_wfs_def TML_Commit_invocation_def  )
  apply  (cases" pc  \<sigma> tb"; simp ; cases "(pc \<sigma>) ta"; simp )
   apply (unfold total_wfs_def read_pre_def Ready_total_def)
  by metis+



lemma Write_invocation_local:
  assumes "thrdsvars"
and "total_wfs (\<tau> \<sigma>) "
and "Write_invocation_inv t  ((pc \<sigma>) t) \<sigma>" 
 and " TML_Write_invocation  t   \<sigma> \<sigma>'"
shows "Write_invocation_inv t  ((pc \<sigma>') t) \<sigma>'"  
  using assms
  apply (simp add: TML_Write_invocation_def Write_invocation_inv_def   total_wfs_def   )
  apply (cases "pc \<sigma> t";simp  )
  apply (unfold Ready_total_def read_pre_def)
  by force


lemma Commit_invocation_local:
  assumes "thrdsvars"
and "total_wfs (\<tau> \<sigma>) "
and "Commit_invocation_inv t  ((pc \<sigma>) t) \<sigma>" 
 and " TML_Commit_invocation  t   \<sigma> \<sigma>'"
shows "Commit_invocation_inv t  ((pc \<sigma>') t) \<sigma>'"  
  using assms
  apply (simp add: TML_Commit_invocation_def Commit_invocation_inv_def   total_wfs_def   )
  apply (cases "pc \<sigma> t";simp  )
  apply (unfold Ready_total_def read_pre_def)
  by metis






end

