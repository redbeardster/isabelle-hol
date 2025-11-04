(*Establishing correctness of the persistent invariant *)

theory DTML_Persistent_Invariant
  imports "DTML" "local_correctness/Commit"  "local_correctness/read_helper/ld_c"  "local_correctness/read_helper/inv_rules"

begin
(*********************************PM_INV**************************)
(*1*)
lemma Begin_pm_inv:
  assumes "thrdsvars"
      and "total_wfs (\<tau> \<sigma>)"
      and "  pm_inv  \<sigma> "
      and "TML_Begin  t   \<sigma> \<sigma>'"
    shows " pm_inv  \<sigma>' " 
  using assms 
  apply (simp add:TML_Begin_def Begin_inv_def total_wfs_def  pm_inv_def  )
  apply (cases "pc \<sigma> t"; simp)
   apply (metis Load_Rules.st_lv_lc lastVal_def ld_opv_ni)
  by (metis assms(2) lastVal_ni ld_opv_ni)


(*2*)
lemma Write_pm_inv:
  assumes "thrdsvars"
      and "total_wfs (\<tau> \<sigma>)"
      and "pm_inv  \<sigma> "
      and "TML_Write  t    \<sigma> \<sigma>'"
    shows " pm_inv  \<sigma>' " 
  using assms 
  apply (simp add:TML_Write_def pm_inv_def total_wfs_def;  simp add: split if_splits )
 apply (cases "pc \<sigma> t";   simp  )

  apply metis
      apply  ( simp add: split: if_split_asm)
  using cas_fail_opv_ni cas_le_daddr apply presburger
  apply (metis (no_types, lifting) cas_le_daddr cas_opv_ni insert_absorb lev_in_opv subset_singletonD)
   using  reg_write_pm_preserved[where y = glb ]
       apply presburger
   apply (metis lastVal_ni ld_opv_ni)
   apply (smt (verit) insertE insert_absorb insert_not_empty lev_in_opv st_opv_daddr_ni)
   by (metis empty_iff flo_opv_ni insert_iff lev_in_opv)


(*3*)
lemma Read_pm_inv:
  assumes "thrdsvars"
      and "total_wfs (\<tau> \<sigma>)"
      and "pm_inv  \<sigma> "
       and "TML_Read  t   \<sigma> \<sigma>'"
    shows " pm_inv  \<sigma>' " 
  using assms 
  apply (simp add:TML_Read_def pm_inv_def total_wfs_def;  simp add: split if_splits )
  apply (cases "pc \<sigma> t";   simp  )
  apply (metis lastVal_ni ld_opv_ni)
     apply metis
  apply (metis (no_types, lifting) cas_le_daddr cas_opv_ni insert_absorb lev_in_opv subset_singletonD)
  apply (metis lastVal_ni ld_opv_ni)
  by metis

(*4*)
lemma Commit_pm_inv:
  assumes "thrdsvars"
      and "total_wfs (\<tau> \<sigma>)"
      and "pm_inv  \<sigma> "
      and "TML_Commit  t   \<sigma> \<sigma>'"
    and "  Commit_inv  t   ((pc \<sigma>) t) \<sigma>  "
    shows " pm_inv  \<sigma>' " 
 using assms 
  apply (simp add:TML_Commit_def pm_inv_def total_wfs_def Commit_inv_def)
  apply (cases "pc \<sigma> t";  simp add: split if_splits )
  using sf_pm_inv_preserved [where y = glb ]
    apply (metis insert_absorb lev_in_opv sf_opv_sub singleton_iff subset_singleton_iff)
  apply blast
  by (metis lev_in_opv singleton_iff st_opv_daddr_ni)



(*5*)
lemma  crash_pm_inv:
assumes  "thrdsvars"
and "TML_Crash  \<sigma> \<sigma>'"
 and "pm_inv  \<sigma> "
shows " pm_inv  \<sigma>' " 
  using assms
  apply(simp add:TML_Crash_def pm_inv_def)
  by (meson opv_ni_s lv_ov_ni)

(*6*)
lemma recover_pm_inv:
assumes "thrdsvars"
and "total_wfs (\<tau> \<sigma>)"
and " TML_Recover t   \<sigma> \<sigma>' "
and "  Recover_inv  t  ((pc \<sigma>) t)  \<sigma>"
and "pm_inv  \<sigma> "
shows  "pm_inv  \<sigma>' "
  using assms
  apply(simp add:TML_Recover_def pm_inv_def  Recover_inv_def total_wfs_def)
  apply (cases "pc \<sigma> t";   simp  )
  using  reg_write_pm_preserved[where y = glb ] 
  apply presburger
  apply (subgoal_tac " get_key (log \<sigma>) \<in> dom (log \<sigma>')  ")
  prefer 2
  using get_key_in_dom apply auto[1]
  apply (smt (z3) insert_absorb lev_in_opv singleton_insert_inj_eq st_opv_daddr_ni)
  apply (metis assms(2) flo_lastVal_ni flo_opv_ni)
  apply (smt (z3) insert_absorb insert_iff lev_in_opv sf_opv_sub singleton_insert_inj_eq' subset_singleton_iff)
  apply meson
  apply (metis assms(2) lastVal_ni ld_opv_ni)
  apply presburger
  apply (metis insertE insert_absorb insert_not_empty lev_in_opv st_opv_daddr_ni)
  apply (metis insertE insert_absorb insert_not_empty lev_in_opv st_opv_daddr_ni)
  by presburger


lemma beginInv_pm_inv:
assumes  "thrdsvars"
and "TML_Begin_invocation t  \<sigma> \<sigma>'"
  and " Begin_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
 and "pm_inv  \<sigma> "
shows  "pm_inv  \<sigma>' "
  using assms
  apply (simp add: TML_Begin_invocation_def Begin_invocation_inv_def total_wfs_def pm_inv_def )
  by (cases "pc \<sigma> t";  simp )



lemma beginResp_pm_inv:
assumes  "thrdsvars"
and "TML_Begin_response t  \<sigma> \<sigma>'"
 and "pm_inv  \<sigma> "
shows  "pm_inv  \<sigma>' "
  using assms
  apply (simp add: TML_Begin_response_def total_wfs_def  pm_inv_def )
  by (cases "pc \<sigma> t";  simp)


lemma readInv_pm_inv:
assumes  "thrdsvars"
and "TML_Read_invocation t  \<sigma> \<sigma>'"
  and " Begin_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
 and "pm_inv  \<sigma> "
shows  "pm_inv  \<sigma>' "
  using assms
  apply (simp add: TML_Read_invocation_def Begin_invocation_inv_def total_wfs_def  pm_inv_def )
 by  (cases "pc \<sigma> t";  simp )



lemma readResp_pm_inv:
assumes  "thrdsvars"
and "TML_Read_response t  \<sigma> \<sigma>'"
 and "pm_inv  \<sigma> "
shows  "pm_inv  \<sigma>' "
  using assms
  apply (simp add: TML_Read_response_def total_wfs_def  pm_inv_def )
  by (cases "pc \<sigma> t";  simp)


lemma writeInv_pm_inv:
assumes  "thrdsvars"
and "TML_Write_invocation t  \<sigma> \<sigma>'"
  and " Write_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
 and "pm_inv  \<sigma> "
shows  "pm_inv  \<sigma>' "
  using assms
  apply (simp add: TML_Write_invocation_def  total_wfs_def pm_inv_def )
  by (cases "pc \<sigma> t";  simp )





lemma writeResp_pm_inv:
assumes  "thrdsvars"
and "TML_Write_response t  \<sigma> \<sigma>'"
 and "pm_inv  \<sigma> "
shows  "pm_inv  \<sigma>' " 
  using assms
  apply (simp add: TML_Write_response_def total_wfs_def pm_inv_def )
  by (cases "pc \<sigma> t";  simp)




lemma commitInv_pm_inv:
assumes  "thrdsvars"
and "TML_Commit_invocation t  \<sigma> \<sigma>'"
  and " Commit_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
 and "pm_inv  \<sigma> "
shows  "pm_inv  \<sigma>' "
  using assms
  apply (simp add: TML_Commit_invocation_def  total_wfs_def pm_inv_def )
  by (cases "pc \<sigma> t";  simp )




lemma commitResp_pm_inv:
assumes  "thrdsvars"
and "TML_Commit_response t  \<sigma> \<sigma>'"
 and "pm_inv  \<sigma> "
shows  "pm_inv  \<sigma>' "
  using assms
  apply (simp add: TML_Commit_response_def total_wfs_def pm_inv_def )
  by (cases "pc \<sigma> t";  simp)



(**************glb not in log*******************)




(*1*)
lemma recover_log:
 assumes "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
  and " TML_Recover syst   \<sigma> \<sigma>' "
 and "  Recover_inv  syst  ((pc \<sigma>) syst)  \<sigma>"
 and " (\<forall>a. a \<in> dom (log \<sigma>) \<longrightarrow> a \<noteq> glb) "
shows " (\<forall>a. a \<in> dom (log \<sigma>') \<longrightarrow> a \<noteq> glb)"
using assms
  apply (simp add:TML_Recover_def total_wfs_def Recover_inv_def)
  apply (cases "pc \<sigma> syst";   simp add: split if_splits)
  using assms(5)by  presburger+

(*2*)
lemma begin_log:
 assumes "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
 and "TML_Begin  t   \<sigma> \<sigma>'"
  and "  Begin_inv  t  ((pc \<sigma>) t) \<sigma>   "
 and " (\<forall>a. a \<in> dom (log \<sigma>) \<longrightarrow> a \<noteq> glb) "
shows " (\<forall>a. a \<in> dom (log \<sigma>') \<longrightarrow> a \<noteq> glb)"
  using assms
 apply (simp add:TML_Begin_def total_wfs_def Begin_inv_def )
  by (cases "pc \<sigma> t";  simp add: split if_splits )

(*3*)
lemma write_log :
  assumes "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
  and " Write_inv  t  ((pc \<sigma>) t) \<sigma> "
 and "TML_Write  t   \<sigma> \<sigma>'"
 and " (\<forall>a. a \<in> dom (log \<sigma>) \<longrightarrow> a \<noteq> glb) "
shows " (\<forall>a. a \<in> dom (log \<sigma>') \<longrightarrow> a \<noteq> glb)"
 using assms
  apply (simp add:TML_Write_def Write_inv_def total_wfs_def   )
  apply (cases "pc \<sigma> t";  simp add: split if_splits )
  apply presburger
  apply (metis gr0I)
  by metis

(*4*)
lemma commit_log:
 assumes "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
  and "  Commit_inv  t   ((pc \<sigma>) t) \<sigma>  "
  and "TML_Commit  t   \<sigma> \<sigma>'"
  and " (\<forall>a. a \<in> dom (log \<sigma>) \<longrightarrow> a \<noteq> glb) "
shows " (\<forall>a. a \<in> dom (log \<sigma>') \<longrightarrow> a \<noteq> glb)"
 using assms
  apply (simp add:TML_Commit_def Commit_inv_def total_wfs_def   )
  by(cases "pc \<sigma> t"; simp )

(*5*)
lemma read_log:
 assumes "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
  and "Read_inv t  ((pc \<sigma>) t) \<sigma>" 
  and "TML_Read  t   \<sigma> \<sigma>'"
  and " (\<forall>a. a \<in> dom (log \<sigma>) \<longrightarrow> a \<noteq> glb) "
shows " (\<forall>a. a \<in> dom (log \<sigma>') \<longrightarrow> a \<noteq> glb)"
  using assms
  apply (unfold  total_wfs_def)
  apply (simp add: TML_Read_def Read_inv_def   )
  apply (cases "pc \<sigma> t";  simp add: split if_splits)
  by presburger+

(*6*)
lemma crash_log:
assumes  "thrdsvars"
and "TML_Crash  \<sigma> \<sigma>'"
  and " (\<forall>a. a \<in> dom (log \<sigma>) \<longrightarrow> a \<noteq> glb) "
shows " (\<forall>a. a \<in> dom (log \<sigma>') \<longrightarrow> a \<noteq> glb)"
  using assms
 by (simp add: TML_Crash_def  total_wfs_def )



lemma beginInv_log:
assumes  "thrdsvars"
and "TML_Begin_invocation t  \<sigma> \<sigma>'"
  and " Begin_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
  and " (\<forall>a. a \<in> dom (log \<sigma>) \<longrightarrow> a \<noteq> glb) "
shows " (\<forall>a. a \<in> dom (log \<sigma>') \<longrightarrow> a \<noteq> glb)"
  using assms
  apply (simp add: TML_Begin_invocation_def Begin_invocation_inv_def total_wfs_def )
  by (cases "pc \<sigma> t";  simp )

lemma beginResp_log:
assumes  "thrdsvars"
and "TML_Begin_response t  \<sigma> \<sigma>'"
  and " (\<forall>a. a \<in> dom (log \<sigma>) \<longrightarrow> a \<noteq> glb) "
shows " (\<forall>a. a \<in> dom (log \<sigma>') \<longrightarrow> a \<noteq> glb)"
  using assms
  apply (simp add: TML_Begin_response_def total_wfs_def )
  by (cases "pc \<sigma> t";  simp)

lemma readInv_log:
assumes  "thrdsvars"
and "TML_Read_invocation t  \<sigma> \<sigma>'"
  and " Begin_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
  and " (\<forall>a. a \<in> dom (log \<sigma>) \<longrightarrow> a \<noteq> glb) "
shows " (\<forall>a. a \<in> dom (log \<sigma>') \<longrightarrow> a \<noteq> glb)"
  using assms
  apply (simp add: TML_Read_invocation_def Begin_invocation_inv_def total_wfs_def )
  by (cases "pc \<sigma> t";  simp )

lemma readResp_log:
assumes  "thrdsvars"
and "TML_Read_response t  \<sigma> \<sigma>'"
  and " (\<forall>a. a \<in> dom (log \<sigma>) \<longrightarrow> a \<noteq> glb) "
shows " (\<forall>a. a \<in> dom (log \<sigma>') \<longrightarrow> a \<noteq> glb)"
  using assms
  apply (simp add: TML_Read_response_def total_wfs_def )
  by (cases "pc \<sigma> t";  simp)


lemma writeInv_log:
assumes  "thrdsvars"
and "TML_Write_invocation t  \<sigma> \<sigma>'"
  and " Write_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
  and " (\<forall>a. a \<in> dom (log \<sigma>) \<longrightarrow> a \<noteq> glb) "
shows " (\<forall>a. a \<in> dom (log \<sigma>') \<longrightarrow> a \<noteq> glb)"
  using assms
  apply (simp add: TML_Write_invocation_def  total_wfs_def )
  by (cases "pc \<sigma> t";  simp )




lemma writeResp_log:
assumes  "thrdsvars"
and "TML_Write_response t  \<sigma> \<sigma>'"
  and " (\<forall>a. a \<in> dom (log \<sigma>) \<longrightarrow> a \<noteq> glb) "
shows " (\<forall>a. a \<in> dom (log \<sigma>') \<longrightarrow> a \<noteq> glb)"
  using assms
  apply (simp add: TML_Write_response_def total_wfs_def )
  by (cases "pc \<sigma> t";  simp)




lemma commitInv_log:
assumes  "thrdsvars"
and "TML_Commit_invocation t  \<sigma> \<sigma>'"
  and " Commit_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
  and " (\<forall>a. a \<in> dom (log \<sigma>) \<longrightarrow> a \<noteq> glb) "
shows " (\<forall>a. a \<in> dom (log \<sigma>') \<longrightarrow> a \<noteq> glb)"
  using assms
  apply (simp add: TML_Commit_invocation_def  total_wfs_def )
  by (cases "pc \<sigma> t";  simp )




lemma commitResp_recidl_log:
assumes  "thrdsvars"
and "TML_Commit_response t  \<sigma> \<sigma>'"
  and " (\<forall>a. a \<in> dom (log \<sigma>) \<longrightarrow> a \<noteq> glb) "
shows " (\<forall>a. a \<in> dom (log \<sigma>') \<longrightarrow> a \<noteq> glb)"
  using assms
  apply (simp add: TML_Commit_response_def total_wfs_def )
  by (cases "pc \<sigma> t";  simp)






(**************glb not in log*******************)
(*1*)
lemma recover_pc_on_rec:
 assumes "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
  and " TML_Recover syst   \<sigma> \<sigma>' "
 and "  Recover_inv  syst  ((pc \<sigma>) syst)  \<sigma>"
 and "((pc \<sigma>) syst) \<noteq> RecIdle   \<longrightarrow> (\<forall> t  \<noteq> syst.  ((pc \<sigma>) t)   \<in> {PC.NotStarted, PC.Aborted, PC.Committed}) "
shows "((pc \<sigma>') syst) \<noteq> RecIdle   \<longrightarrow> (\<forall> t  \<noteq> syst.  ((pc \<sigma>') t)   \<in> {PC.NotStarted, PC.Aborted, PC.Committed}) "
using assms
  apply (simp add:TML_Recover_def total_wfs_def Recover_inv_def)
  apply (cases "pc \<sigma> syst";   simp add: split if_splits)
  apply (case_tac "even (regs (\<tau> \<sigma>) syst c1)")
  apply simp
  apply simp
  by (metis pc_aux)


(*2*)
lemma begin_pc_on_rec:
 assumes "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
 and "TML_Begin  t   \<sigma> \<sigma>'"
  and "  Begin_inv  t  ((pc \<sigma>) t) \<sigma>   "
 and "((pc \<sigma>) syst) \<noteq> RecIdle   \<longrightarrow> (\<forall> t  \<noteq> syst.  ((pc \<sigma>) t)   \<in> {PC.NotStarted, PC.Aborted, PC.Committed}) "
shows "((pc \<sigma>') syst) \<noteq> RecIdle   \<longrightarrow> (\<forall> t  \<noteq> syst.  ((pc \<sigma>') t)   \<in> {PC.NotStarted, PC.Aborted, PC.Committed}) "
  using assms
 apply (simp add:TML_Begin_def total_wfs_def Begin_inv_def )
  apply (cases "pc \<sigma> t";  simp add: split if_splits )
  apply (metis PC.distinct(1) PC.distinct(157) PC.distinct(209) PC.distinct(97) fun_upd_same)
   apply (metis PC.distinct(209))
  by (metis PC.distinct(283) fun_upd_other)




(*3*)
lemma  write_pc_on_rec:
  assumes "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
  and " Write_inv  t  ((pc \<sigma>) t) \<sigma> "
 and "TML_Write  t   \<sigma> \<sigma>'"
 and "((pc \<sigma>) syst) \<noteq> RecIdle   \<longrightarrow> (\<forall> t  \<noteq> syst.  ((pc \<sigma>) t)   \<in> {PC.NotStarted, PC.Aborted, PC.Committed}) "
shows "((pc \<sigma>') syst) \<noteq> RecIdle   \<longrightarrow> (\<forall> t  \<noteq> syst.  ((pc \<sigma>') t)   \<in> {PC.NotStarted, PC.Aborted, PC.Committed}) "
 using assms
  apply (simp add:TML_Write_def Write_inv_def total_wfs_def   )
  apply (cases "pc \<sigma> t";  simp add: split if_splits )
  apply (metis PC.distinct(1153) PC.distinct(1177) PC.distinct(35) PC.distinct(725))
        apply (simp split:if_splits )
  apply (metis PC.distinct(1195) PC.distinct(1219) PC.distinct(37) PC.distinct(727))
  apply (metis PC.distinct(1195) PC.distinct(1219) PC.distinct(37) PC.distinct(727))

       apply (simp split:if_splits )+
       apply (case_tac "  0 < regs (\<tau> \<sigma>') t c1  ")
  apply simp
        apply (metis PC.distinct(1235))
  apply simp
  apply (metis PC.distinct(1235))

  apply (metis PC.distinct(1273))
  apply (case_tac " inLoc \<sigma> t \<notin> dom (log \<sigma>)")
  apply (metis PC.distinct(1309) fun_upd_other)
  apply (metis PC.distinct(1309) fun_upd_other)



  apply (metis PC.distinct(1343))
  apply (metis PC.distinct(1375))
  apply (metis PC.distinct(1405))
  by (metis PC.distinct(1433))




(*4*)
lemma commit_pc_on_rec:
 assumes "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
  and "  Commit_inv  t   ((pc \<sigma>) t) \<sigma>  "
  and "TML_Commit  t   \<sigma> \<sigma>'"
 and "((pc \<sigma>) syst) \<noteq> RecIdle   \<longrightarrow> (\<forall> t  \<noteq> syst.  ((pc \<sigma>) t)   \<in> {PC.NotStarted, PC.Aborted, PC.Committed}) "
shows "((pc \<sigma>') syst) \<noteq> RecIdle   \<longrightarrow> (\<forall> t  \<noteq> syst.  ((pc \<sigma>') t)   \<in> {PC.NotStarted, PC.Aborted, PC.Committed}) "
 using assms
  apply (simp add:TML_Commit_def Commit_inv_def total_wfs_def   )
  apply(cases "pc \<sigma> t"; simp )
  apply (metis PC.distinct(389) PC.distinct(425) PC.distinct(449) PC.distinct(9) pc_aux)

  apply (metis PC.distinct(493))
  apply (metis PC.distinct(559))
  by (metis PC.distinct(623))





(*5*)
lemma read_pc_on_rec:
 assumes "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
  and "Read_inv t  ((pc \<sigma>) t) \<sigma>" 
  and "TML_Read  t   \<sigma> \<sigma>'"
 and "((pc \<sigma>) syst) \<noteq> RecIdle   \<longrightarrow> (\<forall> t  \<noteq> syst.  ((pc \<sigma>) t)   \<in> {PC.NotStarted, PC.Aborted, PC.Committed}) "
shows "((pc \<sigma>') syst) \<noteq> RecIdle   \<longrightarrow> (\<forall> t  \<noteq> syst.  ((pc \<sigma>') t)   \<in> {PC.NotStarted, PC.Aborted, PC.Committed}) "
  using assms
  apply (unfold  total_wfs_def)
  apply (simp add: TML_Read_def Read_inv_def Ready_total_def  )
  apply (cases "pc \<sigma> t";  simp add: split if_splits)
  apply (metis PC.distinct(21) PC.distinct(711) PC.distinct(803) PC.distinct(827))
  apply (metis PC.distinct(23) PC.distinct(713) PC.distinct(859) PC.distinct(883))
   apply (simp split:if_splits )
  apply (metis PC.distinct(913))
  apply (metis PC.distinct(913))
    apply (case_tac "  regs (\<tau> \<sigma>') t c1 = Suc 0")
     apply simp
  apply (metis PC.distinct(965))
    apply simp
  apply (metis PC.distinct(965))

  apply (metis PC.distinct(1015))
   apply (simp split:if_splits )
  apply (metis PC.distinct(1063))
  by (metis PC.distinct(1063))


(*6*)
lemma crash_pc_on_rec:
assumes  "thrdsvars"
and "TML_Crash  \<sigma> \<sigma>'"
 and "((pc \<sigma>) syst) \<noteq> RecIdle   \<longrightarrow> (\<forall> t  \<noteq> syst.  ((pc \<sigma>) t)   \<in> {PC.NotStarted, PC.Aborted, PC.Committed}) "
shows "((pc \<sigma>') syst) \<noteq> RecIdle   \<longrightarrow> (\<forall> t  \<noteq> syst.  ((pc \<sigma>') t)   \<in> {PC.NotStarted, PC.Aborted, PC.Committed}) "
  using assms
 by (simp add: TML_Crash_def  total_wfs_def )




lemma beginInv_pc_on_rec:
assumes  "thrdsvars"
and "TML_Begin_invocation t  \<sigma> \<sigma>'"
  and " Begin_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
 and "((pc \<sigma>) syst) \<noteq> RecIdle   \<longrightarrow> (\<forall> t  \<noteq> syst.  ((pc \<sigma>) t)   \<in> {PC.NotStarted, PC.Aborted, PC.Committed}) "
shows "((pc \<sigma>') syst) \<noteq> RecIdle   \<longrightarrow> (\<forall> t  \<noteq> syst.  ((pc \<sigma>') t)   \<in> {PC.NotStarted, PC.Aborted, PC.Committed}) "
  using assms
  apply (simp add: TML_Begin_invocation_def Begin_invocation_inv_def total_wfs_def )
  apply (cases "pc \<sigma> t";  simp )
  by (metis PC.distinct(133) fun_upd_def)


lemma beginResp_pc_on_rec:
assumes  "thrdsvars"
and "TML_Begin_response t  \<sigma> \<sigma>'"
 and "((pc \<sigma>) syst) \<noteq> RecIdle   \<longrightarrow> (\<forall> t  \<noteq> syst.  ((pc \<sigma>) t)   \<in> {PC.NotStarted, PC.Aborted, PC.Committed}) "
shows "((pc \<sigma>') syst) \<noteq> RecIdle   \<longrightarrow> (\<forall> t  \<noteq> syst.  ((pc \<sigma>') t)   \<in> {PC.NotStarted, PC.Aborted, PC.Committed}) "
  using assms
  apply (simp add: TML_Begin_response_def total_wfs_def )
  apply (cases "pc \<sigma> t";  simp)
  by (metis PC.distinct(355) fun_upd_other)


lemma readInv_pc_on_rec:
assumes  "thrdsvars"
and "TML_Read_invocation t  \<sigma> \<sigma>'"
  and " Begin_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
 and "((pc \<sigma>) syst) \<noteq> RecIdle   \<longrightarrow> (\<forall> t  \<noteq> syst.  ((pc \<sigma>) t)   \<in> {PC.NotStarted, PC.Aborted, PC.Committed}) "
shows "((pc \<sigma>') syst) \<noteq> RecIdle   \<longrightarrow> (\<forall> t  \<noteq> syst.  ((pc \<sigma>') t)   \<in> {PC.NotStarted, PC.Aborted, PC.Committed}) "
  using assms
  apply (simp add: TML_Read_invocation_def Begin_invocation_inv_def total_wfs_def )
  apply (cases "pc \<sigma> t";  simp )
  by (metis PC.distinct(1505) fun_upd_other)


lemma readResp_pc_on_rec:
assumes  "thrdsvars"
and "TML_Read_response t  \<sigma> \<sigma>'"
 and "((pc \<sigma>) syst) \<noteq> RecIdle   \<longrightarrow> (\<forall> t  \<noteq> syst.  ((pc \<sigma>) t)   \<in> {PC.NotStarted, PC.Aborted, PC.Committed}) "
shows "((pc \<sigma>') syst) \<noteq> RecIdle   \<longrightarrow> (\<forall> t  \<noteq> syst.  ((pc \<sigma>') t)   \<in> {PC.NotStarted, PC.Aborted, PC.Committed}) "
  using assms
  apply (simp add: TML_Read_response_def total_wfs_def )
  apply (cases "pc \<sigma> t";  simp)
  by (metis PC.distinct(1109) fun_upd_other)


lemma writeInv_pc_on_rec:
assumes  "thrdsvars"
and "TML_Write_invocation t  \<sigma> \<sigma>'"
  and " Write_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
 and "((pc \<sigma>) syst) \<noteq> RecIdle   \<longrightarrow> (\<forall> t  \<noteq> syst.  ((pc \<sigma>) t)   \<in> {PC.NotStarted, PC.Aborted, PC.Committed}) "
shows "((pc \<sigma>') syst) \<noteq> RecIdle   \<longrightarrow> (\<forall> t  \<noteq> syst.  ((pc \<sigma>') t)   \<in> {PC.NotStarted, PC.Aborted, PC.Committed}) "
  using assms
  apply (simp add: TML_Write_invocation_def  total_wfs_def )
  apply (cases "pc \<sigma> t";  simp )
  by (metis PC.distinct(1505) fun_upd_other)




lemma writeResp_pc_on_rec:
assumes  "thrdsvars"
and "TML_Write_response t  \<sigma> \<sigma>'"
 and "((pc \<sigma>) syst) \<noteq> RecIdle   \<longrightarrow> (\<forall> t  \<noteq> syst.  ((pc \<sigma>) t)   \<in> {PC.NotStarted, PC.Aborted, PC.Committed}) "
shows "((pc \<sigma>') syst) \<noteq> RecIdle   \<longrightarrow> (\<forall> t  \<noteq> syst.  ((pc \<sigma>') t)   \<in> {PC.NotStarted, PC.Aborted, PC.Committed}) "
  using assms
  apply (simp add: TML_Write_response_def total_wfs_def )
  apply (cases "pc \<sigma> t";  simp)
  by (metis PC.distinct(1459) fun_upd_other)




lemma commitInv_pc_on_rec:
assumes  "thrdsvars"
and "TML_Commit_invocation t  \<sigma> \<sigma>'"
  and " Commit_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
 and "((pc \<sigma>) syst) \<noteq> RecIdle   \<longrightarrow> (\<forall> t  \<noteq> syst.  ((pc \<sigma>) t)   \<in> {PC.NotStarted, PC.Aborted, PC.Committed}) "
shows "((pc \<sigma>') syst) \<noteq> RecIdle   \<longrightarrow> (\<forall> t  \<noteq> syst.  ((pc \<sigma>') t)   \<in> {PC.NotStarted, PC.Aborted, PC.Committed}) "
  using assms
  apply (simp add: TML_Commit_invocation_def  total_wfs_def )
  apply (cases "pc \<sigma> t";  simp )
  by (metis PC.distinct(1505) fun_upd_other)




lemma commitResp_pc_on_rec:
assumes  "thrdsvars"
and "TML_Commit_response t  \<sigma> \<sigma>'"
 and "((pc \<sigma>) syst) \<noteq> RecIdle   \<longrightarrow> (\<forall> t  \<noteq> syst.  ((pc \<sigma>) t)   \<in> {PC.NotStarted, PC.Aborted, PC.Committed}) "
shows "((pc \<sigma>') syst) \<noteq> RecIdle   \<longrightarrow> (\<forall> t  \<noteq> syst.  ((pc \<sigma>') t)   \<in> {PC.NotStarted, PC.Aborted, PC.Committed}) "
  using assms
  apply (simp add: TML_Commit_response_def total_wfs_def )
  apply (cases "pc \<sigma> t";  simp)
  by (metis PC.distinct(685))















(*************on recover glb2 *********************************)


(*and "pc cs  syst  = RecIdle  \<longrightarrow> ( lastVal glb (\<tau> cs)  \<ge>recoveredGlb cs ) "
*)
(*1*)
lemma recover_recidl_lvglb_ge_recglb:
 assumes "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
  and " TML_Recover syst   \<sigma> \<sigma>' "
 and "  Recover_inv  syst  ((pc \<sigma>) syst)  \<sigma>"
(*and " thread_prop_comp  \<sigma> t "*)
 and "pc \<sigma>  syst  = RecIdle  \<longrightarrow> ( lastVal glb (\<tau> \<sigma>)  \<ge>recoveredGlb \<sigma> ) "
shows "pc \<sigma>'  syst  = RecIdle  \<longrightarrow> ( lastVal glb (\<tau> \<sigma>')  \<ge>recoveredGlb \<sigma>' ) "
using assms
  apply (simp add:TML_Recover_def total_wfs_def Recover_inv_def)
  apply (cases "pc \<sigma> syst";   simp add: split if_splits)
  apply (case_tac "even (regs (\<tau> \<sigma>) syst c1)")
  apply simp
   apply simp
  apply (metis eq_imp_le st_lastVal_lc)
  apply (metis eq_imp_le st_lastVal_lc)
  apply (case_tac "log \<sigma> = Map.empty ")
  apply simp
  by simp



(*2*)
lemma begin_recidl_lvglb_ge_recglb :
 assumes "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
 and "TML_Begin  t   \<sigma> \<sigma>'"
  and "  Begin_inv  t  ((pc \<sigma>) t) \<sigma>   "
 and " t \<noteq> syst "
 and "pc \<sigma>  syst  = RecIdle  \<longrightarrow> ( lastVal glb (\<tau> \<sigma>)  \<ge>recoveredGlb \<sigma> ) "
shows "pc \<sigma>'  syst  = RecIdle  \<longrightarrow> ( lastVal glb (\<tau> \<sigma>')  \<ge>recoveredGlb \<sigma>' ) "
  using assms
 apply (simp add:TML_Begin_def total_wfs_def Begin_inv_def )
  apply (cases "pc \<sigma> t";  simp add: split if_splits )
  apply (metis assms(2) lastVal_ni)
  by (metis fun_upd_other)



(*3*)
lemma write_recidl_lvglb_ge_recglb  :
  assumes "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
  and " Write_inv  t  ((pc \<sigma>) t) \<sigma> "
 and "TML_Write  t   \<sigma> \<sigma>'"
 and " t \<noteq> syst "
 and "pc \<sigma>  syst  = RecIdle  \<longrightarrow> ( lastVal glb (\<tau> \<sigma>)  \<ge>recoveredGlb \<sigma> ) "
shows "pc \<sigma>'  syst  = RecIdle  \<longrightarrow> ( lastVal glb (\<tau> \<sigma>')  \<ge>recoveredGlb \<sigma>' ) "
 using assms
  apply (simp add:TML_Write_def Write_inv_def total_wfs_def   )
  apply (cases "pc \<sigma> t";  simp add: split if_splits )
      apply  ( simp add: split: if_split_asm)

      apply (case_tac "regs (\<tau> \<sigma>') t c1 = 0  ")
       apply simp
       apply (metis assms(2) cas_fail_lastVal_same)
  apply (subgoal_tac "  regs (\<tau> \<sigma>) t DTML.loc  \<le>  lastVal glb (\<tau> \<sigma>') ")
       prefer 2
  apply (metis Suc_n_not_le_n cas_lc lastVal_def less_nat_zero_code linorder_neqE_nat nat_le_linear)
      apply (subgoal_tac "  regs (\<tau> \<sigma>) t DTML.loc = lastVal glb (\<tau> \<sigma>) ")
       prefer 2
       apply (metis cas_fail_diff_lv gr0I)
      apply simp
  using reg_write_lastVal_ni apply presburger
      apply (metis fun_upd_def)
  apply (metis assms(2) lastVal_ni)
  apply (metis assms(2) lev_in_ov singletonD st_ov_ni total_wfs_def)
  by (metis assms(2) flo_lastVal_ni)


(*4*)
lemma commit_recidl_lvglb_ge_recglb:
 assumes "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
  and "  Commit_inv  t   ((pc \<sigma>) t) \<sigma>  "
  and "TML_Commit  t   \<sigma> \<sigma>'"
 and " t \<noteq> syst "
 and "pc \<sigma>  syst  = RecIdle  \<longrightarrow> ( lastVal glb (\<tau> \<sigma>)  \<ge>recoveredGlb \<sigma> ) "
shows "pc \<sigma>'  syst  = RecIdle  \<longrightarrow> ( lastVal glb (\<tau> \<sigma>')  \<ge>recoveredGlb \<sigma>' ) "
 using assms
  apply (simp add:TML_Commit_def Commit_inv_def total_wfs_def   )
  apply (cases "pc \<sigma> t"; simp )
  apply (metis pc_aux)
  apply (metis lastVal_def sf_nlv_ni)
  by (metis le_SucI st_lastVal_lc)



(*5*)
lemma read_recidl_lvglb_ge_recglb:
 assumes "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
  and "Read_inv t  ((pc \<sigma>) t) \<sigma>" 
  and "TML_Read  t   \<sigma> \<sigma>'"
 and " t \<noteq> syst "
 and "pc \<sigma>  syst  = RecIdle  \<longrightarrow> ( lastVal glb (\<tau> \<sigma>)  \<ge>recoveredGlb \<sigma> ) "
shows "pc \<sigma>'  syst  = RecIdle  \<longrightarrow> ( lastVal glb (\<tau> \<sigma>')  \<ge>recoveredGlb \<sigma>' ) "
  using assms
  apply (unfold  total_wfs_def)
  apply (simp add: TML_Read_def Read_inv_def   )
  apply (cases "pc \<sigma> t";  simp add: split if_splits)
  apply (metis assms(2) lastVal_ni)

      apply  ( simp add: split: if_split_asm)
     apply (case_tac " regs (\<tau> \<sigma>') t c1 =  0  ")
  apply simp
  apply (metis assms(2) cas_fail_lastVal_same)
  apply simp
     apply (subgoal_tac  "  regs (\<tau> \<sigma>) t DTML.loc =  lastVal glb (\<tau> \<sigma>') ") 
      prefer 2
  apply (metis cas_lc lastVal_def zero_less_iff_neq_zero)

  apply (subgoal_tac  "  regs (\<tau> \<sigma>) t DTML.loc =  lastVal glb (\<tau> \<sigma>) ") 
      prefer 2
      apply (metis cas_fail_diff_lv gr_implies_not_zero)
     apply (case_tac "pc \<sigma>  syst  = RecIdle  ")
  apply metis
  apply blast
  apply (metis assms(2) lastVal_ni)
  by metis


(*6*)
lemma crash_recidl_lvglb_ge_recglb:
assumes  "thrdsvars"
and "TML_Crash  \<sigma> \<sigma>'"
 and "pc \<sigma>  syst  = RecIdle  \<longrightarrow> ( lastVal glb (\<tau> \<sigma>)  \<ge>recoveredGlb \<sigma> ) "
shows "pc \<sigma>'  syst  = RecIdle  \<longrightarrow> ( lastVal glb (\<tau> \<sigma>')  \<ge>recoveredGlb \<sigma>' ) "
  using assms
  by (simp add: TML_Crash_def  total_wfs_def )





lemma beginInv_recidl_lvglb_ge_recglb:
assumes  "thrdsvars"
and "TML_Begin_invocation t  \<sigma> \<sigma>'"
  and " Begin_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
 and "pc \<sigma>  syst  = RecIdle  \<longrightarrow> ( lastVal glb (\<tau> \<sigma>)  \<ge>recoveredGlb \<sigma> ) "
shows "pc \<sigma>'  syst  = RecIdle  \<longrightarrow> ( lastVal glb (\<tau> \<sigma>')  \<ge>recoveredGlb \<sigma>' ) "
  using assms
  apply (simp add: TML_Begin_invocation_def Begin_invocation_inv_def total_wfs_def )
  by (cases "pc \<sigma> t";  simp )



lemma beginResp_recidl_lvglb_ge_recglb:
assumes  "thrdsvars"
and "TML_Begin_response t  \<sigma> \<sigma>'"
 and "pc \<sigma>  syst  = RecIdle  \<longrightarrow> ( lastVal glb (\<tau> \<sigma>)  \<ge>recoveredGlb \<sigma> ) "
shows "pc \<sigma>'  syst  = RecIdle  \<longrightarrow> ( lastVal glb (\<tau> \<sigma>')  \<ge>recoveredGlb \<sigma>' ) "
  using assms
  apply (simp add: TML_Begin_response_def total_wfs_def )
  by (cases "pc \<sigma> t";  simp)


lemma readInv_recidl_lvglb_ge_recglb:
assumes  "thrdsvars"
and "TML_Read_invocation t  \<sigma> \<sigma>'"
  and " Begin_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
 and "pc \<sigma>  syst  = RecIdle  \<longrightarrow> ( lastVal glb (\<tau> \<sigma>)  \<ge>recoveredGlb \<sigma> ) "
shows "pc \<sigma>'  syst  = RecIdle  \<longrightarrow> ( lastVal glb (\<tau> \<sigma>')  \<ge>recoveredGlb \<sigma>' ) "
  using assms
  apply (simp add: TML_Read_invocation_def Begin_invocation_inv_def total_wfs_def )
 by  (cases "pc \<sigma> t";  simp )



lemma readResp_recidl_lvglb_ge_recglb:
assumes  "thrdsvars"
and "TML_Read_response t  \<sigma> \<sigma>'"
 and "pc \<sigma>  syst  = RecIdle  \<longrightarrow> ( lastVal glb (\<tau> \<sigma>)  \<ge>recoveredGlb \<sigma> ) "
shows "pc \<sigma>'  syst  = RecIdle  \<longrightarrow> ( lastVal glb (\<tau> \<sigma>')  \<ge>recoveredGlb \<sigma>' ) "
  using assms
  apply (simp add: TML_Read_response_def total_wfs_def )
  by (cases "pc \<sigma> t";  simp)


lemma writeInv_recidl_lvglb_ge_recglb:
assumes  "thrdsvars"
and "TML_Write_invocation t  \<sigma> \<sigma>'"
  and " Write_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
 and "pc \<sigma>  syst  = RecIdle  \<longrightarrow> ( lastVal glb (\<tau> \<sigma>)  \<ge>recoveredGlb \<sigma> ) "
shows "pc \<sigma>'  syst  = RecIdle  \<longrightarrow> ( lastVal glb (\<tau> \<sigma>')  \<ge>recoveredGlb \<sigma>' ) "
  using assms
  apply (simp add: TML_Write_invocation_def  total_wfs_def )
  by (cases "pc \<sigma> t";  simp )





lemma writeResp_recidl_lvglb_ge_recglb:
assumes  "thrdsvars"
and "TML_Write_response t  \<sigma> \<sigma>'"
 and "pc \<sigma>  syst  = RecIdle  \<longrightarrow> ( lastVal glb (\<tau> \<sigma>)  \<ge>recoveredGlb \<sigma> ) "
shows "pc \<sigma>'  syst  = RecIdle  \<longrightarrow> ( lastVal glb (\<tau> \<sigma>')  \<ge>recoveredGlb \<sigma>' ) "
  using assms
  apply (simp add: TML_Write_response_def total_wfs_def )
  by (cases "pc \<sigma> t";  simp)




lemma commitInv_recidl_lvglb_ge_recglb:
assumes  "thrdsvars"
and "TML_Commit_invocation t  \<sigma> \<sigma>'"
  and " Commit_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
 and "pc \<sigma>  syst  = RecIdle  \<longrightarrow> ( lastVal glb (\<tau> \<sigma>)  \<ge>recoveredGlb \<sigma> ) "
shows "pc \<sigma>'  syst  = RecIdle  \<longrightarrow> ( lastVal glb (\<tau> \<sigma>')  \<ge>recoveredGlb \<sigma>' ) "
  using assms
  apply (simp add: TML_Commit_invocation_def  total_wfs_def )
  by (cases "pc \<sigma> t";  simp )




lemma commitResp_recidl_lvglb_ge_recglb:
assumes  "thrdsvars"
and "TML_Commit_response t  \<sigma> \<sigma>'"
 and "pc \<sigma>  syst  = RecIdle  \<longrightarrow> ( lastVal glb (\<tau> \<sigma>)  \<ge>recoveredGlb \<sigma> ) "
shows "pc \<sigma>'  syst  = RecIdle  \<longrightarrow> ( lastVal glb (\<tau> \<sigma>')  \<ge>recoveredGlb \<sigma>' ) "
  using assms
  apply (simp add: TML_Commit_response_def total_wfs_def )
  by (cases "pc \<sigma> t";  simp)











(****************************************************************************************)
(*1*)
lemma  read_loc_le_gl:
   assumes "thrdsvars"
   and "total_wfs (\<tau> \<sigma>)"
   and "TML_Read  t   \<sigma> \<sigma>'"
    and "((pc \<sigma>) t) \<in> reading \<union>{ReadPending, ReadResponding} \<union> {Aborted} "
      and "Read_inv t  ((pc \<sigma>) t) \<sigma>" 
and "pc \<sigma> syst = RecIdle"
and  " pc \<sigma>  syst  = RecIdle \<longrightarrow> (\<forall>t.  ((t \<noteq> syst  \<and> ((pc \<sigma>) t \<noteq>PC.NotStarted \<and>(pc \<sigma>) t \<noteq>PC.BeginPending \<and> (pc \<sigma>) t \<noteq>PC.Begin2  \<and> (pc \<sigma>) t \<noteq>PC.Committed  \<and>(pc \<sigma>) t \<noteq>PC.Aborted  )) \<longrightarrow>   regs (\<tau> \<sigma>) t loc \<le> lastVal glb  (\<tau> \<sigma>) ))"
and " t \<noteq> syst "
(* and "pc \<sigma>  syst  = RecIdle  \<longrightarrow> ( lastVal glb (\<tau> \<sigma>)  \<ge>recoveredGlb \<sigma> ) "*)
shows  "pc \<sigma>'  syst  = RecIdle \<longrightarrow> (\<forall>t.  ((t \<noteq> syst  \<and> ((pc \<sigma>') t \<noteq>PC.NotStarted\<and>(pc \<sigma>') t \<noteq>PC.BeginPending \<and> (pc \<sigma>') t \<noteq>PC.Begin2) \<and> (pc \<sigma>') t \<noteq>PC.Committed  \<and>(pc \<sigma>') t \<noteq>PC.Aborted  ) \<longrightarrow>   regs (\<tau> \<sigma>') t loc \<le> lastVal glb  (\<tau> \<sigma>') ))"
  using assms
apply (unfold  total_wfs_def )
  apply (simp add:TML_Read_def )
  apply (cases "pc \<sigma> t";   simp add: split if_splits)

      apply (metis PC.distinct(101) PC.distinct(177) PC.distinct(23) PC.distinct(713) PC.distinct(883) assms(2) lastVal_ni reg_same_ld_dt)

  apply (smt (z3) PC.distinct(103) PC.distinct(179) PC.distinct(25) PC.distinct(715) PC.distinct(937) pc_aux)  



     apply (case_tac "regs (\<tau> \<sigma>') t c1 = Suc 0")
  apply (subgoal_tac" regs (\<tau> \<sigma>') t loc =lastVal glb  (\<tau> \<sigma>') ")
       prefer 2
       apply (metis cas_lc lastVal_def numeral_1_eq_Suc_0 numeral_eq_one_iff reg_same_CAS_dr zero_neq_one)
      apply (subgoal_tac " lastVal glb (\<tau> \<sigma>') = lastVal glb (\<tau> \<sigma>) ")
  prefer 2
      apply (metis cas_fail_diff_lv cas_lc lastVal_def numeral_1_eq_Suc_0 numeral_eq_one_iff zero_neq_one)
   apply (metis fun_upd_other le_eq_less_or_eq reg_same_CAS_dt)


    apply (case_tac "((pc \<sigma>) t \<noteq>PC.NotStarted \<and> (pc \<sigma>) t \<noteq>PC.Begin2) \<and> (pc \<sigma>) t \<noteq>PC.BeginPending \<and> (pc \<sigma>) t \<noteq>PC.Committed  \<and> (pc \<sigma>) t \<noteq>PC.Aborted ")
  apply (metis (no_types, lifting) One_nat_def assms(2) cas_fail_lastVal_same cas_sv_lc fun_upd_def reg_same_CAS_dt)

    apply simp
  apply (metis PC.distinct(1039) PC.distinct(107) PC.distinct(183) PC.distinct(29) PC.distinct(719) assms(2) lastVal_ni reg_same_ld_dt)
  by (smt(z3) PC.distinct(1087) PC.distinct(109) PC.distinct(185) PC.distinct(31) PC.distinct(721) pc_aux)





(*2*)
lemma write_loc_le_gl:
  assumes "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
  and " Write_inv  t  ((pc \<sigma>) t) \<sigma> "
 and "TML_Write  t   \<sigma> \<sigma>'"
    and "((pc \<sigma>) t) \<in> writing  \<union>{WritePending,WriteResponding} \<union> {Aborted} "
and " t \<noteq> syst "
 (*and "pc \<sigma>  syst  = RecIdle  \<longrightarrow> ( lastVal glb (\<tau> \<sigma>)  \<ge>recoveredGlb \<sigma> ) "*)
and  " pc \<sigma>  syst  = RecIdle \<longrightarrow> (\<forall>t.  ((t \<noteq> syst  \<and> ((pc \<sigma>) t \<noteq>PC.NotStarted \<and>(pc \<sigma>) t \<noteq>PC.BeginPending \<and> (pc \<sigma>) t \<noteq>PC.Begin2)\<and> (pc \<sigma>) t \<noteq>PC.Committed  \<and>(pc \<sigma>) t \<noteq>PC.Aborted     ) \<longrightarrow>   regs (\<tau> \<sigma>) t loc \<le> lastVal glb  (\<tau> \<sigma>) ))"

shows  "pc \<sigma>'  syst  = RecIdle \<longrightarrow> (\<forall>t.  ((t \<noteq> syst  \<and> ((pc \<sigma>') t \<noteq>PC.NotStarted\<and>(pc \<sigma>') t \<noteq>PC.BeginPending \<and> (pc \<sigma>') t \<noteq>PC.Begin2) \<and>  (pc \<sigma>') t \<noteq>PC.Committed   \<and>(pc \<sigma>') t \<noteq>PC.Aborted   ) \<longrightarrow>   regs (\<tau> \<sigma>') t loc \<le> lastVal glb  (\<tau> \<sigma>') ))"

  using assms
 apply (simp add:TML_Write_def Write_inv_def total_wfs_def )
  apply (cases "pc \<sigma> t";   simp add: split if_splits)


  apply (smt (verit) PC.distinct(115) PC.distinct(1219) PC.distinct(191) PC.distinct(37) PC.distinct(727) pc_aux)


 apply (case_tac "regs (\<tau> \<sigma>') t c1 = Suc 0")
  apply (subgoal_tac" Suc (regs (\<tau> \<sigma>') t DTML.loc)  =lastVal glb  (\<tau> \<sigma>') ")
       prefer 2
          apply (metis cas_lc lastVal_def numeral_1_eq_Suc_0 numeral_eq_one_iff reg_same_CAS_dr zero_less_one)
  apply (subgoal_tac " \<forall>t\<noteq>syst. regs (\<tau> \<sigma>') t DTML.loc =  regs (\<tau> \<sigma>) t DTML.loc")
  prefer 2
          apply (metis Suc_inject cas_lc lastVal_def numeral_1_eq_Suc_0 numeral_eq_one_iff reg_same_CAS_dt zero_less_one)
        apply simp
         apply (metis cas_fail_diff_lv le_SucI nat.discI)
 apply (subgoal_tac "memory (\<tau> \<sigma>') =  memory (\<tau> \<sigma>) ")
  prefer 2
  apply (metis cas_fail_mem_same cas_lc neq0_conv numeral_1_eq_Suc_0 numerals(1))
  apply (subgoal_tac "   regs (\<tau> \<sigma>') t c1 = 0 ")
         prefer 2
  apply (metis cas_lc neq0_conv numeral_1_eq_Suc_0 numerals(1))
       apply simp
  using  reg_same_CAS_dr reg_same_CAS_dt 
  apply (metis PC.distinct(117) PC.distinct(193) PC.distinct(39) PC.distinct(729) assms(2) cas_fail_lastVal_same)
  apply (metis nat_le_linear reg_dt_ni reg_write_lastVal_ni reg_write_lc)
      apply (metis fun_upd_other le_eq_less_or_eq)
    apply (metis assms(2) lastVal_ni less_or_eq_imp_le reg_same_ld_dt)
  apply (metis assms(2) nat_le_linear reg_same_st st_lv__daddr_ni)
  by (metis assms(2) flo_lastVal_ni le_refl reg_same_flo)





lemma OV_monotone:
  assumes "mem_structured ts"
and "vbounded ts"
 and "  \<forall> ti l. last_entry ts l \<in>   OTS ts ti l "
 and " \<forall> ti l.  lastVal  l ts  \<in>  [l]\<^sub>ti ts"
and"   glb_monotone_complete_inv ts "
and " local2   \<in>  [glb]\<^sub>t ts "
shows "local2 \<le>  lastVal glb  ts "
 using assms
  apply (simp add:  glb_monotone_complete_inv_def )
 apply (subgoal_tac " \<forall> i. i \<in>  OTS ts t glb   \<longrightarrow>  i \<le>  last_entry ts glb ")
   prefer 2
   apply (subgoal_tac " \<forall> i. i \<in>  OTS ts t glb    \<longrightarrow>  i \<in> last_entry_set ts glb ")
    prefer 2
   apply (simp add: last_entry_set_def)
    apply (simp(no_asm) add: OTS_def OTSF_def)
   apply (subgoal_tac "\<forall>i. i  \<in> last_entry_set ts glb   \<longrightarrow> i \<le>  last_entry ts glb  ")
    prefer 2
   apply (simp add: last_entry_def)
  using  finite_last_entry_set  apply (metis Max_ge)
  apply blast
 apply (subgoal_tac " \<exists> j. j \<in>  OTS ts t glb   \<and> valOf j  glb ts = local2 ")
   prefer 2
apply(simp add: valOf_def)
   apply (simp add: mapval_def)
   apply blast
  apply (subgoal_tac "  \<forall>i. (i \<in> OTS ts t glb  )  \<longrightarrow>  valOf i  glb ts \<le> lastVal glb  ts")
   prefer 2
  apply (metis assms(5) aux comploc_ots glb_monotone_complete_inv_def lastVal_def order_class.order_eq_iff order_le_less valOf_def)
  by metis

(*3*)
lemma begin_loc_le_gl:
  assumes "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
  and "TML_Begin  t   \<sigma> \<sigma>'"
    and "((pc \<sigma>) t) \<in> beginning  \<union>{BeginPending,BeginResponding} \<union> {Aborted} "
and "  (  compval (\<tau> \<sigma>) (memory (\<tau> \<sigma>) ! 0) glb = survived_val (\<tau> \<sigma>) glb  \<and> (pc \<sigma> syst = RecIdle  \<longrightarrow>survived_val (\<tau> \<sigma>) glb   \<le>   recoveredGlb \<sigma>  )) "
and "   glb_monotone_complete_inv  (\<tau> \<sigma>) "
(* and "pc \<sigma>  syst  = RecIdle  \<longrightarrow> ( lastVal glb (\<tau> \<sigma>)  \<ge>recoveredGlb \<sigma> ) "*)
and  " pc \<sigma>  syst  = RecIdle \<longrightarrow> (\<forall>t.  ((t \<noteq> syst  \<and> ((pc \<sigma>) t \<noteq>PC.NotStarted \<and>(pc \<sigma>) t \<noteq>PC.BeginPending \<and> (pc \<sigma>) t \<noteq>PC.Begin2   \<and> (pc \<sigma>) t \<noteq>PC.Committed   \<and>(pc \<sigma>) t \<noteq>PC.Aborted   )) \<longrightarrow>   regs (\<tau> \<sigma>) t loc \<le> lastVal glb  (\<tau> \<sigma>) ))"
shows  "pc \<sigma>'  syst  = RecIdle \<longrightarrow> (\<forall>t.  ((t \<noteq> syst  \<and> ((pc \<sigma>') t \<noteq>PC.NotStarted\<and>(pc \<sigma>') t \<noteq>PC.BeginPending \<and> (pc \<sigma>') t \<noteq>PC.Begin2)  \<and> (pc \<sigma>') t \<noteq>PC.Committed   \<and>(pc \<sigma>') t \<noteq>PC.Aborted) \<longrightarrow>   regs (\<tau> \<sigma>') t loc \<le> lastVal glb  (\<tau> \<sigma>') ))"
  using assms
  apply (simp add:TML_Begin_def)
  apply (cases "pc \<sigma> t";  simp add: split if_splits )
   apply (unfold  total_wfs_def)
  apply (metis OV_monotone assms(2) lastVal_ni ld_ov_lc reg_same_ld_dr)
  apply (case_tac " even (regs (\<tau> \<sigma>) t DTML.loc) ")
  apply simp
by simp


(*
lemma begin_loc_le_gl_comp:
  assumes "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
  and "TML_Begin  t   \<sigma> \<sigma>'"
and "  (  compval (\<tau> \<sigma>) (memory (\<tau> \<sigma>) ! 0) glb = survived_val (\<tau> \<sigma>) glb  \<and> (pc \<sigma> syst = RecIdle  \<longrightarrow>survived_val (\<tau> \<sigma>) glb   \<le>   recoveredGlb \<sigma>  )) "
and "   glb_monotone_complete_inv  (\<tau> \<sigma>) "
(* and "pc \<sigma>  syst  = RecIdle  \<longrightarrow> ( lastVal glb (\<tau> \<sigma>)  \<ge>recoveredGlb \<sigma> ) "*)
 and  " pc \<sigma>  syst  = RecIdle \<longrightarrow> (\<forall>t.  (t \<noteq> syst  \<and> ((pc \<sigma>) t \<notin> {PC.NotStarted,PC.Aborted, PC.Committed,PC.Begin2   }) \<longrightarrow>   regs (\<tau> \<sigma>) t loc \<le> lastVal glb  (\<tau> \<sigma>) ))"
shows" pc \<sigma>' syst  = RecIdle \<longrightarrow> (\<forall>t.  (t \<noteq> syst  \<and> ((pc \<sigma>') t \<notin> {PC.NotStarted,PC.Aborted, PC.Committed,PC.Begin2   }) \<longrightarrow>   regs (\<tau> \<sigma>') t loc \<le> lastVal glb  (\<tau> \<sigma>') ))"

  using assms
  apply (case_tac  "((pc \<sigma>) t) \<in> {Ready,Aborted } \<union> beginning")
using  begin_loc_le_gl  [where \<sigma> = \<sigma> and \<sigma>' = \<sigma>' and t = t]  
  apply fastforce
  apply (case_tac  "((pc \<sigma>) t) \<notin> {Ready,Aborted } \<union> beginning")
  apply (subgoal_tac" \<sigma> = \<sigma>' ")
  prefer 2
 apply (simp add:TML_Begin_def )
  apply (cases "pc \<sigma> t";  simp )
  apply meson
  by linarith
*)



(*4*)
lemma commit_loc_le_gl:
  assumes "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
  and "  Commit_inv  t   ((pc \<sigma>) t) \<sigma>  "
  and "TML_Commit  t   \<sigma> \<sigma>'"
    and "((pc \<sigma>) t) \<in> committing  \<union>{CommitPending,Committed} \<union> {Aborted} "
and "  (  compval (\<tau> \<sigma>) (memory (\<tau> \<sigma>) ! 0) glb = survived_val (\<tau> \<sigma>) glb  \<and> (pc \<sigma> syst = RecIdle  \<longrightarrow>survived_val (\<tau> \<sigma>) glb   \<le>   recoveredGlb \<sigma>  )) "
and "   glb_monotone_inv  (\<tau> \<sigma>) "
 (*and "pc \<sigma>  syst  = RecIdle  \<longrightarrow> ( lastVal glb (\<tau> \<sigma>)  \<ge>recoveredGlb \<sigma> ) "*)
and  " pc \<sigma>  syst  = RecIdle \<longrightarrow> (\<forall>t.  ((t \<noteq> syst  \<and> ((pc \<sigma>) t \<noteq>PC.NotStarted \<and>(pc \<sigma>) t \<noteq>PC.BeginPending \<and> (pc \<sigma>) t \<noteq>PC.Begin2)  \<and> (pc \<sigma>) t \<noteq>PC.Committed  \<and>(pc \<sigma>) t \<noteq>PC.Aborted  ) \<longrightarrow>   regs (\<tau> \<sigma>) t loc \<le> lastVal glb  (\<tau> \<sigma>) ))"
shows  "pc \<sigma>'  syst  = RecIdle \<longrightarrow> (\<forall>t.  ((  t \<noteq> syst  \<and> ((pc \<sigma>') t \<noteq>PC.NotStarted\<and>(pc \<sigma>') t \<noteq>PC.BeginPending \<and> (pc \<sigma>') t \<noteq>PC.Begin2) \<and> (pc \<sigma>') t \<noteq>PC.Committed \<and>(pc \<sigma>') t \<noteq>PC.Aborted  ) \<longrightarrow>   regs (\<tau> \<sigma>') t loc \<le> lastVal glb  (\<tau> \<sigma>') ))"

  using assms
  apply (unfold  total_wfs_def )
  apply (simp add:TML_Commit_def Commit_inv_def  )
  apply (cases "pc \<sigma> t";simp   )
   apply (simp split:if_splits )
  apply (smt (verit) lastVal_def le_refl reg_same_sfence sf_nlv_ni)
  by (metis le_SucI less_or_eq_imp_le reg_same_st st_lastVal_lc)



(*5*)
lemma  crash_loc_le_gl:
assumes  "thrdsvars"
and "TML_Crash  \<sigma> \<sigma>'"
and  " pc \<sigma>  syst  = RecIdle \<longrightarrow> ( \<forall>t.  ((t \<noteq> syst  \<and> ((pc \<sigma>) t \<noteq>PC.NotStarted \<and>(pc \<sigma>) t \<noteq>PC.BeginPending \<and> (pc \<sigma>) t \<noteq>PC.Begin2) \<and> (pc \<sigma>) t \<noteq>PC.Committed   \<and>(pc \<sigma>) t \<noteq>PC.Aborted   ) \<longrightarrow>   regs (\<tau> \<sigma>) t loc \<le> lastVal glb  (\<tau> \<sigma>) ))"
shows  "pc \<sigma>'  syst  = RecIdle \<longrightarrow> (\<forall>t.  ((t \<noteq> syst  \<and> ((pc \<sigma>') t \<noteq>PC.NotStarted\<and>(pc \<sigma>') t \<noteq>PC.BeginPending \<and> (pc \<sigma>') t \<noteq>PC.Begin2) \<and> (pc \<sigma>') t \<noteq>PC.Committed \<and>(pc \<sigma>') t \<noteq>PC.Aborted  ) \<longrightarrow>   regs (\<tau> \<sigma>') t loc \<le> lastVal glb  (\<tau> \<sigma>') ))"
  using assms
  by(simp add: TML_Crash_def crash_step_def crash_trans_def compval_def)



(*6*)
lemma  recover_loc_le_gl:
 assumes "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
  and " TML_Recover syst   \<sigma> \<sigma>' "
 and "  Recover_inv  syst  ((pc \<sigma>) syst)  \<sigma>"
 and  " pc \<sigma>  syst  = RecIdle \<longrightarrow> (\<forall>t.  (t \<noteq> syst  \<and> ((pc \<sigma>) t \<notin> {PC.NotStarted,PC.Aborted,PC.BeginPending,PC.Begin2, PC.Committed    }) \<longrightarrow>   regs (\<tau> \<sigma>) t loc \<le> lastVal glb  (\<tau> \<sigma>) ))"
and " t \<noteq> syst "
(* and "pc \<sigma>  syst  = RecIdle  \<longrightarrow> ( lastVal glb (\<tau> \<sigma>)  \<ge>recoveredGlb \<sigma> ) "*)
and "  compval  (\<tau> \<sigma>)  (memory (\<tau> \<sigma>) !  0)        glb =   survived_val (\<tau> \<sigma>) glb  "
 and"   ( pc \<sigma>  syst  \<noteq>  RecIdle \<longrightarrow>   (\<forall> t \<noteq> syst.  (pc \<sigma> t) \<in>  { PC.NotStarted ,PC.Aborted, PC.Committed } )) "
shows  "pc \<sigma>'  syst  = RecIdle \<longrightarrow> (\<forall>t.  (t \<noteq> syst  \<and>   ((pc \<sigma>') t \<notin> {PC.NotStarted,PC.Aborted, PC.BeginPending,PC.Begin2, PC.Committed     }) \<longrightarrow>   regs (\<tau> \<sigma>') t loc \<le> lastVal glb  (\<tau> \<sigma>') ))"
  using assms
  apply (simp add:TML_Recover_def total_wfs_def Recover_inv_def )
  apply (cases "pc \<sigma> syst";  simp )
  apply ( simp add: split: if_splits)
  apply clarify
   apply simp
  apply blast
  apply metis
  by (metis pc_aux)



lemma beginInv_loc_le_gl:
assumes  "thrdsvars"
and "TML_Begin_invocation t  \<sigma> \<sigma>'"
  and " Begin_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
and  " pc \<sigma>  syst  = RecIdle \<longrightarrow> ( \<forall>t.  ((t \<noteq> syst  \<and> ((pc \<sigma>) t \<noteq>PC.NotStarted \<and>(pc \<sigma>) t \<noteq>PC.BeginPending \<and> (pc \<sigma>) t \<noteq>PC.Begin2) \<and> (pc \<sigma>) t \<noteq>PC.Committed  \<and>(pc \<sigma>) t \<noteq>PC.Aborted     ) \<longrightarrow>   regs (\<tau> \<sigma>) t loc \<le> lastVal glb  (\<tau> \<sigma>) ))"
shows  "pc \<sigma>'  syst  = RecIdle \<longrightarrow> (\<forall>t.  ((t \<noteq> syst  \<and> ((pc \<sigma>') t \<noteq>PC.NotStarted\<and>(pc \<sigma>') t \<noteq>PC.BeginPending \<and> (pc \<sigma>') t \<noteq>PC.Begin2) \<and> (pc \<sigma>') t \<noteq>PC.Committed  \<and>(pc \<sigma>') t \<noteq>PC.Aborted   ) \<longrightarrow>   regs (\<tau> \<sigma>') t loc \<le> lastVal glb  (\<tau> \<sigma>') ))"
  using assms
  apply (simp add: TML_Begin_invocation_def Begin_invocation_inv_def total_wfs_def )
  by (cases "pc \<sigma> t";  simp )



lemma beginResp_loc_le_gl:
assumes  "thrdsvars"
and "TML_Begin_response t  \<sigma> \<sigma>'"
and  " pc \<sigma>  syst  = RecIdle \<longrightarrow> ( \<forall>t.  ((t \<noteq> syst  \<and> ((pc \<sigma>) t \<noteq>PC.NotStarted \<and>(pc \<sigma>) t \<noteq>PC.BeginPending \<and> (pc \<sigma>) t \<noteq>PC.Begin2) \<and> (pc \<sigma>) t \<noteq>PC.Committed  \<and>(pc \<sigma>) t \<noteq>PC.Aborted     ) \<longrightarrow>   regs (\<tau> \<sigma>) t loc \<le> lastVal glb  (\<tau> \<sigma>) ))"
shows  "pc \<sigma>'  syst  = RecIdle \<longrightarrow> (\<forall>t.  ((t \<noteq> syst  \<and> ((pc \<sigma>') t \<noteq>PC.NotStarted\<and>(pc \<sigma>') t \<noteq>PC.BeginPending \<and> (pc \<sigma>') t \<noteq>PC.Begin2) \<and> (pc \<sigma>') t \<noteq>PC.Committed  \<and>(pc \<sigma>') t \<noteq>PC.Aborted  ) \<longrightarrow>   regs (\<tau> \<sigma>') t loc \<le> lastVal glb  (\<tau> \<sigma>') ))"
  using assms
  apply (simp add: TML_Begin_response_def total_wfs_def )
  by (cases "pc \<sigma> t";  simp)


lemma readInv_loc_le_gl:
assumes  "thrdsvars"
and "TML_Read_invocation t  \<sigma> \<sigma>'"
  and " Begin_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
and  " pc \<sigma>  syst  = RecIdle \<longrightarrow> ( \<forall>t.  ((t \<noteq> syst  \<and> ((pc \<sigma>) t \<noteq>PC.NotStarted \<and>(pc \<sigma>) t \<noteq>PC.BeginPending \<and> (pc \<sigma>) t \<noteq>PC.Begin2) \<and> (pc \<sigma>) t \<noteq>PC.Committed  \<and>(pc \<sigma>) t \<noteq>PC.Aborted     ) \<longrightarrow>   regs (\<tau> \<sigma>) t loc \<le> lastVal glb  (\<tau> \<sigma>) ))"
shows  "pc \<sigma>'  syst  = RecIdle \<longrightarrow> (\<forall>t.  ((t \<noteq> syst  \<and> ((pc \<sigma>') t \<noteq>PC.NotStarted\<and>(pc \<sigma>') t \<noteq>PC.BeginPending \<and> (pc \<sigma>') t \<noteq>PC.Begin2) \<and> (pc \<sigma>') t \<noteq>PC.Committed \<and>(pc \<sigma>') t \<noteq>PC.Aborted   ) \<longrightarrow>   regs (\<tau> \<sigma>') t loc \<le> lastVal glb  (\<tau> \<sigma>') ))"
  using assms
  apply (simp add: TML_Read_invocation_def Begin_invocation_inv_def total_wfs_def )
 by  (cases "pc \<sigma> t";  simp )



lemma readResp_loc_le_gl:
assumes  "thrdsvars"
and "TML_Read_response t  \<sigma> \<sigma>'"
and  " pc \<sigma>  syst  = RecIdle \<longrightarrow> ( \<forall>t.  ((t \<noteq> syst  \<and> ((pc \<sigma>) t \<noteq>PC.NotStarted \<and>(pc \<sigma>) t \<noteq>PC.BeginPending \<and> (pc \<sigma>) t \<noteq>PC.Begin2) \<and> (pc \<sigma>) t \<noteq>PC.Committed   \<and>(pc \<sigma>) t \<noteq>PC.Aborted    ) \<longrightarrow>   regs (\<tau> \<sigma>) t loc \<le> lastVal glb  (\<tau> \<sigma>) ))"
shows  "pc \<sigma>'  syst  = RecIdle \<longrightarrow> (\<forall>t.  ((t \<noteq> syst  \<and> ((pc \<sigma>') t \<noteq>PC.NotStarted\<and>(pc \<sigma>') t \<noteq>PC.BeginPending \<and> (pc \<sigma>') t \<noteq>PC.Begin2) \<and> (pc \<sigma>') t \<noteq>PC.Committed \<and>(pc \<sigma>') t \<noteq>PC.Aborted   ) \<longrightarrow>   regs (\<tau> \<sigma>') t loc \<le> lastVal glb  (\<tau> \<sigma>') ))"
  using assms
  apply (simp add: TML_Read_response_def total_wfs_def )
  by (cases "pc \<sigma> t";  simp)


lemma writeInv_loc_le_gl:
assumes  "thrdsvars"
and "TML_Write_invocation t  \<sigma> \<sigma>'"
  and " Write_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
and  " pc \<sigma>  syst  = RecIdle \<longrightarrow> ( \<forall>t.  ((t \<noteq> syst  \<and> ((pc \<sigma>) t \<noteq>PC.NotStarted \<and>(pc \<sigma>) t \<noteq>PC.BeginPending \<and> (pc \<sigma>) t \<noteq>PC.Begin2) \<and> (pc \<sigma>) t \<noteq>PC.Committed  \<and>(pc \<sigma>) t \<noteq>PC.Aborted     ) \<longrightarrow>   regs (\<tau> \<sigma>) t loc \<le> lastVal glb  (\<tau> \<sigma>) ))"
shows  "pc \<sigma>'  syst  = RecIdle \<longrightarrow> (\<forall>t.  ((t \<noteq> syst  \<and> ((pc \<sigma>') t \<noteq>PC.NotStarted\<and>(pc \<sigma>') t \<noteq>PC.BeginPending \<and> (pc \<sigma>') t \<noteq>PC.Begin2) \<and> (pc \<sigma>') t \<noteq>PC.Committed \<and>(pc \<sigma>') t \<noteq>PC.Aborted   ) \<longrightarrow>   regs (\<tau> \<sigma>') t loc \<le> lastVal glb  (\<tau> \<sigma>') ))"
  using assms
  apply (simp add: TML_Write_invocation_def  total_wfs_def )
  by (cases "pc \<sigma> t";  simp )





lemma writeResp_loc_le_gl:
assumes  "thrdsvars"
and "TML_Write_response t  \<sigma> \<sigma>'"
and  " pc \<sigma>  syst  = RecIdle \<longrightarrow> ( \<forall>t.  ((t \<noteq> syst  \<and> ((pc \<sigma>) t \<noteq>PC.NotStarted \<and>(pc \<sigma>) t \<noteq>PC.BeginPending \<and> (pc \<sigma>) t \<noteq>PC.Begin2) \<and> (pc \<sigma>) t \<noteq>PC.Committed  \<and>(pc \<sigma>) t \<noteq>PC.Aborted     ) \<longrightarrow>   regs (\<tau> \<sigma>) t loc \<le> lastVal glb  (\<tau> \<sigma>) ))"
shows  "pc \<sigma>'  syst  = RecIdle \<longrightarrow> (\<forall>t.  ((t \<noteq> syst  \<and> ((pc \<sigma>') t \<noteq>PC.NotStarted\<and>(pc \<sigma>') t \<noteq>PC.BeginPending \<and> (pc \<sigma>') t \<noteq>PC.Begin2) \<and> (pc \<sigma>') t \<noteq>PC.Committed \<and>(pc \<sigma>') t \<noteq>PC.Aborted   ) \<longrightarrow>   regs (\<tau> \<sigma>') t loc \<le> lastVal glb  (\<tau> \<sigma>') ))"
  using assms
  apply (simp add: TML_Write_response_def total_wfs_def )
  by (cases "pc \<sigma> t";  simp)




lemma commitInv_loc_le_gl:
assumes  "thrdsvars"
and "TML_Commit_invocation t  \<sigma> \<sigma>'"
  and " Commit_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
and  " pc \<sigma>  syst  = RecIdle \<longrightarrow> ( \<forall>t.  ((t \<noteq> syst  \<and> ((pc \<sigma>) t \<noteq>PC.NotStarted \<and>(pc \<sigma>) t \<noteq>PC.BeginPending \<and> (pc \<sigma>) t \<noteq>PC.Begin2) \<and> (pc \<sigma>) t \<noteq>PC.Committed  \<and>(pc \<sigma>) t \<noteq>PC.Aborted     ) \<longrightarrow>   regs (\<tau> \<sigma>) t loc \<le> lastVal glb  (\<tau> \<sigma>) ))"
shows  "pc \<sigma>'  syst  = RecIdle \<longrightarrow> (\<forall>t.  ((t \<noteq> syst  \<and> ((pc \<sigma>') t \<noteq>PC.NotStarted\<and>(pc \<sigma>') t \<noteq>PC.BeginPending \<and> (pc \<sigma>') t \<noteq>PC.Begin2) \<and> (pc \<sigma>') t \<noteq>PC.Committed \<and>(pc \<sigma>') t \<noteq>PC.Aborted   ) \<longrightarrow>   regs (\<tau> \<sigma>') t loc \<le> lastVal glb  (\<tau> \<sigma>') ))"
  using assms
  apply (simp add: TML_Commit_invocation_def  total_wfs_def )
  by (cases "pc \<sigma> t";  simp )




lemma commitResp_loc_le_gl:
assumes  "thrdsvars"
and "TML_Commit_response t  \<sigma> \<sigma>'"
and  " pc \<sigma>  syst  = RecIdle \<longrightarrow> ( \<forall>t.  ((t \<noteq> syst  \<and> ((pc \<sigma>) t \<noteq>PC.NotStarted \<and>(pc \<sigma>) t \<noteq>PC.BeginPending \<and> (pc \<sigma>) t \<noteq>PC.Begin2) \<and> (pc \<sigma>) t \<noteq>PC.Committed  \<and>(pc \<sigma>) t \<noteq>PC.Aborted     ) \<longrightarrow>   regs (\<tau> \<sigma>) t loc \<le> lastVal glb  (\<tau> \<sigma>) ))"
shows  "pc \<sigma>'  syst  = RecIdle \<longrightarrow> (\<forall>t.  ((t \<noteq> syst  \<and> ((pc \<sigma>') t \<noteq>PC.NotStarted\<and>(pc \<sigma>') t \<noteq>PC.BeginPending \<and> (pc \<sigma>') t \<noteq>PC.Begin2) \<and> (pc \<sigma>') t \<noteq>PC.Committed \<and>(pc \<sigma>') t \<noteq>PC.Aborted   ) \<longrightarrow>   regs (\<tau> \<sigma>') t loc \<le> lastVal glb  (\<tau> \<sigma>') ))"
  using assms
  apply (simp add: TML_Commit_response_def total_wfs_def )
  by (cases "pc \<sigma> t";  simp)



(****************************************************************************)


(*1*)
lemma  read_loc_gt_rec:
   assumes "thrdsvars"
   and "total_wfs (\<tau> \<sigma>)"
   and "TML_Read  t   \<sigma> \<sigma>'"
    and "((pc \<sigma>) t) \<in> reading \<union>{ReadPending,ReadResponding  } \<union> {Aborted} "
      and "Read_inv t  ((pc \<sigma>) t) \<sigma>" 
and "pc \<sigma> syst = RecIdle"
and "\<forall>t.  (t \<noteq> syst  \<and> ((pc \<sigma>) t \<notin> {PC.NotStarted,PC.Aborted, PC.Committed, BeginPending })  \<and> (writeAux \<sigma> t \<or> readAux \<sigma> t )) \<longrightarrow>  ( regs (\<tau> \<sigma>) t loc \<ge>  recoveredGlb \<sigma> )" 
and " t \<noteq> syst "
 and "pc \<sigma>  syst  = RecIdle  \<longrightarrow> ( lastVal glb (\<tau> \<sigma>)  \<ge>recoveredGlb \<sigma> ) "
(*and "  (  \<forall> i   . pc \<sigma> syst = RecIdle  \<longrightarrow> (  0 <  i \<and>  i < length(memory (\<tau> \<sigma>)) \<and>  comploc (memory (\<tau> \<sigma>)!i) glb = glb  \<longrightarrow> compval (\<tau> \<sigma>) (memory (\<tau> \<sigma>) ! i) glb  \<ge>   recoveredGlb \<sigma>   ) )"
*)
shows  "\<forall> t.  (t \<noteq> syst  \<and> ((pc \<sigma>') t \<notin> {PC.NotStarted,PC.Aborted, PC.Committed, BeginPending}) \<and> (writeAux \<sigma>' t \<or> readAux \<sigma>' t )) \<longrightarrow>  ( regs (\<tau> \<sigma>') t loc \<ge>  recoveredGlb \<sigma>' )" 
  using assms
 using assms
apply (unfold  total_wfs_def )
  apply (simp add:TML_Read_def )
  apply (cases "pc \<sigma> t";   simp add: split if_splits)
  apply (metis PC.distinct(101) PC.distinct(23) PC.distinct(713) PC.distinct(883) reg_same_ld_dt)
     apply ( simp add: split: if_split_asm)
  apply (case_tac " regs (\<tau> \<sigma>') t c1 \<noteq> Suc 0")
  apply simp
     apply (metis reg_same_CAS_dt)
    apply simp
   apply (metis One_nat_def assms(2) cas_succ_eq reg_same_CAS_dr reg_same_CAS_dt)
  apply (metis PC.distinct(1039) PC.distinct(107) PC.distinct(29) PC.distinct(719) reg_same_ld_dt)
  by (metis (no_types, opaque_lifting) PC.distinct(1087) PC.distinct(109) PC.distinct(31) PC.distinct(721) pc_aux)








(*2*)

lemma  recover_loc_gt_rec:
 assumes "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
  and " TML_Recover syst   \<sigma> \<sigma>' "
 and "  Recover_inv  syst  ((pc \<sigma>) syst)  \<sigma>"
  and  " ((pc \<sigma>) syst) \<noteq> RecIdle   \<longrightarrow> (\<forall> t  \<noteq> syst.  ((pc \<sigma>) t)   \<in> {NotStarted, Aborted, Committed})"
and "\<forall>t.  (t \<noteq> syst  \<and> ((pc \<sigma>) t \<notin> {PC.NotStarted,PC.Aborted, PC.Committed, BeginPending })  \<and> (writeAux \<sigma> t \<or> readAux \<sigma> t )) \<longrightarrow>  ( regs (\<tau> \<sigma>) t loc \<ge>  recoveredGlb \<sigma> )" 
shows  "\<forall> t.  (t \<noteq> syst  \<and> ((pc \<sigma>') t \<notin> {PC.NotStarted,PC.Aborted, PC.Committed, BeginPending}) \<and> (writeAux \<sigma>' t \<or> readAux \<sigma>' t )) \<longrightarrow>  ( regs (\<tau> \<sigma>') t loc \<ge>  recoveredGlb \<sigma>' )" 
 using assms
  apply (simp add:TML_Recover_def total_wfs_def Recover_inv_def )
  apply (cases "pc \<sigma> syst";  simp )
  apply metis
  apply metis
        apply metis
       apply metis
      apply metis
     apply metis
    apply ( simp add: split: if_split_asm)
     apply metis
    apply metis
   apply metis
   apply metis
  apply (case_tac " log \<sigma> = Map.empty")
  apply simp
  apply metis
  by (metis pc_aux)




(*3*)
lemma  crash_loc_gt_rec:
assumes  "thrdsvars"
and "TML_Crash  \<sigma> \<sigma>'"
shows  "\<forall> t.  (t \<noteq> syst  \<and> ((pc \<sigma>') t \<notin> {PC.NotStarted,PC.Aborted, PC.Committed}) \<and> (writeAux \<sigma>' t \<or> readAux \<sigma>' t )) \<longrightarrow>  ( regs (\<tau> \<sigma>') t loc \<ge>  recoveredGlb \<sigma>' )" 
  using assms
  apply(simp add: TML_Crash_def crash_step_def crash_trans_def )
  by blast





(*4*)
lemma write_loc_gt_rec:
  assumes "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
  and " Write_inv  t  ((pc \<sigma>) t) \<sigma> "
 and "TML_Write  t   \<sigma> \<sigma>'"
  and " ((pc \<sigma>) t) \<in> {WritePending,WriteResponding, Aborted} \<union> writing "
and " a \<noteq> glb"
and " t \<noteq> syst "
 and "pc \<sigma>  syst  = RecIdle  \<longrightarrow> ( lastVal glb (\<tau> \<sigma>)  \<ge>recoveredGlb \<sigma> ) "
and "\<forall>t.  (t \<noteq> syst  \<and> ((pc \<sigma>) t \<notin> {PC.NotStarted,PC.Aborted, PC.Committed, BeginPending })  \<and> (writeAux \<sigma> t \<or> readAux \<sigma> t )) \<longrightarrow>  ( regs (\<tau> \<sigma>) t loc \<ge>  recoveredGlb \<sigma> )" 
shows  "\<forall> t.  (t \<noteq> syst  \<and> ((pc \<sigma>') t \<notin> {PC.NotStarted,PC.Aborted, PC.Committed, BeginPending}) \<and> (writeAux \<sigma>' t \<or> readAux \<sigma>' t )) \<longrightarrow>  ( regs (\<tau> \<sigma>') t loc \<ge>  recoveredGlb \<sigma>' )" 

  using assms
 apply (simp add:TML_Write_def Write_inv_def total_wfs_def )
  apply (cases "pc \<sigma> t";   simp add: split if_splits)

  apply (metis (no_types, lifting) PC.distinct(115) PC.distinct(1219) PC.distinct(37) PC.distinct(727) pc_aux)
         apply (subgoal_tac "\<forall>t.  (regs (\<tau> \<sigma>') t DTML.loc)  = (regs (\<tau> \<sigma>) t DTML.loc)  ")
          prefer 2
  using  reg_same_CAS_dr
         apply (metis not_gr0 reg_same_CAS_dt)

        apply (case_tac " regs (\<tau> \<sigma>') t c1 = 0")
          apply simp
  apply simp

        apply (metis cas_fail_diff_lv less_numeral_extra(3))
  using reg_dt_ni reg_write_lc apply presburger
  apply (metis fun_upd_other)
  apply (metis reg_same_ld_dt)
  apply (metis reg_same_st)
  by (metis reg_same_flo)


(*5*)
lemma  commit_loc_gt_rec:
  assumes "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
  and "  Commit_inv  t   ((pc \<sigma>) t) \<sigma>  "
  and "TML_Commit  t   \<sigma> \<sigma>'"
  and " ((pc \<sigma>) t) \<in> {CommitPending,Committed,  Aborted} \<union> committing "
 and "pc \<sigma>  syst  = RecIdle  \<longrightarrow> ( lastVal glb (\<tau> \<sigma>)  \<ge>recoveredGlb \<sigma> ) "
and "\<forall>t.  (t \<noteq> syst  \<and> ((pc \<sigma>) t \<notin> {PC.NotStarted,PC.Aborted, PC.Committed, BeginPending })  \<and> (writeAux \<sigma> t \<or> readAux \<sigma> t )) \<longrightarrow>  ( regs (\<tau> \<sigma>) t loc \<ge>  recoveredGlb \<sigma> )" 
shows  "\<forall> t.  (t \<noteq> syst  \<and> ((pc \<sigma>') t \<notin> {PC.NotStarted,PC.Aborted, PC.Committed, BeginPending}) \<and> (writeAux \<sigma>' t \<or> readAux \<sigma>' t )) \<longrightarrow>  ( regs (\<tau> \<sigma>') t loc \<ge>  recoveredGlb \<sigma>' )" 
  using assms
  apply (unfold  total_wfs_def )
  apply (simp add:TML_Commit_def Commit_inv_def  )
  apply (cases "pc \<sigma> t";   simp)
  apply (metis (no_types, lifting) PC.distinct(389) PC.distinct(449) PC.distinct(87) PC.distinct(9) pc_aux)
  apply (metis reg_same_sfence)
  by (metis reg_same_st)




(*6*)
lemma  begin_loc_gt_rec:
  assumes "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
  and "  Begin_inv  t   ((pc \<sigma>) t) \<sigma>  "
  and "TML_Begin  t   \<sigma> \<sigma>'"
  and " ((pc \<sigma>) t) \<in> {BeginPending,BeginResponding, Aborted} \<union> beginning "
and "\<forall>t.  (t \<noteq> syst  \<and> ((pc \<sigma>) t \<notin> {PC.NotStarted,PC.Aborted, PC.Committed, BeginPending })  \<and> (writeAux \<sigma> t \<or> readAux \<sigma> t )) \<longrightarrow>  ( regs (\<tau> \<sigma>) t loc \<ge>  recoveredGlb \<sigma> )" 
shows  "\<forall> t.  (t \<noteq> syst  \<and> ((pc \<sigma>') t \<notin> {PC.NotStarted,PC.Aborted, PC.Committed, BeginPending}) \<and> (writeAux \<sigma>' t \<or> readAux \<sigma>' t )) \<longrightarrow>  ( regs (\<tau> \<sigma>') t loc \<ge>  recoveredGlb \<sigma>' )" 
  using assms
  apply (unfold  total_wfs_def )
  apply (simp add:TML_Begin_def Begin_inv_def  )
  apply (cases "pc \<sigma> t";   simp)
  apply (metis reg_same_ld_dr)
  by (metis (no_types, lifting) pc_aux)





lemma beginInv_loc_gt_rec:
assumes  "thrdsvars"
and "TML_Begin_invocation t  \<sigma> \<sigma>'"
  and " Begin_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
and "\<forall>t.  (t \<noteq> syst  \<and> ((pc \<sigma>) t \<notin> {PC.NotStarted,PC.Aborted, PC.Committed, BeginPending })  \<and> (writeAux \<sigma> t \<or> readAux \<sigma> t )) \<longrightarrow>  ( regs (\<tau> \<sigma>) t loc \<ge>  recoveredGlb \<sigma> )" 
shows  "\<forall> t.  (t \<noteq> syst  \<and> ((pc \<sigma>') t \<notin> {PC.NotStarted,PC.Aborted, PC.Committed, BeginPending}) \<and> (writeAux \<sigma>' t \<or> readAux \<sigma>' t )) \<longrightarrow>  ( regs (\<tau> \<sigma>') t loc \<ge>  recoveredGlb \<sigma>' )" 
  using assms
  apply (simp add: TML_Begin_invocation_def Begin_invocation_inv_def total_wfs_def )
  by (cases "pc \<sigma> t";  simp )



lemma beginResp_loc_gt_rec:
assumes  "thrdsvars"
and "TML_Begin_response t  \<sigma> \<sigma>'"
and "\<forall>t.  (t \<noteq> syst  \<and> ((pc \<sigma>) t \<notin> {PC.NotStarted,PC.Aborted, PC.Committed, BeginPending })  \<and> (writeAux \<sigma> t \<or> readAux \<sigma> t )) \<longrightarrow>  ( regs (\<tau> \<sigma>) t loc \<ge>  recoveredGlb \<sigma> )" 
shows  "\<forall> t.  (t \<noteq> syst  \<and> ((pc \<sigma>') t \<notin> {PC.NotStarted,PC.Aborted, PC.Committed, BeginPending}) \<and> (writeAux \<sigma>' t \<or> readAux \<sigma>' t )) \<longrightarrow>  ( regs (\<tau> \<sigma>') t loc \<ge>  recoveredGlb \<sigma>' )" 
  using assms
  apply (simp add: TML_Begin_response_def total_wfs_def )
  by (cases "pc \<sigma> t";  simp)


lemma readInv_loc_gt_rec:
assumes  "thrdsvars"
and "TML_Read_invocation t  \<sigma> \<sigma>'"
  and " Begin_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
and "\<forall>t.  (t \<noteq> syst  \<and> ((pc \<sigma>) t \<notin> {PC.NotStarted,PC.Aborted, PC.Committed, BeginPending })  \<and> (writeAux \<sigma> t \<or> readAux \<sigma> t )) \<longrightarrow>  ( regs (\<tau> \<sigma>) t loc \<ge>  recoveredGlb \<sigma> )" 
shows  "\<forall> t.  (t \<noteq> syst  \<and> ((pc \<sigma>') t \<notin> {PC.NotStarted,PC.Aborted, PC.Committed, BeginPending}) \<and> (writeAux \<sigma>' t \<or> readAux \<sigma>' t )) \<longrightarrow>  ( regs (\<tau> \<sigma>') t loc \<ge>  recoveredGlb \<sigma>' )" 
  using assms
  apply (simp add: TML_Read_invocation_def Begin_invocation_inv_def total_wfs_def )
 by  (cases "pc \<sigma> t";  simp )



lemma readResp_loc_gt_rec:
assumes  "thrdsvars"
and "TML_Read_response t  \<sigma> \<sigma>'"
and "\<forall>t.  (t \<noteq> syst  \<and> ((pc \<sigma>) t \<notin> {PC.NotStarted,PC.Aborted, PC.Committed, BeginPending })  \<and> (writeAux \<sigma> t \<or> readAux \<sigma> t )) \<longrightarrow>  ( regs (\<tau> \<sigma>) t loc \<ge>  recoveredGlb \<sigma> )" 
shows  "\<forall> t.  (t \<noteq> syst  \<and> ((pc \<sigma>') t \<notin> {PC.NotStarted,PC.Aborted, PC.Committed, BeginPending}) \<and> (writeAux \<sigma>' t \<or> readAux \<sigma>' t )) \<longrightarrow>  ( regs (\<tau> \<sigma>') t loc \<ge>  recoveredGlb \<sigma>' )" 
  using assms
  apply (simp add: TML_Read_response_def total_wfs_def )
  by (cases "pc \<sigma> t";  simp)


lemma writeInv_loc_gt_rec:
assumes  "thrdsvars"
and "TML_Write_invocation t  \<sigma> \<sigma>'"
  and " Write_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
and "\<forall>t.  (t \<noteq> syst  \<and> ((pc \<sigma>) t \<notin> {PC.NotStarted,PC.Aborted, PC.Committed, BeginPending })  \<and> (writeAux \<sigma> t \<or> readAux \<sigma> t )) \<longrightarrow>  ( regs (\<tau> \<sigma>) t loc \<ge>  recoveredGlb \<sigma> )" 
shows  "\<forall> t.  (t \<noteq> syst  \<and> ((pc \<sigma>') t \<notin> {PC.NotStarted,PC.Aborted, PC.Committed, BeginPending}) \<and> (writeAux \<sigma>' t \<or> readAux \<sigma>' t )) \<longrightarrow>  ( regs (\<tau> \<sigma>') t loc \<ge>  recoveredGlb \<sigma>' )" 
  using assms
  apply (simp add: TML_Write_invocation_def  total_wfs_def )
  by (cases "pc \<sigma> t";  simp )





lemma writeResp_loc_gt_rec:
assumes  "thrdsvars"
and "TML_Write_response t  \<sigma> \<sigma>'"
and "\<forall>t.  (t \<noteq> syst  \<and> ((pc \<sigma>) t \<notin> {PC.NotStarted,PC.Aborted, PC.Committed, BeginPending })  \<and> (writeAux \<sigma> t \<or> readAux \<sigma> t )) \<longrightarrow>  ( regs (\<tau> \<sigma>) t loc \<ge>  recoveredGlb \<sigma> )" 
shows  "\<forall> t.  (t \<noteq> syst  \<and> ((pc \<sigma>') t \<notin> {PC.NotStarted,PC.Aborted, PC.Committed, BeginPending}) \<and> (writeAux \<sigma>' t \<or> readAux \<sigma>' t )) \<longrightarrow>  ( regs (\<tau> \<sigma>') t loc \<ge>  recoveredGlb \<sigma>' )" 
  using assms
  apply (simp add: TML_Write_response_def total_wfs_def )
  by (cases "pc \<sigma> t";  simp)




lemma commitInv_loc_gt_rec:
assumes  "thrdsvars"
and "TML_Commit_invocation t  \<sigma> \<sigma>'"
  and " Commit_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
and "\<forall>t.  (t \<noteq> syst  \<and> ((pc \<sigma>) t \<notin> {PC.NotStarted,PC.Aborted, PC.Committed, BeginPending })  \<and> (writeAux \<sigma> t \<or> readAux \<sigma> t )) \<longrightarrow>  ( regs (\<tau> \<sigma>) t loc \<ge>  recoveredGlb \<sigma> )" 
shows  "\<forall> t.  (t \<noteq> syst  \<and> ((pc \<sigma>') t \<notin> {PC.NotStarted,PC.Aborted, PC.Committed, BeginPending}) \<and> (writeAux \<sigma>' t \<or> readAux \<sigma>' t )) \<longrightarrow>  ( regs (\<tau> \<sigma>') t loc \<ge>  recoveredGlb \<sigma>' )" 
  using assms
  apply (simp add: TML_Commit_invocation_def  total_wfs_def )
  by (cases "pc \<sigma> t";  simp )




lemma commitResp_loc_gt_rec:
assumes  "thrdsvars"
and "TML_Commit_response t  \<sigma> \<sigma>'"
and "\<forall>t.  (t \<noteq> syst  \<and> ((pc \<sigma>) t \<notin> {PC.NotStarted,PC.Aborted, PC.Committed, BeginPending })  \<and> (writeAux \<sigma> t \<or> readAux \<sigma> t )) \<longrightarrow>  ( regs (\<tau> \<sigma>) t loc \<ge>  recoveredGlb \<sigma> )" 
shows  "\<forall> t.  (t \<noteq> syst  \<and> ((pc \<sigma>') t \<notin> {PC.NotStarted,PC.Aborted, PC.Committed, BeginPending}) \<and> (writeAux \<sigma>' t \<or> readAux \<sigma>' t )) \<longrightarrow>  ( regs (\<tau> \<sigma>') t loc \<ge>  recoveredGlb \<sigma>' )" 
  using assms
  apply (simp add: TML_Commit_response_def total_wfs_def )
  by (cases "pc \<sigma> t";  simp)




(*****************************************************)
(*1*)
lemma  begin_wr_none_log_lv:
 assumes "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
  and "TML_Begin  t1   \<sigma> \<sigma>'"
and " ( (writer \<sigma> = None \<and>  ((pc \<sigma>) syst) = RecIdle)   \<longrightarrow> ( \<forall> a t. a \<in>  dom (log \<sigma>) \<longrightarrow> [a]\<^sup>A\<^sub>t (\<tau> \<sigma>) =  {lastVal a  (\<tau> \<sigma>)}) )  " 
and   " \<forall>  t.  ( writer \<sigma> = Some t \<longrightarrow> odd (lastVal glb  (\<tau> \<sigma>)) )"
and "  (\<forall>a. a \<in> dom (log \<sigma>) \<longrightarrow> a \<noteq> glb) "
shows " ( (writer \<sigma>' = None \<and>  ((pc \<sigma>') syst) = RecIdle)   \<longrightarrow> ( \<forall> a t. a \<in>  dom (log \<sigma>') \<longrightarrow> [a]\<^sup>A\<^sub>t (\<tau> \<sigma>') =  {lastVal a  (\<tau> \<sigma>')}) ) " 
  using assms
  apply (unfold total_wfs_def)
  apply (simp add: TML_Begin_def )
  apply (cases "pc \<sigma> t1";   simp add: split if_splits)
  apply (metis assms(2) lastVal_ni ld_oav_ni)
  by (metis fun_upd_other)




(*2*)
lemma  read_wr_none_log_lv:
 assumes "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
  and "TML_Read  t1   \<sigma> \<sigma>'"
and " ( (writer \<sigma> = None \<and>  ((pc \<sigma>) syst) = RecIdle)   \<longrightarrow> ( \<forall> a t. a \<in>  dom (log \<sigma>) \<longrightarrow> [a]\<^sup>A\<^sub>t (\<tau> \<sigma>) =  {lastVal a  (\<tau> \<sigma>)}) )  " 
and   " \<forall>  t.  ( writer \<sigma> = Some t \<longrightarrow> odd (lastVal glb  (\<tau> \<sigma>)) )"
 and "Read_inv t1  ((pc \<sigma>) t1) \<sigma>" 
and "  (\<forall>a. a \<in> dom (log \<sigma>) \<longrightarrow> a \<noteq> glb) "
shows " ( (writer \<sigma>' = None \<and>  ((pc \<sigma>') syst) = RecIdle)   \<longrightarrow> ( \<forall> a t. a \<in>  dom (log \<sigma>') \<longrightarrow> [a]\<^sup>A\<^sub>t (\<tau> \<sigma>') =  {lastVal a  (\<tau> \<sigma>')}) ) " 
  using assms
  apply (unfold total_wfs_def)
  apply (simp add: TML_Read_def Read_inv_def )
  apply (cases "pc \<sigma> t1";   simp add: split if_splits)
  apply (metis assms(2) lastVal_ni ld_oav_ni)
     apply metis
  apply (metis cas_le_daddr cas_oav_daddr_ni)
    apply (metis assms(2) lastVal_ni ld_oav_ni)
    by metis

(*3*)
lemma  write_wr_none_log_lv:
  assumes "thrdsvars"
      and "total_wfs (\<tau> \<sigma>)"
      and "TML_Write  t    \<sigma> \<sigma>'"
  and " Write_inv  t  ((pc \<sigma>) t) \<sigma> "
and " ( (writer \<sigma> = None \<and>  ((pc \<sigma>) syst) = RecIdle)   \<longrightarrow> ( \<forall> a t. a \<in>  dom (log \<sigma>) \<longrightarrow> [a]\<^sup>A\<^sub>t (\<tau> \<sigma>) =  {lastVal a  (\<tau> \<sigma>)}) )  " 
and "  (\<forall>a. a \<in> dom (log \<sigma>) \<longrightarrow> a \<noteq> glb) "
shows " ( (writer \<sigma>' = None \<and>  ((pc \<sigma>') syst) = RecIdle)   \<longrightarrow> ( \<forall> a t. a \<in>  dom (log \<sigma>') \<longrightarrow> [a]\<^sup>A\<^sub>t (\<tau> \<sigma>') =  {lastVal a  (\<tau> \<sigma>')}) ) " 
  using assms 
  apply (simp add:TML_Write_def Write_inv_def  total_wfs_def;  simp add: split if_splits )
  apply (cases "pc \<sigma> t";   simp  )
          apply  ( simp add: split: if_split_asm)
          apply  ( simp add: split: if_split_asm)
  using cas_le_daddr cas_oav_daddr_ni by presburger

(*4*)
lemma commit_wr_none_log_lv:
 assumes "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
  and "  Commit_inv  t   ((pc \<sigma>) t) \<sigma>  "
  and "TML_Commit  t   \<sigma> \<sigma>'"
and " ( (writer \<sigma> = None \<and>  ((pc \<sigma>) syst) = RecIdle)   \<longrightarrow> ( \<forall> a t. a \<in>  dom (log \<sigma>) \<longrightarrow> [a]\<^sup>A\<^sub>t (\<tau> \<sigma>) =  {lastVal a  (\<tau> \<sigma>)}) )  " 
and "  (\<forall>a. a \<in> dom (log \<sigma>) \<longrightarrow> a \<noteq> glb) "
shows " ( (writer \<sigma>' = None \<and>  ((pc \<sigma>') syst) = RecIdle)   \<longrightarrow> ( \<forall> a t. a \<in>  dom (log \<sigma>') \<longrightarrow> [a]\<^sup>A\<^sub>t (\<tau> \<sigma>') =  {lastVal a  (\<tau> \<sigma>')}) ) " 
  using assms 
  apply (unfold  total_wfs_def)
  apply (simp add:  Commit_inv_def  TML_Commit_def   )
  apply (cases "pc \<sigma> t";   simp  )
  using Ready_total_def apply blast
  apply (metis option.distinct(1))
  by (metis dom_empty empty_iff)


(*5*)
lemma  crash_wr_none_log_lv:
assumes  "thrdsvars"
and "TML_Crash  \<sigma> \<sigma>'"
and " ( (writer \<sigma> = None \<and>  ((pc \<sigma>) syst) = RecIdle)   \<longrightarrow> ( \<forall> a t. a \<in>  dom (log \<sigma>) \<longrightarrow> [a]\<^sup>A\<^sub>t (\<tau> \<sigma>) =  {lastVal a  (\<tau> \<sigma>)}) )  " 
shows " ( (writer \<sigma>' = None \<and>  ((pc \<sigma>') syst) = RecIdle)   \<longrightarrow> ( \<forall> a t. a \<in>  dom (log \<sigma>') \<longrightarrow> [a]\<^sup>A\<^sub>t (\<tau> \<sigma>') =  {lastVal a  (\<tau> \<sigma>')}) ) " 
  using assms
  by(simp add:TML_Crash_def pm_inv_def)


(*6*)
lemma  recover_wr_none_log_lv:
 assumes "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
  and " TML_Recover syst   \<sigma> \<sigma>' "
 and "  Recover_inv  syst  ((pc \<sigma>) syst)  \<sigma>"
(*and " thread_prop_comp  \<sigma> t "*)
 (* and "((pc \<sigma>) syst) \<in> {RecIdle} \<union> recovering "*)
and " ( (writer \<sigma> = None \<and>  ((pc \<sigma>) syst) = RecIdle)   \<longrightarrow> ( \<forall> a t. a \<in>  dom (log \<sigma>) \<longrightarrow> [a]\<^sup>A\<^sub>t (\<tau> \<sigma>) =  {lastVal a  (\<tau> \<sigma>)}) )  " 
shows " ( (writer \<sigma>' = None \<and>  ((pc \<sigma>') syst) = RecIdle)   \<longrightarrow> ( \<forall> a t. a \<in>  dom (log \<sigma>') \<longrightarrow> [a]\<^sup>A\<^sub>t (\<tau> \<sigma>') =  {lastVal a  (\<tau> \<sigma>')}) ) " 
  using assms
  apply (simp add:TML_Recover_def total_wfs_def Recover_inv_def)
  apply (cases "pc \<sigma> syst";   simp add: split if_splits)
   apply (metis domIff)
  apply (case_tac " log \<sigma> = Map.empty ")
  apply simp
  by simp



lemma beginInv_wr_none_log_lv:
assumes  "thrdsvars"
and "TML_Begin_invocation t  \<sigma> \<sigma>'"
  and " Begin_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
and " ( (writer \<sigma> = None \<and>  ((pc \<sigma>) syst) = RecIdle)   \<longrightarrow> ( \<forall> a t. a \<in>  dom (log \<sigma>) \<longrightarrow> [a]\<^sup>A\<^sub>t (\<tau> \<sigma>) =  {lastVal a  (\<tau> \<sigma>)}) )  " 
shows " ( (writer \<sigma>' = None \<and>  ((pc \<sigma>') syst) = RecIdle)   \<longrightarrow> ( \<forall> a t. a \<in>  dom (log \<sigma>') \<longrightarrow> [a]\<^sup>A\<^sub>t (\<tau> \<sigma>') =  {lastVal a  (\<tau> \<sigma>')}) ) " 
  using assms
  apply (simp add: TML_Begin_invocation_def Begin_invocation_inv_def total_wfs_def )
  by (cases "pc \<sigma> t";  simp )



lemma beginResp_wr_none_log_lv:
assumes  "thrdsvars"
and "TML_Begin_response t  \<sigma> \<sigma>'"
and " ( (writer \<sigma> = None \<and>  ((pc \<sigma>) syst) = RecIdle)   \<longrightarrow> ( \<forall> a t. a \<in>  dom (log \<sigma>) \<longrightarrow> [a]\<^sup>A\<^sub>t (\<tau> \<sigma>) =  {lastVal a  (\<tau> \<sigma>)}) )  " 
shows " ( (writer \<sigma>' = None \<and>  ((pc \<sigma>') syst) = RecIdle)   \<longrightarrow> ( \<forall> a t. a \<in>  dom (log \<sigma>') \<longrightarrow> [a]\<^sup>A\<^sub>t (\<tau> \<sigma>') =  {lastVal a  (\<tau> \<sigma>')}) ) " 
  using assms
  apply (simp add: TML_Begin_response_def total_wfs_def )
  by (cases "pc \<sigma> t";  simp)


lemma readInv_wr_none_log_lv:
assumes  "thrdsvars"
and "TML_Read_invocation t  \<sigma> \<sigma>'"
  and " Begin_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
and " ( (writer \<sigma> = None \<and>  ((pc \<sigma>) syst) = RecIdle)   \<longrightarrow> ( \<forall> a t. a \<in>  dom (log \<sigma>) \<longrightarrow> [a]\<^sup>A\<^sub>t (\<tau> \<sigma>) =  {lastVal a  (\<tau> \<sigma>)}) )  " 
shows " ( (writer \<sigma>' = None \<and>  ((pc \<sigma>') syst) = RecIdle)   \<longrightarrow> ( \<forall> a t. a \<in>  dom (log \<sigma>') \<longrightarrow> [a]\<^sup>A\<^sub>t (\<tau> \<sigma>') =  {lastVal a  (\<tau> \<sigma>')}) ) " 
  using assms
  apply (simp add: TML_Read_invocation_def Begin_invocation_inv_def total_wfs_def )
 by  (cases "pc \<sigma> t";  simp )



lemma readResp_wr_none_log_lv:
assumes  "thrdsvars"
and "TML_Read_response t  \<sigma> \<sigma>'"
and " ( (writer \<sigma> = None \<and>  ((pc \<sigma>) syst) = RecIdle)   \<longrightarrow> ( \<forall> a t. a \<in>  dom (log \<sigma>) \<longrightarrow> [a]\<^sup>A\<^sub>t (\<tau> \<sigma>) =  {lastVal a  (\<tau> \<sigma>)}) )  " 
shows " ( (writer \<sigma>' = None \<and>  ((pc \<sigma>') syst) = RecIdle)   \<longrightarrow> ( \<forall> a t. a \<in>  dom (log \<sigma>') \<longrightarrow> [a]\<^sup>A\<^sub>t (\<tau> \<sigma>') =  {lastVal a  (\<tau> \<sigma>')}) ) " 
  using assms
  apply (simp add: TML_Read_response_def total_wfs_def )
  by (cases "pc \<sigma> t";  simp)


lemma writeInv_wr_none_log_lv:
assumes  "thrdsvars"
and "TML_Write_invocation t  \<sigma> \<sigma>'"
  and " Write_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
and " ( (writer \<sigma> = None \<and>  ((pc \<sigma>) syst) = RecIdle)   \<longrightarrow> ( \<forall> a t. a \<in>  dom (log \<sigma>) \<longrightarrow> [a]\<^sup>A\<^sub>t (\<tau> \<sigma>) =  {lastVal a  (\<tau> \<sigma>)}) )  " 
shows " ( (writer \<sigma>' = None \<and>  ((pc \<sigma>') syst) = RecIdle)   \<longrightarrow> ( \<forall> a t. a \<in>  dom (log \<sigma>') \<longrightarrow> [a]\<^sup>A\<^sub>t (\<tau> \<sigma>') =  {lastVal a  (\<tau> \<sigma>')}) ) " 
  using assms
  apply (simp add: TML_Write_invocation_def  total_wfs_def )
  by (cases "pc \<sigma> t";  simp )





lemma writeResp_wr_none_log_lv:
assumes  "thrdsvars"
and "TML_Write_response t  \<sigma> \<sigma>'"
and " ( (writer \<sigma> = None \<and>  ((pc \<sigma>) syst) = RecIdle)   \<longrightarrow> ( \<forall> a t. a \<in>  dom (log \<sigma>) \<longrightarrow> [a]\<^sup>A\<^sub>t (\<tau> \<sigma>) =  {lastVal a  (\<tau> \<sigma>)}) )  " 
shows " ( (writer \<sigma>' = None \<and>  ((pc \<sigma>') syst) = RecIdle)   \<longrightarrow> ( \<forall> a t. a \<in>  dom (log \<sigma>') \<longrightarrow> [a]\<^sup>A\<^sub>t (\<tau> \<sigma>') =  {lastVal a  (\<tau> \<sigma>')}) ) " 
  using assms
  apply (simp add: TML_Write_response_def total_wfs_def )
  by (cases "pc \<sigma> t";  simp)




lemma commitInv_wr_none_log_lv:
assumes  "thrdsvars"
and "TML_Commit_invocation t  \<sigma> \<sigma>'"
  and " Commit_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
and " ( (writer \<sigma> = None \<and>  ((pc \<sigma>) syst) = RecIdle)   \<longrightarrow> ( \<forall> a t. a \<in>  dom (log \<sigma>) \<longrightarrow> [a]\<^sup>A\<^sub>t (\<tau> \<sigma>) =  {lastVal a  (\<tau> \<sigma>)}) )  " 
shows " ( (writer \<sigma>' = None \<and>  ((pc \<sigma>') syst) = RecIdle)   \<longrightarrow> ( \<forall> a t. a \<in>  dom (log \<sigma>') \<longrightarrow> [a]\<^sup>A\<^sub>t (\<tau> \<sigma>') =  {lastVal a  (\<tau> \<sigma>')}) ) " 
  using assms
  apply (simp add: TML_Commit_invocation_def  total_wfs_def )
  by (cases "pc \<sigma> t";  simp )




lemma commitResp_wr_none_log_lv:
assumes  "thrdsvars"
and "TML_Commit_response t  \<sigma> \<sigma>'"
and " ( (writer \<sigma> = None \<and>  ((pc \<sigma>) syst) = RecIdle)   \<longrightarrow> ( \<forall> a t. a \<in>  dom (log \<sigma>) \<longrightarrow> [a]\<^sup>A\<^sub>t (\<tau> \<sigma>) =  {lastVal a  (\<tau> \<sigma>)}) )  " 
shows " ( (writer \<sigma>' = None \<and>  ((pc \<sigma>') syst) = RecIdle)   \<longrightarrow> ( \<forall> a t. a \<in>  dom (log \<sigma>') \<longrightarrow> [a]\<^sup>A\<^sub>t (\<tau> \<sigma>') =  {lastVal a  (\<tau> \<sigma>')}) ) " 
  using assms
  apply (simp add: TML_Commit_response_def total_wfs_def )
  by (cases "pc \<sigma> t";  simp)





(*********************************************************************)

(*see if you need *)

(*1*)
lemma Begin_c123_writer_inv:
  assumes "thrdsvars"
      and "total_wfs (\<tau> \<sigma>)"
      and "TML_Begin  t   \<sigma> \<sigma>'"
      and "((pc \<sigma>) t) \<in> beginning\<union> {BeginPending,BeginResponding, Aborted} "
  and  "(\<forall>t. ((pc \<sigma>) t) \<in> {Commit2, Commit3,Commit4,Write3,Write4, Write5, Write6, Write7,Write8} \<longrightarrow> writer \<sigma>  =  Some t )"
    shows "(\<forall>t.  ((pc \<sigma>') t) \<in> {Commit2, Commit3,Commit4,Write3,Write4, Write5, Write6, Write7,Write8} \<longrightarrow> writer \<sigma>' =  Some t) " 
  using assms 
  apply (simp add:TML_Begin_def Begin_inv_def total_wfs_def  )
  apply (cases "pc \<sigma> t"; simp)
  by ( simp add: split: if_split_asm)

(*( (\<forall>t.( writer cs = Some t\<longrightarrow> ( \<forall> j \<noteq> t.  ((pc cs) j) \<notin>  {Commit2, Commit3,Commit4,Write3} )  )) )*)

(*2*)
lemma Read_c123_writer_inv:
  assumes "thrdsvars"
      and "total_wfs (\<tau> \<sigma>)"
and "  \<forall>  t.  (     writer \<sigma> = Some t \<longrightarrow> odd (lastVal glb  (\<tau> \<sigma>)) )"
    and "TML_Read  t   \<sigma> \<sigma>'"
    and "((pc \<sigma>) t) \<in> reading \<union>{ReadPending,ReadResponding } \<union> {Aborted} "
      and "Read_inv t  ((pc \<sigma>) t) \<sigma>" 
  and  "(\<forall>t. ((pc \<sigma>) t) \<in> {Commit2, Commit3,Commit4,Write3,Write4, Write5, Write6, Write7,Write8} \<longrightarrow> writer \<sigma>  =  Some t )"
    shows "(\<forall>t.  ((pc \<sigma>') t) \<in> {Commit2, Commit3,Commit4,Write3,Write4, Write5, Write6, Write7,Write8} \<longrightarrow> writer \<sigma>' =  Some t) " 
  using assms 
  apply (simp add:TML_Read_def Read_inv_def total_wfs_def  )
  apply (cases "pc \<sigma> t"; simp)
 apply ( ( simp add: split: if_split_asm))
 apply ( ( simp add: split: if_split_asm))
  by ( ( simp add: split: if_split_asm))


(*3*)
lemma Write_c123_writer_inv:
  assumes "thrdsvars"
      and "total_wfs (\<tau> \<sigma>)"
      and "TML_Write  t    \<sigma> \<sigma>'"
  and " Write_inv  t ((pc \<sigma>) t) \<sigma> "
  and "((pc \<sigma>) t) \<in> {WritePending,WriteResponding } \<union> {Aborted} \<union> writing "
and "  \<forall>  t.  (     writer \<sigma> = Some t \<longrightarrow> odd (lastVal glb  (\<tau> \<sigma>)) )"
  and  "(\<forall>t. ((pc \<sigma>) t) \<in> {Commit2, Commit3,Commit4,Write3,Write4, Write5, Write6, Write7,Write8} \<longrightarrow> writer \<sigma>  =  Some t )"
    shows "(\<forall>t.  ((pc \<sigma>') t) \<in> {Commit2, Commit3,Commit4,Write3,Write4, Write5, Write6, Write7,Write8} \<longrightarrow> writer \<sigma>' =  Some t) " 
  using assms 
  apply (simp add:TML_Write_def Write_inv_def  total_wfs_def;  simp add: split if_splits )
  apply (cases "pc \<sigma> t";   simp  )
         apply  ( simp add: split: if_split_asm)
  apply (smt (z3) Ready_total_def)
         apply  ( simp add: split: if_split_asm)
  apply (smt (verit, best) cas_fail_diff_lv neq0_conv)
  apply metis
  apply (metis pc_aux)
  by metis+



(*4*)
lemma commit_c123_writer_inv:
 assumes "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
  and "  Commit_inv  t   ((pc \<sigma>) t) \<sigma>  "
  and "TML_Commit  t   \<sigma> \<sigma>'"
  and "((pc \<sigma>) t) \<in> {CommitPending,Committed, Aborted} \<union> committing"
and "  \<forall>  t.  (     writer \<sigma> = Some t \<longrightarrow> odd (lastVal glb  (\<tau> \<sigma>)) )"
 and " t \<noteq> syst "
    and  "(\<forall>t. ((pc \<sigma>) t) \<in> {Commit2, Commit3,Commit4,Write3,Write4, Write5, Write6, Write7,Write8} \<longrightarrow> writer \<sigma>  =  Some t )"
    shows "(\<forall>t.  ((pc \<sigma>') t) \<in> {Commit2, Commit3,Commit4,Write3,Write4, Write5, Write6, Write7,Write8} \<longrightarrow> writer \<sigma>' =  Some t) " 
  using assms
  apply (unfold  total_wfs_def)
  apply (simp add: TML_Commit_def Commit_inv_def  )
 apply (cases "pc \<sigma> t";   simp  )
   apply ( simp add: split: if_split_asm)+
  using Ready_total_def apply blast
  apply (smt (z3) option.inject)
  apply metis
  by (smt (verit) option.inject) 


(*5*)
lemma recover_c123_writer_inv:
 assumes "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
  and " TML_Recover syst   \<sigma> \<sigma>' "
 and "  Recover_inv  syst  ((pc \<sigma>) syst)  \<sigma>"
(*and " thread_prop_comp  \<sigma> t "*)
  and "((pc \<sigma>) syst) \<in> {RecIdle} \<union> recovering "
    and  "(\<forall>t. ((pc \<sigma>) t) \<in> {Commit2, Commit3,Commit4,Write3,Write4, Write5, Write6, Write7,Write8} \<longrightarrow> writer \<sigma>  =  Some t )"
    shows "(\<forall>t.  ((pc \<sigma>') t) \<in> {Commit2, Commit3,Commit4,Write3,Write4, Write5, Write6, Write7,Write8} \<longrightarrow> writer \<sigma>' =  Some t) " 
  using assms
  apply (simp add:TML_Recover_def total_wfs_def Recover_inv_def)
  apply (cases "pc \<sigma> syst";   simp add: split if_splits)
    apply ( case_tac " even (regs (\<tau> \<sigma>) syst c1)")
   apply  ( simp add: split: if_split_asm)
  apply  ( simp add: split: if_split_asm)
   apply  (case_tac " log \<sigma> = Map.empty")
  apply simp
  by simp

(*6*)
lemma  crash_c123_writer_inv:
assumes  "thrdsvars"
and "TML_Crash  \<sigma> \<sigma>'"
    and  "(\<forall>t. ((pc \<sigma>) t) \<in> {Commit2, Commit3,Commit4,Write3,Write4, Write5, Write6, Write7,Write8} \<longrightarrow> writer \<sigma>  =  Some t )"
    shows "(\<forall>t.  ((pc \<sigma>') t) \<in> {Commit2, Commit3,Commit4,Write3,Write4, Write5, Write6, Write7,Write8} \<longrightarrow> writer \<sigma>' =  Some t) " 
  using assms
  by(simp add:TML_Crash_def pm_inv_def)





lemma beginInv_c123_writer_inv:
assumes  "thrdsvars"
and "TML_Begin_invocation t  \<sigma> \<sigma>'"
  and " Begin_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
    and  "(\<forall>t. ((pc \<sigma>) t) \<in> {Commit2, Commit3,Commit4,Write3,Write4, Write5, Write6, Write7,Write8} \<longrightarrow> writer \<sigma>  =  Some t )"
    shows "(\<forall>t.  ((pc \<sigma>') t) \<in> {Commit2, Commit3,Commit4,Write3,Write4, Write5, Write6, Write7,Write8} \<longrightarrow> writer \<sigma>' =  Some t) " 
  using assms
  apply (simp add: TML_Begin_invocation_def Begin_invocation_inv_def total_wfs_def )
  apply (cases "pc \<sigma> t";  simp )
  by (metis option.sel)+


lemma beginResp_c123_writer_inv:
assumes  "thrdsvars"
and "TML_Begin_response t  \<sigma> \<sigma>'"
    and  "(\<forall>t. ((pc \<sigma>) t) \<in> {Commit2, Commit3,Commit4,Write3,Write4, Write5, Write6, Write7,Write8} \<longrightarrow> writer \<sigma>  =  Some t )"
    shows "(\<forall>t.  ((pc \<sigma>') t) \<in> {Commit2, Commit3,Commit4,Write3,Write4, Write5, Write6, Write7,Write8} \<longrightarrow> writer \<sigma>' =  Some t) " 
  using assms
  apply (simp add: TML_Begin_response_def total_wfs_def )
  apply (cases "pc \<sigma> t";  simp)
  by (metis option.sel)+


lemma readInv_c123_writer_inv:
assumes  "thrdsvars"
and "TML_Read_invocation t  \<sigma> \<sigma>'"
  and " Begin_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
    and  "(\<forall>t. ((pc \<sigma>) t) \<in> {Commit2, Commit3,Commit4,Write3,Write4, Write5, Write6, Write7,Write8} \<longrightarrow> writer \<sigma>  =  Some t )"
    shows "(\<forall>t.  ((pc \<sigma>') t) \<in> {Commit2, Commit3,Commit4,Write3,Write4, Write5, Write6, Write7,Write8} \<longrightarrow> writer \<sigma>' =  Some t) " 
  using assms
  apply (simp add: TML_Read_invocation_def Begin_invocation_inv_def total_wfs_def )
  apply (cases "pc \<sigma> t";  simp)
  by (metis option.sel)+



lemma readResp_c123_writer_inv:
assumes  "thrdsvars"
and "TML_Read_response t  \<sigma> \<sigma>'"
    and  "(\<forall>t. ((pc \<sigma>) t) \<in> {Commit2, Commit3,Commit4,Write3,Write4, Write5, Write6, Write7,Write8} \<longrightarrow> writer \<sigma>  =  Some t )"
    shows "(\<forall>t.  ((pc \<sigma>') t) \<in> {Commit2, Commit3,Commit4,Write3,Write4, Write5, Write6, Write7,Write8} \<longrightarrow> writer \<sigma>' =  Some t) " 
  using assms
  apply (simp add: TML_Read_response_def total_wfs_def )
  apply (cases "pc \<sigma> t";  simp)
  by (metis option.sel)+


lemma writeInv_c123_writer_inv:
assumes  "thrdsvars"
and "TML_Write_invocation t  \<sigma> \<sigma>'"
  and " Write_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
    and  "(\<forall>t. ((pc \<sigma>) t) \<in> {Commit2, Commit3,Commit4,Write3,Write4, Write5, Write6, Write7,Write8} \<longrightarrow> writer \<sigma>  =  Some t )"
    shows "(\<forall>t.  ((pc \<sigma>') t) \<in> {Commit2, Commit3,Commit4,Write3,Write4, Write5, Write6, Write7,Write8} \<longrightarrow> writer \<sigma>' =  Some t) " 
  using assms
  apply (simp add: TML_Write_invocation_def  total_wfs_def )
   apply (cases "pc \<sigma> t";  simp)
  by (metis option.sel)+





lemma writeResp_c123_writer_inv:
assumes  "thrdsvars"
and "TML_Write_response t  \<sigma> \<sigma>'"
    and  "(\<forall>t. ((pc \<sigma>) t) \<in> {Commit2, Commit3,Commit4,Write3,Write4, Write5, Write6, Write7,Write8} \<longrightarrow> writer \<sigma>  =  Some t )"
    shows "(\<forall>t.  ((pc \<sigma>') t) \<in> {Commit2, Commit3,Commit4,Write3,Write4, Write5, Write6, Write7,Write8} \<longrightarrow> writer \<sigma>' =  Some t) " 
  using assms
  apply (simp add: TML_Write_response_def total_wfs_def )
  apply (cases "pc \<sigma> t";  simp)
  by (metis option.sel)+




lemma commitInv_c123_writer_inv:
assumes  "thrdsvars"
and "TML_Commit_invocation t  \<sigma> \<sigma>'"
  and " Commit_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
    and  "(\<forall>t. ((pc \<sigma>) t) \<in> {Commit2, Commit3,Commit4,Write3,Write4, Write5, Write6, Write7,Write8} \<longrightarrow> writer \<sigma>  =  Some t )"
    shows "(\<forall>t.  ((pc \<sigma>') t) \<in> {Commit2, Commit3,Commit4,Write3,Write4, Write5, Write6, Write7,Write8} \<longrightarrow> writer \<sigma>' =  Some t) " 
  using assms
  apply (simp add: TML_Commit_invocation_def  total_wfs_def )
  apply (cases "pc \<sigma> t";  simp)
  by (metis option.sel)+




lemma commitResp_c123_writer_inv:
assumes  "thrdsvars"
and "TML_Commit_response t  \<sigma> \<sigma>'"
    and  "(\<forall>t. ((pc \<sigma>) t) \<in> {Commit2, Commit3,Commit4,Write3,Write4, Write5, Write6, Write7,Write8} \<longrightarrow> writer \<sigma>  =  Some t )"
    shows "(\<forall>t.  ((pc \<sigma>') t) \<in> {Commit2, Commit3,Commit4,Write3,Write4, Write5, Write6, Write7,Write8} \<longrightarrow> writer \<sigma>' =  Some t) " 
  using assms
  apply (simp add: TML_Commit_response_def total_wfs_def )
  apply (cases "pc \<sigma> t";  simp)
  by (metis option.sel)+









(*************on recover glb *********************************)

(* pc cs  syst  = RecIdle \<longrightarrow> even (recoveredGlb cs ) *)
(*1*)
lemma recover_recidl_recglb_even :
 assumes "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
  and " TML_Recover syst   \<sigma> \<sigma>' "
 and "  Recover_inv  syst  ((pc \<sigma>) syst)  \<sigma>"
(*and " thread_prop_comp  \<sigma> t "*)
and "  pc \<sigma>  syst  = RecIdle \<longrightarrow> even (recoveredGlb \<sigma> )   "
shows  "  pc \<sigma>'  syst  = RecIdle \<longrightarrow> even (recoveredGlb \<sigma>' )  "

using assms
  apply (simp add:TML_Recover_def total_wfs_def Recover_inv_def)
  apply (cases "pc \<sigma> syst";   simp add: split if_splits)


   apply ( simp add: split: if_splits)


  apply metis
  apply metis
  apply (case_tac " log \<sigma> = Map.empty ")
  apply simp
  by simp


(*2*)
lemma begin_recidl_recglb_even :
 assumes "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
 and "TML_Begin  t   \<sigma> \<sigma>'"
  and "  Begin_inv  t  ((pc \<sigma>) t) \<sigma>   "
 and " t \<noteq> syst "
and "  pc \<sigma>  syst  = RecIdle \<longrightarrow> even (recoveredGlb \<sigma> )   "
shows  "  pc \<sigma>'  syst  = RecIdle \<longrightarrow> even (recoveredGlb \<sigma>' )  "
  using assms
 apply (simp add:TML_Begin_def total_wfs_def Begin_inv_def )
  apply (cases "pc \<sigma> t";  simp add: split if_splits )
  by metis


(*3*)
lemma write_recidl_recglb_even :
  assumes "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
  and " Write_inv  t  ((pc \<sigma>) t) \<sigma> "
 and "TML_Write  t   \<sigma> \<sigma>'"
 and " t \<noteq> syst "
and "  pc \<sigma>  syst  = RecIdle \<longrightarrow> even (recoveredGlb \<sigma> )   "
shows  "  pc \<sigma>'  syst  = RecIdle \<longrightarrow> even (recoveredGlb \<sigma>' )  "
 using assms
  apply (simp add:TML_Write_def Write_inv_def total_wfs_def   )
  apply (cases "pc \<sigma> t";  simp add: split if_splits )
      apply  ( simp add: split: if_split_asm)
  apply (metis neq0_conv)
  by metis


(*4*)
lemma commit_recidl_recglb_even:
 assumes "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
  and "  Commit_inv  t   ((pc \<sigma>) t) \<sigma>  "
  and "TML_Commit  t   \<sigma> \<sigma>'"
 and " t \<noteq> syst "
and "  pc \<sigma>  syst  = RecIdle \<longrightarrow> even (recoveredGlb \<sigma> )   "
shows  "  pc \<sigma>'  syst  = RecIdle \<longrightarrow> even (recoveredGlb \<sigma>' )  "
 using assms
  apply (simp add:TML_Commit_def Commit_inv_def total_wfs_def   )
  apply (cases "pc \<sigma> t"; simp )
  by ( simp add: split: if_split_asm)


(*5*)
lemma read_recidl_recglb_even:
 assumes "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
  and "Read_inv t  ((pc \<sigma>) t) \<sigma>" 
  and "TML_Read  t   \<sigma> \<sigma>'"
and " a \<noteq> glb"
 and " t \<noteq> syst "
and "  pc \<sigma>  syst  = RecIdle \<longrightarrow> even (recoveredGlb \<sigma> )   "
shows  "  pc \<sigma>'  syst  = RecIdle \<longrightarrow> even (recoveredGlb \<sigma>' )  "
  using assms
  apply (unfold  total_wfs_def)
  apply (simp add: TML_Read_def Read_inv_def   )
  apply (cases "pc \<sigma> t";  simp add: split if_splits)
  apply  ( simp add: split: if_split_asm)
  apply (metis fun_upd_other)
  by  ( simp add: split: if_split_asm)

(*6*)
lemma crash_recidl_recglb_even:
assumes  "thrdsvars"
and "TML_Crash  \<sigma> \<sigma>'"
and "  pc \<sigma>  syst  = RecIdle \<longrightarrow> even (recoveredGlb \<sigma> )   "
shows  "  pc \<sigma>'  syst  = RecIdle \<longrightarrow> even (recoveredGlb \<sigma>' )  "
  using assms
  by (simp add: TML_Crash_def  total_wfs_def )


lemma beginInv_recidl_recglb_even:
assumes  "thrdsvars"
and "TML_Begin_invocation t  \<sigma> \<sigma>'"
  and " Begin_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
and "  pc \<sigma>  syst  = RecIdle \<longrightarrow> even (recoveredGlb \<sigma> )   "
shows  "  pc \<sigma>'  syst  = RecIdle \<longrightarrow> even (recoveredGlb \<sigma>' )  "
  using assms
  apply (simp add: TML_Begin_invocation_def Begin_invocation_inv_def total_wfs_def )
  by (cases "pc \<sigma> t";  simp )



lemma beginResp_recidl_recglb_even:
assumes  "thrdsvars"
and "TML_Begin_response t  \<sigma> \<sigma>'"
and "  pc \<sigma>  syst  = RecIdle \<longrightarrow> even (recoveredGlb \<sigma> )   "
shows  "  pc \<sigma>'  syst  = RecIdle \<longrightarrow> even (recoveredGlb \<sigma>' )  "
  using assms
  apply (simp add: TML_Begin_response_def total_wfs_def )
  by (cases "pc \<sigma> t";  simp)


lemma readInv_recidl_recglb_even:
assumes  "thrdsvars"
and "TML_Read_invocation t  \<sigma> \<sigma>'"
  and " Begin_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
and "  pc \<sigma>  syst  = RecIdle \<longrightarrow> even (recoveredGlb \<sigma> )   "
shows  "  pc \<sigma>'  syst  = RecIdle \<longrightarrow> even (recoveredGlb \<sigma>' )  "
  using assms
  apply (simp add: TML_Read_invocation_def Begin_invocation_inv_def total_wfs_def )
 by  (cases "pc \<sigma> t";  simp )



lemma readResp_recidl_recglb_even:
assumes  "thrdsvars"
and "TML_Read_response t  \<sigma> \<sigma>'"
and "  pc \<sigma>  syst  = RecIdle \<longrightarrow> even (recoveredGlb \<sigma> )   "
shows  "  pc \<sigma>'  syst  = RecIdle \<longrightarrow> even (recoveredGlb \<sigma>' )  "
  using assms
  apply (simp add: TML_Read_response_def total_wfs_def )
  by (cases "pc \<sigma> t";  simp)


lemma writeInv_recidl_recglb_even:
assumes  "thrdsvars"
and "TML_Write_invocation t  \<sigma> \<sigma>'"
  and " Write_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
and "  pc \<sigma>  syst  = RecIdle \<longrightarrow> even (recoveredGlb \<sigma> )   "
shows  "  pc \<sigma>'  syst  = RecIdle \<longrightarrow> even (recoveredGlb \<sigma>' )  "
  using assms
  apply (simp add: TML_Write_invocation_def  total_wfs_def )
  by (cases "pc \<sigma> t";  simp )





lemma writeResp_recidl_recglb_even:
assumes  "thrdsvars"
and "TML_Write_response t  \<sigma> \<sigma>'"
and "  pc \<sigma>  syst  = RecIdle \<longrightarrow> even (recoveredGlb \<sigma> )   "
shows  "  pc \<sigma>'  syst  = RecIdle \<longrightarrow> even (recoveredGlb \<sigma>' )  "
  using assms
  apply (simp add: TML_Write_response_def total_wfs_def )
  by (cases "pc \<sigma> t";  simp)




lemma commitInv_recidl_recglb_even:
assumes  "thrdsvars"
and "TML_Commit_invocation t  \<sigma> \<sigma>'"
  and " Commit_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
and "  pc \<sigma>  syst  = RecIdle \<longrightarrow> even (recoveredGlb \<sigma> )   "
shows  "  pc \<sigma>'  syst  = RecIdle \<longrightarrow> even (recoveredGlb \<sigma>' )  "
  using assms
  apply (simp add: TML_Commit_invocation_def  total_wfs_def )
  by (cases "pc \<sigma> t";  simp )




lemma commitResp_recidl_recglb_even:
assumes  "thrdsvars"
and "TML_Commit_response t  \<sigma> \<sigma>'"
and "  pc \<sigma>  syst  = RecIdle \<longrightarrow> even (recoveredGlb \<sigma> )   "
shows  "  pc \<sigma>'  syst  = RecIdle \<longrightarrow> even (recoveredGlb \<sigma>' )  "
  using assms
  apply (simp add: TML_Commit_response_def total_wfs_def )
  by (cases "pc \<sigma> t";  simp)





(******************************************************COH LESS THAN VRNEW *********************************************************************)

lemma ld_coh_le_vrew1:
  assumes "ts [r   \<leftarrow> a ]\<^sub>t ts'"
and " ( (coh ts t b \<le> vrnew ts  t) ) "
and "total_wfs ts"
shows   "  (  (coh ts' t b  \<le> vrnew ts' t) ) "
  using assms

 apply (case_tac " a = b ")
  apply (simp add:  step_def)
  apply (simp add: load_trans_def  Let_def)
  apply clarify

  apply (subgoal_tac "  coh ts' t a \<le> vrnew ts' t" )
   prefer 2
   apply (case_tac "  ind \<noteq> coh ts  t a ")
   apply (subgoal_tac "  (coh ts' t a ) = ind")
  prefer 2
    apply simp
   apply ( simp  add: split: if_split_asm)
  apply ( simp  add: split: if_split_asm)
  apply blast
   apply (unfold total_wfs_def)
  by (metis Load_Rules.vrnew_ld_st_sadrr assms(1) coh_ld_st_dadrr dual_order.trans)



lemma cas_fail_coh_le_vrew:
  assumes "  step t ( CAS y  v1 v2 r) ts ts'    "
and " ( (coh ts t x \<le> vrnew ts  t) ) "
and "total_wfs ts"
and  "regs ts' t r = 0 "
shows   "  (  (coh ts' t x  \<le> vrnew ts' t) ) "
  using assms
  apply (case_tac " y = x  ")
   apply (simp add: step_def)
   apply clarify
  apply (unfold total_wfs_def)
  apply (subgoal_tac "  ts' = cas_fail_trans t  ind x v1 v2 r ts ")
  prefer 2
  apply (metis cas_suc_reg not_one_le_zero zero_less_one_class.zero_le_one)
   apply (simp add: cas_fail_trans_def  Let_def)
  using CAS_Rules.vrnew_ld_st_sadrr assms(3) cas_coh_st_ni le_trans by presburger



(*1*)
lemma begin_coh_le_vrnew_inv:
  assumes "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
  and "TML_Begin  t   \<sigma> \<sigma>'"
 (* and "  Begin_inv  t  ((pc \<sigma>) t) \<sigma>   "*)
 and " t \<noteq> syst "
 and " ((pc \<sigma>) t) \<in> {BeginResponding,BeginPending} \<union>beginning \<union> {Aborted} "
(*and " a \<noteq> glb"*)
 and " \<forall>t. t = syst \<or> (writer \<sigma> = Some t)  \<or>  pc \<sigma> t = Committed\<or>  pc \<sigma> t = CommitResponding \<or>   ( ( coh (\<tau> \<sigma>) t a) \<le> vrnew (\<tau> \<sigma>) t) "
shows  " \<forall>t. t = syst \<or>( writer \<sigma>' = Some t)  \<or>  pc \<sigma>' t = Committed    \<or>  pc \<sigma> t = CommitResponding \<or>   pc \<sigma>' t = CommitPending \<or> ( ( coh (\<tau> \<sigma>') t a) \<le> vrnew (\<tau> \<sigma>') t) "
  using assms
 apply (simp add:TML_Begin_def total_wfs_def Begin_inv_def )
  apply (cases "pc \<sigma> t";  simp add: split if_splits )
    apply clarify
  apply (metis PC.distinct(95) PC.distinct(97))
  apply (metis PC.distinct(171) PC.distinct(173) assms(2) ld_coh_dt_ni ld_coh_le_vrew1 ld_vrnew_dt_ni)
  apply (metis PC.distinct(247) fun_upd_other)


  apply (metis PC.distinct(163) PC.distinct(173) assms(2) ld_coh_dt_ni ld_coh_le_vrew1 ld_vrnew_dt_ni)
  by (metis PC.distinct(237) PC.distinct(247) fun_upd_other)






(*2*)
lemma write_coh_le_vrnew_inv:
  assumes "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
  and " Write_inv  t  ((pc \<sigma>) t) \<sigma> "
 and "TML_Write  t  \<sigma> \<sigma>'"
 (* and " ((pc \<sigma>) t) \<in> {Ready, Aborted} \<union> writing "*)
(*and " a \<noteq> glb"*)
 and " t \<noteq> syst "
and "  \<forall>  t.  (     writer \<sigma> = Some t \<longrightarrow> odd (lastVal glb  (\<tau> \<sigma>)) )"
 and " \<forall>t. t = syst \<or> (writer \<sigma> = Some t)  \<or>    pc \<sigma> t = Committed \<or>   pc \<sigma> t = CommitPending \<or>  ( ( coh (\<tau> \<sigma>) t a) \<le> vrnew (\<tau> \<sigma>) t) "
shows  " \<forall>t. t = syst \<or>( writer \<sigma>' = Some t)  \<or>  pc \<sigma>' t = Committed    \<or>   pc \<sigma>' t = CommitPending  \<or>  ( ( coh (\<tau> \<sigma>') t a) \<le> vrnew (\<tau> \<sigma>') t) "
  using assms
  apply (simp add:TML_Write_def Write_inv_def total_wfs_def   )
  apply (cases "pc \<sigma> t";  simp add: split if_splits )
  apply ( simp add: split: if_split_asm)
         apply (metis PC.distinct(405) PC.distinct(725))
  apply (case_tac "  even (regs (\<tau> \<sigma>) t DTML.loc)")
  apply (metis PC.distinct(407) PC.distinct(727) pc_aux)
  apply (metis PC.distinct(407) PC.distinct(727) pc_aux)
  
       apply (case_tac " 0 < regs (\<tau> \<sigma>') t c1  ")
  apply simp
using  CAS_Rules.vrnew_ld_st_sadrr
  apply (metis assms(2) cas_coh_dt_ni cas_fail_diff_lv cas_vrnew_dt_ni less_numeral_extra(3))
  apply simp
  apply (metis PC.distinct(409) PC.distinct(729) assms(2) cas_coh_dt_ni cas_fail_coh_le_vrew cas_vrnew_dt_ni)
  using assms(2) reg_coh_ni reg_vrnew_ni apply presburger
  apply (metis fun_upd_apply)
  apply (metis assms(2) ld_coh_dt_ni ld_vrnew_dt_ni)
  apply (metis assms(2) reg_coh_dt_ni st_vrnew_dt_ni)
    by (metis assms(2) flo_coh_ni flo_vrnew_ni)


(*3*)
lemma commit_coh_le_vrnew_inv:
 assumes "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
  and "  Commit_inv  t   ((pc \<sigma>) t) \<sigma>  "
  and "TML_Commit  t   \<sigma> \<sigma>'"
(*and " a \<noteq> glb"*)
 and " t \<noteq> syst "
 and " \<forall>t. t = syst \<or>    writer \<sigma> = Some t \<or>  pc \<sigma> t = CommitResponding  \<or> ( ( coh (\<tau> \<sigma>) t a) \<le> vrnew (\<tau> \<sigma>) t) "
shows  " \<forall>t. t = syst \<or>   writer \<sigma>' = Some t \<or> pc \<sigma>' t = CommitResponding \<or> ( ( coh (\<tau> \<sigma>') t a) \<le> vrnew (\<tau> \<sigma>') t) "
  using assms
  apply (simp add: TML_Commit_def Commit_inv_def  total_wfs_def  )
  apply (cases "pc \<sigma> t";  simp add: split if_splits)
 apply (subgoal_tac "( \<forall>t.  coh (\<tau> \<sigma>') t a = coh (\<tau> \<sigma>) t a) ")
  prefer 2
  apply (metis assms(2) sf_coh_ni)
  apply (metis PC.distinct(387) fun_upd_def)

   apply (subgoal_tac " writeAux \<sigma>' t  ")
  prefer 2
  apply blast
  apply (simp add: split if_splits)
   apply (metis assms(2) sf_coh_ni sf_vrnew_dt_ni)
  by (metis assms(2) reg_coh_dt_ni st_vrnew_dt_ni)




(*4*)
lemma read_coh_le_vrnew_inv:
 assumes "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
  and "Read_inv t  ((pc \<sigma>) t) \<sigma>" 
  and "TML_Read  t   \<sigma> \<sigma>'"
(*and " a \<noteq> glb"*)
 and " t \<noteq> syst "
  and " ((pc \<sigma>) t) \<in> {Ready, Aborted} \<union> reading "
 and " \<forall>t. t = syst \<or>    writer \<sigma> = Some t \<or>      pc \<sigma> t = CommitResponding  \<or>  ( ( coh (\<tau> \<sigma>) t a) \<le> vrnew (\<tau> \<sigma>) t) "
shows  " \<forall>t. t = syst \<or> writer \<sigma>' = Some t    \<or>  pc \<sigma>' t = CommitResponding \<or>  ( ( coh (\<tau> \<sigma>') t a) \<le> vrnew (\<tau> \<sigma>') t) "
  using assms
  apply (unfold  total_wfs_def)
  apply (simp add: TML_Read_def Read_inv_def   )
  apply (cases "pc \<sigma> t";  simp add: split if_splits)
      apply (simp add: Ready_total_def read_pre_def)
      apply (metis PC.distinct(653) assms(2) ld_coh_dt_ni ld_coh_le_vrew1 ld_vrnew_dt_ni)
  apply (case_tac " even (regs (\<tau> \<sigma>) t DTML.loc) \<and> \<not> readAux \<sigma> t")
  apply (metis PC.distinct(655) pc_aux)
  apply (metis PC.distinct(655) pc_aux)



    apply (case_tac "(regs (\<tau> \<sigma>') t c1 = 1) ")
  apply simp
  using cas_coh_dt_ni cas_succ_vnrew_eq_length
  apply (metis One_nat_def assms(2) cas_vrnew_dt_ni)
  apply simp
using  cas_coh_dt_ni cas_fail_coh_le_vrew cas_sv_lc cas_vrnew_dt_ni
 assms(2) ld_coh_dt_ni ld_coh_le_vrew1 ld_vrnew_dt_ni
  apply (metis (mono_tags, lifting) One_nat_def PC.distinct(657))
  apply (metis PC.distinct(659) assms(2) ld_coh_dt_ni ld_coh_le_vrew1 ld_vrnew_dt_ni)


  by (metis PC.distinct(661) pc_aux)




(*ld_coh_lt_vrew_simp*)

(*5*)
lemma recover_coh_le_vrnew_inv:
 assumes "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
  and " TML_Recover syst   \<sigma> \<sigma>' "
 and "  Recover_inv  syst  ((pc \<sigma>) syst)  \<sigma>"
 and " \<forall>t. t = syst \<or>    writer \<sigma> = Some t \<or>  pc \<sigma> t =  CommitResponding   \<or>  ( ( coh (\<tau> \<sigma>) t a) \<le> vrnew (\<tau> \<sigma>) t) "
shows  " \<forall>t. t = syst \<or> writer \<sigma>' = Some t   \<or>  pc \<sigma>' t =  CommitResponding  \<or> ( ( coh (\<tau> \<sigma>') t a) \<le> vrnew (\<tau> \<sigma>') t) "
  using assms

  apply (simp add: TML_Recover_def Recover_inv_def   )
  apply (cases "pc \<sigma> syst";  simp add: split if_splits)
  apply (metis reg_coh_ni reg_vrnew_ni)
  apply (metis reg_coh_dt_ni st_vrnew_dt_ni)
  apply (metis flo_coh_ni flo_vrnew_ni)
  apply (metis sf_coh_ni sf_vrnew_dt_ni)
  apply metis
  apply (metis ld_coh_dt_ni ld_vrnew_dt_ni)
  apply (metis pc_aux)
  apply (metis reg_coh_dt_ni st_vrnew_dt_ni)
  apply (metis reg_coh_dt_ni st_vrnew_dt_ni)
  by (metis pc_aux)



(*6*)
lemma crash_coh_le_vrnew_inv:
assumes  "thrdsvars"
and "TML_Crash  \<sigma> \<sigma>'"
 and " \<forall>t. t = syst \<or>    writer \<sigma> = Some t \<or>  pc \<sigma> t =  CommitResponding \<or>  ( ( coh (\<tau> \<sigma>) t a) \<le> vrnew (\<tau> \<sigma>) t) "
shows  " \<forall>t. t = syst \<or> writer \<sigma>' = Some t   \<or>  pc \<sigma>' t = CommitResponding  \<or> ( ( coh (\<tau> \<sigma>') t a) \<le> vrnew (\<tau> \<sigma>') t) "
  using assms
  apply (simp add: TML_Crash_def  total_wfs_def )
  apply (simp add:  crash_step_def)
  by(simp add:  crash_trans_def   )




lemma beginInv_coh_le_vrnew_inv:
assumes  "thrdsvars"
and "TML_Begin_invocation t  \<sigma> \<sigma>'"
  and " Begin_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
 and " \<forall>t. t = syst \<or>    writer \<sigma> = Some t\<or>  pc \<sigma> t = CommitResponding  \<or>   pc \<sigma> t =  CommitResponding \<or>  ( ( coh (\<tau> \<sigma>) t a) \<le> vrnew (\<tau> \<sigma>) t) "
shows  " \<forall>t. t = syst \<or> writer \<sigma>' = Some t   \<or>   pc \<sigma>' t =  CommitResponding   \<or> ( ( coh (\<tau> \<sigma>') t a) \<le> vrnew (\<tau> \<sigma>') t) "
  using assms
  apply (simp add: TML_Begin_invocation_def Begin_invocation_inv_def total_wfs_def )
  apply (cases "pc \<sigma> t";  simp )
  by (metis PC.distinct(17) PC.distinct(19) bot.extremum_unique bot_nat_def)


lemma beginResp_coh_le_vrnew_inv:
assumes  "thrdsvars"
and "TML_Begin_response t  \<sigma> \<sigma>'"
and " \<forall>t. t = syst \<or>    writer \<sigma> = Some t \<or>  pc \<sigma> t =  CommitResponding  \<or>  ( ( coh (\<tau> \<sigma>) t a) \<le> vrnew (\<tau> \<sigma>) t) "
shows  " \<forall>t. t = syst \<or> writer \<sigma>' = Some t   \<or>  pc \<sigma>' t =  CommitResponding    \<or> ( ( coh (\<tau> \<sigma>') t a) \<le> vrnew (\<tau> \<sigma>') t) "
  using assms
  apply (simp add: TML_Begin_response_def total_wfs_def )
  apply (cases "pc \<sigma> t";  simp)
  by (metis PC.distinct(309) PC.distinct(317))



lemma readInv_coh_le_vrnew_inv:
assumes  "thrdsvars"
and "TML_Read_invocation t  \<sigma> \<sigma>'"
  and " Begin_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
and " \<forall>t. t = syst \<or>    writer \<sigma> = Some t \<or>  pc \<sigma> t =  CommitResponding  \<or>  ( ( coh (\<tau> \<sigma>) t a) \<le> vrnew (\<tau> \<sigma>) t) "
shows  " \<forall>t. t = syst \<or> writer \<sigma>' = Some t   \<or>  pc \<sigma>' t =  CommitResponding    \<or> ( ( coh (\<tau> \<sigma>') t a) \<le> vrnew (\<tau> \<sigma>') t) "
  using assms
  apply (simp add: TML_Read_invocation_def Begin_invocation_inv_def total_wfs_def )
  apply  (cases "pc \<sigma> t";  simp )
  by (metis PC.distinct(707))


lemma readResp_coh_le_vrnew_inv:
assumes  "thrdsvars"
and "TML_Read_response t  \<sigma> \<sigma>'"
and " \<forall>t. t = syst \<or>    writer \<sigma> = Some t  \<or>  pc \<sigma> t = CommitResponding \<or>  ( ( coh (\<tau> \<sigma>) t a) \<le> vrnew (\<tau> \<sigma>) t) "
shows  " \<forall>t. t = syst \<or> writer \<sigma>' = Some t   \<or>  pc \<sigma>' t = CommitResponding  \<or> ( ( coh (\<tau> \<sigma>') t a) \<le> vrnew (\<tau> \<sigma>') t) "
  using assms
  apply (simp add: TML_Read_response_def total_wfs_def )
   apply  (cases "pc \<sigma> t";  simp )
  by (metis PC.distinct(663))


lemma writeInv_coh_le_vrnew_inv:
assumes  "thrdsvars"
and "TML_Write_invocation t  \<sigma> \<sigma>'"
  and " Write_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
and " \<forall>t. t = syst \<or>    writer \<sigma> = Some t  \<or>  pc \<sigma> t = CommitResponding  \<or>  ( ( coh (\<tau> \<sigma>) t a) \<le> vrnew (\<tau> \<sigma>) t) "
shows  " \<forall>t. t = syst \<or> writer \<sigma>' = Some t    \<or>  pc \<sigma>' t  = CommitResponding   \<or> ( ( coh (\<tau> \<sigma>') t a) \<le> vrnew (\<tau> \<sigma>') t) "
  using assms
  apply (simp add: TML_Write_invocation_def  total_wfs_def )
  apply (cases "pc \<sigma> t";  simp )
  by (metis PC.distinct(707))


lemma writeResp_coh_le_vrnew_inv:
assumes  "thrdsvars"
and "TML_Write_response t  \<sigma> \<sigma>'"
 and " Write_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
and " \<forall>t. t = syst \<or>    writer \<sigma> = Some t  \<or>  pc \<sigma> t = CommitResponding    \<or>  ( ( coh (\<tau> \<sigma>) t a) \<le> vrnew (\<tau> \<sigma>) t) "
shows  " \<forall>t. t = syst \<or> writer \<sigma>' = Some t    \<or>  pc \<sigma>' t = CommitResponding     \<or> ( ( coh (\<tau> \<sigma>') t a) \<le> vrnew (\<tau> \<sigma>') t) "
  using assms
  apply (simp add: TML_Write_response_def total_wfs_def )
  apply (cases "pc \<sigma> t";  simp)
  by (metis PC.distinct(683))




lemma commitInv_coh_le_vrnew_inv:
assumes  "thrdsvars"
and "TML_Commit_invocation t  \<sigma> \<sigma>'"
  and " Commit_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
and " \<forall>t. t = syst \<or>    writer \<sigma> = Some t \<or>  pc \<sigma> t = CommitResponding  \<or>  ( ( coh (\<tau> \<sigma>) t a) \<le> vrnew (\<tau> \<sigma>) t) "
shows  " \<forall>t. t = syst \<or> writer \<sigma>' = Some t  \<or>  pc \<sigma>' t = CommitResponding     \<or> ( ( coh (\<tau> \<sigma>') t a) \<le> vrnew (\<tau> \<sigma>') t) "
  using assms
  apply (simp add: TML_Commit_invocation_def total_wfs_def )
  apply(cases "pc \<sigma> t";  simp)
  by (metis PC.distinct(707))





lemma commitResp_coh_le_vrnew_inv:
assumes  "thrdsvars"
and "TML_Commit_response t  \<sigma> \<sigma>'"
and " \<forall>t. t = syst \<or>    writer \<sigma> = Some t  \<or>  pc \<sigma> t = CommitResponding   \<or>  ( ( coh (\<tau> \<sigma>) t a) \<le> vrnew (\<tau> \<sigma>) t) "
shows  " \<forall>t. t = syst \<or> writer \<sigma>' = Some t  \<or>  pc \<sigma>' t = CommitResponding   \<or> ( ( coh (\<tau> \<sigma>') t a) \<le> vrnew (\<tau> \<sigma>') t) "
  using assms
  apply (simp add: TML_Commit_response_def total_wfs_def )
  apply (cases "pc \<sigma> t";  simp)
  apply clarify
  oops

(****************************************************END*****************************************************************)


(*****************************TO BE TRANSFERED*************************************** *)
(*

lemma Read_Crash_global:
  assumes "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
  and "pm_inv \<sigma> "
and  " \<forall>  t.  (   writer \<sigma> = Some t \<longrightarrow> odd (lastVal glb  (\<tau> \<sigma>)) )"
 and " \<forall>  t. (  (   writer \<sigma>  = Some t    \<longrightarrow> \<lceil>glb\<rceil>\<^sub>t (\<tau> \<sigma>) ))"
and "glb_monotone_inv (\<tau> \<sigma>) "
and " mem_tml_prop    glb a  (\<tau> \<sigma>) "
and " mem_tml_prop    glb b (\<tau> \<sigma>) "
  and "  Read_inv  t4   b ((pc \<sigma>) t4) \<sigma> "
   and " TML_Crash  \<sigma> \<sigma>'"
  and "((pc \<sigma>) t4) \<in> {Ready} \<union>  reading \<union> {Aborted} "
 and "thread_prop_comp \<sigma> t4 "

shows  "  Read_inv  t4   b ((pc \<sigma>') t4) \<sigma>'  " 
  using assms
 apply (unfold thrdsvars_def )
  apply (simp add:TML_Crash_def Read_inv_def thread_prop_comp_def )
  by (cases "pc \<sigma> t4";  simp add: split if_splits)



lemma Read_Recover_global:
  assumes "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
  and "pm_inv \<sigma> "
and  " \<forall>  t.  (   writer \<sigma> = Some t \<longrightarrow> odd (lastVal glb  (\<tau> \<sigma>)) )"
 and " \<forall>  t. (  (   writer \<sigma>  = Some t    \<longrightarrow> \<lceil>glb\<rceil>\<^sub>t (\<tau> \<sigma>) ))"
and "glb_monotone_inv (\<tau> \<sigma>) "
and " mem_tml_prop    glb a  (\<tau> \<sigma>) "
and " mem_tml_prop    glb b (\<tau> \<sigma>) "
and "  Read_inv  t5  b ((pc \<sigma>) t5)  \<sigma>  "
  and " Recover_inv   t4  ((pc \<sigma>) t4) \<sigma>  "
   and " TML_Read  t5 b  \<sigma> \<sigma>'"
  and "((pc \<sigma>) t5) \<in> {Ready} \<union>  reading \<union> {Aborted} "
  and "((pc \<sigma>) t4) \<in> {RecIdle } \<union> recovering" 
and "t4 \<noteq> t5 "
  and "thread_prop_comp \<sigma> t5 "
 and "thread_prop_comp \<sigma> t4 "

shows  "  Recover_inv  t4  ((pc \<sigma>') t4) \<sigma>'  " 
  using assms
 apply (unfold thrdsvars_def )
  apply (simp add:TML_Read_def Read_inv_def Recover_inv_def  )
  apply (cases" pc  \<sigma> t5"; simp ; cases "(pc \<sigma>) t4"; simp )
 apply (simp split:if_splits )
 apply (simp split:if_splits )
  by(simp split:if_splits )

(*  by (smt (z3) PC.distinct(315) PC.distinct(317) PC.distinct(319) PC.distinct(321) PC.distinct(323) PC.distinct(325) PC.distinct(327) PC.distinct(329) PC.distinct(331) PC.distinct(355) PC.distinct(357) PC.distinct(359) PC.distinct(361) PC.distinct(363) PC.distinct(365) PC.distinct(367) PC.distinct(369) PC.distinct(371) PC.distinct(393) PC.distinct(395) PC.distinct(397) PC.distinct(399) PC.distinct(401) PC.distinct(403) PC.distinct(405) PC.distinct(407) PC.distinct(409) PC.distinct(429) PC.distinct(431) PC.distinct(433) PC.distinct(435) PC.distinct(437) PC.distinct(439) PC.distinct(441) PC.distinct(443) PC.distinct(445) PC.distinct(625) PC.distinct(627) PC.distinct(629) PC.distinct(631) PC.distinct(633) PC.distinct(635) PC.distinct(637) PC.distinct(639) PC.distinct(641) PC.distinct(663) PC.distinct(665) PC.distinct(681) PC.distinct(683) PC.distinct(697) PC.distinct(699) PC.distinct(711) PC.distinct(713) PC.distinct(723) PC.distinct(725) PC.distinct(733) PC.distinct(735) PC.distinct(741) PC.distinct(743) PC.distinct(747) PC.distinct(749) PC.distinct(751) PC.distinct(753))
*)


lemma Begin_Recover_global:
assumes " Recover_inv   t4  ((pc \<sigma>) t4) \<sigma>  "
   and"TML_Begin t5  \<sigma> \<sigma>'"
 and  " Begin_inv  t5  ((pc \<sigma>') t5) \<sigma>'  "
  and "((pc \<sigma>) t5) \<in> {Ready} \<union>  beginning"
  and "((pc \<sigma>) t4) \<in> {RecIdle } \<union> recovering" 
  and "thread_prop_comp \<sigma> t5 "
 and "thread_prop_comp \<sigma> t4 "
shows  "  Recover_inv  t4  ((pc \<sigma>') t4) \<sigma>'  " 
  using assms
  using assms
  apply (simp add:TML_Begin_def Begin_inv_def Recover_inv_def thread_prop_comp_def )
  oops


*)


(************************************ glb_monotone_preserved**********and***** glb_monotone_complete**  *COMPLETED **********************************)

lemma cas_succ_glb_monotone_preserved_spec:
  assumes "  glb_monotone_inv  (\<tau> \<sigma>) "
 and "vbounded (\<tau> \<sigma>)"
and "  \<lceil>glb : (regs (\<tau> \<sigma>) t DTML.loc) \<rceil> (\<tau> \<sigma>) "
and "mem_structured (\<tau> \<sigma>)"
and  "(\<tau> \<sigma>')  =
       cas_succ_trans t  (last_entry (\<tau> \<sigma>) glb)  glb (regs (\<tau> \<sigma>) t DTML.loc)
        (Suc (regs (\<tau> \<sigma>) t DTML.loc)) c1  v1 v2 (\<tau> \<sigma>)"
(*and "  \<lceil>glb\<rceil>\<^sub>t ts "*)
and " \<forall> ti l. last_entry (\<tau> \<sigma>) l \<in>   OTS (\<tau> \<sigma>) ti l "
and " \<forall> ti l. lastVal  l (\<tau> \<sigma>)  \<in>  [l]\<^sub>ti (\<tau> \<sigma>) " 
shows   " glb_monotone_inv  (\<tau> \<sigma>') "
  using assms
  apply (unfold glb_monotone_inv_def)
  using  cas_succ_glb_monotone_preserved [where  glb = glb and t = t ]
  by presburger



lemma cas_succ_glb_monotone_complete_preserved_spec:
  assumes "  glb_monotone_complete_inv  (\<tau> \<sigma>) "
 and "vbounded (\<tau> \<sigma>)"
and "  \<lceil>glb : (regs (\<tau> \<sigma>) t DTML.loc) \<rceil> (\<tau> \<sigma>) "
and "mem_structured (\<tau> \<sigma>)"
and  "(\<tau> \<sigma>')  =
       cas_succ_trans t  (last_entry (\<tau> \<sigma>) glb)  glb (regs (\<tau> \<sigma>) t DTML.loc)
        (Suc (regs (\<tau> \<sigma>) t DTML.loc)) c1 v1 v2 (\<tau> \<sigma>)"
(*and "  \<lceil>glb\<rceil>\<^sub>t ts "*)
and " \<forall> ti l. last_entry (\<tau> \<sigma>) l \<in>   OTS (\<tau> \<sigma>) ti l "
and " \<forall> ti l. lastVal  l (\<tau> \<sigma>)  \<in>  [l]\<^sub>ti (\<tau> \<sigma>) " 
shows   "  glb_monotone_complete_inv   (\<tau> \<sigma>') "
  using assms
  apply (unfold   glb_monotone_complete_inv_def)
  using  cas_succ_glb_monotone_complete_preserved [where  glb = glb and t = t ]
  by presburger





lemma cas_succ_read_glb_monotone_preserved_spec:
  assumes "  glb_monotone_inv  (\<tau> \<sigma>) "
 and "vbounded (\<tau> \<sigma>)"
and "  \<lceil>glb : (regs (\<tau> \<sigma>) t DTML.loc) \<rceil> (\<tau> \<sigma>) "
and "mem_structured (\<tau> \<sigma>)"
and  "(\<tau> \<sigma>')  =
       cas_succ_trans t  (last_entry (\<tau> \<sigma>) glb)  glb (regs (\<tau> \<sigma>) t DTML.loc)
        ((regs (\<tau> \<sigma>) t DTML.loc)) c1 v1 v2 (\<tau> \<sigma>)"
(*and "  \<lceil>glb\<rceil>\<^sub>t ts "*)
and " \<forall> ti l. last_entry (\<tau> \<sigma>) l \<in>   OTS (\<tau> \<sigma>) ti l "
and " \<forall> ti l. lastVal  l (\<tau> \<sigma>)  \<in>  [l]\<^sub>ti (\<tau> \<sigma>) " 
shows   " glb_monotone_inv  (\<tau> \<sigma>') "
  using assms
  apply (unfold glb_monotone_inv_def)
  using  cas_succ_read_glb_monotone_preserved [where  glb = glb and t = t ]
  by presburger


lemma cas_succ_read_glb_monotone_complete_preserved_spec:
  assumes "  glb_monotone_complete_inv  (\<tau> \<sigma>) "
 and "vbounded (\<tau> \<sigma>)"
and "  \<lceil>glb : (regs (\<tau> \<sigma>) t DTML.loc) \<rceil> (\<tau> \<sigma>) "
and "mem_structured (\<tau> \<sigma>)"
and  "(\<tau> \<sigma>')  =
       cas_succ_trans t  (last_entry (\<tau> \<sigma>) glb)  glb (regs (\<tau> \<sigma>) t DTML.loc)
        ((regs (\<tau> \<sigma>) t DTML.loc)) c1 v1 v2 (\<tau> \<sigma>)"
(*and "  \<lceil>glb\<rceil>\<^sub>t ts "*)
and " \<forall> ti l. last_entry (\<tau> \<sigma>) l \<in>   OTS (\<tau> \<sigma>) ti l "
and " \<forall> ti l. lastVal  l (\<tau> \<sigma>)  \<in>  [l]\<^sub>ti (\<tau> \<sigma>) " 
shows   " glb_monotone_complete_inv  (\<tau> \<sigma>') "
  using assms
  apply (unfold glb_monotone_complete_inv_def)
  using  cas_succ_read_glb_monotone_complete_preserved [where  glb = glb and t = t ]
  by presburger







lemma cas_fail_read_glb_monotone_preserved_spec:
  assumes "     \<forall>i j. 0 < j \<and>
          j < length (memory (\<tau> \<sigma>)) \<and>
          0 < i \<and> i < length (memory (\<tau> \<sigma>)) \<and> i \<le> j \<and> Msg.loc (memory (\<tau> \<sigma>) ! i) = glb \<and> Msg.loc (memory (\<tau> \<sigma>) ! j) = glb \<longrightarrow>
          compval (\<tau> \<sigma>) (memory (\<tau> \<sigma>) ! i) glb \<le> compval (\<tau> \<sigma>) (memory (\<tau> \<sigma>) ! j) glb
"
 and "vbounded (\<tau> \<sigma>)"
and "mem_structured (\<tau> \<sigma>)"
and "\<tau> \<sigma> [CAS glb regs (\<tau> \<sigma>) t DTML.loc regs (\<tau> \<sigma>) t DTML.loc c1]\<^sub>t \<tau> \<sigma>'"
and "regs  (\<tau> \<sigma>') t c1 = 0"
shows    "     \<forall>i j. 0 < j \<and>
          j < length (memory (\<tau> \<sigma>')) \<and>
          0 < i \<and> i < length (memory (\<tau> \<sigma>')) \<and> i \<le> j \<and> Msg.loc (memory (\<tau> \<sigma>') ! i) = glb \<and> Msg.loc (memory (\<tau> \<sigma>') ! j) = glb \<longrightarrow>
          compval (\<tau> \<sigma>') (memory (\<tau> \<sigma>') ! i) glb \<le> compval (\<tau> \<sigma>') (memory (\<tau> \<sigma>') ! j) glb"
  using assms
  apply (subgoal_tac " memory  (\<tau> \<sigma>) = memory  (\<tau> \<sigma>')")
   prefer 2
   apply (simp add: step_def)
   apply clarify
  apply (subgoal_tac " \<tau> \<sigma>' =
           cas_fail_trans t ind glb (regs (\<tau> \<sigma>) t DTML.loc)
            (regs (\<tau> \<sigma>) t DTML.loc) c1 (\<tau> \<sigma>)")
  prefer 2
  apply (metis cas_suc_reg zero_neq_one)
  apply (metis assms(4) cas_fail_mem_same)
  apply (simp add:  cas_fail_trans_def)
  by (smt (verit, best) mem_structured_def)




lemma cas_fail_read_glb_monotone_complete_preserved_spec:
  assumes "     \<forall>i j. 0 < j \<and>
          j < length (memory (\<tau> \<sigma>)) \<and>
          0 \<le>  i \<and> i < length (memory (\<tau> \<sigma>)) \<and> i \<le> j \<and> comploc (memory (\<tau> \<sigma>)!i) glb = glb  \<and> comploc (memory (\<tau> \<sigma>)!j) glb = glb  \<longrightarrow>
          compval (\<tau> \<sigma>) (memory (\<tau> \<sigma>) ! i) glb \<le> compval (\<tau> \<sigma>) (memory (\<tau> \<sigma>) ! j) glb
"
 and "vbounded (\<tau> \<sigma>)"
and "mem_structured (\<tau> \<sigma>)"
and "\<tau> \<sigma> [CAS glb regs (\<tau> \<sigma>) t DTML.loc regs (\<tau> \<sigma>) t DTML.loc c1]\<^sub>t \<tau> \<sigma>'"
and "regs  (\<tau> \<sigma>') t c1 = 0"
shows    "     \<forall>i j. 0 < j \<and>
          j < length (memory (\<tau> \<sigma>')) \<and>
          0 \<le> i \<and> i < length (memory (\<tau> \<sigma>')) \<and> i \<le> j \<and> comploc (memory (\<tau> \<sigma>')!i) glb = glb \<and> comploc (memory (\<tau> \<sigma>')!j) glb = glb \<longrightarrow>
          compval (\<tau> \<sigma>') (memory (\<tau> \<sigma>') ! i) glb \<le> compval (\<tau> \<sigma>') (memory (\<tau> \<sigma>') ! j) glb"
  using assms
  apply (subgoal_tac " memory  (\<tau> \<sigma>) = memory  (\<tau> \<sigma>')")
   prefer 2
   apply (simp add: step_def)
   apply clarify
  apply (subgoal_tac " \<tau> \<sigma>' =
           cas_fail_trans t ind glb (regs (\<tau> \<sigma>) t DTML.loc)
            (regs (\<tau> \<sigma>) t DTML.loc) c1 (\<tau> \<sigma>)")
  prefer 2
  apply (metis cas_suc_reg zero_neq_one)
  apply (metis assms(4) cas_fail_mem_same)
  apply (simp add:  cas_fail_trans_def )
  apply (unfold  mem_structured_def)
  by (smt (z3) survived_val_preserved_cas)




(* \<tau> \<sigma> [a := v]\<^sub>t \<tau> \<sigma>'*)
lemma st_ni_glb_monotone_preserved_spec:
 assumes "  glb_monotone_inv  (\<tau> \<sigma>) "
 and "vbounded (\<tau> \<sigma>)"
and "mem_structured (\<tau> \<sigma>)"
and "  step t ( Store  a v ) (\<tau> \<sigma>)  (\<tau> \<sigma>' )"
and "a \<noteq> glb"
(*and "  \<lceil>glb\<rceil>\<^sub>t ts "*)
and " \<forall> ti l. last_entry (\<tau> \<sigma>) l \<in>   OTS (\<tau> \<sigma>) ti l "
and " \<forall> ti l. lastVal  l (\<tau> \<sigma>)  \<in>  [l]\<^sub>ti (\<tau> \<sigma>) " 
shows   " glb_monotone_inv  (\<tau> \<sigma>') "
 using assms
  apply (unfold glb_monotone_inv_def)
  using  st_ni_glb_monotonicity_preserved [where  glb = glb and t = t ]
  by presburger


lemma st_ni_glb_monotone_complete_preserved_spec:
 assumes "  glb_monotone_complete_inv  (\<tau> \<sigma>) "
 and "vbounded (\<tau> \<sigma>)"
and "mem_structured (\<tau> \<sigma>)"
and "  step t ( Store  a v ) (\<tau> \<sigma>)  (\<tau> \<sigma>' )"
and "a \<noteq> glb"
(*and "  \<lceil>glb\<rceil>\<^sub>t ts "*)
and " \<forall> ti l. last_entry (\<tau> \<sigma>) l \<in>   OTS (\<tau> \<sigma>) ti l "
and " \<forall> ti l. lastVal  l (\<tau> \<sigma>)  \<in>  [l]\<^sub>ti (\<tau> \<sigma>) " 
shows   " glb_monotone_complete_inv  (\<tau> \<sigma>') "
 using assms
  apply (unfold glb_monotone_complete_inv_def)
  using   st_ni_glb_complete_monotonicity_preserved [where  glb = glb and t = t ]
  by metis








(*1*)
(*inv for write*)
lemma write_glb_monotone_inv:
  assumes "thrdsvars"
      and "total_wfs (\<tau> \<sigma>)"
      and "TML_Write  t    \<sigma> \<sigma>'"
and " \<forall>  t.  glb_monotone_inv  (\<tau> \<sigma>) "
 and "  Write_inv  t  ((pc \<sigma>) t) \<sigma>  " 
shows " \<forall>  t.  glb_monotone_inv (\<tau> \<sigma>') "
   using assms
  apply (simp add:TML_Write_def total_wfs_def Write_inv_def)
  apply (cases "pc \<sigma> t";  simp  )
        apply  (simp add: split: if_split_asm)
         apply  (simp add: split: if_split_asm)

          apply (subgoal_tac " memory (\<tau> \<sigma>')  = memory (\<tau> \<sigma>)  ")
   prefer 2
   using  cas_fail_mem_same 
           apply presburger
          apply (simp add: glb_monotone_inv_def)
 apply (subgoal_tac   "(\<forall>i.(i\<ge>0\<and>i<length(memory (\<tau> \<sigma>))) \<longrightarrow> ( memory (\<tau> \<sigma>))!i =( memory (\<tau> \<sigma>'))!i) ")
    prefer 2
          apply (metis cas_lc mem_l_cas_succ_step neq0_conv)

         apply (simp add: step_def)
         apply clarify
   apply (subgoal_tac "  \<tau> \<sigma>' =
       cas_succ_trans t (last_entry (\<tau> \<sigma>) glb) glb (regs (\<tau> \<sigma>) t DTML.loc)
        (Suc (regs (\<tau> \<sigma>) t DTML.loc)) c1 nv mnv (\<tau> \<sigma>) ")
          prefer 2
           apply (metis cas_fail_reg zero_less_iff_neq_zero)
          apply (subgoal_tac "\<lceil>  glb: (regs (\<tau> \<sigma>) t DTML.loc) \<rceil> (\<tau> \<sigma>) ")
           prefer 2
           apply (metis cas_fail_reg compval_def zero_less_iff_neq_zero)
 using   cas_succ_glb_monotone_preserved_spec
  apply (metis PC.distinct(19) PC.distinct(229) PC.distinct(401) PC.distinct(403) PC.distinct(405) PC.distinct(407) PC.distinct(409) PC.distinct(411) PC.distinct(413) PC.distinct(417))

      apply (subgoal_tac " memory (\<tau> \<sigma>')  = memory (\<tau> \<sigma>)  ")
       prefer 2
  using reg_write_mem apply presburger

  using glb_monotone_inv_def
       apply (metis PC.distinct(21) PC.distinct(231) PC.distinct(427) PC.distinct(429) PC.distinct(431) PC.distinct(433) PC.distinct(435) PC.distinct(437) PC.distinct(439) PC.distinct(443) reg_write__crash)


  using ld_monotone_preserved glb_monotone_inv_def 
  apply (metis ld_crash ld_step_mem)

  using  st_ni_glb_monotone_preserved_spec [where t = t ]
  apply (metis PC.distinct(237) PC.distinct(27) PC.distinct(493) PC.distinct(495) PC.distinct(497) PC.distinct(499) PC.distinct(501) PC.distinct(503) PC.distinct(505) PC.distinct(509))
     apply (subgoal_tac " memory (\<tau> \<sigma>')  = memory (\<tau> \<sigma>)  ")
    prefer 2
  apply (simp add: step_def)
   apply (unfold glb_monotone_inv_def)
  by (smt (z3) PC.distinct(239) PC.distinct(29) PC.distinct(511) PC.distinct(513) PC.distinct(515) PC.distinct(517) PC.distinct(519) PC.distinct(521) PC.distinct(523) PC.distinct(527) flo_crash)


(*1*)
lemma write_glb_monotone_complete_inv:
  assumes "thrdsvars"
      and "total_wfs (\<tau> \<sigma>)"
      and "TML_Write  t    \<sigma> \<sigma>'"
and " \<forall>  t.  glb_monotone_complete_inv  (\<tau> \<sigma>) "
 and "  Write_inv  t  ((pc \<sigma>) t) \<sigma>  " 
shows " \<forall>  t.  glb_monotone_complete_inv (\<tau> \<sigma>') "
  using assms
  apply (simp add:TML_Write_def total_wfs_def Write_inv_def)
  apply (cases "pc \<sigma> t";  simp  )
        apply  (simp add: split: if_split_asm)
         apply  (simp add: split: if_split_asm)
          apply (subgoal_tac " memory (\<tau> \<sigma>')  = memory (\<tau> \<sigma>)  ")
   prefer 2
   using  cas_fail_mem_same 
           apply presburger
        apply (simp add:  glb_monotone_complete_inv_def)
        apply (subgoal_tac " survived_val (\<tau> \<sigma>') glb  =  survived_val (\<tau> \<sigma>) glb  ")
         prefer 2
   using survived_val_preserved_cas apply presburger
   apply presburger
 apply (subgoal_tac   "(\<forall>i.(i\<ge>0\<and>i<length(memory (\<tau> \<sigma>))) \<longrightarrow> ( memory (\<tau> \<sigma>))!i =( memory (\<tau> \<sigma>'))!i) ")
    prefer 2
          apply (metis cas_lc mem_l_cas_succ_step neq0_conv)
         apply (simp add: step_def)
         apply clarify
   apply (subgoal_tac "  \<tau> \<sigma>' =
       cas_succ_trans t (last_entry (\<tau> \<sigma>) glb) glb (regs (\<tau> \<sigma>) t DTML.loc)
        (Suc (regs (\<tau> \<sigma>) t DTML.loc)) c1 nv mnv (\<tau> \<sigma>) ")
          prefer 2
           apply (metis cas_fail_reg zero_less_iff_neq_zero)
          apply (subgoal_tac "\<lceil>  glb: (regs (\<tau> \<sigma>) t DTML.loc) \<rceil> (\<tau> \<sigma>) ")
           prefer 2
           apply (metis cas_fail_reg compval_def zero_less_iff_neq_zero)
   using   cas_succ_glb_monotone_complete_preserved_spec
  apply (metis PC.distinct(19) PC.distinct(229) PC.distinct(401) PC.distinct(403) PC.distinct(405) PC.distinct(407) PC.distinct(409) PC.distinct(411) PC.distinct(413) PC.distinct(417))

      apply (subgoal_tac " memory (\<tau> \<sigma>')  = memory (\<tau> \<sigma>)  ")
       prefer 2
  using reg_write_mem apply presburger
  using glb_monotone_complete_inv_def
       apply (metis PC.distinct(21) PC.distinct(231) PC.distinct(427) PC.distinct(429) PC.distinct(431) PC.distinct(433) PC.distinct(435) PC.distinct(437) PC.distinct(439) PC.distinct(443) reg_write__crash)
  using ld_monotone_preserved glb_monotone_complete_inv_def 
  apply (metis ld_crash ld_step_mem)
  using  st_ni_glb_monotone_complete_preserved_spec [where t = t ]
  apply (metis PC.distinct(237) PC.distinct(27) PC.distinct(493) PC.distinct(495) PC.distinct(497) PC.distinct(499) PC.distinct(501) PC.distinct(503) PC.distinct(505) PC.distinct(509))
     apply (subgoal_tac " memory (\<tau> \<sigma>')  = memory (\<tau> \<sigma>)  ")
    prefer 2
  apply (simp add: step_def)
   apply (unfold glb_monotone_complete_inv_def)
  by (smt (z3) PC.distinct(239) PC.distinct(29) PC.distinct(511) PC.distinct(513) PC.distinct(515) PC.distinct(517) PC.distinct(519) PC.distinct(521) PC.distinct(523) PC.distinct(527) flo_crash)




(*2*)
(*inv for commit*)
lemma commit_glb_monotone_inv:
 assumes "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
  and "  Commit_inv  t   ((pc \<sigma>) t) \<sigma>  "
  and "TML_Commit  t   \<sigma> \<sigma>'"
and " \<forall>  t.  glb_monotone_inv  (\<tau> \<sigma>) "
shows " \<forall>  t.  glb_monotone_inv (\<tau> \<sigma>') "
  using assms
  apply (simp add: TML_Commit_def Commit_inv_def  total_wfs_def  )
  apply (cases "pc \<sigma> t";  simp add: split if_splits)
          apply (subgoal_tac " memory (\<tau> \<sigma>')  = memory (\<tau> \<sigma>)  ")
       prefer 2
       apply (metis step_mem_sfence)
     apply (unfold glb_monotone_inv_def)
   apply (smt (z3) PC.distinct(121) PC.distinct(123) PC.distinct(125) PC.distinct(127) PC.distinct(129) PC.distinct(131) PC.distinct(133) PC.distinct(137) PC.distinct(3) PC.distinct(99) sfence_crash)
   apply (subgoal_tac " \<lceil>glb: (lastVal glb (\<tau> \<sigma>))\<rceil> (\<tau> \<sigma>) ")
    prefer 2
    apply (metis lastVal_def)
  using st_glb_monotone_preserved  [where t = t and glb = glb ]
  by (metis (no_types, lifting))

(*2*)
lemma commit_glb_monotone_commit_inv:
 assumes "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
  and "  Commit_inv  t   ((pc \<sigma>) t) \<sigma>  "
  and "TML_Commit  t   \<sigma> \<sigma>'"
and " \<forall>  t.   glb_monotone_complete_inv  (\<tau> \<sigma>) "
shows " \<forall>  t.  glb_monotone_complete_inv (\<tau> \<sigma>') "
  using assms
  apply (simp add: TML_Commit_def Commit_inv_def  total_wfs_def  )
  apply (cases "pc \<sigma> t";  simp add: split if_splits)
          apply (subgoal_tac " memory (\<tau> \<sigma>')  = memory (\<tau> \<sigma>)  ")
       prefer 2
       apply (metis step_mem_sfence)
     apply (unfold  glb_monotone_complete_inv_def)
   apply (smt (z3) PC.distinct(121) PC.distinct(123) PC.distinct(125) PC.distinct(127) PC.distinct(129) PC.distinct(131) PC.distinct(133) PC.distinct(137) PC.distinct(3) PC.distinct(99) sfence_crash)
   apply (subgoal_tac " \<lceil>glb: (lastVal glb (\<tau> \<sigma>))\<rceil> (\<tau> \<sigma>) ")
    prefer 2
    apply (metis lastVal_def)
  using st_glb_monotone_complete_preserved  [where t = t and glb = glb ]
  by (metis (no_types, lifting))







(*3*)
(*and " \<forall>  t. ((pc \<sigma>) t \<in> recovering \<union> beginning \<union> { Aborted, Committed})  \<or> glb_monotone_inv  (\<tau> \<sigma>) "*)
(*inv for begin*)
lemma  begin_glb_monotone_inv:
  assumes "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
  and "TML_Begin  t   \<sigma> \<sigma>'"
  and "  Begin_inv  t  ((pc \<sigma>) t) \<sigma>   "
and " \<forall>  t.  glb_monotone_inv  (\<tau> \<sigma>) "
shows " \<forall>  t. glb_monotone_inv (\<tau> \<sigma>') "
  using assms
  apply (simp add: TML_Begin_def Begin_inv_def  total_wfs_def )
  apply (cases "pc \<sigma> t";  simp add: split if_splits)

 apply (subgoal_tac " memory (\<tau> \<sigma>')  = memory (\<tau> \<sigma>)  ")
    prefer 2
  apply (simp add: step_def)
  apply (metis mem_ld_trans)

   apply (unfold glb_monotone_inv_def)
   apply simp
   apply (elim conjE)
  by (metis ld_crash ld_step_mem)
 


(*3*)
lemma  begin_glb_monotone_complete_inv:
  assumes "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
  and "TML_Begin  t   \<sigma> \<sigma>'"
  and "  Begin_inv  t  ((pc \<sigma>) t) \<sigma>   "
and " \<forall>  t.  glb_monotone_complete_inv  (\<tau> \<sigma>) "
shows " \<forall>  t. glb_monotone_complete_inv (\<tau> \<sigma>') "
  using assms
  apply (simp add: TML_Begin_def Begin_inv_def  total_wfs_def )
  apply (cases "pc \<sigma> t";  simp add: split if_splits)

 apply (subgoal_tac " memory (\<tau> \<sigma>')  = memory (\<tau> \<sigma>)  ")
    prefer 2
  apply (simp add: step_def)
  apply (metis mem_ld_trans)

   apply (unfold glb_monotone_complete_inv_def)
   apply simp
  apply (smt (z3) survived_val_preserved_load)
  apply (elim conjE)
  by metis









(*4*)
(* \<lceil>glb: (lastVal glb (\<tau> \<sigma>))\<rceil> remember this (i dont remember why to remember this, check again) *)
lemma  read_glb_monotone_inv:
   assumes "thrdsvars"
   and "total_wfs (\<tau> \<sigma>)"
   and "TML_Read  t   \<sigma> \<sigma>'"
    and "((pc \<sigma>) t) \<in> reading \<union>{Ready} \<union> {Aborted} "
      and "Read_inv t  ((pc \<sigma>) t) \<sigma>" 
and " \<forall>  t.  glb_monotone_inv  (\<tau> \<sigma>) "
shows " \<forall>  t. glb_monotone_inv (\<tau> \<sigma>') "
  using assms
  apply (unfold  total_wfs_def )
  apply (simp add:TML_Read_def Read_inv_def  )
  apply (cases "pc \<sigma> t";   simp add: split if_splits)
  apply ( simp add: split: if_split_asm)
      apply (simp add: glb_monotone_inv_def)
      apply (subgoal_tac " memory (\<tau> \<sigma>) = memory (\<tau> \<sigma>') ")
       prefer 2
  using ld_step_mem apply presburger
  apply (subgoal_tac"  mem_structured (\<tau> \<sigma>') ")
  prefer 2
       apply (meson mem_structured_preserved)
      apply (unfold mem_structured_def)
      apply simp
  apply metis
  apply metis 
      apply(case_tac " regs (\<tau> \<sigma>') t c1 = Suc 0")
       apply simp 
 apply (subgoal_tac   "(\<forall>i.(i\<ge>0\<and>i<length(memory (\<tau> \<sigma>))) \<longrightarrow> ( memory (\<tau> \<sigma>))!i =( memory (\<tau> \<sigma>'))!i) ")
      prefer 2
  apply (metis assms(2) mem_l_cas_succ_step numeral_1_eq_Suc_0 numerals(1) total_wfs_def)
        apply (simp add: step_def)
         apply clarify
   apply (subgoal_tac "   \<tau> \<sigma>' = cas_succ_trans t ind glb (regs (\<tau> \<sigma>) t DTML.loc) (regs (\<tau> \<sigma>) t DTML.loc) c1 nv mnv (\<tau> \<sigma>) ")
      prefer 2
  apply (metis assms(2) cas_fail_reg n_not_Suc_n total_wfs_def)
          apply (subgoal_tac "\<lceil>  glb: (regs (\<tau> \<sigma>) t DTML.loc) \<rceil> (\<tau> \<sigma>) ")
      prefer 2
  apply (metis assms(2) cas_fail_reg compval_def n_not_Suc_n total_wfs_def)
 
  using  cas_succ_read_glb_monotone_preserved_spec [where \<sigma> = \<sigma> and t = t  ] 
  apply (metis assms(2) cas_fail_reg numeral_1_eq_Suc_0 numeral_eq_one_iff total_wfs_def zero_neq_one)
   
     apply (unfold glb_monotone_inv_def)
     apply (subgoal_tac " regs (\<tau> \<sigma>') t c1 =  0  ")
     prefer 2
  apply (metis assms(2) cas_lc numeral_1_eq_Suc_0 numerals(1) total_wfs_def)
  using  cas_fail_read_glb_monotone_preserved_spec [where t = t and \<sigma> = \<sigma> and \<sigma>' = \<sigma>'] 
    apply (metis mem_structured_def)
 apply (simp add: glb_monotone_inv_def)
      apply (subgoal_tac " memory (\<tau> \<sigma>) = memory (\<tau> \<sigma>') ")
       prefer 2
  using ld_step_mem 
  apply (metis mem_structured_def)
  apply (subgoal_tac"  mem_structured (\<tau> \<sigma>') ")
  prefer 2
  apply (metis mem_structured_def)
  apply simp
  using mem_structured_def apply blast
  by presburger


(*4*)
lemma  read_glb_monotone_completed_inv:
   assumes "thrdsvars"
   and "total_wfs (\<tau> \<sigma>)"
   and "TML_Read  t   \<sigma> \<sigma>'"
    and "((pc \<sigma>) t) \<in> reading \<union>{Ready} \<union> {Aborted} "
      and "Read_inv t  ((pc \<sigma>) t) \<sigma>" 
and " \<forall>  t.  glb_monotone_complete_inv  (\<tau> \<sigma>) "
shows " \<forall>  t. glb_monotone_complete_inv (\<tau> \<sigma>') "
  using assms
  apply (unfold  total_wfs_def )
  apply (simp add:TML_Read_def Read_inv_def  )
  apply (cases "pc \<sigma> t";   simp add: split if_splits)
  apply ( simp add: split: if_split_asm)
      apply (simp add: glb_monotone_complete_inv_def)
      apply (subgoal_tac " memory (\<tau> \<sigma>) = memory (\<tau> \<sigma>') ")
       prefer 2
  using ld_step_mem apply presburger
  apply (subgoal_tac"  mem_structured (\<tau> \<sigma>') ")
  prefer 2
       apply (meson mem_structured_preserved)
      apply (unfold mem_structured_def)
      apply simp
  apply (smt (z3) survived_val_preserved_load)


     apply metis

(*  apply metis *)
      apply(case_tac " regs (\<tau> \<sigma>') t c1 = Suc 0")
       apply simp 
 apply (subgoal_tac   "(\<forall>i.(i\<ge>0\<and>i<length(memory (\<tau> \<sigma>))) \<longrightarrow> ( memory (\<tau> \<sigma>))!i =( memory (\<tau> \<sigma>'))!i) ")
      prefer 2
  apply (metis assms(2) mem_l_cas_succ_step numeral_1_eq_Suc_0 numerals(1) total_wfs_def)
        apply (simp add: step_def)
         apply clarify
   apply (subgoal_tac "   \<tau> \<sigma>' = cas_succ_trans t ind glb (regs (\<tau> \<sigma>) t DTML.loc) (regs (\<tau> \<sigma>) t DTML.loc) c1 nv mnv (\<tau> \<sigma>) ")
      prefer 2
  apply (metis assms(2) cas_fail_reg n_not_Suc_n total_wfs_def)
          apply (subgoal_tac "\<lceil>  glb: (regs (\<tau> \<sigma>) t DTML.loc) \<rceil> (\<tau> \<sigma>) ")
      prefer 2
  apply (metis assms(2) cas_fail_reg compval_def n_not_Suc_n total_wfs_def)
 
  using  cas_succ_read_glb_monotone_complete_preserved_spec [where \<sigma> = \<sigma> and t = t  ] 
  apply (metis assms(2) cas_fail_reg numeral_1_eq_Suc_0 numeral_eq_one_iff total_wfs_def zero_neq_one)
   
     apply (unfold glb_monotone_complete_inv_def)
     apply (subgoal_tac " regs (\<tau> \<sigma>') t c1 =  0  ")
     prefer 2
  apply (metis assms(2) cas_lc numeral_1_eq_Suc_0 numerals(1) total_wfs_def)
  using  cas_fail_read_glb_monotone_complete_preserved_spec [where t = t and \<sigma> = \<sigma> and \<sigma>' = \<sigma>'] 
    apply (metis mem_structured_def)
 apply (simp add: glb_monotone_complete_inv_def)
      apply (subgoal_tac " memory (\<tau> \<sigma>) = memory (\<tau> \<sigma>') ")
       prefer 2
  using ld_step_mem 
  apply (metis mem_structured_def)
  apply (subgoal_tac"  mem_structured (\<tau> \<sigma>') ")
  prefer 2
  apply (metis mem_structured_def)
   apply simp

  apply (subgoal_tac "   survived_val (\<tau> \<sigma>') glb  =   survived_val (\<tau> \<sigma>) glb  ")
  prefer 2
  apply (metis survived_val_preserved_load)
   apply (unfold   mem_structured_def)
  apply (smt (z3))
  by presburger

 





(*5*)
lemma crash_glb_monotone_inv:
assumes  "thrdsvars"
and "TML_Crash  \<sigma> \<sigma>'"
and " \<forall>  t.  glb_monotone_inv  (\<tau> \<sigma>) "
shows " \<forall>  t. glb_monotone_inv (\<tau> \<sigma>') "
  using assms
  apply (simp add: TML_Crash_def  total_wfs_def  glb_monotone_inv_def)
  by (simp add:  crash_step_def)



(*5*)
lemma crash_glb_monotone_complete_inv:
assumes  "thrdsvars"
and "TML_Crash  \<sigma> \<sigma>'"
and " \<forall>  t.  glb_monotone_complete_inv  (\<tau> \<sigma>) "
shows " \<forall>  t. glb_monotone_complete_inv (\<tau> \<sigma>') "
  using assms
  apply (simp add: TML_Crash_def  total_wfs_def  glb_monotone_complete_inv_def)
  by (simp add:  crash_step_def)






(*6*)
lemma recover_glb_monotone_inv:
 assumes "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
  and " TML_Recover syst   \<sigma> \<sigma>' "
 and "  Recover_inv  syst  ((pc \<sigma>) syst)  \<sigma>"
(*and " thread_prop_comp  \<sigma> t "*)
  and "((pc \<sigma>) syst) \<in> {RecIdle} \<union> recovering "
and " \<forall> ti l. last_entry (\<tau> \<sigma>) l \<in>   OTS (\<tau> \<sigma>) ti l "
and " \<forall> ti l. lastVal  l (\<tau> \<sigma>)  \<in>  [l]\<^sub>ti (\<tau> \<sigma>) " 
and " \<forall>  t.  glb_monotone_inv  (\<tau> \<sigma>) "
shows " \<forall>  t. glb_monotone_inv (\<tau> \<sigma>') "
 using assms


  apply (simp add: TML_Recover_def Recover_inv_def   )
  apply (cases "pc \<sigma> syst";  simp add: split if_splits)

 apply (subgoal_tac " memory (\<tau> \<sigma>')  = memory (\<tau> \<sigma>)  ")
       prefer 2
  using reg_write_mem apply presburger
  using glb_monotone_inv_def
       apply (metis PC.distinct(21) PC.distinct(231) PC.distinct(427) PC.distinct(429) PC.distinct(431) PC.distinct(433) PC.distinct(435) PC.distinct(437) PC.distinct(439) PC.distinct(443) reg_write__crash)
     apply (subgoal_tac " get_key (log \<sigma>)  \<noteq> glb ")
      prefer 2
      apply (simp add:  get_key_def)
      apply (metis get_key_in_dom verit_sko_ex_indirect)
  using st_ni_glb_monotone_preserved_spec [where \<sigma> = \<sigma> and \<sigma>' = \<sigma>' and t = syst]
  using total_wfs_def
  apply meson
   apply (subgoal_tac " memory (\<tau> \<sigma>')  = memory (\<tau> \<sigma>)  ")
    prefer 2
  apply (simp add: step_def)
   apply (unfold glb_monotone_inv_def)
     apply (metis flo_crash)
 apply (subgoal_tac " memory (\<tau> \<sigma>')  = memory (\<tau> \<sigma>)  ")
    prefer 2
  apply (metis assms(2) step_mem_sfence total_wfs_def)
    apply (metis sfence_crash)
 apply (subgoal_tac " memory (\<tau> \<sigma>')  = memory (\<tau> \<sigma>)  ")
    prefer 2
       apply (simp add: step_def)
       apply (metis mem_ld_trans)
  apply metis
     apply (case_tac "  even (regs (\<tau> \<sigma>) syst c1) ")
  apply presburger
     apply presburger

  apply (subgoal_tac " (\<forall>i. 0 < i \<and> i < length (memory (\<tau> \<sigma>)) \<longrightarrow> Msg.loc (memory (\<tau> \<sigma>') ! i) \<noteq> glb) ")
  prefer 2
     apply (metis mem_l_step zero_le)
  apply (metis (no_types, opaque_lifting) Suc_eq_plus1 le_eq_less_or_eq less_trans_Suc nat_neq_iff st_mem_length)
  apply (subgoal_tac " (\<forall>i. 0 < i \<and> i < length (memory (\<tau> \<sigma>)) \<longrightarrow> Msg.loc (memory (\<tau> \<sigma>') ! i) \<noteq> glb) ")
  prefer 2
  apply (metis mem_l_step zero_le)
  apply (metis add.commute le_eq_less_or_eq linorder_neqE_nat not_less_eq plus_1_eq_Suc st_mem_length)
  by presburger



(*6*)
lemma recover_glb_monotone_complete_inv:
 assumes "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
  and " TML_Recover syst   \<sigma> \<sigma>' "
 and "  Recover_inv  syst  ((pc \<sigma>) syst)  \<sigma>"
and "  compval (\<tau> \<sigma>) (memory (\<tau> \<sigma>) ! 0) glb = survived_val (\<tau> \<sigma>) glb"
(*and " thread_prop_comp  \<sigma> t "*)
  and "((pc \<sigma>) syst) \<in> {RecIdle} \<union> recovering "
and " \<forall> ti l. last_entry (\<tau> \<sigma>) l \<in>   OTS (\<tau> \<sigma>) ti l "
and " \<forall> ti l. lastVal  l (\<tau> \<sigma>)  \<in>  [l]\<^sub>ti (\<tau> \<sigma>) " 
and " \<forall>  t.  glb_monotone_complete_inv  (\<tau> \<sigma>) "
shows " \<forall>  t. glb_monotone_complete_inv (\<tau> \<sigma>') "
 using assms
  apply (simp add: TML_Recover_def Recover_inv_def   )
  apply (cases "pc \<sigma> syst";  simp add: split if_splits)

 apply (subgoal_tac " memory (\<tau> \<sigma>')  = memory (\<tau> \<sigma>)  ")
       prefer 2
  using reg_write_mem apply presburger
  using glb_monotone_complete_inv_def
       apply (metis PC.distinct(21) PC.distinct(231) PC.distinct(427) PC.distinct(429) PC.distinct(431) PC.distinct(433) PC.distinct(435) PC.distinct(437) PC.distinct(439) PC.distinct(443) reg_write__crash)
     apply (subgoal_tac " get_key (log \<sigma>)  \<noteq> glb ")
      prefer 2
      apply (simp add:  get_key_def)
      apply (metis get_key_in_dom verit_sko_ex_indirect)
  using st_ni_glb_monotone_complete_preserved_spec [where \<sigma> = \<sigma> and \<sigma>' = \<sigma>' and t = syst]
  using total_wfs_def
  apply meson
   apply (subgoal_tac " memory (\<tau> \<sigma>')  = memory (\<tau> \<sigma>)  ")
    prefer 2
  apply (simp add: step_def)
   apply (unfold  glb_monotone_complete_inv_def)
     apply (metis flo_crash)
 apply (subgoal_tac " memory (\<tau> \<sigma>')  = memory (\<tau> \<sigma>)  ")
    prefer 2
  apply (metis assms(2) step_mem_sfence total_wfs_def)
    apply (metis sfence_crash)
 apply (subgoal_tac " memory (\<tau> \<sigma>')  = memory (\<tau> \<sigma>)  ")
    prefer 2
       apply (simp add: step_def)
       apply (metis mem_ld_trans)
  apply (metis ld_crash)
     apply metis

apply (subgoal_tac " (\<forall>i. 0 <  i \<and> i < length (memory (\<tau> \<sigma>)) \<longrightarrow>   Msg.loc (memory (\<tau> \<sigma>') ! i) \<noteq> glb )   ")
     prefer 2
     apply (metis mem_l_step zero_le)

apply (subgoal_tac " (\<forall>i. 0 <  i \<and> i < length (memory (\<tau> \<sigma>)) \<longrightarrow>   comploc (memory (\<tau> \<sigma>') ! i) glb \<noteq> glb )   ")
     prefer 2
  using loc_eq_comploc total_wfs_def 
  apply (metis assms(1) comploc_wr_same less_or_eq_imp_le)

    apply (subgoal_tac "comploc (memory (\<tau> \<sigma>)!0) glb =  glb")
     prefer 2
     apply (simp add: comploc_def total_wfs_def )

  apply (subgoal_tac "comploc (memory (\<tau> \<sigma>')!  (length( memory (\<tau> \<sigma>)))   )   glb =  glb")
     prefer 2
  apply (metis comploc_def st_loc)

  apply (subgoal_tac "compval (\<tau> \<sigma>') (memory (\<tau> \<sigma>')!  (length( memory (\<tau> \<sigma>)))   )   glb = Suc (Suc (survived_val (\<tau> \<sigma>) glb)) ")
     prefer 2
  apply (unfold total_wfs_def)
  apply (metis Store_Rules.st_lv_lc st_lastEntry_lc)
  apply (metis assms(2) compval_def last_entry_last_comp_loc le_Suc_eq le_eq_less_or_eq le_numeral_extra(3) mem_l_step nat_le_linear st_lastEntry_lc st_wfs_preserved survived_val_preserved_store)
  apply (smt (z3) Suc_n_not_le_n assms(2) compval_def last_entry_last_comp_loc le_eq_less_or_eq loc_eq_comploc mem_l_step nat_le_linear st_lastEntry_lc st_val st_wfs_preserved survived_val_preserved_store)
  by presburger




lemma beginInv_glb_monotone_complete_inv:
assumes  "thrdsvars"
and "TML_Begin_invocation t  \<sigma> \<sigma>'"
  and " Begin_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
and " \<forall>  t.  glb_monotone_complete_inv  (\<tau> \<sigma>) "
shows " \<forall>  t. glb_monotone_complete_inv (\<tau> \<sigma>') "
  using assms
  apply (simp add: TML_Begin_invocation_def Begin_invocation_inv_def total_wfs_def )
  by  (cases "pc \<sigma> t";  simp )




lemma beginResp_glb_monotone_complete_inv:
assumes  "thrdsvars"
and "TML_Begin_response t  \<sigma> \<sigma>'"
and " \<forall>  t.  glb_monotone_complete_inv  (\<tau> \<sigma>) "
shows " \<forall>  t. glb_monotone_complete_inv (\<tau> \<sigma>') "
  using assms
  apply (simp add: TML_Begin_response_def total_wfs_def )
  by (cases "pc \<sigma> t";  simp)



lemma readInv_glb_monotone_complete_inv:
assumes  "thrdsvars"
and "TML_Read_invocation t  \<sigma> \<sigma>'"
  and " Begin_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
and " \<forall>  t.  glb_monotone_complete_inv  (\<tau> \<sigma>) "
shows " \<forall>  t. glb_monotone_complete_inv (\<tau> \<sigma>') "
  using assms
  apply (simp add: TML_Read_invocation_def Begin_invocation_inv_def total_wfs_def )
  by  (cases "pc \<sigma> t";  simp )




lemma readResp_glb_monotone_complete_inv:
assumes  "thrdsvars"
and "TML_Read_response t  \<sigma> \<sigma>'"
and " \<forall>  t.  glb_monotone_complete_inv  (\<tau> \<sigma>) "
shows " \<forall>  t. glb_monotone_complete_inv (\<tau> \<sigma>') "
  using assms
  apply (simp add: TML_Read_response_def total_wfs_def )
  by (cases "pc \<sigma> t";  simp )
 


lemma writeInv_glb_monotone_complete_inv:
assumes  "thrdsvars"
and "TML_Write_invocation t  \<sigma> \<sigma>'"
  and " Write_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
and " \<forall>  t.  glb_monotone_complete_inv  (\<tau> \<sigma>) "
shows " \<forall>  t. glb_monotone_complete_inv (\<tau> \<sigma>') "
  using assms
  apply (simp add: TML_Write_invocation_def  total_wfs_def )
  by  (cases "pc \<sigma> t";  simp )



lemma writeResp_glb_monotone_complete_inv:
assumes  "thrdsvars"
and "TML_Write_response t  \<sigma> \<sigma>'"
 and " Write_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
and " \<forall>  t.  glb_monotone_complete_inv  (\<tau> \<sigma>) "
shows " \<forall>  t. glb_monotone_complete_inv (\<tau> \<sigma>') "
  using assms
  apply (simp add: TML_Write_response_def total_wfs_def )
  by  (cases "pc \<sigma> t";  simp )




lemma commitInv_glb_monotone_complete_inv:
assumes  "thrdsvars"
and "TML_Commit_invocation t  \<sigma> \<sigma>'"
  and " Commit_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
and " \<forall>  t.  glb_monotone_complete_inv  (\<tau> \<sigma>) "
shows " \<forall>  t. glb_monotone_complete_inv (\<tau> \<sigma>') "
  using assms
  apply (simp add: TML_Commit_invocation_def total_wfs_def )
  by(cases "pc \<sigma> t";  simp)






lemma commitResp_glb_monotone_complete_inv:
assumes  "thrdsvars"
and "TML_Commit_response t  \<sigma> \<sigma>'"
and " \<forall>  t.  glb_monotone_complete_inv  (\<tau> \<sigma>) "
shows " \<forall>  t. glb_monotone_complete_inv (\<tau> \<sigma>') "
  using assms
  apply (simp add: TML_Commit_response_def total_wfs_def )
  by (cases "pc \<sigma> t";  simp)






lemma beginInv_glb_monotone_inv:
assumes  "thrdsvars"
and "TML_Begin_invocation t  \<sigma> \<sigma>'"
  and " Begin_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
and " \<forall>  t.  glb_monotone_inv  (\<tau> \<sigma>) "
shows " \<forall>  t. glb_monotone_inv (\<tau> \<sigma>') "
  using assms
  apply (simp add: TML_Begin_invocation_def Begin_invocation_inv_def total_wfs_def )
  by  (cases "pc \<sigma> t";  simp )




lemma beginResp_glb_monotone_inv:
assumes  "thrdsvars"
and "TML_Begin_response t  \<sigma> \<sigma>'"
and " \<forall>  t.  glb_monotone_inv  (\<tau> \<sigma>) "
shows " \<forall>  t. glb_monotone_inv (\<tau> \<sigma>') "
  using assms
  apply (simp add: TML_Begin_response_def total_wfs_def )
  by (cases "pc \<sigma> t";  simp)



lemma readInv_glb_monotone__inv:
assumes  "thrdsvars"
and "TML_Read_invocation t  \<sigma> \<sigma>'"
  and " Begin_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
and " \<forall>  t.  glb_monotone_inv  (\<tau> \<sigma>) "
shows " \<forall>  t. glb_monotone_inv (\<tau> \<sigma>') "
  using assms
  apply (simp add: TML_Read_invocation_def Begin_invocation_inv_def total_wfs_def )
  by  (cases "pc \<sigma> t";  simp )




lemma readResp_glb_monotone_inv:
assumes  "thrdsvars"
and "TML_Read_response t  \<sigma> \<sigma>'"
and " \<forall>  t.  glb_monotone_inv  (\<tau> \<sigma>) "
shows " \<forall>  t. glb_monotone_inv (\<tau> \<sigma>') "
  using assms
  apply (simp add: TML_Read_response_def total_wfs_def )
  by (cases "pc \<sigma> t";  simp )
 


lemma writeInv_glb_monotone_inv:
assumes  "thrdsvars"
and "TML_Write_invocation t  \<sigma> \<sigma>'"
  and " Write_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
and " \<forall>  t.  glb_monotone_inv  (\<tau> \<sigma>) "
shows " \<forall>  t. glb_monotone_inv (\<tau> \<sigma>') "
  using assms
  apply (simp add: TML_Write_invocation_def  total_wfs_def )
  by  (cases "pc \<sigma> t";  simp )



lemma writeResp_glb_monotone_inv:
assumes  "thrdsvars"
and "TML_Write_response t  \<sigma> \<sigma>'"
 and " Write_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
and " \<forall>  t.  glb_monotone_inv  (\<tau> \<sigma>) "
shows " \<forall>  t. glb_monotone_inv (\<tau> \<sigma>') "
  using assms
  apply (simp add: TML_Write_response_def total_wfs_def )
  by  (cases "pc \<sigma> t";  simp )




lemma commitInv_glb_monotone_inv:
assumes  "thrdsvars"
and "TML_Commit_invocation t  \<sigma> \<sigma>'"
  and " Commit_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
and " \<forall>  t.  glb_monotone_inv  (\<tau> \<sigma>) "
shows " \<forall>  t. glb_monotone_inv (\<tau> \<sigma>') "
  using assms
  apply (simp add: TML_Commit_invocation_def total_wfs_def )
  by(cases "pc \<sigma> t";  simp)






lemma commitResp_glb_monotone_inv:
assumes  "thrdsvars"
and "TML_Commit_response t  \<sigma> \<sigma>'"
and " \<forall>  t.  glb_monotone_inv  (\<tau> \<sigma>) "
shows " \<forall>  t. glb_monotone_inv (\<tau> \<sigma>') "
  using assms
  apply (simp add: TML_Commit_response_def total_wfs_def )
  by (cases "pc \<sigma> t";  simp)







(********************************WRITER EVEN INV :odd**************COMPLETED***************************)

(*1*)
lemma  begin_writer_odd_inv:
  assumes "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
  and "TML_Begin  t   \<sigma> \<sigma>'"
  and "  Begin_inv  t  ((pc \<sigma>) t) \<sigma>   "
and   " \<forall>  t.  ( writer \<sigma> = Some t \<longrightarrow> odd (lastVal glb  (\<tau> \<sigma>)) )"
shows  " \<forall>  t.  ( writer \<sigma>' = Some t \<longrightarrow> odd (lastVal glb  (\<tau> \<sigma>')) )"
 using assms
 apply (simp add: TML_Begin_def Begin_inv_def  total_wfs_def )
  apply (cases "pc \<sigma> t";  simp add: split if_splits)
   apply (metis assms(2) lastVal_ni)
  by metis

(*2*)
lemma crash_writer_odd_inv:
assumes  "thrdsvars"
and "TML_Crash  \<sigma> \<sigma>'"
and   " \<forall>  t.  ( writer \<sigma> = Some t \<longrightarrow> odd (lastVal glb  (\<tau> \<sigma>)) )"
shows  " \<forall>  t.  ( writer \<sigma>' = Some t \<longrightarrow> odd (lastVal glb  (\<tau> \<sigma>')) )"
  using assms
  by (simp add:TML_Crash_def)

(*3*)
lemma write_writer_odd_inv:
  assumes "thrdsvars"
      and "total_wfs (\<tau> \<sigma>)"
      and "TML_Write  t    \<sigma> \<sigma>'"
and   " \<forall>  t.  (  writer \<sigma> = Some t \<longrightarrow> odd (lastVal glb  (\<tau> \<sigma>)) )"
 and "  Write_inv  t  ((pc \<sigma>) t) \<sigma>  " 
shows   " \<forall>  t.  ( writer \<sigma>' = Some t \<longrightarrow> odd (lastVal glb  (\<tau> \<sigma>')) )"
 using assms
  apply (simp add:TML_Write_def total_wfs_def Write_inv_def)
  apply (cases "pc \<sigma> t";  simp  )
      apply  (simp add: split: if_split_asm)
     apply  (simp add: split: if_split_asm)
  apply (metis cas_fail_lv_ni lastVal_def)
  apply (metis cas_lc even_Suc gr0_implies_Suc lastVal_def nat.discI)
  using reg_write_lastVal_ni apply presburger
  apply (metis assms(2) lastVal_ni)
  apply (metis assms(2) lev_in_ov singletonD st_ov_ni total_wfs_def)
  by (metis assms(2) flo_ov_ni lev_in_ov singleton_iff total_wfs_def)

(*4*)
lemma  commit_writer_odd_inv:
  assumes "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
  and "  Commit_inv  t   ((pc \<sigma>) t) \<sigma>  "
  and "TML_Commit  t   \<sigma> \<sigma>'"
and "  \<forall>  t.  (     writer \<sigma> = Some t \<longrightarrow> odd (lastVal glb  (\<tau> \<sigma>)) )"
shows  " \<forall>  t.  (  writer \<sigma>' = Some t \<longrightarrow> odd (lastVal glb  (\<tau> \<sigma>')) )  " 
  using assms
  apply (simp add:TML_Commit_def total_wfs_def Commit_inv_def)
  apply (cases "pc \<sigma> t";  simp  )
  by (metis lastVal_def sf_nlv_ni)


(*5*)
lemma  read_writer_odd_inv:
   assumes "thrdsvars"
   and "total_wfs (\<tau> \<sigma>)"
   and "TML_Read  t   \<sigma> \<sigma>'"
      and "Read_inv t  ((pc \<sigma>) t) \<sigma>" 
and "  \<forall>  t.  (     writer \<sigma> = Some t \<longrightarrow> odd (lastVal glb  (\<tau> \<sigma>)) )"
shows  " \<forall>  t.  (  writer \<sigma>' = Some t \<longrightarrow> odd (lastVal glb  (\<tau> \<sigma>')) )  " 
  using assms
  apply (unfold  total_wfs_def )
  apply (simp add:TML_Read_def Read_inv_def  )
  apply (cases "pc \<sigma> t";   simp add: split if_splits)
      apply ( simp add: split: if_split_asm)
  using assms(2) lastVal_ni apply presburger
      apply ( simp add: split: if_split_asm)
  apply (metis assms(2) cas_fail_diff_lv cas_fail_lastVal_same)
  apply (metis assms(2) lastVal_ni)
  by presburger


(*6*)
lemma recover_writer_odd_inv:
 assumes "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
  and " TML_Recover syst   \<sigma> \<sigma>' "
 and "  Recover_inv  syst  ((pc \<sigma>) syst)  \<sigma>"
and " \<forall> ti l. last_entry (\<tau> \<sigma>) l \<in>   OTS (\<tau> \<sigma>) ti l "
and " \<forall> ti l. lastVal  l (\<tau> \<sigma>)  \<in>  [l]\<^sub>ti (\<tau> \<sigma>) " 
and "  \<forall>  t.  (     writer \<sigma> = Some t \<longrightarrow> odd (lastVal glb  (\<tau> \<sigma>)) )"
shows  " \<forall>  t.  (  writer \<sigma>' = Some t \<longrightarrow> odd (lastVal glb  (\<tau> \<sigma>')) )  " 
 using assms
  apply (simp add:TML_Recover_def total_wfs_def Recover_inv_def)
  apply (cases "pc \<sigma> syst";   simp add: split if_splits)
    apply ( case_tac " even (regs (\<tau> \<sigma>) syst c1)")
  apply (metis option.distinct(1))
  apply (metis option.distinct(1))
  apply ( case_tac " log \<sigma> = Map.empty")
  apply (metis option.distinct(1))
  by (metis option.discI)






lemma beginInv_writer_odd_inv:
assumes  "thrdsvars"
and "TML_Begin_invocation t  \<sigma> \<sigma>'"
  and " Begin_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
and "  \<forall>  t.  (     writer \<sigma> = Some t \<longrightarrow> odd (lastVal glb  (\<tau> \<sigma>)) )"
shows  " \<forall>  t.  (  writer \<sigma>' = Some t \<longrightarrow> odd (lastVal glb  (\<tau> \<sigma>')) )  " 
 using assms
  apply (simp add: TML_Begin_invocation_def Begin_invocation_inv_def total_wfs_def )
  by  (cases "pc \<sigma> t";  simp )




lemma beginResp_writer_odd_inv:
assumes  "thrdsvars"
and "TML_Begin_response t  \<sigma> \<sigma>'"
and "  \<forall>  t.  (     writer \<sigma> = Some t \<longrightarrow> odd (lastVal glb  (\<tau> \<sigma>)) )"
shows  " \<forall>  t.  (  writer \<sigma>' = Some t \<longrightarrow> odd (lastVal glb  (\<tau> \<sigma>')) )  " 
 using assms
  apply (simp add: TML_Begin_response_def total_wfs_def )
  by (cases "pc \<sigma> t";  simp)



lemma readInv_writer_odd_inv:
assumes  "thrdsvars"
and "TML_Read_invocation t  \<sigma> \<sigma>'"
  and " Begin_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
and "  \<forall>  t.  (     writer \<sigma> = Some t \<longrightarrow> odd (lastVal glb  (\<tau> \<sigma>)) )"
shows  " \<forall>  t.  (  writer \<sigma>' = Some t \<longrightarrow> odd (lastVal glb  (\<tau> \<sigma>')) )  " 
 using assms
  apply (simp add: TML_Read_invocation_def Begin_invocation_inv_def total_wfs_def )
  by  (cases "pc \<sigma> t";  simp )




lemma readResp_writer_odd_inv:
assumes  "thrdsvars"
and "TML_Read_response t  \<sigma> \<sigma>'"
and "  \<forall>  t.  (     writer \<sigma> = Some t \<longrightarrow> odd (lastVal glb  (\<tau> \<sigma>)) )"
shows  " \<forall>  t.  (  writer \<sigma>' = Some t \<longrightarrow> odd (lastVal glb  (\<tau> \<sigma>')) )  " 
 using assms
  apply (simp add: TML_Read_response_def total_wfs_def )
  by (cases "pc \<sigma> t";  simp )
 


lemma writeInv_writer_odd_inv:
assumes  "thrdsvars"
and "TML_Write_invocation t  \<sigma> \<sigma>'"
  and " Write_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
and "  \<forall>  t.  (     writer \<sigma> = Some t \<longrightarrow> odd (lastVal glb  (\<tau> \<sigma>)) )"
shows  " \<forall>  t.  (  writer \<sigma>' = Some t \<longrightarrow> odd (lastVal glb  (\<tau> \<sigma>')) )  " 
 using assms
  apply (simp add: TML_Write_invocation_def  total_wfs_def )
  by  (cases "pc \<sigma> t";  simp )



lemma writeResp_writer_odd_inv:
assumes  "thrdsvars"
and "TML_Write_response t  \<sigma> \<sigma>'"
 and " Write_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
and "  \<forall>  t.  (     writer \<sigma> = Some t \<longrightarrow> odd (lastVal glb  (\<tau> \<sigma>)) )"
shows  " \<forall>  t.  (  writer \<sigma>' = Some t \<longrightarrow> odd (lastVal glb  (\<tau> \<sigma>')) )  " 
 using assms
  apply (simp add: TML_Write_response_def total_wfs_def )
  by  (cases "pc \<sigma> t";  simp )




lemma commitInv_writer_odd_inv:
assumes  "thrdsvars"
and "TML_Commit_invocation t  \<sigma> \<sigma>'"
  and " Commit_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
and "  \<forall>  t.  (     writer \<sigma> = Some t \<longrightarrow> odd (lastVal glb  (\<tau> \<sigma>)) )"
shows  " \<forall>  t.  (  writer \<sigma>' = Some t \<longrightarrow> odd (lastVal glb  (\<tau> \<sigma>')) )  " 
 using assms
  apply (simp add: TML_Commit_invocation_def total_wfs_def )
  by(cases "pc \<sigma> t";  simp)






lemma commitResp_writer_odd_inv:
assumes  "thrdsvars"
and "TML_Commit_response t  \<sigma> \<sigma>'"
and "  \<forall>  t.  (     writer \<sigma> = Some t \<longrightarrow> odd (lastVal glb  (\<tau> \<sigma>)) )"
shows  " \<forall>  t.  (  writer \<sigma>' = Some t \<longrightarrow> odd (lastVal glb  (\<tau> \<sigma>')) )  " 
 using assms
  apply (simp add: TML_Commit_response_def total_wfs_def )
  by (cases "pc \<sigma> t";  simp)














(********************************* commit_even_lastval_pctnotcommit4 **********************)
(*see if you need *)
(*1*)
lemma commit_even_lastval_pctnotcommit4 :
  assumes "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
  and "  Commit_inv  t   ((pc \<sigma>) t) \<sigma>  "
  and "TML_Commit  t   \<sigma> \<sigma>'"
and "  \<forall>  t.   ((  even (lastVal glb  (\<tau> \<sigma>)) \<and> writer \<sigma> \<noteq> None) \<longrightarrow> pc \<sigma> (the ( writer \<sigma>) )   \<noteq> Commit4  )"
shows  " \<forall>  t. ( (  even (lastVal glb  (\<tau> \<sigma>'))\<and> writer \<sigma>' \<noteq> None)  \<longrightarrow> pc \<sigma>' (the ( writer \<sigma>') )   \<noteq> Commit4  )  " 
  using assms
  apply (simp add:TML_Commit_def total_wfs_def Commit_inv_def)
  apply (cases "pc \<sigma> t";  simp  )
    apply  (simp add: split: if_split_asm)
  apply (metis option.sel)
  by (smt (z3) Ready_total_def option.sel pc_aux)

(*2*)
lemma writer_even_lastval_pctnotcommit4:
  assumes "thrdsvars"
      and "total_wfs (\<tau> \<sigma>)"
      and "TML_Write  t    \<sigma> \<sigma>'"
 and "  Write_inv  t  ((pc \<sigma>) t) \<sigma>  " 
and "  \<forall>  t.   ((  even (lastVal glb  (\<tau> \<sigma>)) \<and> writer \<sigma> \<noteq> None) \<longrightarrow> pc \<sigma> (the ( writer \<sigma>) )   \<noteq> Commit4  )"
shows  " \<forall>  t. ( (  even (lastVal glb  (\<tau> \<sigma>'))\<and> writer \<sigma>' \<noteq> None)  \<longrightarrow> pc \<sigma>' (the ( writer \<sigma>') )   \<noteq> Commit4  )  " 
 using assms
  apply (simp add:TML_Write_def total_wfs_def Write_inv_def)
  apply (cases "pc \<sigma> t";  simp  )
   apply  (simp add: split: if_split_asm)
   apply  (simp add: split: if_split_asm)
  using assms(2) cas_fail_lastVal_same apply presburger
  by  (simp add: split: if_split_asm)



(*3*)
lemma  read_even_lastval_pctnotcommit4:
   assumes "thrdsvars"
   and "total_wfs (\<tau> \<sigma>)"
   and "TML_Read  t   \<sigma> \<sigma>'"
      and "Read_inv t  ((pc \<sigma>) t) \<sigma>" 
and "  \<forall>  t.   ((  even (lastVal glb  (\<tau> \<sigma>)) \<and> writer \<sigma> \<noteq> None) \<longrightarrow> pc \<sigma> (the ( writer \<sigma>) )   \<noteq> Commit4  )"
shows  " \<forall>  t. ( (  even (lastVal glb  (\<tau> \<sigma>'))\<and> writer \<sigma>' \<noteq> None)  \<longrightarrow> pc \<sigma>' (the ( writer \<sigma>') )   \<noteq> Commit4  )  "
  using assms
  apply (unfold  total_wfs_def )
  apply (simp add:TML_Read_def Read_inv_def  )
  apply (cases "pc \<sigma> t";   simp add: split if_splits)
  apply (metis assms(2) lastVal_ni)
  apply  (simp add: split: if_split_asm)

     apply (case_tac " regs (\<tau> \<sigma>') t c1 = Suc 0" )
      apply simp
      apply (metis Zero_not_Suc cas_fail_diff_lv)
     apply simp
  apply (metis assms(2) cas_fail_diff_lv cas_fail_lastVal_same)
  apply (metis assms(2) lastVal_ni)
  by  (simp add: split: if_split_asm)

(*4*)
lemma  begin_even_lastval_pctnotcommit4:
  assumes "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
  and "TML_Begin  t   \<sigma> \<sigma>'"
  and "  Begin_inv  t  ((pc \<sigma>) t) \<sigma>   "
and "  \<forall>  t.   ((  even (lastVal glb  (\<tau> \<sigma>)) \<and> writer \<sigma> \<noteq> None) \<longrightarrow> pc \<sigma> (the ( writer \<sigma>) )   \<noteq> Commit4  )"
shows  " \<forall>  t. ( (  even (lastVal glb  (\<tau> \<sigma>'))\<and> writer \<sigma>' \<noteq> None)  \<longrightarrow> pc \<sigma>' (the ( writer \<sigma>') )   \<noteq> Commit4  )  "
 using assms
 apply (simp add: TML_Begin_def Begin_inv_def  total_wfs_def )
  apply (cases "pc \<sigma> t";   simp add: split if_splits)
  apply (metis assms(2) lastVal_ni)
  by (metis fun_upd_other option.sel)

(*5*)
lemma  recover_even_lastval_pctnotcommit4:
 assumes "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
  and " TML_Recover syst   \<sigma> \<sigma>' "
 and "  Recover_inv  syst  ((pc \<sigma>) syst)  \<sigma>"
and " \<forall> ti l. last_entry (\<tau> \<sigma>) l \<in>   OTS (\<tau> \<sigma>) ti l "
and " \<forall> ti l. lastVal  l (\<tau> \<sigma>)  \<in>  [l]\<^sub>ti (\<tau> \<sigma>) " 
and "  \<forall>  t.   ((  even (lastVal glb  (\<tau> \<sigma>)) \<and> writer \<sigma> \<noteq> None) \<longrightarrow> pc \<sigma> (the ( writer \<sigma>) )   \<noteq> Commit4  )"
shows  " \<forall>  t. ( (  even (lastVal glb  (\<tau> \<sigma>'))\<and> writer \<sigma>' \<noteq> None)  \<longrightarrow> pc \<sigma>' (the ( writer \<sigma>') )   \<noteq> Commit4  )  "
 using assms
   apply (simp add:   Recover_inv_def TML_Recover_def)
apply (cases "pc \<sigma> syst";   simp add: split if_splits)
  apply  (simp add: split: if_split_asm)
  by (simp add: split: if_split_asm)


(*6*)
lemma crash_even_lastval_pctnotcommit4:
assumes  "thrdsvars"
and "TML_Crash  \<sigma> \<sigma>'"
and "  \<forall>  t.   ((  even (lastVal glb  (\<tau> \<sigma>)) \<and> writer \<sigma> \<noteq> None) \<longrightarrow> pc \<sigma> (the ( writer \<sigma>) )   \<noteq> Commit4  )"
shows  " \<forall>  t. ( (  even (lastVal glb  (\<tau> \<sigma>'))\<and> writer \<sigma>' \<noteq> None)  \<longrightarrow> pc \<sigma>' (the ( writer \<sigma>') )   \<noteq> Commit4  )  "
 using assms
  by (simp add:TML_Crash_def)





lemma beginInv_even_lastval_pctnotcommit4:
assumes  "thrdsvars"
and "TML_Begin_invocation t  \<sigma> \<sigma>'"
  and " Begin_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
and "  \<forall>  t.   ((  even (lastVal glb  (\<tau> \<sigma>)) \<and> writer \<sigma> \<noteq> None) \<longrightarrow> pc \<sigma> (the ( writer \<sigma>) )   \<noteq> Commit4  )"
shows  " \<forall>  t. ( (  even (lastVal glb  (\<tau> \<sigma>'))\<and> writer \<sigma>' \<noteq> None)  \<longrightarrow> pc \<sigma>' (the ( writer \<sigma>') )   \<noteq> Commit4  )  "
 using assms
  apply (simp add: TML_Begin_invocation_def Begin_invocation_inv_def total_wfs_def )
  by  (cases "pc \<sigma> t";  simp )




lemma beginResp_even_lastval_pctnotcommit4:
assumes  "thrdsvars"
and "TML_Begin_response t  \<sigma> \<sigma>'"
and "  \<forall>  t.   ((  even (lastVal glb  (\<tau> \<sigma>)) \<and> writer \<sigma> \<noteq> None) \<longrightarrow> pc \<sigma> (the ( writer \<sigma>) )   \<noteq> Commit4  )"
shows  " \<forall>  t. ( (  even (lastVal glb  (\<tau> \<sigma>'))\<and> writer \<sigma>' \<noteq> None)  \<longrightarrow> pc \<sigma>' (the ( writer \<sigma>') )   \<noteq> Commit4  )  "
 using assms
  apply (simp add: TML_Begin_response_def total_wfs_def )
  by (cases "pc \<sigma> t";  simp)



lemma readInv_even_lastval_pctnotcommit4:
assumes  "thrdsvars"
and "TML_Read_invocation t  \<sigma> \<sigma>'"
  and " Begin_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
and "  \<forall>  t.   ((  even (lastVal glb  (\<tau> \<sigma>)) \<and> writer \<sigma> \<noteq> None) \<longrightarrow> pc \<sigma> (the ( writer \<sigma>) )   \<noteq> Commit4  )"
shows  " \<forall>  t. ( (  even (lastVal glb  (\<tau> \<sigma>'))\<and> writer \<sigma>' \<noteq> None)  \<longrightarrow> pc \<sigma>' (the ( writer \<sigma>') )   \<noteq> Commit4  )  "
 using assms
  apply (simp add: TML_Read_invocation_def Begin_invocation_inv_def total_wfs_def )
  by  (cases "pc \<sigma> t";  simp )




lemma readResp_even_lastval_pctnotcommit4:
assumes  "thrdsvars"
and "TML_Read_response t  \<sigma> \<sigma>'"
and "  \<forall>  t.   ((  even (lastVal glb  (\<tau> \<sigma>)) \<and> writer \<sigma> \<noteq> None) \<longrightarrow> pc \<sigma> (the ( writer \<sigma>) )   \<noteq> Commit4  )"
shows  " \<forall>  t. ( (  even (lastVal glb  (\<tau> \<sigma>'))\<and> writer \<sigma>' \<noteq> None)  \<longrightarrow> pc \<sigma>' (the ( writer \<sigma>') )   \<noteq> Commit4  )  "
 using assms
  apply (simp add: TML_Read_response_def total_wfs_def )
  by (cases "pc \<sigma> t";  simp )
 


lemma writeInv_even_lastval_pctnotcommit4:
assumes  "thrdsvars"
and "TML_Write_invocation t  \<sigma> \<sigma>'"
  and " Write_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
and "  \<forall>  t.   ((  even (lastVal glb  (\<tau> \<sigma>)) \<and> writer \<sigma> \<noteq> None) \<longrightarrow> pc \<sigma> (the ( writer \<sigma>) )   \<noteq> Commit4  )"
shows  " \<forall>  t. ( (  even (lastVal glb  (\<tau> \<sigma>'))\<and> writer \<sigma>' \<noteq> None)  \<longrightarrow> pc \<sigma>' (the ( writer \<sigma>') )   \<noteq> Commit4  )  "
 using assms
  apply (simp add: TML_Write_invocation_def  total_wfs_def )
  by  (cases "pc \<sigma> t";  simp )



lemma writeResp_even_lastval_pctnotcommit4:
assumes  "thrdsvars"
and "TML_Write_response t  \<sigma> \<sigma>'"
 and " Write_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
and "  \<forall>  t.   ((  even (lastVal glb  (\<tau> \<sigma>)) \<and> writer \<sigma> \<noteq> None) \<longrightarrow> pc \<sigma> (the ( writer \<sigma>) )   \<noteq> Commit4  )"
shows  " \<forall>  t. ( (  even (lastVal glb  (\<tau> \<sigma>'))\<and> writer \<sigma>' \<noteq> None)  \<longrightarrow> pc \<sigma>' (the ( writer \<sigma>') )   \<noteq> Commit4  )  "
 using assms
  apply (simp add: TML_Write_response_def total_wfs_def )
  by  (cases "pc \<sigma> t";  simp )




lemma commitInv_even_lastval_pctnotcommit4:
assumes  "thrdsvars"
and "TML_Commit_invocation t  \<sigma> \<sigma>'"
  and " Commit_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
and "  \<forall>  t.   ((  even (lastVal glb  (\<tau> \<sigma>)) \<and> writer \<sigma> \<noteq> None) \<longrightarrow> pc \<sigma> (the ( writer \<sigma>) )   \<noteq> Commit4  )"
shows  " \<forall>  t. ( (  even (lastVal glb  (\<tau> \<sigma>'))\<and> writer \<sigma>' \<noteq> None)  \<longrightarrow> pc \<sigma>' (the ( writer \<sigma>') )   \<noteq> Commit4  )  "
 using assms
  apply (simp add: TML_Commit_invocation_def total_wfs_def )
  by(cases "pc \<sigma> t";  simp)






lemma commitResp_even_lastval_pctnotcommit4:
assumes  "thrdsvars"
and "TML_Commit_response t  \<sigma> \<sigma>'"
and "  \<forall>  t.   ((  even (lastVal glb  (\<tau> \<sigma>)) \<and> writer \<sigma> \<noteq> None) \<longrightarrow> pc \<sigma> (the ( writer \<sigma>) )   \<noteq> Commit4  )"
shows  " \<forall>  t. ( (  even (lastVal glb  (\<tau> \<sigma>'))\<and> writer \<sigma>' \<noteq> None)  \<longrightarrow> pc \<sigma>' (the ( writer \<sigma>') )   \<noteq> Commit4  )  "
 using assms
  apply (simp add: TML_Commit_response_def total_wfs_def )
  by (cases "pc \<sigma> t";  simp)








(****************************************************writer_lastglb_inv******completed*****************************************************)

(*1*)
lemma  commit_writer_lastglb_inv:
  assumes "total_wfs (\<tau> \<sigma>)"
  and "  Commit_inv  t   ((pc \<sigma>) t) \<sigma>  "
  and "TML_Commit  t   \<sigma> \<sigma>'"
and " \<forall>  t. (  (   writer \<sigma>  = Some t    \<longrightarrow> \<lceil>glb\<rceil>\<^sub>t (\<tau> \<sigma>) ))"
shows  " \<forall>  t. (  (  writer \<sigma>'  = Some t    \<longrightarrow> \<lceil>glb\<rceil>\<^sub>t (\<tau> \<sigma>') ))"
 using assms
  apply (simp add:TML_Commit_def total_wfs_def Commit_inv_def)
  apply (cases "pc \<sigma> t";  simp add: split if_splits )
  by (smt (verit) assms(1) insertE insert_absorb insert_not_empty le_in_ots sf_ots_ni total_wfs_def)


(*2*)
lemma write_writer_lastglb_inv:
  assumes "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
  and "TML_Write  t    \<sigma> \<sigma>'"
 and " \<forall>  t. (  (   writer \<sigma>  = Some t    \<longrightarrow> \<lceil>glb\<rceil>\<^sub>t (\<tau> \<sigma>) ))"
 and "  Write_inv  t  ((pc \<sigma>) t) \<sigma>  " 
shows  " \<forall>  t. (  (  writer \<sigma>'  = Some t    \<longrightarrow> \<lceil>glb\<rceil>\<^sub>t (\<tau> \<sigma>') ))"
 using assms
  apply (simp add:TML_Write_def total_wfs_def Write_inv_def)
  apply (cases "pc \<sigma> t";  simp add: split if_splits )
  apply  (simp add: split: if_split_asm)
     apply (case_tac "regs (\<tau> \<sigma>') t c1 = 1 ")
      apply clarify
      apply (case_tac " t = ta ")
  apply (metis assms(2) cas_lastEntry total_wfs_def zero_less_one zero_neq_one)
      apply (subgoal_tac "  writer \<sigma>' \<noteq>  Some ta")
       prefer 2
       apply (metis One_nat_def option.inject zero_less_Suc)
      apply linarith
     apply (subgoal_tac "regs (\<tau> \<sigma>') t c1 = 0 ")
      prefer 2
      apply (metis cas_sv_lc neq0_conv)
     apply (subgoal_tac " OTS (\<tau> \<sigma>')  t glb \<subseteq> OTS  (\<tau> \<sigma>)  t glb")
      prefer 2
      apply (metis assms(2) cas_fail_ots_sub total_wfs_def)
  apply (subgoal_tac "  ( last_entry (\<tau> \<sigma>')  glb \<in>   OTS (\<tau> \<sigma>)  t glb)")
      prefer 2
      apply (metis assms(2) in_mono le_in_ots total_wfs_def)
     apply clarify
     apply (case_tac " ta = t ")
      apply (metis assms(2) cas_le_ni total_wfs_def)
  apply (subgoal_tac " OTS (\<tau> \<sigma>')  ta glb \<subseteq> OTS  (\<tau> \<sigma>)  ta glb")
      prefer 2
      apply (metis assms(2) cas_fail_ots_sub total_wfs_def)
  apply (subgoal_tac "  ( last_entry (\<tau> \<sigma>')  glb \<in>   OTS (\<tau> \<sigma>)  ta glb)")
      prefer 2
      apply (metis assms(2) le_in_ots subset_eq total_wfs_def)
  apply (metis assms(2) insertE insert_absorb insert_not_empty le_in_ots subset_singletonD total_wfs_def)
  using reg_le_ni apply presburger
  apply (metis assms(2) insertE insert_absorb insert_not_empty ld_ots_sub le_in_ots subset_singleton_iff total_wfs_def)
    apply (metis st_ots_lm_ni)
  by (smt (verit, best) assms(2) flo_ots_ni insert_absorb le_in_ots singleton_insert_inj_eq subset_insertI total_wfs_def)
 



(*3*)
lemma  read_writer_lastglb_inv:
   assumes "thrdsvars"
   and "total_wfs (\<tau> \<sigma>)"
   and "TML_Read  t   \<sigma> \<sigma>'"
      and "Read_inv t  ((pc \<sigma>) t) \<sigma>" 
 and " \<forall>  t. (  (   writer \<sigma>  = Some t    \<longrightarrow> \<lceil>glb\<rceil>\<^sub>t (\<tau> \<sigma>) ))"
and   " \<forall>  t.  (  writer \<sigma> = Some t \<longrightarrow> odd (lastVal glb  (\<tau> \<sigma>)) )"
shows  " \<forall>  t. (  (  writer \<sigma>'  = Some t    \<longrightarrow> \<lceil>glb\<rceil>\<^sub>t (\<tau> \<sigma>') ))"

  using assms
  apply (unfold  total_wfs_def )
  apply (simp add:TML_Read_def Read_inv_def  )
  apply (cases "pc \<sigma> t";   simp add: split if_splits)
  apply (metis OTS_def assms(2) insert_absorb ld_ots_sub le_in_otsf singleton_iff subset_singleton_iff total_wfs_def)
      apply ( simp add: split: if_split_asm)
     apply (case_tac "regs (\<tau> \<sigma>') t c1 = Suc 0  ")
  apply (metis Zero_not_Suc cas_fail_diff_lv)
     apply simp

     apply clarify

     apply (elim disjE)

  apply metis
     apply (subgoal_tac "  \<lceil>glb\<rceil>\<^sub>ta \<tau> \<sigma> ")
      prefer 2
  apply blast

     apply (subgoal_tac "  OTS (\<tau> \<sigma>') t glb   \<subseteq> OTS (\<tau> \<sigma>) t glb ")
      prefer 2
      apply (metis assms(2) cas_fail_diff_lv cas_fail_ots_sub total_wfs_def)

     apply (subgoal_tac " last_entry (\<tau> \<sigma>') glb  =  last_entry (\<tau> \<sigma>) glb")
      prefer 2
      apply (subgoal_tac " memory (\<tau> \<sigma>) = memory (\<tau> \<sigma>') ")
  prefer 2
       apply (metis cas_fail_diff_lv cas_fail_mem_same)
      apply (simp add: last_entry_def)
      apply (simp add: last_entry_set_def)
  apply (metis assms(2) cas_fail_diff_lv cas_fail_ots_sub insert_absorb le_in_ots subset_singletonD total_wfs_def)
  apply (metis assms(2) insert_absorb ld_last_entry ld_ots_sub le_in_ots subset_singletonD total_wfs_def)
  by  presburger




(*4*)
lemma begin_writer_lastglb_inv:
  assumes "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
  and "TML_Begin  t   \<sigma> \<sigma>'"
 and " \<forall>  t. (  (   writer \<sigma>  = Some t    \<longrightarrow> \<lceil>glb\<rceil>\<^sub>t (\<tau> \<sigma>) ))"
shows  " \<forall>  t. (  (  writer \<sigma>'  = Some t    \<longrightarrow> \<lceil>glb\<rceil>\<^sub>t (\<tau> \<sigma>') ))"
  using assms
 apply (simp add:TML_Begin_def total_wfs_def )
  apply (cases "pc \<sigma> t";  simp add: split if_splits )
  apply (metis assms(2) insert_absorb ld_last_entry ld_ots_sub le_in_ots subset_singletonD total_wfs_def)
  by metis




(*5*)
lemma crash_writer_lastglb_inv:
assumes  "thrdsvars"
and "TML_Crash  \<sigma> \<sigma>'"
 and " \<forall>  t. (  (   writer \<sigma>  = Some t    \<longrightarrow> \<lceil>glb\<rceil>\<^sub>t (\<tau> \<sigma>) ))"
shows  " \<forall>  t. (  (  writer \<sigma>'  = Some t    \<longrightarrow> \<lceil>glb\<rceil>\<^sub>t (\<tau> \<sigma>') ))"
  using assms
  by (simp add:TML_Crash_def)

(*6*)
lemma recover_writer_lastglb_inv:
 assumes "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
  and " TML_Recover syst  \<sigma> \<sigma>' "
 and "  Recover_inv  syst  ((pc \<sigma>) syst)  \<sigma>"
and " \<forall> ti l. last_entry (\<tau> \<sigma>) l \<in>   OTS (\<tau> \<sigma>) ti l "
and " \<forall> ti l. lastVal  l (\<tau> \<sigma>)  \<in>  [l]\<^sub>ti (\<tau> \<sigma>) " 
 and " \<forall>  t. (  (   writer \<sigma>  = Some t    \<longrightarrow> \<lceil>glb\<rceil>\<^sub>t (\<tau> \<sigma>) ))"
shows   " \<forall>  t. (  (  writer \<sigma>'  = Some t    \<longrightarrow> \<lceil>glb\<rceil>\<^sub>t (\<tau> \<sigma>') ))"
 using assms
  apply (simp add:TML_Recover_def total_wfs_def Recover_inv_def)
  apply (cases "pc \<sigma> syst";   simp add: split if_splits)
  apply (metis option.distinct(1))
  by (metis option.distinct(1))




lemma beginInv_writer_lastglb_inv:
assumes  "thrdsvars"
and "TML_Begin_invocation t  \<sigma> \<sigma>'"
  and " Begin_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
 and " \<forall>  t. (  (   writer \<sigma>  = Some t    \<longrightarrow> \<lceil>glb\<rceil>\<^sub>t (\<tau> \<sigma>) ))"
shows   " \<forall>  t. (  (  writer \<sigma>'  = Some t    \<longrightarrow> \<lceil>glb\<rceil>\<^sub>t (\<tau> \<sigma>') ))"
 using assms
  apply (simp add: TML_Begin_invocation_def Begin_invocation_inv_def total_wfs_def )
  by  (cases "pc \<sigma> t";  simp )




lemma beginResp_writer_lastglb_inv:
assumes  "thrdsvars"
and "TML_Begin_response t  \<sigma> \<sigma>'"
 and " \<forall>  t. (  (   writer \<sigma>  = Some t    \<longrightarrow> \<lceil>glb\<rceil>\<^sub>t (\<tau> \<sigma>) ))"
shows   " \<forall>  t. (  (  writer \<sigma>'  = Some t    \<longrightarrow> \<lceil>glb\<rceil>\<^sub>t (\<tau> \<sigma>') ))"
 using assms
  apply (simp add: TML_Begin_response_def total_wfs_def )
  by (cases "pc \<sigma> t";  simp)



lemma readInv_writer_lastglb_inv:
assumes  "thrdsvars"
and "TML_Read_invocation t  \<sigma> \<sigma>'"
  and " Begin_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
 and " \<forall>  t. (  (   writer \<sigma>  = Some t    \<longrightarrow> \<lceil>glb\<rceil>\<^sub>t (\<tau> \<sigma>) ))"
shows   " \<forall>  t. (  (  writer \<sigma>'  = Some t    \<longrightarrow> \<lceil>glb\<rceil>\<^sub>t (\<tau> \<sigma>') ))"
 using assms
  apply (simp add: TML_Read_invocation_def Begin_invocation_inv_def total_wfs_def )
  by  (cases "pc \<sigma> t";  simp )




lemma readResp_writer_lastglb_inv:
assumes  "thrdsvars"
and "TML_Read_response t  \<sigma> \<sigma>'"
 and " \<forall>  t. (  (   writer \<sigma>  = Some t    \<longrightarrow> \<lceil>glb\<rceil>\<^sub>t (\<tau> \<sigma>) ))"
shows   " \<forall>  t. (  (  writer \<sigma>'  = Some t    \<longrightarrow> \<lceil>glb\<rceil>\<^sub>t (\<tau> \<sigma>') ))"
 using assms
  apply (simp add: TML_Read_response_def total_wfs_def )
  by (cases "pc \<sigma> t";  simp )
 


lemma writeInv_writer_lastglb_inv:
assumes  "thrdsvars"
and "TML_Write_invocation t  \<sigma> \<sigma>'"
  and " Write_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
 and " \<forall>  t. (  (   writer \<sigma>  = Some t    \<longrightarrow> \<lceil>glb\<rceil>\<^sub>t (\<tau> \<sigma>) ))"
shows   " \<forall>  t. (  (  writer \<sigma>'  = Some t    \<longrightarrow> \<lceil>glb\<rceil>\<^sub>t (\<tau> \<sigma>') ))"
 using assms
  apply (simp add: TML_Write_invocation_def  total_wfs_def )
  by  (cases "pc \<sigma> t";  simp )



lemma writeResp_writer_lastglb_inv:
assumes  "thrdsvars"
and "TML_Write_response t  \<sigma> \<sigma>'"
 and " Write_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
 and " \<forall>  t. (  (   writer \<sigma>  = Some t    \<longrightarrow> \<lceil>glb\<rceil>\<^sub>t (\<tau> \<sigma>) ))"
shows   " \<forall>  t. (  (  writer \<sigma>'  = Some t    \<longrightarrow> \<lceil>glb\<rceil>\<^sub>t (\<tau> \<sigma>') ))"
 using assms
  apply (simp add: TML_Write_response_def total_wfs_def )
  by  (cases "pc \<sigma> t";  simp )




lemma commitInv_writer_lastglb_inv:
assumes  "thrdsvars"
and "TML_Commit_invocation t  \<sigma> \<sigma>'"
  and " Commit_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
 and " \<forall>  t. (  (   writer \<sigma>  = Some t    \<longrightarrow> \<lceil>glb\<rceil>\<^sub>t (\<tau> \<sigma>) ))"
shows   " \<forall>  t. (  (  writer \<sigma>'  = Some t    \<longrightarrow> \<lceil>glb\<rceil>\<^sub>t (\<tau> \<sigma>') ))"
 using assms
  apply (simp add: TML_Commit_invocation_def total_wfs_def )
  by(cases "pc \<sigma> t";  simp)






lemma commitResp_writer_lastglb_inv:
assumes  "thrdsvars"
and "TML_Commit_response t  \<sigma> \<sigma>'"
 and " \<forall>  t. (  (   writer \<sigma>  = Some t    \<longrightarrow> \<lceil>glb\<rceil>\<^sub>t (\<tau> \<sigma>) ))"
shows   " \<forall>  t. (  (  writer \<sigma>'  = Some t    \<longrightarrow> \<lceil>glb\<rceil>\<^sub>t (\<tau> \<sigma>') ))"
 using assms
  apply (simp add: TML_Commit_response_def total_wfs_def )
  by (cases "pc \<sigma> t";  simp)













(**********************mem_tml_prop************completed*******************************************************************************)
(*1*)
lemma commit_mem_inv:
  assumes "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
  and "  Commit_inv  t   ((pc \<sigma>) t) \<sigma>  "
  and "TML_Commit  t   \<sigma> \<sigma>'"
and " n \<noteq> glb"
and " mem_tml_prop   glb  n (\<tau> \<sigma>) "
shows  " mem_tml_prop  glb n  (\<tau> \<sigma>')"
 using assms
  apply (simp add:TML_Commit_def total_wfs_def Commit_inv_def  )
  apply (cases "pc \<sigma> t";  simp add: split if_splits )

  using  sfence_mem_inv [where n = n and c = glb and t = t ]
  using assms(1) assms(2) mem_tml_prop_def apply blast

  apply (subgoal_tac " even ( Suc (lastVal glb (\<tau> \<sigma>))  )")
   prefer 2
   apply (metis even_Suc)
  using commit_up_glb_mem_inv  [where n = n  and t = t ]
  using assms(1) assms(2) by blast


(*2*)
lemma write_mem_inv:
  assumes "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
  and " Write_inv  t  ((pc \<sigma>) t) \<sigma> "
 and "TML_Write  t   \<sigma> \<sigma>'"
and " b \<noteq> glb"
 and " \<forall>  t. (  (   writer \<sigma>  = Some t    \<longrightarrow> \<lceil>glb\<rceil>\<^sub>t (\<tau> \<sigma>) ))"
and " mem_tml_prop   glb  b (\<tau> \<sigma>) "
shows  " mem_tml_prop  glb b  (\<tau> \<sigma>')"
 using assms
  apply (simp add:TML_Write_def Write_inv_def   )
  apply (cases "pc \<sigma> t";  simp add: split if_splits )
      apply ( simp add: split: if_split_asm)
     apply (case_tac " regs (\<tau> \<sigma>') t c1 = 0 ")
  using assms(1) write_cas_fail_mem_inv apply blast
  using assms(1) cas_succ_mem_inv apply blast
 apply (simp add:  mem_tml_prop_def update_reg_def)
    apply (subgoal_tac "\<lceil>glb\<rceil>\<^sub>t (\<tau> \<sigma>')" )
     prefer 2
  using write_writer_lastglb_inv 
  using assms(1) assms(3) assms(4) assms(5) apply presburger
  using assms(1) ld_mem_inv apply blast


    apply (subgoal_tac " odd( lastVal glb (\<tau> \<sigma>'))  ")
     prefer 2
  using total_wfs_def 
     apply (metis lev_in_ov singletonD st_ov_ni)
 using total_wfs_def 
   apply (metis assms(1) st_ots_lm_ni write_write_a_mem_inv)
  using assms(1) flo_mem_inv by blast

(*3*)
lemma begin_mem_inv:
  assumes "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
  and "TML_Begin  t   \<sigma> \<sigma>'"
and " mem_tml_prop   glb  a (\<tau> \<sigma>) "
shows  " mem_tml_prop  glb a  (\<tau> \<sigma>')"
  using assms
 apply (simp add:TML_Begin_def total_wfs_def )
  apply (cases "pc \<sigma> t";  simp add: split if_splits )
  using assms(1) assms(2) ld_mem_inv apply blast
  by metis



(*4*)
lemma  read_mem_inv:
   assumes "thrdsvars"
   and "total_wfs (\<tau> \<sigma>)"
   and "TML_Read  t   \<sigma> \<sigma>'"
      and "Read_inv t  ((pc \<sigma>) t) \<sigma>" 
and " mem_tml_prop   glb  b (\<tau> \<sigma>) "
shows  " mem_tml_prop  glb b  (\<tau> \<sigma>')"
  using assms
 apply (unfold  total_wfs_def )
  apply (simp add:TML_Read_def Read_inv_def  )
  apply (cases "pc \<sigma> t";   simp add: split if_splits)
  using assms(1) assms(2) ld_mem_inv apply blast
      apply ( simp add: split: if_split_asm)
     apply (case_tac "regs (\<tau> \<sigma>') t c1 = Suc 0 ")
  apply (metis assms(1) assms(2) cas_succ_mem_inv numeral_1_eq_Suc_0 numerals(1) zero_neq_one)
  apply (metis assms(1) assms(2) cas_succ_mem_inv write_cas_fail_mem_inv)
  using assms(1) assms(2) ld_mem_inv apply blast
  by presburger


(*5*)
lemma  crash_mem_inv:
assumes  "thrdsvars"
and "TML_Crash  \<sigma> \<sigma>'"
and " mem_tml_prop   glb  b (\<tau> \<sigma>) "
shows  " mem_tml_prop  glb b  (\<tau> \<sigma>')"
  using assms
  apply(simp add:TML_Crash_def)
  apply (subgoal_tac " length (memory (\<tau> \<sigma>')) = 1 ")
  prefer 2
   apply (simp add: crash_step_def crash_trans_def)
  apply (unfold  mem_tml_prop_def )
  by linarith

(*6*)
lemma recover_mem_inv:
 assumes "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
  and " TML_Recover syst   \<sigma> \<sigma>' "
 and "  Recover_inv  syst  ((pc \<sigma>) syst)  \<sigma>"
and " \<forall> ti l. last_entry (\<tau> \<sigma>) l \<in>   OTS (\<tau> \<sigma>) ti l "
and " \<forall> ti l. lastVal  l (\<tau> \<sigma>)  \<in>  [l]\<^sub>ti (\<tau> \<sigma>) " 
and " mem_tml_prop   glb  b (\<tau> \<sigma>) "
shows  " mem_tml_prop  glb b  (\<tau> \<sigma>')"
 using assms
  apply (simp add:TML_Recover_def total_wfs_def Recover_inv_def)
  apply (cases "pc \<sigma> syst";   simp add: split if_splits)
         apply (simp add: update_reg_def  mem_tml_prop_def)
         defer
  apply (metis assms(1) assms(2) flo_mem_inv)
  apply (metis assms(1) assms(2) sfence_mem_inv)
  apply (metis assms(1) assms(2) ld_mem_inv)
  apply presburger
    prefer 3
    apply presburger
   apply (meson assms(1) assms(2) recover_up_glb_mem_inv)
  apply (metis assms(1) assms(2) recover_up_glb_mem_inv)
        apply (subgoal_tac "(get_key (log \<sigma>))  \<noteq> glb ")
         prefer 2
         apply (metis get_key_in_dom)
        apply (subgoal_tac "(\<forall>i. 0 < i \<and> i < length (memory (\<tau> \<sigma>')) \<longrightarrow> Msg.loc (memory (\<tau> \<sigma>') ! i) \<noteq> glb)  ")
         prefer 2
         apply (simp add: step_def)
         apply (simp add: store_trans_def)
  apply (metis Msg.sel(1) less_antisym less_or_eq_imp_le mem_l nth_append_length store_add)
        apply (unfold  mem_tml_prop_def)
  by (meson Suc_le_eq i_noteqo_loc le_trans less_imp_le_nat mem_structured_preserved)




lemma beginInv_mem_inv:
assumes  "thrdsvars"
and "TML_Begin_invocation t  \<sigma> \<sigma>'"
  and " Begin_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
and " mem_tml_prop   glb  b (\<tau> \<sigma>) "
shows  " mem_tml_prop  glb b  (\<tau> \<sigma>')"
 using assms
  apply (simp add: TML_Begin_invocation_def Begin_invocation_inv_def total_wfs_def )
  by  (cases "pc \<sigma> t";  simp )




lemma beginResp_mem_inv:
assumes  "thrdsvars"
and "TML_Begin_response t  \<sigma> \<sigma>'"
and " mem_tml_prop   glb  b (\<tau> \<sigma>) "
shows  " mem_tml_prop  glb b  (\<tau> \<sigma>')"
 using assms
  apply (simp add: TML_Begin_response_def total_wfs_def )
  by (cases "pc \<sigma> t";  simp)



lemma readInv_mem_inv:
assumes  "thrdsvars"
and "TML_Read_invocation t  \<sigma> \<sigma>'"
  and " Begin_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
and " mem_tml_prop   glb  b (\<tau> \<sigma>) "
shows  " mem_tml_prop  glb b  (\<tau> \<sigma>')"
 using assms
  apply (simp add: TML_Read_invocation_def Begin_invocation_inv_def total_wfs_def )
  by  (cases "pc \<sigma> t";  simp )




lemma readResp_mem_inv:
assumes  "thrdsvars"
and "TML_Read_response t  \<sigma> \<sigma>'"
and " mem_tml_prop   glb  b (\<tau> \<sigma>) "
shows  " mem_tml_prop  glb b  (\<tau> \<sigma>')"
 using assms
  apply (simp add: TML_Read_response_def total_wfs_def )
  by (cases "pc \<sigma> t";  simp )
 


lemma writeInv_mem_inv:
assumes  "thrdsvars"
and "TML_Write_invocation t  \<sigma> \<sigma>'"
  and " Write_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
and " mem_tml_prop   glb  b (\<tau> \<sigma>) "
shows  " mem_tml_prop  glb b  (\<tau> \<sigma>')"
 using assms
  apply (simp add: TML_Write_invocation_def  total_wfs_def )
  by  (cases "pc \<sigma> t";  simp )



lemma writeResp_mem_inv:
assumes  "thrdsvars"
and "TML_Write_response t  \<sigma> \<sigma>'"
 and " Write_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
and " mem_tml_prop   glb  b (\<tau> \<sigma>) "
shows  " mem_tml_prop  glb b  (\<tau> \<sigma>')"
 using assms
  apply (simp add: TML_Write_response_def total_wfs_def )
  by  (cases "pc \<sigma> t";  simp )




lemma commitInv_mem_inv:
assumes  "thrdsvars"
and "TML_Commit_invocation t  \<sigma> \<sigma>'"
  and " Commit_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
and " mem_tml_prop   glb  b (\<tau> \<sigma>) "
shows  " mem_tml_prop  glb b  (\<tau> \<sigma>')"
 using assms
  apply (simp add: TML_Commit_invocation_def total_wfs_def )
  by(cases "pc \<sigma> t";  simp)






lemma commitResp_mem_inv:
assumes  "thrdsvars"
and "TML_Commit_response t  \<sigma> \<sigma>'"
and " mem_tml_prop   glb  b (\<tau> \<sigma>) "
shows  " mem_tml_prop  glb b  (\<tau> \<sigma>')"
 using assms
  apply (simp add: TML_Commit_response_def total_wfs_def )
  by (cases "pc \<sigma> t";  simp)












(****************************INVARIANTS FOR READ ***********************************************************************)
(*
lemma ld_coh_lt_vrnew:
  assumes "(\<tau> \<sigma>) [val   \<leftarrow> a ]\<^sub>t (\<tau> \<sigma>')"
and " \<forall>t. t = syst \<or> ( writeAux \<sigma> t) \<or> ( ( \<nexists>i .i \<in> OTS (\<tau> \<sigma>) t a \<and> i = coh (\<tau> \<sigma>) t a) \<or> coh (\<tau> \<sigma>') t a = 0) "
 and " t \<noteq> syst "
and "total_wfs (\<tau> \<sigma> )"
and "  writeAux \<sigma> t = False "
and "  writeAux \<sigma>' t = False "
and " a \<noteq> glb"
shows " vrnew (\<tau> \<sigma>' ) t \<ge>  coh (\<tau> \<sigma>' ) t a " 
 using assms
  apply (simp add: total_wfs_def   step_def)
  apply (simp add: vbounded_def)
  apply (subgoal_tac "  vrnew (\<tau> \<sigma>' ) t \<ge>  0")
  prefer 2
  apply blast
  apply (case_tac "  ( \<nexists>i .i \<in> OTS (\<tau> \<sigma>) t a \<and> i = coh (\<tau> \<sigma>) t a)")
  apply (simp add: load_trans_def Let_def)
  apply clarify
  apply (subgoal_tac "  ind \<noteq> coh (\<tau> \<sigma>) t a")
  prefer 2
  apply blast
  apply simp
  by metis


*)

(************************************************************END************************************************************************************************************)
(**********************************************loc_less_than_glb******Completed****************************************************************************)




(*************************************************write_writer_none_length_glb*******completed*****NEWVERSION**************FIXED 1810**********************************************************************)

(*1*)
lemma write_writer_none_length_glb:
  assumes "thrdsvars"
      and "total_wfs (\<tau> \<sigma>)"
      and "TML_Write  t    \<sigma> \<sigma>'"
 and "  Write_inv  t  ((pc \<sigma>) t) \<sigma>  " 
and " \<forall>t. (writer \<sigma> = None \<and>   pc \<sigma> syst = RecIdle  )  \<longrightarrow> ( comploc  (memory(\<tau> \<sigma>) !  (length( memory (\<tau> \<sigma>))-1)   ) glb  = glb)  "
shows  "\<forall>t.( writer \<sigma>' = None \<and>     pc \<sigma>' syst = RecIdle )  \<longrightarrow>  (comploc   (memory(\<tau> \<sigma>') ! (length( memory (\<tau> \<sigma>'))-1) ) glb  = glb ) " 
  using assms
  apply (simp add:TML_Write_def total_wfs_def Write_inv_def)
  apply (cases "pc \<sigma> t";  simp add: split if_splits )
  apply presburger
  apply presburger
  apply presburger
  apply presburger
  apply meson
  apply presburger
  apply presburger
  apply presburger
  apply presburger
  apply presburger
  apply presburger
  apply presburger
  apply (unfold  Ready_total_def)
  apply metis
  apply (metis cas_fail_mem_same neq0_conv option.distinct(1))
  apply presburger+
  apply metis
  apply (metis cas_fail_mem_same neq0_conv option.distinct(1))
 by presburger+
  




(*
lemma begin_writer_none_length_glb:
  assumes "thrdsvars"
      and "total_wfs (\<tau> \<sigma>)"
     and "TML_Begin  t   \<sigma> \<sigma>'"
  and "  Begin_inv  t  ((pc \<sigma>) t) \<sigma>   "
and " thread_prop_comp  \<sigma> t "
and " \<forall>t. (writer \<sigma> = None \<and>  ( \<not> crashAux \<sigma> \<or> (pc \<sigma>) t = NotStarted  ) )  \<longrightarrow> ( Msg.loc  (memory(\<tau> \<sigma>) !  (length( memory (\<tau> \<sigma>))-1)    )  = glb)  "
shows  "\<forall>t.( writer \<sigma>' = None \<and>   ( \<not> crashAux \<sigma>' \<or>  (pc \<sigma>') t = NotStarted ) )  \<longrightarrow>  (Msg.loc  (memory(\<tau> \<sigma>') ! (length( memory (\<tau> \<sigma>'))-1)   )  = glb ) "
  using assms
  apply (simp add:TML_Begin_def total_wfs_def Begin_inv_def)
  apply (cases "pc \<sigma> t";  simp add: split if_splits )
    apply (metis ld_step_mem)
   apply (metis ld_step_mem)
  by metis

*)
(*2*)
lemma begin_writer_none_length_glb:
  assumes "thrdsvars"
      and "total_wfs (\<tau> \<sigma>)"
     and "TML_Begin  t   \<sigma> \<sigma>'"
  and "  Begin_inv  t  ((pc \<sigma>) t) \<sigma>   "
and " \<forall>t. (writer \<sigma> = None \<and>   pc \<sigma> syst = RecIdle  )  \<longrightarrow> ( comploc  (memory(\<tau> \<sigma>) !  (length( memory (\<tau> \<sigma>))-1)   ) glb  = glb)  "
shows  "\<forall>t.( writer \<sigma>' = None \<and>     pc \<sigma>' syst = RecIdle )  \<longrightarrow>   ( comploc  (memory(\<tau> \<sigma>') !  (length( memory (\<tau> \<sigma>'))-1)   ) glb   = glb ) "
  using assms
  apply (simp add:TML_Begin_def total_wfs_def Begin_inv_def)
  apply (cases "pc \<sigma> t";  simp add: split if_splits )
  apply presburger
  by (metis ld_step_mem)+
  

(*3*)
lemma crash_writer_none_length_glb:
assumes  "thrdsvars"
and "TML_Crash  \<sigma> \<sigma>'"
and " total_wfs (\<tau> \<sigma>) "
and " \<forall>t. (writer \<sigma> = None \<and>   pc \<sigma> syst = RecIdle  )  \<longrightarrow>  ( comploc  (memory(\<tau> \<sigma>) !  (length( memory (\<tau> \<sigma>))-1)   ) glb   = glb)  "
shows  "\<forall>t.( writer \<sigma>' = None \<and>     pc \<sigma>' syst = RecIdle )  \<longrightarrow>   ( comploc  (memory(\<tau> \<sigma>') !  (length( memory (\<tau> \<sigma>'))-1)   ) glb    = glb ) "
  using assms
  by(simp add:TML_Crash_def)





(*4*)
lemma recover_writer_none_length_glb:
 assumes "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
  and " TML_Recover syst   \<sigma> \<sigma>' "
 and "  Recover_inv  syst  ((pc \<sigma>) syst)  \<sigma>"
and " \<forall> ti l. last_entry (\<tau> \<sigma>) l \<in>   OTS (\<tau> \<sigma>) ti l "
and " \<forall> ti l. lastVal  l (\<tau> \<sigma>)  \<in>  [l]\<^sub>ti (\<tau> \<sigma>) " 
and " \<forall>t. (writer \<sigma> = None \<and>   pc \<sigma> syst = RecIdle  )  \<longrightarrow>  ( comploc  (memory(\<tau> \<sigma>) !  (length( memory (\<tau> \<sigma>))-1)   ) glb  = glb)  "
shows  "\<forall>t.( writer \<sigma>' = None \<and>     pc \<sigma>' syst = RecIdle )  \<longrightarrow>   ( comploc  (memory(\<tau> \<sigma>') !  (length( memory (\<tau> \<sigma>'))-1)   ) glb = glb ) "

 using assms
  apply (simp add:TML_Recover_def total_wfs_def Recover_inv_def)
  apply (cases "pc \<sigma> syst";   simp add: split if_splits)
     apply ( simp add: split: if_split_asm)
    apply (case_tac "  even (survived_val (\<tau> \<sigma>) glb) ")
     apply simp
  apply simp
  apply (metis Nat.add_0_right One_nat_def add_Suc_right diff_Suc_Suc minus_nat.diff_0 st_loc st_mem_length)
  apply (metis Nat.add_0_right One_nat_def add_Suc_right diff_Suc_Suc minus_nat.diff_0 st_loc st_mem_length)
  apply (case_tac " log \<sigma> = Map.empty ")
  apply simp
  by simp





(*5*)
lemma read_writer_none_length_glb:
  assumes "thrdsvars"
      and "total_wfs (\<tau> \<sigma>)"
    and "TML_Read  t   \<sigma> \<sigma>'"
  and "  Read_inv  t   ((pc \<sigma>') t)  \<sigma>'  "
and " \<forall>t. (writer \<sigma> = None \<and>   pc \<sigma> syst = RecIdle  )  \<longrightarrow>  ( comploc  (memory(\<tau> \<sigma>) !  (length( memory (\<tau> \<sigma>))-1)   ) glb  = glb)  "
shows  "\<forall>t.( writer \<sigma>' = None \<and>     pc \<sigma>' syst = RecIdle )  \<longrightarrow>   ( comploc  (memory(\<tau> \<sigma>') !  (length( memory (\<tau> \<sigma>'))-1)   ) glb  = glb)  "

  using assms
  apply (simp add:TML_Read_def total_wfs_def Read_inv_def)
  apply (cases "pc \<sigma> t";  simp add: split if_splits )
  apply (metis ld_step_mem)
                      apply ( simp add: split: if_split_asm)
  apply presburger
                      apply presburger
                      apply presburger
                      apply presburger
                      apply presburger
                      apply (metis ld_step_mem)
  apply presburger+
                      apply (metis ld_step_mem)


                      apply ( simp add: split: if_split_asm)
  apply (unfold Ready_total_def)

     apply (case_tac "regs (\<tau> \<sigma>') t c1 = Suc 0 ")
      apply (simp add: step_def)
      apply clarify
  apply (subgoal_tac "  \<tau> \<sigma>' =
           cas_succ_trans t ind glb (regs (\<tau> \<sigma>) t DTML.loc) (regs (\<tau> \<sigma>) t DTML.loc) c1 nv mnv (\<tau> \<sigma>)")
  prefer 2
       apply (metis Suc_neq_Zero cas_fail_reg)
  apply (subgoal_tac" (length( memory (\<tau> \<sigma>'))-1) =  (length( memory (\<tau> \<sigma>)))   ")
  prefer 2
  using cas_suc_mem_l apply presburger
  using One_nat_def cas_suc_loc apply presburger
  apply simp
  apply (smt (z3) One_nat_def cas_fail_mem_same cas_sv_lc)
    apply (metis ld_step_mem)
    apply  ( simp add: split: if_split_asm)
 by presburger+





(*6*)
lemma commit_writer_none_length_glb:
  assumes "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
  and "  Commit_inv  t   ((pc \<sigma>) t) \<sigma>  "
  and "TML_Commit  t   \<sigma> \<sigma>'"
and " \<forall>t. (writer \<sigma> = None \<and>   pc \<sigma> syst = RecIdle  )  \<longrightarrow>  ( comploc  (memory(\<tau> \<sigma>) !  (length( memory (\<tau> \<sigma>))-1)   ) glb   = glb)  "
shows  "\<forall>t.( writer \<sigma>' = None \<and>     pc \<sigma>' syst = RecIdle )  \<longrightarrow>   ( comploc  (memory(\<tau> \<sigma>') !  (length( memory (\<tau> \<sigma>'))-1)   ) glb  = glb ) "

 using assms
  apply (simp add:TML_Commit_def total_wfs_def Commit_inv_def  )
  apply (cases "pc \<sigma> t";  simp add: split if_splits )
                     apply presburger
                     apply presburger
  apply presburger

                     apply (metis option.distinct(1))
  apply meson
  apply (unfold Ready_total_def)
  apply metis
  apply (metis option.discI)
  apply presburger
apply (metis Nat.add_0_right add_Suc_right diff_Suc_Suc minus_nat.diff_0 numeral_1_eq_Suc_0 numerals(1) st_loc st_mem_length)
                     apply (metis Nat.add_0_right add_Suc_right diff_Suc_Suc minus_nat.diff_0 numeral_1_eq_Suc_0 numerals(1) st_loc st_mem_length)
  by presburger+






lemma beginInv_writer_none_length_glb:
assumes  "thrdsvars"
and "TML_Begin_invocation t  \<sigma> \<sigma>'"
  and " Begin_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
and " \<forall>t. (writer \<sigma> = None \<and>   pc \<sigma> syst = RecIdle  )  \<longrightarrow>  ( comploc  (memory(\<tau> \<sigma>) !  (length( memory (\<tau> \<sigma>))-1)   ) glb   = glb)  "
shows  "\<forall>t.( writer \<sigma>' = None \<and>     pc \<sigma>' syst = RecIdle )  \<longrightarrow>   ( comploc  (memory(\<tau> \<sigma>') !  (length( memory (\<tau> \<sigma>'))-1)   ) glb  = glb ) "
 using assms
  apply (simp add: TML_Begin_invocation_def Begin_invocation_inv_def total_wfs_def )
  apply  (cases "pc \<sigma> t";  simp )
  by presburger+



lemma beginResp_writer_none_length_glb:
assumes  "thrdsvars"
and "TML_Begin_response t  \<sigma> \<sigma>'"
and " \<forall>t. (writer \<sigma> = None \<and>   pc \<sigma> syst = RecIdle  )  \<longrightarrow>  ( comploc  (memory(\<tau> \<sigma>) !  (length( memory (\<tau> \<sigma>))-1)   ) glb   = glb)  "
shows  "\<forall>t.( writer \<sigma>' = None \<and>     pc \<sigma>' syst = RecIdle )  \<longrightarrow>   ( comploc  (memory(\<tau> \<sigma>') !  (length( memory (\<tau> \<sigma>'))-1)   ) glb  = glb ) "
 using assms
  apply (simp add: TML_Begin_response_def total_wfs_def )
  apply (cases "pc \<sigma> t";  simp)
  by presburger+


lemma readInv_writer_none_length_glb:
assumes  "thrdsvars"
and "TML_Read_invocation t  \<sigma> \<sigma>'"
  and " Begin_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
and " \<forall>t. (writer \<sigma> = None \<and>   pc \<sigma> syst = RecIdle  )  \<longrightarrow>  ( comploc  (memory(\<tau> \<sigma>) !  (length( memory (\<tau> \<sigma>))-1)   ) glb   = glb)  "
shows  "\<forall>t.( writer \<sigma>' = None \<and>     pc \<sigma>' syst = RecIdle )  \<longrightarrow>   ( comploc  (memory(\<tau> \<sigma>') !  (length( memory (\<tau> \<sigma>'))-1)   ) glb  = glb ) "
 using assms
  apply (simp add: TML_Read_invocation_def Begin_invocation_inv_def total_wfs_def )
  apply  (cases "pc \<sigma> t";  simp )
  by presburger+



lemma readResp_writer_none_length_glb:
assumes  "thrdsvars"
and "TML_Read_response t  \<sigma> \<sigma>'"
and " \<forall>t. (writer \<sigma> = None \<and>   pc \<sigma> syst = RecIdle  )  \<longrightarrow>  ( comploc  (memory(\<tau> \<sigma>) !  (length( memory (\<tau> \<sigma>))-1)   ) glb   = glb)  "
shows  "\<forall>t.( writer \<sigma>' = None \<and>     pc \<sigma>' syst = RecIdle )  \<longrightarrow>   ( comploc  (memory(\<tau> \<sigma>') !  (length( memory (\<tau> \<sigma>'))-1)   ) glb  = glb ) "
 using assms
  apply (simp add: TML_Read_response_def total_wfs_def )
  apply  (cases "pc \<sigma> t";  simp )
  by presburger+
 


lemma writeInv_writer_none_length_glb:
assumes  "thrdsvars"
and "TML_Write_invocation t  \<sigma> \<sigma>'"
  and " Write_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
and " \<forall>t. (writer \<sigma> = None \<and>   pc \<sigma> syst = RecIdle  )  \<longrightarrow>  ( comploc  (memory(\<tau> \<sigma>) !  (length( memory (\<tau> \<sigma>))-1)   ) glb   = glb)  "
shows  "\<forall>t.( writer \<sigma>' = None \<and>     pc \<sigma>' syst = RecIdle )  \<longrightarrow>   ( comploc  (memory(\<tau> \<sigma>') !  (length( memory (\<tau> \<sigma>'))-1)   ) glb  = glb ) "
 using assms
  apply (simp add: TML_Write_invocation_def  total_wfs_def )
  apply  (cases "pc \<sigma> t";  simp )
  by presburger+



lemma writeResp_writer_none_length_glb:
assumes  "thrdsvars"
and "TML_Write_response t  \<sigma> \<sigma>'"
 and " Write_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
and " \<forall>t. (writer \<sigma> = None \<and>   pc \<sigma> syst = RecIdle  )  \<longrightarrow>  ( comploc  (memory(\<tau> \<sigma>) !  (length( memory (\<tau> \<sigma>))-1)   ) glb   = glb)  "
shows  "\<forall>t.( writer \<sigma>' = None \<and>     pc \<sigma>' syst = RecIdle )  \<longrightarrow>   ( comploc  (memory(\<tau> \<sigma>') !  (length( memory (\<tau> \<sigma>'))-1)   ) glb  = glb ) "
 using assms
  apply (simp add: TML_Write_response_def total_wfs_def )
   apply  (cases "pc \<sigma> t";  simp )
  by presburger+




lemma commitInv_writer_none_length_glb:
assumes  "thrdsvars"
and "TML_Commit_invocation t  \<sigma> \<sigma>'"
  and " Commit_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
and " \<forall>t. (writer \<sigma> = None \<and>   pc \<sigma> syst = RecIdle  )  \<longrightarrow>  ( comploc  (memory(\<tau> \<sigma>) !  (length( memory (\<tau> \<sigma>))-1)   ) glb   = glb)  "
shows  "\<forall>t.( writer \<sigma>' = None \<and>     pc \<sigma>' syst = RecIdle )  \<longrightarrow>   ( comploc  (memory(\<tau> \<sigma>') !  (length( memory (\<tau> \<sigma>'))-1)   ) glb  = glb ) "
 using assms
  apply (simp add: TML_Commit_invocation_def total_wfs_def )
  apply  (cases "pc \<sigma> t";  simp )
  by presburger+






lemma commitResp_writer_none_length_glb:
assumes  "thrdsvars"
and "TML_Commit_response t  \<sigma> \<sigma>'"
and " \<forall>t. (writer \<sigma> = None \<and>   pc \<sigma> syst = RecIdle  )  \<longrightarrow>  ( comploc  (memory(\<tau> \<sigma>) !  (length( memory (\<tau> \<sigma>))-1)   ) glb   = glb)  "
shows  "\<forall>t.( writer \<sigma>' = None \<and>     pc \<sigma>' syst = RecIdle )  \<longrightarrow>   ( comploc  (memory(\<tau> \<sigma>') !  (length( memory (\<tau> \<sigma>'))-1)   ) glb  = glb ) "
 using assms
  apply (simp add: TML_Commit_response_def total_wfs_def )
   apply  (cases "pc \<sigma> t";  simp )
  by presburger+




(**********************************************mem_prop3***mem_prop4* completed***************FIXED 1810************************************************************)


(*1*)
lemma commit_mem_inv3:
  assumes "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
  and "  Commit_inv  t   ((pc \<sigma>) t) \<sigma>  "
  and "TML_Commit  t   \<sigma> \<sigma>'"
and " mem_tml_prop3   (\<tau> \<sigma>) "
and " glb_monotone_inv   (\<tau> \<sigma>) "
shows  " mem_tml_prop3   (\<tau> \<sigma>')"
 using assms
  apply (simp add:TML_Commit_def total_wfs_def Commit_inv_def  )
  apply (cases "pc \<sigma> t";  simp add: split if_splits )
  using assms(1) assms(2) sfence_mem_inv3 apply blast
  by (metis assms(1) assms(2) commit_up_glb_mem_inv3 lastVal_def)


(*1*)
lemma commit_mem_inv4:
  assumes "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
  and "  Commit_inv  t   ((pc \<sigma>) t) \<sigma>  "
  and "TML_Commit  t   \<sigma> \<sigma>'"
and " mem_tml_prop4   (\<tau> \<sigma>) "
and " glb_monotone_complete_inv   (\<tau> \<sigma>) "
shows  " mem_tml_prop4   (\<tau> \<sigma>')"
 using assms
  apply (simp add:TML_Commit_def total_wfs_def Commit_inv_def  )
  apply (cases "pc \<sigma> t";  simp add: split if_splits )
  using assms(1) assms(2) sfence_mem_inv4 apply blast
  using  commit_up_glb_mem_inv4
  by (metis assms(1) assms(2) commit_up_glb_mem_inv4 lastVal_def)



(*2*)
lemma begin_mem_inv3:
  assumes "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
  and "TML_Begin  t   \<sigma> \<sigma>'"
and " mem_tml_prop3   (\<tau> \<sigma>) "
shows  " mem_tml_prop3   (\<tau> \<sigma>')"
  using assms
 apply (simp add:TML_Begin_def total_wfs_def )
  apply (cases "pc \<sigma> t";  simp add: split if_splits )
  using assms(1) assms(2) ld_mem_inv3 apply blast
  by metis




(*2*)
lemma begin_mem_inv4:
  assumes "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
  and "TML_Begin  t   \<sigma> \<sigma>'"
and " mem_tml_prop4   (\<tau> \<sigma>) "
shows  " mem_tml_prop4   (\<tau> \<sigma>')"
  using assms
 apply (simp add:TML_Begin_def total_wfs_def )
  apply (cases "pc \<sigma> t";  simp add: split if_splits )
  using assms(1) assms(2) ld_mem_inv4 apply blast
  by metis


(*3*)
lemma write_mem_inv3:
  assumes "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
  and " Write_inv  t  ((pc \<sigma>) t) \<sigma> "
 and "TML_Write  t   \<sigma> \<sigma>'"
and " mem_tml_prop3   (\<tau> \<sigma>) "
and " glb_monotone_inv   (\<tau> \<sigma>) "
shows  " mem_tml_prop3   (\<tau> \<sigma>')"
  using assms
 apply (simp add:TML_Write_def Write_inv_def total_wfs_def )
  apply (cases "pc \<sigma> t";  simp add: split if_splits )
  apply ( simp add: split: if_split_asm)

  apply (case_tac "regs (\<tau> \<sigma>') t c1 \<noteq> 0 ")
  apply simp
  using  write_cas_succ_mem_inv_v3
  using assms(1) assms(2) apply blast
  using assms(1) assms(2) write_cas_fail_mem_inv_v3 apply blast
      defer
  using assms(1) assms(2) ld_mem_inv3 apply blast
  using assms(1) assms(2) write_write_a_mem_inv_v3 apply blast
  using assms(1) assms(2) flo_mem_inv3 apply blast
 apply (unfold  mem_tml_prop3_def)
  by (metis reg_write__crash reg_write_mem)

(*3*)
lemma write_mem_inv4:
  assumes "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
  and " Write_inv  t  ((pc \<sigma>) t) \<sigma> "
 and "TML_Write  t   \<sigma> \<sigma>'"
and " mem_tml_prop4   (\<tau> \<sigma>) "
and " glb_monotone_complete_inv   (\<tau> \<sigma>) "
shows  " mem_tml_prop4   (\<tau> \<sigma>')"
  using assms
 apply (simp add:TML_Write_def Write_inv_def total_wfs_def )
  apply (cases "pc \<sigma> t";  simp add: split if_splits )
  apply ( simp add: split: if_split_asm)

  apply (case_tac "regs (\<tau> \<sigma>') t c1 \<noteq> 0 ")
  apply simp
  using  write_cas_succ_mem_inv_v4
  using assms(1) assms(2) apply blast
  using assms(1) assms(2) write_cas_fail_mem_inv_v4 apply blast
      defer
  using assms(1) assms(2) ld_mem_inv4 apply blast
  using assms(1) assms(2) write_write_a_mem_inv_v4 apply blast
  using assms(1) assms(2) flo_mem_inv4 apply blast
 apply (unfold  mem_tml_prop4_def)
  by (metis reg_write__crash reg_write_mem)




lemma read_cas_succ_mem_inv_v3:
  assumes "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
and " \<tau> \<sigma> [CAS glb    regs ( \<tau> \<sigma>)  t DTML.loc (regs  (\<tau> \<sigma>)  t DTML.loc) c1]\<^sub>t \<tau> \<sigma>'"
and " mem_tml_prop3 (\<tau> \<sigma>) "
and " regs ( \<tau> \<sigma>') t c1 \<noteq> 0 "
and " writer \<sigma> = None "
and "pc \<sigma> syst = RecIdle"
and " \<forall>t. (writer \<sigma> = None \<and>   pc \<sigma> syst = RecIdle  )  \<longrightarrow>   comploc  (memory(\<tau> \<sigma>) !  (length( memory (\<tau> \<sigma>))-1)   ) glb   = glb  "
shows  " mem_tml_prop3 (\<tau> \<sigma>')"

  using assms
  apply (simp add: step_def)
  apply clarify
  apply (subgoal_tac "   \<tau> \<sigma>' =
           cas_succ_trans t ind glb (regs (\<tau> \<sigma>) t DTML.loc)
            (regs (\<tau> \<sigma>) t DTML.loc) c1 nv mnv (\<tau> \<sigma>)  ")
   prefer 2
   apply (metis assms(2) assms(5) cas_fail_reg total_wfs_def)
  apply (unfold total_wfs_def  glb_monotone_inv_def )

apply (subgoal_tac "   comploc  (memory(\<tau> \<sigma>') !  (length( memory (\<tau> \<sigma>))-1)   ) glb =     comploc  (memory(\<tau> \<sigma>) !  (length( memory (\<tau> \<sigma>))-1)   ) glb  ")
   prefer 2
  apply (metis One_nat_def assms(1) assms(2) aux comploc_cas_succ_same_trans diff_Suc_less gr_implies_not0 le0 less_SucE zero_less_Suc)



apply (subgoal_tac " \<forall> i. i < length (memory  (\<tau>  \<sigma>) ) \<longrightarrow>(memory  (\<tau>  \<sigma>')) ! i = (memory  (\<tau>  \<sigma>)) ! i ")
   prefer 2
  using le0 mem_l_casucc apply presburger
 apply (subgoal_tac " (State.loc (memory  (\<tau>  \<sigma>')!(length (memory  (\<tau>  \<sigma>)))) ) = glb ")
   prefer 2
  using cas_suc_loc apply presburger
  apply (subgoal_tac "  (length( memory (\<tau> \<sigma>))-1)  = (last_entry (\<tau> \<sigma>)  glb)   ")
   prefer 2
   apply (unfold last_entry_def)
   apply (subgoal_tac " \<forall>i. i \<in> last_entry_set (\<tau> \<sigma>) glb \<longrightarrow> i \<le>  (length( memory (\<tau> \<sigma>))-1) ")
    prefer 2
    apply (simp(no_asm) add: last_entry_set_def)
    apply (metis Nat.lessE One_nat_def diff_Suc_1 le_eq_less_or_eq)
   apply (subgoal_tac " (length( memory (\<tau> \<sigma>))-1)  \<in>  last_entry_set (\<tau> \<sigma>) glb ")
    prefer 2
  apply (metis Suc_diff_1 assms(2) assms(8) aux diff_less last_entry_def last_entry_in_last_entry_set last_entry_last_comp_loc less_antisym less_nat_zero_code less_numeral_extra(1) neq0_conv)


  using  finite_last_entry_set last_entry_in_last_entry_set
  apply (metis Max_eqI)
  apply (subgoal_tac "  compval (\<tau> \<sigma>')  (memory(\<tau> \<sigma>') !  (length( memory (\<tau>  \<sigma>)))  ) glb =  compval(\<tau> \<sigma>')   (memory(\<tau> \<sigma>') !  (length( memory (\<tau> \<sigma>))-1) ) glb ")
   prefer 2
  apply (metis assms(1) assms(2) assms(3) aux cas_suc_compval cas_suc_reg cas_succ_eq compval_cas_succ_same_trans lastVal_def last_entry_def)
  apply (unfold mem_tml_prop3_def)
  
  by (smt (z3) Nat.lessE Suc_lessD assms(1) assms(2) assms(8) cas_suc_mem_l compval_cas_succ_same_trans diff_Suc_1 i_noteqo_loc less_imp_le_nat less_trans_Suc)



lemma read_cas_succ_mem_inv_v4:
  assumes "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
and " \<tau> \<sigma> [CAS glb    regs ( \<tau> \<sigma>)  t DTML.loc (regs  (\<tau> \<sigma>)  t DTML.loc) c1]\<^sub>t \<tau> \<sigma>'"
and " mem_tml_prop4 (\<tau> \<sigma>) "
and " regs ( \<tau> \<sigma>') t c1 \<noteq> 0 "
and " writer \<sigma> = None "
and "pc \<sigma> syst = RecIdle"
and " \<forall>t. (writer \<sigma> = None \<and>   pc \<sigma> syst = RecIdle  )  \<longrightarrow>   comploc  (memory(\<tau> \<sigma>) !  (length( memory (\<tau> \<sigma>))-1)   ) glb   = glb  "
shows  " mem_tml_prop4 (\<tau> \<sigma>')"

  using assms
  apply (simp add: step_def)
  apply clarify
  apply (subgoal_tac "   \<tau> \<sigma>' =
           cas_succ_trans t ind glb (regs (\<tau> \<sigma>) t DTML.loc)
            (regs (\<tau> \<sigma>) t DTML.loc) c1 nv mnv (\<tau> \<sigma>)  ")
   prefer 2
   apply (metis assms(2) assms(5) cas_fail_reg total_wfs_def)
  apply (unfold total_wfs_def  glb_monotone_inv_def )
  apply (subgoal_tac "   comploc  (memory(\<tau> \<sigma>') !  (length( memory (\<tau> \<sigma>))-1)   ) glb =     comploc  (memory(\<tau> \<sigma>) !  (length( memory (\<tau> \<sigma>))-1)   ) glb  ")
   prefer 2
  apply (metis One_nat_def assms(1) assms(2) aux comploc_cas_succ_same_trans diff_Suc_less gr_implies_not0 le0 less_SucE zero_less_Suc)

apply (subgoal_tac " \<forall> i. i < length (memory  (\<tau>  \<sigma>) ) \<longrightarrow>(memory  (\<tau>  \<sigma>')) ! i = (memory  (\<tau>  \<sigma>)) ! i ")
   prefer 2
  using le0 mem_l_casucc apply presburger
 apply (subgoal_tac " (State.loc (memory  (\<tau>  \<sigma>')!(length (memory  (\<tau>  \<sigma>)))) ) = glb ")
   prefer 2
  using cas_suc_loc apply presburger
  apply (subgoal_tac "  (length( memory (\<tau> \<sigma>))-1)  = (last_entry (\<tau> \<sigma>)  glb)   ")
   prefer 2
   apply (unfold last_entry_def)
   apply (subgoal_tac " \<forall>i. i \<in> last_entry_set (\<tau> \<sigma>) glb \<longrightarrow> i \<le>  (length( memory (\<tau> \<sigma>))-1) ")
    prefer 2
    apply (simp(no_asm) add: last_entry_set_def)
    apply (metis Nat.lessE One_nat_def diff_Suc_1 le_eq_less_or_eq)
   apply (subgoal_tac " (length( memory (\<tau> \<sigma>))-1)  \<in>  last_entry_set (\<tau> \<sigma>) glb ")
    prefer 2

  apply (metis Suc_diff_1 assms(2) assms(8) aux diff_less last_entry_def last_entry_in_last_entry_set last_entry_last_comp_loc less_antisym less_nat_zero_code less_numeral_extra(1) neq0_conv)
  using  finite_last_entry_set last_entry_in_last_entry_set
  apply (metis Max_eqI)
  apply (subgoal_tac "  compval (\<tau> \<sigma>')  (memory(\<tau> \<sigma>') !  (length( memory (\<tau>  \<sigma>)))  ) glb =  compval(\<tau> \<sigma>')   (memory(\<tau> \<sigma>') !  (length( memory (\<tau> \<sigma>))-1) ) glb ")
   prefer 2
  apply (metis assms(1) assms(2) assms(3) aux cas_suc_compval cas_suc_reg cas_succ_eq compval_cas_succ_same_trans lastVal_def last_entry_def)
  apply (unfold mem_tml_prop4_def)

 apply (subgoal_tac " (comploc (memory  (\<tau>  \<sigma>')!(length (memory  (\<tau>  \<sigma>))))  glb ) = glb ")
   prefer 2
  using comploc_def apply presburger

  apply (subgoal_tac " (length (memory  (\<tau>  \<sigma>')))  = (length (memory  (\<tau>  \<sigma>))) + 1 ")
  prefer 2
  using length_s apply presburger
  by (smt (z3) Nat.add_0_right Nat.lessE add_Suc_right assms(1) assms(2) assms(8) compval_cas_succ_same_trans diff_add_inverse i_noteqo_loc le_antisym less_or_eq_imp_le less_trans_Suc not_less_eq plus_1_eq_Suc)



(*4*)
lemma  read_mem_inv3:
   assumes "thrdsvars"
   and "total_wfs (\<tau> \<sigma>)"
   and "TML_Read  t   \<sigma> \<sigma>'"
      and "Read_inv t  ((pc \<sigma>) t) \<sigma>" 
and " glb_monotone_inv   (\<tau> \<sigma>) "
and "  \<forall>  t.  (     writer \<sigma> = Some t \<longrightarrow> odd (lastVal glb  (\<tau> \<sigma>)) )"
and "pc \<sigma> syst = RecIdle"
and " \<forall>t. (writer \<sigma> = None \<and>   pc \<sigma> syst = RecIdle  )  \<longrightarrow>   comploc  (memory(\<tau> \<sigma>) !  (length( memory (\<tau> \<sigma>))-1)   ) glb   = glb  "
and " mem_tml_prop3   (\<tau> \<sigma>) "
shows  " mem_tml_prop3   (\<tau> \<sigma>')"
  using assms
 apply (unfold  total_wfs_def )
  apply (simp add:TML_Read_def Read_inv_def  )
  apply (cases "pc \<sigma> t";   simp add: split if_splits)
  using assms(1) assms(2) ld_mem_inv3 apply blast
      apply ( simp add: split: if_split_asm)
  apply (case_tac "regs (\<tau> \<sigma>') t c1= Suc 0 ")
  apply simp
      apply (subgoal_tac " writer \<sigma> = None ")
       prefer 2
      apply (metis Zero_not_Suc cas_fail_diff_lv not_Some_eq)
  apply (metis Zero_not_Suc assms(1) assms(2) assms(7) assms(8) assms(9) numeral_1_eq_Suc_0 numerals(1) read_cas_succ_mem_inv_v3)
     defer
  using assms(1) assms(2) ld_mem_inv3 apply blast
   apply presburger
  apply (subgoal_tac " memory (\<tau> \<sigma>) = memory (\<tau> \<sigma>') ")
   prefer 2
  apply (metis One_nat_def cas_fail_mem_same cas_lc)
  apply (unfold  mem_tml_prop3_def)
  by (smt (z3) Suc_lessD less_trans_Suc mem_structured_preserved val_eq_compval)




(*4*)
lemma  read_mem_inv4:
   assumes "thrdsvars"
   and "total_wfs (\<tau> \<sigma>)"
   and "TML_Read  t   \<sigma> \<sigma>'"
      and "Read_inv t  ((pc \<sigma>) t) \<sigma>" 
and " glb_monotone_inv   (\<tau> \<sigma>) "
and "  \<forall>  t.  (     writer \<sigma> = Some t \<longrightarrow> odd (lastVal glb  (\<tau> \<sigma>)) )"
and "pc \<sigma> syst = RecIdle"
and " \<forall>t. (writer \<sigma> = None \<and>   pc \<sigma> syst = RecIdle  )  \<longrightarrow>   comploc  (memory(\<tau> \<sigma>) !  (length( memory (\<tau> \<sigma>))-1)   ) glb   = glb  "
and " mem_tml_prop4   (\<tau> \<sigma>) "
shows  " mem_tml_prop4   (\<tau> \<sigma>')"
  using assms
 apply (unfold  total_wfs_def )
  apply (simp add:TML_Read_def Read_inv_def  )
  apply (cases "pc \<sigma> t";   simp add: split if_splits)
  using assms(1) assms(2) ld_mem_inv4 apply blast
      apply ( simp add: split: if_split_asm)
  apply (case_tac "regs (\<tau> \<sigma>') t c1= Suc 0 ")
  apply simp
      apply (subgoal_tac " writer \<sigma> = None ")
       prefer 2
      apply (metis Zero_not_Suc cas_fail_diff_lv not_Some_eq)
  apply (metis Zero_not_Suc assms(1) assms(2) assms(7) assms(8) assms(9) numeral_1_eq_Suc_0 numerals(1) read_cas_succ_mem_inv_v4)
     defer
  using assms(1) assms(2) ld_mem_inv4 apply blast
   apply presburger
  apply (subgoal_tac " memory (\<tau> \<sigma>) = memory (\<tau> \<sigma>') ")
   prefer 2
   apply (metis One_nat_def cas_fail_mem_same cas_lc)
  apply (unfold mem_tml_prop4_def)
  using compval_def comploc_def
  by (smt (z3) survived_val_preserved_cas)



(*5*)
lemma  crash_mem_inv3:
assumes  "thrdsvars"
and "TML_Crash  \<sigma> \<sigma>'"
and " mem_tml_prop3   (\<tau> \<sigma>) "
shows  " mem_tml_prop3   (\<tau> \<sigma>')"
  using assms
  apply(simp add:TML_Crash_def)
  apply (subgoal_tac " length (memory (\<tau> \<sigma>')) = 1 ")
  prefer 2
   apply (simp add: crash_step_def crash_trans_def)
  apply (unfold  mem_tml_prop3_def )
  by (metis bot.extremum_strict bot_nat_def less_one)



(*5*)
lemma  crash_mem_inv4:
assumes  "thrdsvars"
and "TML_Crash  \<sigma> \<sigma>'"
and " mem_tml_prop4   (\<tau> \<sigma>) "
shows  " mem_tml_prop4   (\<tau> \<sigma>')"
  using assms
  apply(simp add:TML_Crash_def)
  apply (subgoal_tac " length (memory (\<tau> \<sigma>')) = 1 ")
  prefer 2
   apply (simp add: crash_step_def crash_trans_def)
  apply (unfold  mem_tml_prop4_def )
  by (metis bot.extremum_strict bot_nat_def less_one)




(*6*)
lemma recover_mem_inv3:
 assumes "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
  and " TML_Recover syst   \<sigma> \<sigma>' "
 and "  Recover_inv  syst  ((pc \<sigma>) syst)  \<sigma>"
and " mem_tml_prop3   (\<tau> \<sigma>) "
shows  " mem_tml_prop3   (\<tau> \<sigma>')"
 using assms
  apply (simp add:TML_Recover_def total_wfs_def Recover_inv_def)
  apply (cases "pc \<sigma> syst";   simp add: split if_splits)
         apply (simp add: update_reg_def  mem_tml_prop3_def)
  apply presburger
        defer
  apply (metis assms(1) assms(2) flo_mem_inv3)
  apply (metis assms(1) assms(2) sfence_mem_inv3)
  apply (metis assms(1) assms(2) ld_mem_inv3)
  apply presburger
    prefer 3
    apply presburger
   prefer 3
  using mem_tml_prop3_def
  apply (metis assms(1) assms(2) get_key_in_dom write_write_a_mem_inv_v3)
        apply (subgoal_tac "(\<forall>i. 0 < i \<and> i < length (memory (\<tau> \<sigma>)) \<longrightarrow> Msg.loc (memory (\<tau> \<sigma>') ! i) \<noteq> glb)  ")
    prefer 2
    apply (elim conjE)
    apply (metis assms(1) assms(2) loc_wr_same)
   apply (unfold  mem_tml_prop3_def)
  apply (metis (no_types, opaque_lifting) Nat.add_0_right One_nat_def add_Suc_right le_imp_less_Suc less_eq_Suc_le less_nat_zero_code less_or_eq_imp_le linorder_neqE_nat not_less_eq st_lastEntry_lc st_mem_length)
   apply (subgoal_tac "(\<forall>i. 0 < i \<and> i < length (memory (\<tau> \<sigma>)) \<longrightarrow> Msg.loc (memory (\<tau> \<sigma>') ! i) \<noteq> glb)  ")
    prefer 2
    apply (elim conjE)
   apply (metis assms(1) assms(2) loc_wr_same)
  by (metis (no_types, opaque_lifting) Nat.add_0_right One_nat_def add_Suc_right less_nat_zero_code  linorder_neqE_nat not_less_eq  st_mem_length)


(*6*)
lemma recover_mem_inv4:
 assumes "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
  and " TML_Recover syst   \<sigma> \<sigma>' "
 and "  Recover_inv  syst  ((pc \<sigma>) syst)  \<sigma>"
and "  compval  (\<tau> \<sigma>)  (memory (\<tau> \<sigma>) !  0)        glb =   survived_val (\<tau> \<sigma>) glb  "
and " mem_tml_prop4   (\<tau> \<sigma>) "
shows  " mem_tml_prop4   (\<tau> \<sigma>')"
  using assms
  

  apply (simp add:TML_Recover_def total_wfs_def Recover_inv_def)


  apply (cases "pc \<sigma> syst";   simp add: split if_splits)
  apply (metis gr0I less_zeroE loc_eq_comploc mem_tml_prop4_def reg_write_mem)
 (* apply presburger*)
        defer
  apply (metis assms(1) assms(2) flo_mem_inv4)
  apply (metis assms(1) assms(2) sfence_mem_inv4)
  apply (metis assms(1) assms(2) ld_mem_inv4)
  apply presburger
    prefer 3
    apply presburger
   prefer 3
  using mem_tml_prop4_def
  apply (metis assms(1) assms(2) get_key_in_dom write_write_a_mem_inv_v4)
        apply (subgoal_tac "(\<forall>i. 0 < i \<and> i < length (memory (\<tau> \<sigma>)) \<longrightarrow> Msg.loc (memory (\<tau> \<sigma>') ! i) \<noteq> glb)  ")
    prefer 2
    apply (elim conjE)
    apply (metis assms(1) assms(2) loc_wr_same)
      apply (subgoal_tac "(\<forall>i. 0 < i \<and> i < length (memory (\<tau> \<sigma>)) \<longrightarrow> comploc (memory (\<tau> \<sigma>') ! i) glb \<noteq> glb)  ")
    prefer 2
  apply (metis assms(1) assms(2) comploc_wr_same less_imp_le_nat loc_eq_comploc)

    apply (subgoal_tac "(  comploc (memory (\<tau> \<sigma>') !  length (memory (\<tau> \<sigma>))     ) glb =  glb)  ")
    prefer 2
    apply (metis last_entry_loc mem_structured_preserved st_lastEntry_lc vbounded_preserved)

   apply (subgoal_tac "(  compval  (\<tau> \<sigma>')  (memory (\<tau> \<sigma>') !  length (memory (\<tau> \<sigma>))     ) glb =  Suc (Suc (survived_val (\<tau> \<sigma>) glb)))  ")
    prefer 2
  apply (metis (mono_tags, lifting) Store_Rules.st_lv_lc st_lastEntry_lc)
  apply (subgoal_tac "(comploc (memory (\<tau> \<sigma>) ! 0) glb = glb)  ")
    prefer 2
  apply (simp add: comploc_def)
  apply (smt (z3) Suc_n_not_le_n assms(2) assms(5) compval_def gr0I last_entry_last_comp_loc le_antisym lessI less_imp_le_nat linorder_neqE_nat mem_l_step mem_tml_prop4_def st_lastEntry_lc st_wfs_preserved survived_val_preserved_store)


  apply (subgoal_tac "(  comploc (memory (\<tau> \<sigma>') !  length (memory (\<tau> \<sigma>))     ) glb =  glb)  ")
    prefer 2
    apply (metis last_entry_loc mem_structured_preserved st_lastEntry_lc vbounded_preserved)

   apply (subgoal_tac "(  compval  (\<tau> \<sigma>')  (memory (\<tau> \<sigma>') !  length (memory (\<tau> \<sigma>))     ) glb =   (Suc (survived_val (\<tau> \<sigma>) glb)))  ")
    prefer 2
  apply (metis (mono_tags, lifting) Store_Rules.st_lv_lc st_lastEntry_lc)
  apply (subgoal_tac "(comploc (memory (\<tau> \<sigma>) ! 0) glb = glb)  ")
    prefer 2
  apply (simp add: comploc_def)
  by (smt (z3) assms(2) assms(5) compval_def gr0I last_entry_last_comp_loc le_antisym less_imp_le_nat linorder_neqE_nat loc_eq_comploc mem_l_step mem_structured_preserved mem_tml_prop4_def n_not_Suc_n st_lastEntry_lc st_wfs_preserved survived_val_preserved_store)




lemma beginInvr_mem_inv3:
assumes  "thrdsvars"
and "TML_Begin_invocation t  \<sigma> \<sigma>'"
  and " Begin_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
and " mem_tml_prop3   (\<tau> \<sigma>) "
shows  " mem_tml_prop3   (\<tau> \<sigma>')"
 using assms
  apply (simp add: TML_Begin_invocation_def Begin_invocation_inv_def total_wfs_def )
  by  (cases "pc \<sigma> t";  simp )




lemma beginRespr_mem_inv3:
assumes  "thrdsvars"
and "TML_Begin_response t  \<sigma> \<sigma>'"
and " mem_tml_prop3   (\<tau> \<sigma>) "
shows  " mem_tml_prop3   (\<tau> \<sigma>')"
 using assms
  apply (simp add: TML_Begin_response_def total_wfs_def )
  by (cases "pc \<sigma> t";  simp)



lemma readInvr_mem_inv3 :
assumes  "thrdsvars"
and "TML_Read_invocation t  \<sigma> \<sigma>'"
  and " Begin_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
and " mem_tml_prop3   (\<tau> \<sigma>) "
shows  " mem_tml_prop3   (\<tau> \<sigma>')"
 using assms
  apply (simp add: TML_Read_invocation_def Begin_invocation_inv_def total_wfs_def )
  by  (cases "pc \<sigma> t";  simp )




lemma readRespr_mem_inv3:
assumes  "thrdsvars"
and "TML_Read_response t  \<sigma> \<sigma>'"
and " mem_tml_prop3   (\<tau> \<sigma>) "
shows  " mem_tml_prop3   (\<tau> \<sigma>')"
 using assms
  apply (simp add: TML_Read_response_def total_wfs_def )
  by (cases "pc \<sigma> t";  simp )
 


lemma writeInvr_mem_inv3:
assumes  "thrdsvars"
and "TML_Write_invocation t  \<sigma> \<sigma>'"
  and " Write_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
and " mem_tml_prop3   (\<tau> \<sigma>) "
shows  " mem_tml_prop3   (\<tau> \<sigma>')"
 using assms
  apply (simp add: TML_Write_invocation_def  total_wfs_def )
  by  (cases "pc \<sigma> t";  simp )



lemma writeRespr_mem_inv3:
assumes  "thrdsvars"
and "TML_Write_response t  \<sigma> \<sigma>'"
 and " Write_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
and " mem_tml_prop3   (\<tau> \<sigma>) "
shows  " mem_tml_prop3   (\<tau> \<sigma>')"
 using assms
  apply (simp add: TML_Write_response_def total_wfs_def )
  by  (cases "pc \<sigma> t";  simp )




lemma commitInvr_mem_inv3:
assumes  "thrdsvars"
and "TML_Commit_invocation t  \<sigma> \<sigma>'"
  and " Commit_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
and " mem_tml_prop3   (\<tau> \<sigma>) "
shows  " mem_tml_prop3   (\<tau> \<sigma>')"
 using assms
  apply (simp add: TML_Commit_invocation_def total_wfs_def )
  by(cases "pc \<sigma> t";  simp)


lemma commitRespr_mem_inv3:
assumes  "thrdsvars"
and "TML_Commit_response t  \<sigma> \<sigma>'"
and " mem_tml_prop3   (\<tau> \<sigma>) "
shows  " mem_tml_prop3   (\<tau> \<sigma>')"
 using assms
  apply (simp add: TML_Commit_response_def total_wfs_def )
  by (cases "pc \<sigma> t";  simp)




lemma beginInvr_mem_inv4:
assumes  "thrdsvars"
and "TML_Begin_invocation t  \<sigma> \<sigma>'"
  and " Begin_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
and " mem_tml_prop4   (\<tau> \<sigma>) "
shows  " mem_tml_prop4   (\<tau> \<sigma>')"
 using assms
  apply (simp add: TML_Begin_invocation_def Begin_invocation_inv_def total_wfs_def )
  by  (cases "pc \<sigma> t";  simp )




lemma beginRespr_mem_inv4:
assumes  "thrdsvars"
and "TML_Begin_response t  \<sigma> \<sigma>'"
and " mem_tml_prop4   (\<tau> \<sigma>) "
shows  " mem_tml_prop4   (\<tau> \<sigma>')"
 using assms
  apply (simp add: TML_Begin_response_def total_wfs_def )
  by (cases "pc \<sigma> t";  simp)



lemma readInvr_mem_inv4 :
assumes  "thrdsvars"
and "TML_Read_invocation t  \<sigma> \<sigma>'"
  and " Begin_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
and " mem_tml_prop4   (\<tau> \<sigma>) "
shows  " mem_tml_prop4   (\<tau> \<sigma>')"
 using assms
  apply (simp add: TML_Read_invocation_def Begin_invocation_inv_def total_wfs_def )
  by  (cases "pc \<sigma> t";  simp )




lemma readRespr_mem_inv4:
assumes  "thrdsvars"
and "TML_Read_response t  \<sigma> \<sigma>'"
and " mem_tml_prop4   (\<tau> \<sigma>) "
shows  " mem_tml_prop4   (\<tau> \<sigma>')"
 using assms
  apply (simp add: TML_Read_response_def total_wfs_def )
  by (cases "pc \<sigma> t";  simp )
 


lemma writeInvr_mem_inv4:
assumes  "thrdsvars"
and "TML_Write_invocation t  \<sigma> \<sigma>'"
  and " Write_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
and " mem_tml_prop4   (\<tau> \<sigma>) "
shows  " mem_tml_prop4   (\<tau> \<sigma>')"
 using assms
  apply (simp add: TML_Write_invocation_def  total_wfs_def )
  by  (cases "pc \<sigma> t";  simp )



lemma writeRespr_mem_inv4:
assumes  "thrdsvars"
and "TML_Write_response t  \<sigma> \<sigma>'"
 and " Write_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
and " mem_tml_prop4   (\<tau> \<sigma>) "
shows  " mem_tml_prop4   (\<tau> \<sigma>')"
 using assms
  apply (simp add: TML_Write_response_def total_wfs_def )
  by  (cases "pc \<sigma> t";  simp )




lemma commitInvr_mem_inv4:
assumes  "thrdsvars"
and "TML_Commit_invocation t  \<sigma> \<sigma>'"
  and " Commit_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
and " mem_tml_prop4   (\<tau> \<sigma>) "
shows  " mem_tml_prop4   (\<tau> \<sigma>')"
 using assms
  apply (simp add: TML_Commit_invocation_def total_wfs_def )
  by(cases "pc \<sigma> t";  simp)


lemma commitRespr_mem_inv4:
assumes  "thrdsvars"
and "TML_Commit_response t  \<sigma> \<sigma>'"
and " mem_tml_prop4   (\<tau> \<sigma>) "
shows  " mem_tml_prop4   (\<tau> \<sigma>')"
 using assms
  apply (simp add: TML_Commit_response_def total_wfs_def )
  by (cases "pc \<sigma> t";  simp)




(*      apply ( simp add: split: if_splits)


  apply (subgoal_tac "even ( regs (\<tau> \<sigma>) syst c1 )")

  prefer 2*)

(***************************************************************)

(*
(*valOf  i l \<sigma> *)
definition "read_prop cs0 as0 \<equiv>
    pc cs0 syst = RecIdle   \<longrightarrow>(\<forall> n l. (0 \<le> (write_count ( (valOf n l (\<tau> cs0)) - (recoveredGlb  cs0) ))    \<and>
                                       (write_count ( (valOf n l (\<tau> cs0)) - (recoveredGlb  cs0)  ))  \<le> write_count (logical_glb cs0 ) 
                                      \<and>  comploc ((memory (\<tau> cs0))!n) glb= glb \<and> l \<noteq> glb) \<longrightarrow>  ((tmemory as0) !(write_count ( (valOf n l (\<tau> cs0))  - (recoveredGlb  cs0)  ))  ) l = valOf (last_entry_lim (\<tau> cs0) l n) l (\<tau> cs0)  ) "
*)


(*1*)
lemma  begin_complocglb_le_lvglb:
 assumes "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
  and "TML_Begin  t1   \<sigma> \<sigma>'"
and "    (\<forall> n. (0 \<le> n \<and> n  < length (memory (\<tau> \<sigma>))  \<and> comploc ((memory (\<tau> \<sigma>))!n) glb= glb) \<longrightarrow>  (valOf n glb  (\<tau> \<sigma>)) \<le> lastVal glb  (\<tau> \<sigma>) ) "
shows "    (\<forall> n. (0 \<le> n \<and> n  < length (memory (\<tau> \<sigma>'))  \<and> comploc ((memory (\<tau> \<sigma>'))!n) glb= glb) \<longrightarrow>  (valOf n glb  (\<tau> \<sigma>')) \<le> lastVal glb  (\<tau> \<sigma>') ) "
 using assms
  apply (simp add:TML_Begin_def total_wfs_def Begin_inv_def )
  apply (cases "pc \<sigma> t1";   simp add: split if_splits)
  apply (metis assms(2) lastVal_ni ld_crash ld_step_mem valOf_def)
  by (metis fun_upd_other)


(*2*)
lemma  read_complocglb_le_lvglb:
   assumes "thrdsvars"
   and "total_wfs (\<tau> \<sigma>)"
   and "TML_Read  t1   \<sigma> \<sigma>'"
      and "Read_inv t1  ((pc \<sigma>) t1) \<sigma>" 
and "  (  compval (\<tau> \<sigma>) (memory (\<tau> \<sigma>) ! 0) glb = survived_val (\<tau> \<sigma>) glb  \<and> (pc \<sigma> syst = RecIdle  \<longrightarrow>survived_val (\<tau> \<sigma>) glb   \<le>   recoveredGlb \<sigma>  )) "
and "glb_monotone_inv  (\<tau> \<sigma>)"
 and "pc \<sigma>  syst  = RecIdle  \<longrightarrow> ( lastVal glb (\<tau> \<sigma>)  \<ge>recoveredGlb \<sigma> ) "

and "   (\<forall> n. (0 \<le> n \<and> n  < length (memory (\<tau> \<sigma>))  \<and> comploc ((memory (\<tau> \<sigma>))!n) glb= glb) \<longrightarrow>  (valOf n glb  (\<tau> \<sigma>)) \<le> lastVal glb  (\<tau> \<sigma>) ) "
shows "   (\<forall> n. (0 \<le> n \<and> n  < length (memory (\<tau> \<sigma>'))  \<and> comploc ((memory (\<tau> \<sigma>'))!n) glb= glb) \<longrightarrow>  (valOf n glb  (\<tau> \<sigma>')) \<le> lastVal glb  (\<tau> \<sigma>') ) "
  using assms
  apply (unfold  total_wfs_def )
  apply (simp add:TML_Read_def Read_inv_def )
  apply (cases "pc \<sigma> t1";   simp add: split if_splits)
  apply (metis assms(2) bot_nat_0.extremum lastVal_ni ld_step_mem ld_valOf_nle_ni)
  apply (metis assms(6) cas_fail_crash)
  apply (case_tac " regs (\<tau> \<sigma>') t1 c1 = Suc 0  ")
      apply (subgoal_tac "lastVal glb (\<tau> \<sigma>') = lastVal glb (\<tau> \<sigma>) ")
       prefer 2

  apply (metis assms(2) cas_fail_diff_lv cas_fail_lastVal_same cas_possible_lv_lc lastVal_def)


 apply (simp add: step_def)
  apply clarify 
 apply (subgoal_tac "   \<tau> \<sigma>' =
           cas_succ_trans t1 ind glb (regs (\<tau> \<sigma>) t1 DTML.loc)
            (regs (\<tau> \<sigma>) t1 DTML.loc) c1 nv mnv (\<tau> \<sigma>)  ")
         prefer 2
       apply (metis One_nat_def cas_fail_reg zero_neq_one)

apply (subgoal_tac "  valOf (last_entry  (\<tau> \<sigma>)  glb)  glb  (\<tau> \<sigma>) =    (regs (\<tau> \<sigma>) t1 DTML.loc)")
   prefer 2
       apply (simp(no_asm) add: valOf_def)
  apply (metis cas_fail_reg nat.discI)


apply (subgoal_tac "   last_entry  (\<tau> \<sigma>')  glb =  length (memory (\<tau> \<sigma>)) ")
       prefer 2

       apply (metis Nat.add_0_right add_Suc_right cas_succ_lastentry diff_Suc_Suc length_s minus_nat.diff_0 numeral_1_eq_Suc_0 numerals(1))

 apply (subgoal_tac "  valOf (last_entry  (\<tau> \<sigma>')   glb)  glb  (\<tau> \<sigma>') =     (regs (\<tau> \<sigma>) t1 DTML.loc) ")
       prefer 2
  apply (metis lastVal_def valOf_def)


 (* apply (subgoal_tac "  valOf (last_entry  (\<tau> \<sigma>')   glb)  glb  (\<tau> \<sigma>') =     (regs (\<tau> \<sigma>) t1 DTML.loc) ")
   prefer 2
  apply (simp(no_asm) add: cas_succ_trans_def  valOf_def )*)
apply (subgoal_tac " (\<forall>i.(i>0\<and>i<length(memory  (\<tau> \<sigma>) )) \<longrightarrow> ( memory  (\<tau> \<sigma>) )!i =( memory  (\<tau> \<sigma>') )!i) ")
   prefer 2

  apply (metis mem_l_casucc nat_less_le)




apply (subgoal_tac " \<forall> i .(i>0\<and>i<length(memory  (\<tau> \<sigma>) )) \<longrightarrow>  ( valOf  i glb   (\<tau> \<sigma>')   = valOf  i glb   (\<tau> \<sigma>)  )")
   prefer 2
        apply (simp(no_asm)  add: valOf_def)
  apply (metis survived_val_cas_succ)


apply (subgoal_tac "  \<forall>  j . (  (0 < j \<and>  j < length(memory (\<tau> \<sigma>))  \<and> comploc ((memory (\<tau> \<sigma>))!j) glb = glb)   \<longrightarrow>  valOf  j  glb  (\<tau> \<sigma>)  \<le>   (regs (\<tau> \<sigma>) t1 DTML.loc) ) ")
  prefer 2  
apply (subgoal_tac " \<forall> j . (0 < j \<and>  j < length(memory  (\<tau> \<sigma>))  \<and> comploc ((memory  (\<tau> \<sigma>))!j) glb = glb)  \<longrightarrow>  j \<le> last_entry   (\<tau> \<sigma>)  glb  ")
   prefer 2
    apply (subgoal_tac "\<forall> j .(0 <  j \<and>  j < length(memory  (\<tau> \<sigma>))  \<and> comploc ((memory  (\<tau> \<sigma>))!j) glb = glb)  \<longrightarrow>  j \<in> last_entry_set  (\<tau> \<sigma>) glb")
  prefer 2
          apply (simp (no_asm) add: last_entry_set_def)



    apply (subgoal_tac "\<forall> i. i \<in>  last_entry_set (\<tau> \<sigma>)  glb \<longrightarrow> i \<le>  last_entry  (\<tau> \<sigma>)  glb  ")
     prefer 2
  apply (simp(no_asm) add: last_entry_def)
  using  finite_last_entry_set    apply (metis Max_ge)
       apply metis
  apply (metis assms(8) lastVal_def nat_less_le valOf_def)



      apply (intro conjI impI)
       apply (simp(no_asm) add: valOf_def )
       apply (subgoal_tac " memory (\<tau> \<sigma>') ! n = Init_Msg ")
        prefer 2
        apply (unfold mem_structured_def)
        apply blast
       apply (metis le_trans survived_val_cas_succ)
      apply (subgoal_tac " n \<noteq> 0 ")
       prefer 2
  apply (metis cas_succ_wfs mem_structured_def)
      apply (subgoal_tac " lastVal glb (\<tau> \<sigma>) =  regs (\<tau> \<sigma>) t1 DTML.loc")
  prefer 2
       apply (metis lastVal_def valOf_def)

      apply (subgoal_tac " \<forall>j. 0 < j \<and> j < length (memory (\<tau> \<sigma>')) \<and> comploc (memory (\<tau> \<sigma>') ! j) glb = glb \<longrightarrow> valOf j glb (\<tau> \<sigma>') \<le> regs (\<tau> \<sigma>) t1 DTML.loc ")
       prefer 2

apply (subgoal_tac " \<forall> j . (0 < j \<and>  j < length(memory (\<tau> \<sigma>') )  \<and> comploc ((memory )(\<tau> \<sigma>')!j) glb = glb)  \<longrightarrow>  j \<le> last_entry  (\<tau> \<sigma>')  glb  ")
   prefer 2
    apply (subgoal_tac "\<forall> j .(0 < j \<and>  j < length(memory (\<tau> \<sigma>'))  \<and> comploc ((memory (\<tau> \<sigma>'))!j) glb = glb)  \<longrightarrow>  j \<in> last_entry_set (\<tau> \<sigma>') glb")
  prefer 2
     apply (simp(no_asm) add: last_entry_set_def)
    apply (subgoal_tac "\<forall> i. i \<in>  last_entry_set  (\<tau> \<sigma>')  glb \<longrightarrow> i \<le>  last_entry  (\<tau> \<sigma>')  glb  ")
     prefer 2
  apply (simp(no_asm) add: last_entry_def)
  using  finite_last_entry_set    apply (metis Max_ge)
    apply metis
  apply (metis le_SucI nat_le_linear nless_le)
  apply (metis assms(2) cas_succ_wfs loc_eq_comploc neq0_conv total_wfs_def)

     apply (subgoal_tac " memory (\<tau> \<sigma>) = memory (\<tau> \<sigma>' ) ")
      prefer 2
  apply (metis assms(2) cas_fail_mem_same cas_lc numeral_1_eq_Suc_0 numerals(1) total_wfs_def)
  apply (metis (no_types, opaque_lifting) aux cas_fail_lv_ni cas_possible_lv_lc compval_def gr_implies_not_zero lastVal_def mem_structured_def neq0_conv survived_val_preserved_cas valOf_def val_eq_compval zero_less_iff_neq_zero)
  apply (metis assms(2) lastVal_ni ld_crash ld_step_mem mem_structured_def valOf_def)
  by  metis


(*3*)
lemma write_complocglb_le_lvglb:
  assumes "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
  and " Write_inv  t  ((pc \<sigma>) t) \<sigma> "
 and "TML_Write  t   \<sigma> \<sigma>'"
and "glb_monotone_inv  (\<tau> \<sigma>)"
 and "pc \<sigma>  syst  = RecIdle  \<longrightarrow> ( lastVal glb (\<tau> \<sigma>)  \<ge>recoveredGlb \<sigma> ) "
and "  (  compval (\<tau> \<sigma>) (memory (\<tau> \<sigma>) ! 0) glb = survived_val (\<tau> \<sigma>) glb  \<and> (pc \<sigma> syst = RecIdle  \<longrightarrow>survived_val (\<tau> \<sigma>) glb   \<le>   recoveredGlb \<sigma>  )) "
and "    (\<forall> n. (0 \<le> n \<and> n  < length (memory (\<tau> \<sigma>))  \<and> comploc ((memory (\<tau> \<sigma>))!n) glb= glb) \<longrightarrow>  (valOf n glb  (\<tau> \<sigma>)) \<le> lastVal glb  (\<tau> \<sigma>) ) "
and " syst \<noteq> t"
shows " (\<forall> n. (0 \<le> n \<and> n  < length (memory (\<tau> \<sigma>'))  \<and> comploc ((memory (\<tau> \<sigma>'))!n) glb= glb) \<longrightarrow>  (valOf n glb  (\<tau> \<sigma>')) \<le> lastVal glb  (\<tau> \<sigma>') ) "
  using assms

 apply (simp add:TML_Write_def Write_inv_def total_wfs_def )
  apply (cases "pc \<sigma> t";  simp add: split if_splits )
  apply ( simp add: split: if_split_asm)

       apply (case_tac " 0 < regs (\<tau> \<sigma>') t c1   ")

   (*   apply (subgoal_tac "lastVal glb (\<tau> \<sigma>') = lastVal glb (\<tau> \<sigma>)+1 ")
       prefer 2

  apply (metis assms(2) cas_fail_diff_lv cas_fail_lastVal_same cas_possible_lv_lc lastVal_def)*)


 apply (simp add: step_def)
  apply clarify 
 apply (subgoal_tac "    \<tau> \<sigma>' =
                 cas_succ_trans t ind glb (regs (\<tau> \<sigma>) t DTML.loc) (Suc (regs (\<tau> \<sigma>) t DTML.loc)) c1 nv mnv (\<tau> \<sigma>) ")
         prefer 2
  apply (metis cas_fail_reg gr_implies_not0)

apply (subgoal_tac "  valOf (last_entry  (\<tau> \<sigma>)  glb)  glb  (\<tau> \<sigma>) =    (regs (\<tau> \<sigma>) t DTML.loc)")
   prefer 2
  apply (metis Suc_leI Suc_le_D Zero_not_Suc cas_fail_reg compval_def valOf_def)


apply (subgoal_tac "   last_entry  (\<tau> \<sigma>')  glb =  length (memory (\<tau> \<sigma>)) ")
       prefer 2

       apply (metis Nat.add_0_right add_Suc_right cas_succ_lastentry diff_Suc_Suc length_s minus_nat.diff_0 numeral_1_eq_Suc_0 numerals(1))

 apply (subgoal_tac "  valOf (last_entry  (\<tau> \<sigma>')   glb)  glb  (\<tau> \<sigma>') =     (regs (\<tau> \<sigma>) t DTML.loc)+1 ")
         prefer 2
  apply (metis Suc_eq_plus1 cas_suc_compval valOf_def)


 (* apply (subgoal_tac "  valOf (last_entry  (\<tau> \<sigma>')   glb)  glb  (\<tau> \<sigma>') =     (regs (\<tau> \<sigma>) t1 DTML.loc) ")
   prefer 2
  apply (simp(no_asm) add: cas_succ_trans_def  valOf_def )*)
apply (subgoal_tac " (\<forall>i.(i>0\<and>i<length(memory  (\<tau> \<sigma>) )) \<longrightarrow> ( memory  (\<tau> \<sigma>) )!i =( memory  (\<tau> \<sigma>') )!i) ")
   prefer 2

  apply (metis mem_l_casucc nat_less_le)




apply (subgoal_tac " \<forall> i .(i>0\<and>i<length(memory  (\<tau> \<sigma>) )) \<longrightarrow>  ( valOf  i glb   (\<tau> \<sigma>')   = valOf  i glb   (\<tau> \<sigma>)  )")
   prefer 2
        apply (simp(no_asm)  add: valOf_def)
  apply (metis survived_val_cas_succ)


apply (subgoal_tac "  \<forall>  j . (  (0 < j \<and>  j < length(memory (\<tau> \<sigma>))  \<and> comploc ((memory (\<tau> \<sigma>))!j) glb = glb)   \<longrightarrow>  valOf  j  glb  (\<tau> \<sigma>)  \<le>   (regs (\<tau> \<sigma>) t DTML.loc) ) ")
  prefer 2  
apply (subgoal_tac " \<forall> j . (0 < j \<and>  j < length(memory  (\<tau> \<sigma>))  \<and> comploc ((memory  (\<tau> \<sigma>))!j) glb = glb)  \<longrightarrow>  j \<le> last_entry   (\<tau> \<sigma>)  glb  ")
   prefer 2
    apply (subgoal_tac "\<forall> j .(0 <  j \<and>  j < length(memory  (\<tau> \<sigma>))  \<and> comploc ((memory  (\<tau> \<sigma>))!j) glb = glb)  \<longrightarrow>  j \<in> last_entry_set  (\<tau> \<sigma>) glb")
  prefer 2
          apply (simp (no_asm) add: last_entry_set_def)



    apply (subgoal_tac "\<forall> i. i \<in>  last_entry_set (\<tau> \<sigma>)  glb \<longrightarrow> i \<le>  last_entry  (\<tau> \<sigma>)  glb  ")
     prefer 2
  apply (simp(no_asm) add: last_entry_def)
  using  finite_last_entry_set    apply (metis Max_ge)
          apply metis
  apply (metis comploc_def lastVal_def valOf_def)


      apply (intro conjI impI)
       apply (simp(no_asm) add: valOf_def )
       apply (subgoal_tac " memory (\<tau> \<sigma>') ! n = Init_Msg ")
        prefer 2
        apply (unfold mem_structured_def)
          apply blast
  
  apply (metis Suc_eq_plus1 lastVal_def le_trans less_Suc_eq_le less_imp_le_nat survived_val_cas_succ valOf_def)

      apply (subgoal_tac " n \<noteq> 0 ")
       prefer 2
  apply (metis cas_succ_wfs mem_structured_def)
      apply (subgoal_tac " lastVal glb (\<tau> \<sigma>) =  regs (\<tau> \<sigma>) t DTML.loc")
  prefer 2
       apply (metis lastVal_def valOf_def)

      apply (subgoal_tac " \<forall>j. 0 < j \<and> j < length (memory (\<tau> \<sigma>')) \<and> comploc (memory (\<tau> \<sigma>') ! j) glb = glb \<longrightarrow> valOf j glb (\<tau> \<sigma>') \<le> regs (\<tau> \<sigma>) t DTML.loc+1 ")
       prefer 2

apply (subgoal_tac " \<forall> j . (0 < j \<and>  j < length(memory (\<tau> \<sigma>') )  \<and> comploc ((memory )(\<tau> \<sigma>')!j) glb = glb)  \<longrightarrow>  j \<le> last_entry  (\<tau> \<sigma>')  glb  ")
   prefer 2
    apply (subgoal_tac "\<forall> j .(0 < j \<and>  j < length(memory (\<tau> \<sigma>'))  \<and> comploc ((memory (\<tau> \<sigma>'))!j) glb = glb)  \<longrightarrow>  j \<in> last_entry_set (\<tau> \<sigma>') glb")
  prefer 2
     apply (simp(no_asm) add: last_entry_set_def)
    apply (subgoal_tac "\<forall> i. i \<in>  last_entry_set  (\<tau> \<sigma>')  glb \<longrightarrow> i \<le>  last_entry  (\<tau> \<sigma>')  glb  ")
     prefer 2
  apply (simp(no_asm) add: last_entry_def)
  using  finite_last_entry_set    apply (metis Max_ge)
          apply metis
  apply (metis le_eq_less_or_eq trans_le_add1)
  apply (metis Suc_eq_plus1 bot_nat_0.not_eq_extremum lastVal_def le_Suc_eq length_s less_SucE valOf_def)
       apply (subgoal_tac " memory (\<tau> \<sigma>) =memory (\<tau> \<sigma>' ) ")
  prefer 2
  apply (metis cas_fail_mem_same mem_structured_def neq0_conv)
       apply (simp add: valOf_def)
  apply (smt (z3) assms(2) cas_fail_lastVal_same survived_val_preserved_cas)
  apply (metis reg_write__crash reg_write_lastVal_ni reg_write_mem valOf_def)
  apply (metis (no_types, opaque_lifting) assms(2) lastVal_ni ld_crash ld_step_mem total_wfs_def valOf_def)
 
     apply (subgoal_tac "comploc ((memory (\<tau> \<sigma>'))! (length(memory (\<tau> \<sigma>)))) glb \<noteq> glb ")
      prefer 2
  apply (metis (no_types, lifting) assms(2) last_entry_bounded length_greater_0_conv loc_eq_comploc mem_structured_preserved st_lastEntry_lc st_loc total_wfs_def vbounded_preserved)
     apply (subgoal_tac " (length(memory (\<tau> \<sigma>'))) = (length(memory (\<tau> \<sigma>))) +1 ")
      prefer 2
  apply (meson st_mem_length)
apply (subgoal_tac " (\<forall>i.(i>0\<and>i<length(memory  (\<tau> \<sigma>) )) \<longrightarrow> ( memory  (\<tau> \<sigma>) )!i =( memory  (\<tau> \<sigma>') )!i) ")
   prefer 2
  apply (metis mem_l_step nat_less_le)
    apply (simp add: valOf_def)
  apply (smt (z3) assms(2) le_numeral_extra(3) le_trans length_greater_0_conv less_Suc_eq_0_disj less_antisym mem_l_step st_lv__daddr_ni survived_val_preserved_store)

 apply (subgoal_tac " memory (\<tau> \<sigma>) =memory (\<tau> \<sigma>' ) ")
  prefer 2
    apply (simp add: step_def)
  by (metis assms(2) flo_crash flo_lastVal_ni valOf_def)


(*4*)
lemma commit_complocglb_le_lvglb:
  assumes "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
  and "  Commit_inv  t   ((pc \<sigma>) t) \<sigma>  "
  and "TML_Commit  t   \<sigma> \<sigma>'"
and "glb_monotone_inv  (\<tau> \<sigma>)"
 and "pc \<sigma>  syst  = RecIdle  \<longrightarrow> ( lastVal glb (\<tau> \<sigma>)  \<ge>recoveredGlb \<sigma> ) "
and "  (  compval (\<tau> \<sigma>) (memory (\<tau> \<sigma>) ! 0) glb = survived_val (\<tau> \<sigma>) glb  \<and> (pc \<sigma> syst = RecIdle  \<longrightarrow>survived_val (\<tau> \<sigma>) glb   \<le>   recoveredGlb \<sigma>  )) "
and "   (\<forall> n. (0 \<le> n \<and> n  < length (memory (\<tau> \<sigma>))  \<and> comploc ((memory (\<tau> \<sigma>))!n) glb= glb) \<longrightarrow>  (valOf n glb  (\<tau> \<sigma>)) \<le> lastVal glb  (\<tau> \<sigma>) ) "
and " syst \<noteq> t"
shows "    (\<forall> n. (0 \<le> n \<and> n  < length (memory (\<tau> \<sigma>'))  \<and> comploc ((memory (\<tau> \<sigma>'))!n) glb= glb) \<longrightarrow>  (valOf n glb  (\<tau> \<sigma>')) \<le> lastVal glb  (\<tau> \<sigma>') ) "
  using assms
  apply (unfold  total_wfs_def )
  apply (simp add:TML_Commit_def Commit_inv_def  )
  apply (cases "pc \<sigma> t";simp   )

  
    apply (metis lastVal_def sf_nlv_ni sfence_crash step_mem_sfence valOf_def)

apply (subgoal_tac " \<forall> i. i < length (memory  (\<tau>  \<sigma>) ) \<longrightarrow>(memory  (\<tau>  \<sigma>')) ! i = (memory  (\<tau>  \<sigma>)) ! i ")
   prefer 2
  apply (metis le0 mem_l_step)
 apply (subgoal_tac " (State.loc (memory  (\<tau>  \<sigma>')!(length (memory  (\<tau>  \<sigma>)))) ) = glb ")
   prefer 2
  apply (meson st_loc)
  apply (subgoal_tac " compval (\<tau> \<sigma>)   ((memory  (\<tau>  \<sigma>))!  (last_entry (\<tau> \<sigma>)  glb))    glb    \<ge>   recoveredGlb \<sigma>   ")
         prefer 2
  apply (metis lastVal_def)
        apply (subgoal_tac " compval (\<tau> \<sigma>)   ((memory  (\<tau>  \<sigma>))!  (last_entry (\<tau> \<sigma>)  glb))    glb   =  (regs (\<tau> \<sigma>) t DTML.loc)")
      prefer 2
  apply (metis lastVal_def)
 apply (subgoal_tac "compval (\<tau> \<sigma>')  (memory (\<tau> \<sigma>') !length(memory  (\<tau> \<sigma>)))  glb    \<ge>   recoveredGlb \<sigma> ")
  prefer 2       
           apply (metis Store_Rules.st_lv_lc le_Suc_eq st_lastEntry_lc)
  apply (subgoal_tac " length (memory  (\<tau> \<sigma>')) = length(memory  (\<tau> \<sigma>)) + 1 ")
  prefer 2
  apply (meson st_mem_length)
     apply (intro allI conjI impI)
  apply (smt (z3) Nat.add_0_right Store_Rules.st_lv_lc add_Suc_right assms(1) assms(2) bot_nat_0.extremum compval_wr_same less_SucE nat_le_linear not_less_eq_eq numeral_1_eq_Suc_0 numerals(1) st_lastEntry_lc st_lastVal_lc valOf_def)
  by  (smt (z3) Nat.add_0_right Store_Rules.st_lv_lc add_Suc_right assms(1) assms(2) bot_nat_0.extremum compval_wr_same less_SucE nat_le_linear not_less_eq_eq numeral_1_eq_Suc_0 numerals(1) st_lastEntry_lc st_lastVal_lc valOf_def)
 



(*5*)
lemma crash_locglb_le_lvglb:
assumes  "thrdsvars"
and "TML_Crash  \<sigma> \<sigma>'"
and "   (\<forall> n. (0 \<le> n \<and> n  < length (memory (\<tau> \<sigma>))  \<and> comploc ((memory (\<tau> \<sigma>))!n) glb= glb) \<longrightarrow>  (valOf n glb  (\<tau> \<sigma>)) \<le> lastVal glb  (\<tau> \<sigma>) ) "
shows "   (\<forall> n. (0 \<le> n \<and> n  < length (memory (\<tau> \<sigma>'))  \<and> comploc ((memory (\<tau> \<sigma>'))!n) glb= glb) \<longrightarrow>  (valOf n glb  (\<tau> \<sigma>')) \<le> lastVal glb  (\<tau> \<sigma>') ) "
  using assms
  apply (simp add:    TML_Crash_def  total_wfs_def   )
 apply (subgoal_tac " length (memory (\<tau> \<sigma>')) = 1 ")
  prefer 2
   apply (simp add: crash_step_def crash_trans_def)

apply (subgoal_tac " last_entry_set (\<tau> \<sigma>') glb  = {0} ")
    prefer 2
   apply (simp add: last_entry_set_def crash_step_def crash_trans_def)
  apply fastforce

  apply (subgoal_tac " last_entry (\<tau> \<sigma>') glb   = 0 " )
   prefer 2
   apply (simp add: last_entry_def)
  apply (subgoal_tac "  survived_val (\<tau> \<sigma>') glb = lastVal glb   (\<tau> \<sigma>') ")
  prefer 2
   apply (simp add: crash_step_def crash_trans_def lastVal_def )
  by (metis lastVal_def less_one order_class.order_eq_iff valOf_def)



(*6*)
lemma  recover_locglb_le_lvglb:
 assumes "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
  and " TML_Recover syst   \<sigma> \<sigma>' "
 and "  Recover_inv  syst  ((pc \<sigma>) syst)  \<sigma>"
and "  (\<forall> n. (0 \<le> n \<and> n  < length (memory (\<tau> \<sigma>))  \<and> comploc ((memory (\<tau> \<sigma>))!n) glb= glb) \<longrightarrow>  (valOf n glb  (\<tau> \<sigma>)) \<le> lastVal glb  (\<tau> \<sigma>) ) "
and "  (  compval (\<tau> \<sigma>) (memory (\<tau> \<sigma>) ! 0) glb = survived_val (\<tau> \<sigma>) glb  \<and> (pc \<sigma> syst = RecIdle  \<longrightarrow>survived_val (\<tau> \<sigma>) glb   \<le>   recoveredGlb \<sigma>  )) "
shows "   (\<forall> n. (0 \<le> n \<and> n  < length (memory (\<tau> \<sigma>'))  \<and> comploc ((memory (\<tau> \<sigma>'))!n) glb= glb) \<longrightarrow>  (valOf n glb  (\<tau> \<sigma>')) \<le> lastVal glb  (\<tau> \<sigma>') ) "
 using assms
  apply (simp add:TML_Recover_def total_wfs_def Recover_inv_def )


  apply (cases "pc \<sigma> syst";   simp add: split if_splits)



         apply (case_tac "  even (regs (\<tau> \<sigma>) syst c1)")

  apply (metis reg_write__crash reg_write_lastVal_ni reg_write_mem valOf_def)
  apply (metis reg_write__crash reg_write_lastVal_ni reg_write_mem valOf_def)


     apply (subgoal_tac "comploc ((memory (\<tau> \<sigma>'))! (length(memory (\<tau> \<sigma>)))) glb \<noteq> glb ")
         prefer 2
  apply (metis gr_implies_not0 i_noteqo_loc last_entry_bounded last_entry_loc mem_structured_preserved nat_neq_iff st_lastEntry_lc vbounded_preserved)
     apply (subgoal_tac " (length(memory (\<tau> \<sigma>'))) = (length(memory (\<tau> \<sigma>))) +1 ")
      prefer 2
  apply (meson st_mem_length)
apply (subgoal_tac " (\<forall>i.(i>0\<and>i<length(memory  (\<tau> \<sigma>) )) \<longrightarrow> ( memory  (\<tau> \<sigma>) )!i =( memory  (\<tau> \<sigma>') )!i) ")
   prefer 2
  apply (metis mem_l_step nat_less_le)
    apply (simp add: valOf_def)
  apply (smt (z3) assms(2) less_Suc_eq less_Suc_eq_le mem_l_step st_loc st_lv__daddr_ni survived_val_preserved_store zero_less_Suc)
       apply (subgoal_tac " memory (\<tau> \<sigma>) =  memory (\<tau> \<sigma>') ")
        prefer 2
  apply (simp add: step_def)
  apply (metis flo_crash gr_zeroI lastVal_def last_entry_bounded last_entry_loc loc_eq_comploc mem_structured_preserved valOf_def vbounded_preserved)
  apply (metis lastVal_def sf_nlv_ni sfence_crash step_mem_sfence valOf_def)
  apply (metis lastVal_def ld_crash ld_last_entry ld_step_mem valOf_def)
  apply presburger
   apply (subgoal_tac "  lastVal glb (\<tau> \<sigma>') = Suc (Suc (survived_val (\<tau> \<sigma>) glb))")
  prefer 2
  apply (meson st_lastVal_lc)
   apply (subgoal_tac "  lastVal glb (\<tau> \<sigma>) = (survived_val (\<tau> \<sigma>) glb) ")
    prefer 2
  apply (metis assms(6) gr0I i_noteqo_loc lastVal_def last_entry_bounded last_entry_loc)
   apply (simp add: valOf_def)

apply (subgoal_tac " \<forall> i. i < length (memory  (\<tau>  \<sigma>) ) \<longrightarrow>(memory  (\<tau>  \<sigma>')) ! i = (memory  (\<tau>  \<sigma>)) ! i ")
   prefer 2
  apply (metis le0 mem_l_step)
 apply (subgoal_tac " (State.loc (memory  (\<tau>  \<sigma>')!(length (memory  (\<tau>  \<sigma>)))) ) = glb ")
   prefer 2
  apply (meson st_loc)

        apply (subgoal_tac " compval (\<tau> \<sigma>)   ((memory  (\<tau>  \<sigma>))!  (last_entry (\<tau> \<sigma>)  glb))    glb   = (survived_val (\<tau> \<sigma>) glb)")
    prefer 2
  apply (metis lastVal_def)

  apply (subgoal_tac " length (memory  (\<tau> \<sigma>')) = length(memory  (\<tau> \<sigma>)) + 1 ")
  prefer 2
  apply (meson st_mem_length)
     apply (intro allI conjI impI)
  apply (metis le_SucI le_add2 plus_1_eq_Suc survived_val_preserved_store)
  apply (smt (z3) Nat.add_0_right add_Suc_right le_Suc_eq less_SucE numeral_1_eq_Suc_0 numerals(1) st_val)


 apply (subgoal_tac "  lastVal glb (\<tau> \<sigma>') =  (Suc (survived_val (\<tau> \<sigma>) glb))")
  prefer 2
  apply (meson st_lastVal_lc)
   apply (subgoal_tac "  lastVal glb (\<tau> \<sigma>) = (survived_val (\<tau> \<sigma>) glb) ")
    prefer 2
  apply (metis assms(6) gr0I i_noteqo_loc lastVal_def last_entry_bounded last_entry_loc)
   apply (simp add: valOf_def)

apply (subgoal_tac " \<forall> i. i < length (memory  (\<tau>  \<sigma>) ) \<longrightarrow>(memory  (\<tau>  \<sigma>')) ! i = (memory  (\<tau>  \<sigma>)) ! i ")
   prefer 2
  apply (metis le0 mem_l_step)
 apply (subgoal_tac " (State.loc (memory  (\<tau>  \<sigma>')!(length (memory  (\<tau>  \<sigma>)))) ) = glb ")
   prefer 2
  apply (meson st_loc)

        apply (subgoal_tac " compval (\<tau> \<sigma>)   ((memory  (\<tau>  \<sigma>))!  (last_entry (\<tau> \<sigma>)  glb))    glb   = (survived_val (\<tau> \<sigma>) glb)")
    prefer 2
  apply (metis lastVal_def)

  apply (subgoal_tac " length (memory  (\<tau> \<sigma>')) = length(memory  (\<tau> \<sigma>)) + 1 ")
  prefer 2
  apply (meson st_mem_length)
     apply (intro allI conjI impI)
  apply (metis le_SucI le_add2 plus_1_eq_Suc survived_val_preserved_store)
  apply (smt (z3) Nat.add_0_right add_Suc_right le_Suc_eq less_SucE numeral_1_eq_Suc_0 numerals(1) st_val)

  by presburger





lemma beginInvr_locglb_le_lvglb:
assumes  "thrdsvars"
and "TML_Begin_invocation t  \<sigma> \<sigma>'"
  and " Begin_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
and "   (\<forall> n. (0 \<le> n \<and> n  < length (memory (\<tau> \<sigma>))  \<and> comploc ((memory (\<tau> \<sigma>))!n) glb= glb) \<longrightarrow>  (valOf n glb  (\<tau> \<sigma>)) \<le> lastVal glb  (\<tau> \<sigma>) ) "
shows "   (\<forall> n. (0 \<le> n \<and> n  < length (memory (\<tau> \<sigma>'))  \<and> comploc ((memory (\<tau> \<sigma>'))!n) glb= glb) \<longrightarrow>  (valOf n glb  (\<tau> \<sigma>')) \<le> lastVal glb  (\<tau> \<sigma>') ) "
 using assms
  apply (simp add: TML_Begin_invocation_def Begin_invocation_inv_def total_wfs_def )
  by  (cases "pc \<sigma> t";  simp )




lemma beginResp_locglb_le_lvglb:
assumes  "thrdsvars"
and "TML_Begin_response t  \<sigma> \<sigma>'"
and "   (\<forall> n. (0 \<le> n \<and> n  < length (memory (\<tau> \<sigma>))  \<and> comploc ((memory (\<tau> \<sigma>))!n) glb= glb) \<longrightarrow>  (valOf n glb  (\<tau> \<sigma>)) \<le> lastVal glb  (\<tau> \<sigma>) ) "
shows "   (\<forall> n. (0 \<le> n \<and> n  < length (memory (\<tau> \<sigma>'))  \<and> comploc ((memory (\<tau> \<sigma>'))!n) glb= glb) \<longrightarrow>  (valOf n glb  (\<tau> \<sigma>')) \<le> lastVal glb  (\<tau> \<sigma>') ) "
 using assms
  apply (simp add: TML_Begin_response_def total_wfs_def )
  by (cases "pc \<sigma> t";  simp)



lemma readInv_locglb_le_lvglb:
assumes  "thrdsvars"
and "TML_Read_invocation t  \<sigma> \<sigma>'"
  and " Begin_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
and "   (\<forall> n. (0 \<le> n \<and> n  < length (memory (\<tau> \<sigma>))  \<and> comploc ((memory (\<tau> \<sigma>))!n) glb= glb) \<longrightarrow>  (valOf n glb  (\<tau> \<sigma>)) \<le> lastVal glb  (\<tau> \<sigma>) ) "
shows "   (\<forall> n. (0 \<le> n \<and> n  < length (memory (\<tau> \<sigma>'))  \<and> comploc ((memory (\<tau> \<sigma>'))!n) glb= glb) \<longrightarrow>  (valOf n glb  (\<tau> \<sigma>')) \<le> lastVal glb  (\<tau> \<sigma>') ) "
 using assms
  apply (simp add: TML_Read_invocation_def Begin_invocation_inv_def total_wfs_def )
  by  (cases "pc \<sigma> t";  simp )




lemma readResp_locglb_le_lvglb:
assumes  "thrdsvars"
and "TML_Read_response t  \<sigma> \<sigma>'"
and "   (\<forall> n. (0 \<le> n \<and> n  < length (memory (\<tau> \<sigma>))  \<and> comploc ((memory (\<tau> \<sigma>))!n) glb= glb) \<longrightarrow>  (valOf n glb  (\<tau> \<sigma>)) \<le> lastVal glb  (\<tau> \<sigma>) ) "
shows "   (\<forall> n. (0 \<le> n \<and> n  < length (memory (\<tau> \<sigma>'))  \<and> comploc ((memory (\<tau> \<sigma>'))!n) glb= glb) \<longrightarrow>  (valOf n glb  (\<tau> \<sigma>')) \<le> lastVal glb  (\<tau> \<sigma>') ) "
 using assms
  apply (simp add: TML_Read_response_def total_wfs_def )
  by (cases "pc \<sigma> t";  simp )
 


lemma writeInv_locglb_le_lvglb:
assumes  "thrdsvars"
and "TML_Write_invocation t  \<sigma> \<sigma>'"
  and " Write_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
and "   (\<forall> n. (0 \<le> n \<and> n  < length (memory (\<tau> \<sigma>))  \<and> comploc ((memory (\<tau> \<sigma>))!n) glb= glb) \<longrightarrow>  (valOf n glb  (\<tau> \<sigma>)) \<le> lastVal glb  (\<tau> \<sigma>) ) "
shows "   (\<forall> n. (0 \<le> n \<and> n  < length (memory (\<tau> \<sigma>'))  \<and> comploc ((memory (\<tau> \<sigma>'))!n) glb= glb) \<longrightarrow>  (valOf n glb  (\<tau> \<sigma>')) \<le> lastVal glb  (\<tau> \<sigma>') ) "
 using assms
  apply (simp add: TML_Write_invocation_def  total_wfs_def )
  by  (cases "pc \<sigma> t";  simp )



lemma writeResp_locglb_le_lvglb:
assumes  "thrdsvars"
and "TML_Write_response t  \<sigma> \<sigma>'"
 and " Write_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
and "   (\<forall> n. (0 \<le> n \<and> n  < length (memory (\<tau> \<sigma>))  \<and> comploc ((memory (\<tau> \<sigma>))!n) glb= glb) \<longrightarrow>  (valOf n glb  (\<tau> \<sigma>)) \<le> lastVal glb  (\<tau> \<sigma>) ) "
shows "   (\<forall> n. (0 \<le> n \<and> n  < length (memory (\<tau> \<sigma>'))  \<and> comploc ((memory (\<tau> \<sigma>'))!n) glb= glb) \<longrightarrow>  (valOf n glb  (\<tau> \<sigma>')) \<le> lastVal glb  (\<tau> \<sigma>') ) "
 using assms
  apply (simp add: TML_Write_response_def total_wfs_def )
  by  (cases "pc \<sigma> t";  simp )




lemma commitInv_locglb_le_lvglb:
assumes  "thrdsvars"
and "TML_Commit_invocation t  \<sigma> \<sigma>'"
  and " Commit_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
and "   (\<forall> n. (0 \<le> n \<and> n  < length (memory (\<tau> \<sigma>))  \<and> comploc ((memory (\<tau> \<sigma>))!n) glb= glb) \<longrightarrow>  (valOf n glb  (\<tau> \<sigma>)) \<le> lastVal glb  (\<tau> \<sigma>) ) "
shows "   (\<forall> n. (0 \<le> n \<and> n  < length (memory (\<tau> \<sigma>'))  \<and> comploc ((memory (\<tau> \<sigma>'))!n) glb= glb) \<longrightarrow>  (valOf n glb  (\<tau> \<sigma>')) \<le> lastVal glb  (\<tau> \<sigma>') ) "
 using assms
  apply (simp add: TML_Commit_invocation_def total_wfs_def )
  by(cases "pc \<sigma> t";  simp)


lemma commitResp_locglb_le_lvglb:
assumes  "thrdsvars"
and "TML_Commit_response t  \<sigma> \<sigma>'"
and "   (\<forall> n. (0 \<le> n \<and> n  < length (memory (\<tau> \<sigma>))  \<and> comploc ((memory (\<tau> \<sigma>))!n) glb= glb) \<longrightarrow>  (valOf n glb  (\<tau> \<sigma>)) \<le> lastVal glb  (\<tau> \<sigma>) ) "
shows "   (\<forall> n. (0 \<le> n \<and> n  < length (memory (\<tau> \<sigma>'))  \<and> comploc ((memory (\<tau> \<sigma>'))!n) glb= glb) \<longrightarrow>  (valOf n glb  (\<tau> \<sigma>')) \<le> lastVal glb  (\<tau> \<sigma>') ) "
 using assms
  apply (simp add: TML_Commit_response_def total_wfs_def )
  by (cases "pc \<sigma> t";  simp)







(**************************************************************************************)



(*****************************************************rec_le_glb****************************)

(*1*)
lemma  crash_rec_le_glb:
assumes  "thrdsvars"
and "TML_Crash  \<sigma> \<sigma>'"
and "  (  \<forall> i   . (  0 <  i \<and>  i < length(memory (\<tau> \<sigma>)) \<and>  comploc (memory (\<tau> \<sigma>)!i) glb = glb  \<longrightarrow> compval (\<tau> \<sigma>) (memory (\<tau> \<sigma>) ! i) glb  \<ge>   recoveredGlb \<sigma>   ) )"
shows  "  (  \<forall> i   .  (  0 <  i \<and>  i < length(memory (\<tau> \<sigma>')) \<and>  comploc (memory (\<tau> \<sigma>')!i) glb = glb  \<longrightarrow> compval (\<tau> \<sigma>') (memory (\<tau> \<sigma>') ! i) glb  \<ge>   recoveredGlb \<sigma>'   ) )"
  using assms
  apply (simp add: TML_Crash_def  total_wfs_def )
  apply (subgoal_tac " length (memory (\<tau> \<sigma>' )) = 1 ")
  prefer 2
   apply (simp add: crash_step_def)
  by linarith


lemma  crash_rec_leq_glb:
assumes  "thrdsvars"
and "TML_Crash  \<sigma> \<sigma>'"
and "  (  \<forall> i   . (  pc \<sigma> syst = RecIdle \<and>   0 \<le>  i \<and>  i < length(memory (\<tau> \<sigma>)) \<and>  comploc (memory (\<tau> \<sigma>)!i) glb = glb  \<longrightarrow> compval (\<tau> \<sigma>) (memory (\<tau> \<sigma>) ! i) glb  \<ge>   recoveredGlb \<sigma>   ) )"
shows  "  (  \<forall> i   .  ( pc \<sigma>' syst = RecIdle \<and>  0 \<le>  i \<and>  i < length(memory (\<tau> \<sigma>')) \<and>  comploc (memory (\<tau> \<sigma>')!i) glb = glb  \<longrightarrow> compval (\<tau> \<sigma>') (memory (\<tau> \<sigma>') ! i) glb  \<ge>   recoveredGlb \<sigma>'   ) )"
  using assms
  by (simp add: TML_Crash_def   )



(*2*)
lemma begin_rec_le_glb:
  assumes "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
  and "TML_Begin  t   \<sigma> \<sigma>'"
and " t \<noteq>  syst"
 and "Begin_inv t  ((pc \<sigma>) t)   \<sigma> "
and "  (  \<forall> i   .(  0 <  i \<and>  i < length(memory (\<tau> \<sigma>)) \<and>  comploc (memory (\<tau> \<sigma>)!i) glb = glb  \<longrightarrow> compval (\<tau> \<sigma>) (memory (\<tau> \<sigma>) ! i) glb  \<ge>   recoveredGlb \<sigma>   ) )"
shows  "  (  \<forall> i   .  (  0 <  i \<and>  i < length(memory (\<tau> \<sigma>')) \<and>  comploc (memory (\<tau> \<sigma>')!i) glb = glb  \<longrightarrow> compval (\<tau> \<sigma>') (memory (\<tau> \<sigma>') ! i) glb  \<ge>   recoveredGlb \<sigma>'   ) )"
  using assms
  apply (unfold total_wfs_def)
 apply (simp add:TML_Begin_def  del: comploc_def compval_def )
  apply (cases "pc \<sigma> t"; simp)
  apply (metis (mono_tags, opaque_lifting) comploc_def ld_step_mem loc_eq_comploc)
  apply ( simp add: split: if_split_asm)
  apply (metis assms(6) comploc_def compval_def survived_val_cas_fail)
  by (metis assms(6) comploc_def compval_def survived_val_cas_fail)




lemma begin_rec_leq_glb:
  assumes "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
  and "TML_Begin  t   \<sigma> \<sigma>'"
and " t \<noteq>  syst"
 and "Begin_inv t  ((pc \<sigma>) t)   \<sigma> "
and "  (  \<forall> i   .((  pc \<sigma> syst = RecIdle \<and>  0 \<le>  i \<and>  i < length(memory (\<tau> \<sigma>)) \<and>  comploc (memory (\<tau> \<sigma>)!i) glb = glb ) \<longrightarrow> compval (\<tau> \<sigma>) (memory (\<tau> \<sigma>) ! i) glb  \<ge>   recoveredGlb \<sigma>   ) )"
shows  "  (  \<forall> i   . ( ( pc \<sigma>' syst = RecIdle \<and>  0 \<le>  i \<and>  i < length(memory (\<tau> \<sigma>')) \<and>  comploc (memory (\<tau> \<sigma>')!i) glb = glb ) \<longrightarrow> compval (\<tau> \<sigma>') (memory (\<tau> \<sigma>') ! i) glb  \<ge>   recoveredGlb \<sigma>'   ) )"
  using assms
  apply (unfold total_wfs_def)
 apply (simp add:TML_Begin_def  del: comploc_def compval_def )
  apply (cases "pc \<sigma> t"; simp)

  apply (smt (z3) ld_step_mem survived_val_cas_fail survived_val_preserved_load) 
  apply (case_tac "  even (regs (\<tau> \<sigma>) t DTML.loc)")
  apply simp
  apply (smt (verit, del_insts))
  by (smt (z3) pc_aux)




(*3*)
lemma write_rec_le_gl:
  assumes "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
  and " Write_inv  t  ((pc \<sigma>) t) \<sigma> "
 and "TML_Write  t   \<sigma> \<sigma>'"
and "  (  \<forall> i   . (  0 <  i \<and>  i < length(memory (\<tau> \<sigma>)) \<and>  comploc (memory (\<tau> \<sigma>)!i) glb = glb  \<longrightarrow> compval (\<tau> \<sigma>) (memory (\<tau> \<sigma>) ! i) glb  \<ge>   recoveredGlb \<sigma>   ) )"
and " t \<noteq> syst "
 and "pc \<sigma>  syst  = RecIdle  \<longrightarrow> ( lastVal glb (\<tau> \<sigma>)  \<ge>recoveredGlb \<sigma> ) "
shows  "  (  \<forall> i   .  (  0 <  i \<and>  i < length(memory (\<tau> \<sigma>')) \<and>  comploc (memory (\<tau> \<sigma>')!i) glb = glb  \<longrightarrow> compval (\<tau> \<sigma>') (memory (\<tau> \<sigma>') ! i) glb  \<ge>   recoveredGlb \<sigma>'   ) )"
  using assms
 apply (simp add:TML_Write_def Write_inv_def total_wfs_def del :comploc_def compval_def  )
  apply (cases "pc \<sigma> t";  simp add: split if_splits )
  apply ( simp add: split: if_split_asm)
  apply (metis assms(5) comploc_def compval_def survived_val_cas_fail)
  apply (metis assms(5) comploc_def compval_def survived_val_cas_fail)




  apply (case_tac "regs (\<tau> \<sigma>') t c1 \<noteq> 0 ")
apply (simp add: step_def)
  apply clarify 
 apply (subgoal_tac "  \<tau> \<sigma>' =
       cas_succ_trans t ind glb (regs (\<tau> \<sigma>) t DTML.loc) (Suc (regs (\<tau> \<sigma>) t DTML.loc))  c1 nv mnv
        (\<tau> \<sigma>) ")
         prefer 2
  apply (metis cas_fail_reg less_numeral_extra(3))
apply (subgoal_tac " \<forall> i. i < length (memory  (\<tau>  \<sigma>) ) \<longrightarrow>(memory  (\<tau>  \<sigma>')) ! i = (memory  (\<tau>  \<sigma>)) ! i ")
   prefer 2
  using le0 mem_l_casucc apply metis
 apply (subgoal_tac " (State.loc (memory  (\<tau>  \<sigma>')!(length (memory  (\<tau>  \<sigma>)))) ) = glb ")
   prefer 2
  using cas_suc_loc apply presburger
  apply (subgoal_tac " compval (\<tau> \<sigma>)   ((memory  (\<tau>  \<sigma>))!  (last_entry (\<tau> \<sigma>)  glb))    glb    \<ge>   recoveredGlb \<sigma>   ")
         prefer 2
  apply (metis lastVal_def)
        apply (subgoal_tac " compval (\<tau> \<sigma>)   ((memory  (\<tau>  \<sigma>))!  (last_entry (\<tau> \<sigma>)  glb))    glb   =  (regs (\<tau> \<sigma>) t DTML.loc)")
         prefer 2
  apply (metis cas_fail_reg compval_def neq0_conv)
 apply (subgoal_tac "compval (\<tau> \<sigma>')  (memory (\<tau> \<sigma>') !length(memory  (\<tau> \<sigma>)))  glb    \<ge>   recoveredGlb \<sigma> ")
  prefer 2
  apply (metis cas_suc_compval le_Suc_eq)
  apply (subgoal_tac " length (memory  (\<tau> \<sigma>')) = length(memory  (\<tau> \<sigma>)) + 1 ")
  prefer 2
  using length_s apply presburger
   apply (subgoal_tac "  (\<forall>i. 0 < i \<and> i < length (memory (\<tau> \<sigma>)) \<longrightarrow> (memory (\<tau> \<sigma>)!i ) =(memory (\<tau> \<sigma>')!i)  ) ")
            prefer 2
  apply metis
           apply (intro conjI impI)
  apply (metis (mono_tags, opaque_lifting) cas_succ_wfs comploc_def i_noteqo_loc)
  apply (metis Nat.add_0_right add_Suc_right cas_succ_wfs less_Suc_eq numeral_1_eq_Suc_0 numerals(1) val_eq_compval)
  apply (subgoal_tac "  memory (\<tau> \<sigma>') =  memory (\<tau> \<sigma>) ")
  prefer 2
  apply (metis cas_fail_mem_same)
  apply simp
       apply (metis (mono_tags, opaque_lifting) comploc_def loc_eq_comploc)
  apply (metis (mono_tags, opaque_lifting) comploc_def loc_eq_comploc reg_write_mem)
     apply (metis (mono_tags, lifting) comploc_def fun_upd_apply loc_eq_comploc)
  apply (metis assms(5) comploc_def compval_def ld_step_mem survived_val_cas_fail survived_val_preserved_load)
  apply (subgoal_tac "  comploc (memory (\<tau> \<sigma>')! (length (memory (\<tau> \<sigma>))))   glb \<noteq> glb   ")
  prefer 2
  apply (metis assms(2) aux bot_nat_0.not_eq_extremum less_nat_zero_code loc_eq_comploc st_lastEntry_lc st_loc st_wfs_preserved total_wfs_def)
  apply (subgoal_tac " length (memory  (\<tau> \<sigma>')) = length(memory  (\<tau> \<sigma>)) + 1 ")
  prefer 2
  apply (metis st_mem_length)
 apply (subgoal_tac "  (\<forall>i. 0 < i \<and> i < length (memory (\<tau> \<sigma>)) \<longrightarrow> (memory (\<tau> \<sigma>)!i ) =(memory (\<tau> \<sigma>')!i)  ) ")
      prefer 2
  apply (metis less_imp_le_nat mem_l_step)
     apply (intro conjI impI allI)
  apply (metis (mono_tags, opaque_lifting) comploc_def i_noteqo_loc mem_structured_preserved)
  apply (metis (no_types, opaque_lifting) Suc_eq_plus1 diff_is_0_eq less_eq_Suc_le nat_neq_iff st_loc zero_less_diff)
 apply (subgoal_tac "  memory (\<tau> \<sigma>') =  memory (\<tau> \<sigma>) ")
  prefer 2
   apply (simp add: step_def)
  by (metis compval_def survived_val_cas_fail survived_val_preserved_flushopt val_eq_compval)



lemma write_rec_leq_gl:
  assumes "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
  and " Write_inv  t  ((pc \<sigma>) t) \<sigma> "
 and "TML_Write  t   \<sigma> \<sigma>'"
and "  (  \<forall> i   . ( ( pc \<sigma> syst = RecIdle \<and>  0 \<le>  i \<and>  i < length(memory (\<tau> \<sigma>)) \<and>  comploc (memory (\<tau> \<sigma>)!i) glb = glb ) \<longrightarrow> compval (\<tau> \<sigma>) (memory (\<tau> \<sigma>) ! i) glb  \<ge>   recoveredGlb \<sigma>   ) )"
and " t \<noteq> syst "
 and "pc \<sigma>  syst  = RecIdle  \<longrightarrow> ( lastVal glb (\<tau> \<sigma>)  \<ge>recoveredGlb \<sigma> ) "
shows  "  (  \<forall> i   .  ((  pc \<sigma>' syst = RecIdle \<and>  0 \<le>  i \<and>  i < length(memory (\<tau> \<sigma>')) \<and>  comploc (memory (\<tau> \<sigma>')!i) glb = glb ) \<longrightarrow> compval (\<tau> \<sigma>') (memory (\<tau> \<sigma>') ! i) glb  \<ge>   recoveredGlb \<sigma>'   ) )"
  using assms
 apply (simp add:TML_Write_def Write_inv_def total_wfs_def del :comploc_def compval_def  )
  apply (cases "pc \<sigma> t";  simp add: split if_splits )
  apply ( simp add: split: if_split_asm)
  apply (metis assms(5) comploc_def compval_def survived_val_cas_fail)
  apply (metis assms(5) comploc_def compval_def survived_val_cas_fail)




  apply (case_tac "regs (\<tau> \<sigma>') t c1 \<noteq> 0 ")
apply (simp add: step_def)
  apply clarify 
 apply (subgoal_tac "  \<tau> \<sigma>' =
       cas_succ_trans t ind glb (regs (\<tau> \<sigma>) t DTML.loc) (Suc (regs (\<tau> \<sigma>) t DTML.loc)) c1 nv mnv
        (\<tau> \<sigma>) ")
         prefer 2
  apply (metis cas_fail_reg less_numeral_extra(3))
apply (subgoal_tac " \<forall> i. i < length (memory  (\<tau>  \<sigma>) ) \<longrightarrow>(memory  (\<tau>  \<sigma>')) ! i = (memory  (\<tau>  \<sigma>)) ! i ")
   prefer 2
  using le0 mem_l_casucc apply metis
 apply (subgoal_tac " (State.loc (memory  (\<tau>  \<sigma>')!(length (memory  (\<tau>  \<sigma>)))) ) = glb ")
   prefer 2
  using cas_suc_loc apply presburger
  apply (subgoal_tac " compval (\<tau> \<sigma>)   ((memory  (\<tau>  \<sigma>))!  (last_entry (\<tau> \<sigma>)  glb))    glb    \<ge>   recoveredGlb \<sigma>   ")
         prefer 2
  apply (metis lastVal_def)
        apply (subgoal_tac " compval (\<tau> \<sigma>)   ((memory  (\<tau>  \<sigma>))!  (last_entry (\<tau> \<sigma>)  glb))    glb   =  (regs (\<tau> \<sigma>) t DTML.loc)")
         prefer 2
  apply (metis cas_fail_reg compval_def neq0_conv)
 apply (subgoal_tac "compval (\<tau> \<sigma>')  (memory (\<tau> \<sigma>') !length(memory  (\<tau> \<sigma>)))  glb    \<ge>   recoveredGlb \<sigma> ")
  prefer 2
  apply (metis cas_suc_compval le_Suc_eq)
  apply (subgoal_tac " length (memory  (\<tau> \<sigma>')) = length(memory  (\<tau> \<sigma>)) + 1 ")
  prefer 2
  using length_s apply presburger
   apply (subgoal_tac "  (\<forall>i. 0 \<le> i \<and> i < length (memory (\<tau> \<sigma>)) \<longrightarrow> (memory (\<tau> \<sigma>)!i ) =(memory (\<tau> \<sigma>')!i)  ) ")
            prefer 2
  apply metis
        apply (intro conjI impI)
  apply (metis Nat.add_0_right add_Suc_right compval_def less_Suc_eq numeral_1_eq_Suc_0 numerals(1) survived_val_cas_fail survived_val_cas_succ)

  apply (metis Nat.add_0_right add_Suc_right compval_def less_antisym numeral_1_eq_Suc_0 numerals(1))


  apply (subgoal_tac "  memory (\<tau> \<sigma>') =  memory (\<tau> \<sigma>) ")
  prefer 2
        apply (metis cas_fail_mem_same)
  apply (metis survived_val_cas_fail survived_val_preserved_cas)

  apply (metis reg_write_mem survived_val_cas_fail survived_val_preserved_reg_write)

  apply metis

  apply (metis ld_step_mem survived_val_cas_fail survived_val_preserved_load)

  apply (subgoal_tac "  comploc (memory (\<tau> \<sigma>')! (length (memory (\<tau> \<sigma>))))   glb \<noteq> glb   ")
  prefer 2
  apply (metis assms(2) aux bot_nat_0.not_eq_extremum less_nat_zero_code loc_eq_comploc st_lastEntry_lc st_loc st_wfs_preserved total_wfs_def)
  apply (subgoal_tac " length (memory  (\<tau> \<sigma>')) = length(memory  (\<tau> \<sigma>)) + 1 ")
  prefer 2
  apply (metis st_mem_length)
 apply (subgoal_tac "  (\<forall>i. 0 \<le> i \<and> i < length (memory (\<tau> \<sigma>)) \<longrightarrow> (memory (\<tau> \<sigma>)!i ) =(memory (\<tau> \<sigma>')!i)  ) ")
      prefer 2
  apply (metis less_imp_le_nat mem_l_step)
   apply (intro conjI impI allI)
    apply (unfold mem_structured_def)
  apply (metis length_greater_0_conv survived_val_cas_fail survived_val_preserved_store)
  apply (metis (no_types, opaque_lifting) Suc_eq_plus1 comploc_def le0 linorder_neqE_nat not_less_eq)
 apply (subgoal_tac "  memory (\<tau> \<sigma>') =  memory (\<tau> \<sigma>) ")
  prefer 2
   apply (simp add: step_def)
  by (metis compval_def survived_val_cas_fail survived_val_preserved_flushopt val_eq_compval)







(*4*)
lemma  read_rec_le_gl:
   assumes "thrdsvars"
   and "total_wfs (\<tau> \<sigma>)"
   and "TML_Read  t   \<sigma> \<sigma>'"
      and "Read_inv t  ((pc \<sigma>) t) \<sigma>" 
and "pc \<sigma> syst = RecIdle"
and "  (  \<forall> i   . (  0 <  i \<and>  i < length(memory (\<tau> \<sigma>)) \<and>  comploc (memory (\<tau> \<sigma>)!i) glb = glb  \<longrightarrow> compval (\<tau> \<sigma>) (memory (\<tau> \<sigma>) ! i) glb  \<ge>   recoveredGlb \<sigma>   ) )"
and " t \<noteq> syst "
 and "pc \<sigma>  syst  = RecIdle  \<longrightarrow> ( lastVal glb (\<tau> \<sigma>)  \<ge>recoveredGlb \<sigma> ) "
shows  "  (  \<forall> i   . (  0 <  i \<and>  i < length(memory (\<tau> \<sigma>')) \<and>  comploc (memory (\<tau> \<sigma>')!i) glb = glb  \<longrightarrow> compval (\<tau> \<sigma>') (memory (\<tau> \<sigma>') ! i) glb  \<ge>   recoveredGlb \<sigma>'   ) )"
  using assms
apply (unfold  total_wfs_def )
  apply (simp add:TML_Read_def Read_inv_def del: comploc_def compval_def  )

  apply (cases "pc \<sigma> t";   simp add: split if_splits)
  apply (metis (mono_tags, opaque_lifting) comploc_def ld_step_mem loc_eq_comploc)


  prefer 2
       apply (case_tac " regs (\<tau> \<sigma>') t c1 = Suc 0 ")
 apply (simp add: step_def)
  apply clarify 
 apply (subgoal_tac "   \<tau> \<sigma>' =
           cas_succ_trans t ind glb (regs (\<tau> \<sigma>) t DTML.loc)
            (regs (\<tau> \<sigma>) t DTML.loc) c1 nv mnv (\<tau> \<sigma>)  ")
         prefer 2
  apply (metis One_nat_def cas_fail_reg zero_neq_one)
apply (subgoal_tac " \<forall> i. i < length (memory  (\<tau>  \<sigma>) ) \<longrightarrow>(memory  (\<tau>  \<sigma>')) ! i = (memory  (\<tau>  \<sigma>)) ! i ")
   prefer 2
  using le0 mem_l_casucc apply metis
 apply (subgoal_tac " (State.loc (memory  (\<tau>  \<sigma>')!(length (memory  (\<tau>  \<sigma>)))) ) = glb ")
   prefer 2
  using cas_suc_loc apply presburger
  apply (subgoal_tac " compval (\<tau> \<sigma>)   ((memory  (\<tau>  \<sigma>))!  (last_entry (\<tau> \<sigma>)  glb))    glb    \<ge>   recoveredGlb \<sigma>   ")
         prefer 2
  apply (metis lastVal_def)
        apply (subgoal_tac " compval (\<tau> \<sigma>)   ((memory  (\<tau>  \<sigma>))!  (last_entry (\<tau> \<sigma>)  glb))    glb   =  (regs (\<tau> \<sigma>) t DTML.loc)")
         prefer 2
         apply (metis cas_fail_reg compval_def n_not_Suc_n)
 apply (subgoal_tac "compval (\<tau> \<sigma>')  (memory (\<tau> \<sigma>') !length(memory  (\<tau> \<sigma>)))  glb    \<ge>   recoveredGlb \<sigma> ")
  prefer 2
         apply (metis cas_suc_compval)
  apply (subgoal_tac " length (memory  (\<tau> \<sigma>')) = length(memory  (\<tau> \<sigma>)) + 1 ")
  prefer 2
  using length_s apply presburger
  apply (metis Nat.add_0_right add_Suc_right compval_def less_antisym numeral_1_eq_Suc_0 numerals(1) survived_val_cas_fail survived_val_cas_succ val_eq_compval)
 apply (subgoal_tac " memory (\<tau> \<sigma>) = memory (\<tau> \<sigma>' ) ")
  prefer 2
      apply (metis cas_fail_mem_same cas_lc numeral_1_eq_Suc_0 numeral_One)
     apply (simp)
     apply (metis (no_types, opaque_lifting) comploc_def i_noteqo_loc)
  apply (case_tac " even (regs (\<tau> \<sigma>) t DTML.loc) \<and> \<not> readAux \<sigma> t")
  apply simp
  apply (metis assms(6) comploc_def compval_def survived_val_cas_fail)
  apply simp
  apply (metis (no_types, opaque_lifting) comploc_def loc_eq_comploc)
   apply (metis comploc_def i_noteqo_loc ld_step_mem)
  by (metis compval_def ld_step_mem survived_val_cas_fail survived_val_preserved_load val_eq_compval)




lemma  read_rec_leq_gl:
   assumes "thrdsvars"
   and "total_wfs (\<tau> \<sigma>)"
   and "TML_Read  t   \<sigma> \<sigma>'"
  and "((pc \<sigma>) t) \<in> {Ready, Aborted} \<union> reading "
      and "Read_inv t  ((pc \<sigma>) t) \<sigma>" 
and "pc \<sigma> syst = RecIdle"
and "  (  \<forall> i   .   ( (pc \<sigma> syst = RecIdle \<and>  0 \<le>  i \<and>  i < length(memory (\<tau> \<sigma>)) \<and>  comploc (memory (\<tau> \<sigma>)!i) glb = glb )  \<longrightarrow> compval (\<tau> \<sigma>) (memory (\<tau> \<sigma>) ! i) glb  \<ge>   recoveredGlb \<sigma>   ) )"
and " t \<noteq> syst "
 and "pc \<sigma>  syst  = RecIdle  \<longrightarrow> ( lastVal glb (\<tau> \<sigma>)  \<ge>recoveredGlb \<sigma> ) "
shows  "  ( (  \<forall> i   .  (  pc \<sigma>' syst = RecIdle \<and> 0 <  i \<and>  i < length(memory (\<tau> \<sigma>')) \<and>  comploc (memory (\<tau> \<sigma>')!i) glb = glb   ) \<longrightarrow> compval (\<tau> \<sigma>') (memory (\<tau> \<sigma>') ! i) glb  \<ge>   recoveredGlb \<sigma>'   ) )"
  using assms
apply (unfold  total_wfs_def )
  apply (simp add:TML_Read_def Read_inv_def del: comploc_def compval_def  )
  apply (cases "pc \<sigma> t";   simp add: split if_splits)
  apply (metis (mono_tags, opaque_lifting) comploc_def ld_step_mem loc_eq_comploc)

  prefer 2
       apply (case_tac " regs (\<tau> \<sigma>') t c1 = Suc 0 ")
 apply (simp add: step_def)
  apply clarify 
 apply (subgoal_tac "   \<tau> \<sigma>' =
           cas_succ_trans t ind glb (regs (\<tau> \<sigma>) t DTML.loc)
            (regs (\<tau> \<sigma>) t DTML.loc) c1 nv mnv (\<tau> \<sigma>)  ")
         prefer 2
  apply (metis One_nat_def cas_fail_reg zero_neq_one)
apply (subgoal_tac " \<forall> i. i < length (memory  (\<tau>  \<sigma>) ) \<longrightarrow>(memory  (\<tau>  \<sigma>')) ! i = (memory  (\<tau>  \<sigma>)) ! i ")
   prefer 2
  using le0 mem_l_casucc apply metis
 apply (subgoal_tac " (State.loc (memory  (\<tau>  \<sigma>')!(length (memory  (\<tau>  \<sigma>)))) ) = glb ")
   prefer 2
  using cas_suc_loc apply presburger
  apply (subgoal_tac " compval (\<tau> \<sigma>)   ((memory  (\<tau>  \<sigma>))!  (last_entry (\<tau> \<sigma>)  glb))    glb    \<ge>   recoveredGlb \<sigma>   ")
         prefer 2
  apply (metis lastVal_def)
        apply (subgoal_tac " compval (\<tau> \<sigma>)   ((memory  (\<tau>  \<sigma>))!  (last_entry (\<tau> \<sigma>)  glb))    glb   =  (regs (\<tau> \<sigma>) t DTML.loc)")
         prefer 2
         apply (metis cas_fail_reg compval_def n_not_Suc_n)
 apply (subgoal_tac "compval (\<tau> \<sigma>')  (memory (\<tau> \<sigma>') !length(memory  (\<tau> \<sigma>)))  glb    \<ge>   recoveredGlb \<sigma> ")
  prefer 2
         apply (metis cas_suc_compval)
  apply (subgoal_tac " length (memory  (\<tau> \<sigma>')) = length(memory  (\<tau> \<sigma>)) + 1 ")
  prefer 2
  using length_s apply presburger
  apply (metis Nat.add_0_right add_Suc_right compval_def less_antisym numeral_1_eq_Suc_0 numerals(1) survived_val_cas_fail survived_val_cas_succ val_eq_compval)
 apply (subgoal_tac " memory (\<tau> \<sigma>) = memory (\<tau> \<sigma>' ) ")
  prefer 2
      apply (metis cas_fail_mem_same cas_lc numeral_1_eq_Suc_0 numeral_One)
     apply (simp)
     apply (metis (no_types, opaque_lifting) comploc_def i_noteqo_loc)
  apply (case_tac " even (regs (\<tau> \<sigma>) t DTML.loc) \<and> \<not> readAux \<sigma> t")
  apply simp
  apply (metis assms(6) comploc_def compval_def survived_val_cas_fail)
  apply simp
  apply (metis (no_types, opaque_lifting) comploc_def loc_eq_comploc)
     apply (metis comploc_def i_noteqo_loc ld_step_mem)
    apply metis
  apply (metis assms(7) comploc_def less_or_eq_imp_le val_eq_compval)
  by (metis (mono_tags) comploc_def i_noteqo_loc)




(*5*)
lemma commit_rec_le_gl:
  assumes "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
  and "  Commit_inv  t   ((pc \<sigma>) t) \<sigma>  "
  and "TML_Commit  t   \<sigma> \<sigma>'"
and "pc \<sigma> syst = RecIdle"
and "  (  \<forall> i   .  (  0 <  i \<and>  i < length(memory (\<tau> \<sigma>)) \<and>  comploc (memory (\<tau> \<sigma>)!i) glb = glb  \<longrightarrow> compval (\<tau> \<sigma>) (memory (\<tau> \<sigma>) ! i) glb  \<ge>   recoveredGlb \<sigma>   ) )"
and " t \<noteq> syst "
 and "pc \<sigma>  syst  = RecIdle  \<longrightarrow> ( lastVal glb (\<tau> \<sigma>)  \<ge>recoveredGlb \<sigma> ) "
shows  "  (  \<forall> i   .  (  0 <  i \<and>  i < length(memory (\<tau> \<sigma>')) \<and>  comploc (memory (\<tau> \<sigma>')!i) glb = glb  \<longrightarrow> compval (\<tau> \<sigma>') (memory (\<tau> \<sigma>') ! i) glb  \<ge>   recoveredGlb \<sigma>'   ) )"
  using assms
  apply (unfold  total_wfs_def )
  apply (simp add:TML_Commit_def Commit_inv_def del: comploc_def compval_def   )
  apply (cases "pc \<sigma> t";simp  )
    apply (metis compval_def step_mem_sfence survived_val_cas_fail survived_val_preserved_sfence val_eq_compval)
  apply (metis (mono_tags, opaque_lifting) comploc_def i_noteqo_loc step_mem_sfence)
apply (subgoal_tac " \<forall> i. i < length (memory  (\<tau>  \<sigma>) ) \<longrightarrow>(memory  (\<tau>  \<sigma>')) ! i = (memory  (\<tau>  \<sigma>)) ! i ")
   prefer 2
  apply (metis le0 mem_l_step)
 apply (subgoal_tac " (State.loc (memory  (\<tau>  \<sigma>')!(length (memory  (\<tau>  \<sigma>)))) ) = glb ")
   prefer 2
  apply (meson st_loc)
  apply (subgoal_tac " compval (\<tau> \<sigma>)   ((memory  (\<tau>  \<sigma>))!  (last_entry (\<tau> \<sigma>)  glb))    glb    \<ge>   recoveredGlb \<sigma>   ")
         prefer 2
  apply (metis lastVal_def)
        apply (subgoal_tac " compval (\<tau> \<sigma>)   ((memory  (\<tau>  \<sigma>))!  (last_entry (\<tau> \<sigma>)  glb))    glb   =  (regs (\<tau> \<sigma>) t DTML.loc)")
      prefer 2
  apply (metis lastVal_def)
 apply (subgoal_tac "compval (\<tau> \<sigma>')  (memory (\<tau> \<sigma>') !length(memory  (\<tau> \<sigma>)))  glb    \<ge>   recoveredGlb \<sigma> ")
  prefer 2       
           apply (metis Store_Rules.st_lv_lc le_Suc_eq st_lastEntry_lc)
  apply (subgoal_tac " length (memory  (\<tau> \<sigma>')) = length(memory  (\<tau> \<sigma>)) + 1 ")
  prefer 2
  apply (meson st_mem_length)
     apply (intro allI conjI impI)
  apply (metis (mono_tags, opaque_lifting) comploc_def i_noteqo_loc mem_structured_preserved)
  by (metis (mono_tags, lifting) Nat.add_0_right add_Suc_right le_imp_less_Suc less_SucE less_imp_le_nat numeral_1_eq_Suc_0 numerals(1) st_val)


lemma commit_rec_leq_gl:
  assumes "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
  and "  Commit_inv  t   ((pc \<sigma>) t) \<sigma>  "
  and "TML_Commit  t   \<sigma> \<sigma>'"
and "pc \<sigma> syst = RecIdle"
and "  (  \<forall> i   .(  pc \<sigma> syst = RecIdle \<and>  0 \<le>  i \<and>  i < length(memory (\<tau> \<sigma>)) \<and>  comploc (memory (\<tau> \<sigma>)!i) glb = glb)  \<longrightarrow> compval (\<tau> \<sigma>) (memory (\<tau> \<sigma>) ! i) glb  \<ge>   recoveredGlb \<sigma>    )"
and " t \<noteq> syst "
 and "pc \<sigma>  syst  = RecIdle  \<longrightarrow> ( lastVal glb (\<tau> \<sigma>)  \<ge>recoveredGlb \<sigma> ) "
shows  "  (  \<forall> i   . (  pc \<sigma>' syst = RecIdle  \<and>  0 \<le>  i \<and>  i < length(memory (\<tau> \<sigma>')) \<and>  comploc (memory (\<tau> \<sigma>')!i) glb = glb ) \<longrightarrow> compval (\<tau> \<sigma>') (memory (\<tau> \<sigma>') ! i) glb  \<ge>   recoveredGlb \<sigma>'    )"
  using assms
  apply (unfold  total_wfs_def )
  apply (simp add:TML_Commit_def Commit_inv_def del: comploc_def compval_def   )
  apply (cases "pc \<sigma> t";simp  )
    apply (smt (z3) step_mem_sfence survived_val_cas_fail survived_val_preserved_sfence)
  apply (smt (verit) step_mem_sfence survived_val_cas_fail survived_val_preserved_sfence)
apply (subgoal_tac " \<forall> i. i < length (memory  (\<tau>  \<sigma>) ) \<longrightarrow>(memory  (\<tau>  \<sigma>')) ! i = (memory  (\<tau>  \<sigma>)) ! i ")
   prefer 2
  apply (metis le0 mem_l_step)
 apply (subgoal_tac " (State.loc (memory  (\<tau>  \<sigma>')!(length (memory  (\<tau>  \<sigma>)))) ) = glb ")
   prefer 2
  apply (meson st_loc)
  apply (subgoal_tac " compval (\<tau> \<sigma>)   ((memory  (\<tau>  \<sigma>))!  (last_entry (\<tau> \<sigma>)  glb))    glb    \<ge>   recoveredGlb \<sigma>   ")
         prefer 2
  apply (metis lastVal_def)
        apply (subgoal_tac " compval (\<tau> \<sigma>)   ((memory  (\<tau>  \<sigma>))!  (last_entry (\<tau> \<sigma>)  glb))    glb   =  (regs (\<tau> \<sigma>) t DTML.loc)")
      prefer 2
  apply (metis lastVal_def)
 apply (subgoal_tac "compval (\<tau> \<sigma>')  (memory (\<tau> \<sigma>') !length(memory  (\<tau> \<sigma>)))  glb    \<ge>   recoveredGlb \<sigma> ")
  prefer 2       
           apply (metis Store_Rules.st_lv_lc le_Suc_eq st_lastEntry_lc)
  apply (subgoal_tac " length (memory  (\<tau> \<sigma>')) = length(memory  (\<tau> \<sigma>)) + 1 ")
  prefer 2
  apply (meson st_mem_length)
   apply (intro allI conjI impI)
    apply (unfold  mem_structured_def)
  apply (smt (z3) length_0_conv less_nat_zero_code linorder_neqE_nat survived_val_cas_fail survived_val_preserved_store)
  by (smt (z3) Nat.add_0_right add_Suc_right le_imp_less_Suc less_Suc_eq less_or_eq_imp_le numeral_1_eq_Suc_0 numerals(1) st_val)



lemmas [simp del] = compval_def comploc_def

(*6*)
lemma  recover_rec_le_glb:
 assumes "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
  and " TML_Recover syst   \<sigma> \<sigma>' "
 and "  Recover_inv  syst  ((pc \<sigma>) syst)  \<sigma>"
and "  (  \<forall> i   .  (  0 <  i \<and>  i < length(memory (\<tau> \<sigma>)) \<and>  comploc (memory (\<tau> \<sigma>)!i) glb = glb  \<longrightarrow> compval (\<tau> \<sigma>) (memory (\<tau> \<sigma>) ! i) glb  \<ge>   recoveredGlb \<sigma>   ) )"
shows  "  (  \<forall> i   .  (  0 <  i \<and>  i < length(memory (\<tau> \<sigma>')) \<and>  comploc (memory (\<tau> \<sigma>')!i) glb = glb  \<longrightarrow> compval (\<tau> \<sigma>') (memory (\<tau> \<sigma>') ! i) glb  \<ge>   recoveredGlb \<sigma>'   ) )"
 using assms
  apply (simp add:TML_Recover_def total_wfs_def Recover_inv_def )
  apply (cases "pc \<sigma> syst";   simp add: split if_splits)
  apply (simp add: compval_def comploc_def)

          apply (case_tac "  even (regs (\<tau> \<sigma>) syst c1)")
  apply (metis (no_types, lifting) comploc_def loc_eq_comploc reg_write_mem)
  apply (metis (no_types, lifting) comploc_def loc_eq_comploc reg_write_mem)

  apply (metis assms(2) aux comploc_ots i_noteqo_loc last_entry_last_comp_loc le_in_ots neq0_conv st_ots_ni st_wfs_preserved)
  apply (metis assms(2) aux bot_nat_0.not_eq_extremum comploc_ots flo_ots_ni flo_wfs_preserved last_entry_last_comp_loc le_in_ots loc_eq_comploc)
  apply (metis i_noteqo_loc step_mem_sfence)
  apply (meson i_noteqo_loc)
  apply (metis i_noteqo_loc ld_step_mem)
  apply (metis loc_eq_comploc)
  apply (metis Store_Rules.st_lv_lc assms(1) assms(2) cas_fail_crash last_entry_last_comp_loc le_eq_less_or_eq linorder_neqE_nat loc_eq_comploc loc_wr_same mem_structured_preserved st_lastEntry_lc st_wfs_preserved)
  apply (metis Store_Rules.st_lv_lc assms(1) assms(2) cas_fail_crash last_entry_last_comp_loc le_eq_less_or_eq linorder_neqE_nat loc_eq_comploc loc_wr_same mem_structured_preserved st_lastEntry_lc st_wfs_preserved)
  by (metis loc_eq_comploc)



lemma beginInvr_rec_le_glb:
assumes  "thrdsvars"
and "TML_Begin_invocation t  \<sigma> \<sigma>'"
  and " Begin_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
and "  (  \<forall> i   .   ( (pc \<sigma> syst = RecIdle \<and>  0 <  i \<and>  i < length(memory (\<tau> \<sigma>)) \<and>  comploc (memory (\<tau> \<sigma>)!i) glb = glb )  \<longrightarrow> compval (\<tau> \<sigma>) (memory (\<tau> \<sigma>) ! i) glb  \<ge>   recoveredGlb \<sigma>   ) )"
shows " (  \<forall> i   .   ( (pc \<sigma> syst = RecIdle \<and>  0 <  i \<and>  i < length(memory (\<tau> \<sigma>')) \<and>  comploc (memory (\<tau> \<sigma>')!i) glb = glb )  \<longrightarrow> compval (\<tau> \<sigma>') (memory (\<tau> \<sigma>') ! i) glb  \<ge>   recoveredGlb \<sigma>'   ) ) "
 using assms
  apply (simp add: TML_Begin_invocation_def Begin_invocation_inv_def total_wfs_def )
  by  (cases "pc \<sigma> t";  simp )




lemma beginResp_rec_le_glb:
assumes  "thrdsvars"
and "TML_Begin_response t  \<sigma> \<sigma>'"
and "  (  \<forall> i   .   ( (pc \<sigma> syst = RecIdle \<and>  0 <  i \<and>  i < length(memory (\<tau> \<sigma>)) \<and>  comploc (memory (\<tau> \<sigma>)!i) glb = glb )  \<longrightarrow> compval (\<tau> \<sigma>) (memory (\<tau> \<sigma>) ! i) glb  \<ge>   recoveredGlb \<sigma>   ) )"
shows " (  \<forall> i   .   ( (pc \<sigma> syst = RecIdle \<and>  0 <  i \<and>  i < length(memory (\<tau> \<sigma>')) \<and>  comploc (memory (\<tau> \<sigma>')!i) glb = glb )  \<longrightarrow> compval (\<tau> \<sigma>') (memory (\<tau> \<sigma>') ! i) glb  \<ge>   recoveredGlb \<sigma>'   ) ) "
 using assms
  apply (simp add: TML_Begin_response_def total_wfs_def )
  by (cases "pc \<sigma> t";  simp)



lemma readInv_rec_le_glb:
assumes  "thrdsvars"
and "TML_Read_invocation t  \<sigma> \<sigma>'"
  and " Begin_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
and "  (  \<forall> i   .   ( (pc \<sigma> syst = RecIdle \<and>  0 <  i \<and>  i < length(memory (\<tau> \<sigma>)) \<and>  comploc (memory (\<tau> \<sigma>)!i) glb = glb )  \<longrightarrow> compval (\<tau> \<sigma>) (memory (\<tau> \<sigma>) ! i) glb  \<ge>   recoveredGlb \<sigma>   ) )"
shows " (  \<forall> i   .   ( (pc \<sigma> syst = RecIdle \<and>  0 <  i \<and>  i < length(memory (\<tau> \<sigma>')) \<and>  comploc (memory (\<tau> \<sigma>')!i) glb = glb )  \<longrightarrow> compval (\<tau> \<sigma>') (memory (\<tau> \<sigma>') ! i) glb  \<ge>   recoveredGlb \<sigma>'   ) ) "
 using assms
  apply (simp add: TML_Read_invocation_def Begin_invocation_inv_def total_wfs_def )
  by  (cases "pc \<sigma> t";  simp )




lemma readResp_rec_le_glb:
assumes  "thrdsvars"
and "TML_Read_response t  \<sigma> \<sigma>'"
and "  (  \<forall> i   .   ( (pc \<sigma> syst = RecIdle \<and>  0 <  i \<and>  i < length(memory (\<tau> \<sigma>)) \<and>  comploc (memory (\<tau> \<sigma>)!i) glb = glb )  \<longrightarrow> compval (\<tau> \<sigma>) (memory (\<tau> \<sigma>) ! i) glb  \<ge>   recoveredGlb \<sigma>   ) )"
shows " (  \<forall> i   .   ( (pc \<sigma> syst = RecIdle \<and>  0 <  i \<and>  i < length(memory (\<tau> \<sigma>')) \<and>  comploc (memory (\<tau> \<sigma>')!i) glb = glb )  \<longrightarrow> compval (\<tau> \<sigma>') (memory (\<tau> \<sigma>') ! i) glb  \<ge>   recoveredGlb \<sigma>'   ) ) "
 using assms
  apply (simp add: TML_Read_response_def total_wfs_def )
  by (cases "pc \<sigma> t";  simp )
 


lemma writeInv_rec_le_glb:
assumes  "thrdsvars"
and "TML_Write_invocation t  \<sigma> \<sigma>'"
  and " Write_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
and "  (  \<forall> i   .   ( (pc \<sigma> syst = RecIdle \<and>  0 <  i \<and>  i < length(memory (\<tau> \<sigma>)) \<and>  comploc (memory (\<tau> \<sigma>)!i) glb = glb )  \<longrightarrow> compval (\<tau> \<sigma>) (memory (\<tau> \<sigma>) ! i) glb  \<ge>   recoveredGlb \<sigma>   ) )"
shows " (  \<forall> i   .   ( (pc \<sigma> syst = RecIdle \<and>  0 <  i \<and>  i < length(memory (\<tau> \<sigma>')) \<and>  comploc (memory (\<tau> \<sigma>')!i) glb = glb )  \<longrightarrow> compval (\<tau> \<sigma>') (memory (\<tau> \<sigma>') ! i) glb  \<ge>   recoveredGlb \<sigma>'   ) ) "
 using assms
  apply (simp add: TML_Write_invocation_def  total_wfs_def )
  by  (cases "pc \<sigma> t";  simp )



lemma writeResp_rec_le_glb:
assumes  "thrdsvars"
and "TML_Write_response t  \<sigma> \<sigma>'"
 and " Write_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
and "  (  \<forall> i   .   ( (pc \<sigma> syst = RecIdle \<and>  0 <  i \<and>  i < length(memory (\<tau> \<sigma>)) \<and>  comploc (memory (\<tau> \<sigma>)!i) glb = glb )  \<longrightarrow> compval (\<tau> \<sigma>) (memory (\<tau> \<sigma>) ! i) glb  \<ge>   recoveredGlb \<sigma>   ) )"
shows " (  \<forall> i   .   ( (pc \<sigma> syst = RecIdle \<and>  0 <  i \<and>  i < length(memory (\<tau> \<sigma>')) \<and>  comploc (memory (\<tau> \<sigma>')!i) glb = glb )  \<longrightarrow> compval (\<tau> \<sigma>') (memory (\<tau> \<sigma>') ! i) glb  \<ge>   recoveredGlb \<sigma>'   ) ) "
 using assms
  apply (simp add: TML_Write_response_def total_wfs_def )
  by  (cases "pc \<sigma> t";  simp )




lemma commitInv_rec_le_glb:
assumes  "thrdsvars"
and "TML_Commit_invocation t  \<sigma> \<sigma>'"
  and " Commit_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
and "  (  \<forall> i   .   ( (pc \<sigma> syst = RecIdle \<and>  0 <  i \<and>  i < length(memory (\<tau> \<sigma>)) \<and>  comploc (memory (\<tau> \<sigma>)!i) glb = glb )  \<longrightarrow> compval (\<tau> \<sigma>) (memory (\<tau> \<sigma>) ! i) glb  \<ge>   recoveredGlb \<sigma>   ) )"
shows " (  \<forall> i   .   ( (pc \<sigma> syst = RecIdle \<and>  0 <  i \<and>  i < length(memory (\<tau> \<sigma>')) \<and>  comploc (memory (\<tau> \<sigma>')!i) glb = glb )  \<longrightarrow> compval (\<tau> \<sigma>') (memory (\<tau> \<sigma>') ! i) glb  \<ge>   recoveredGlb \<sigma>'   ) ) "
 using assms
  apply (simp add: TML_Commit_invocation_def total_wfs_def )
  by(cases "pc \<sigma> t";  simp)


lemma commitResp_rec_le_glb:
assumes  "thrdsvars"
and "TML_Commit_response t  \<sigma> \<sigma>'"
and "  (  \<forall> i   .   ( (pc \<sigma> syst = RecIdle \<and>  0 <  i \<and>  i < length(memory (\<tau> \<sigma>)) \<and>  comploc (memory (\<tau> \<sigma>)!i) glb = glb )  \<longrightarrow> compval (\<tau> \<sigma>) (memory (\<tau> \<sigma>) ! i) glb  \<ge>   recoveredGlb \<sigma>   ) )"
shows " (  \<forall> i   .   ( (pc \<sigma> syst = RecIdle \<and>  0 <  i \<and>  i < length(memory (\<tau> \<sigma>')) \<and>  comploc (memory (\<tau> \<sigma>')!i) glb = glb )  \<longrightarrow> compval (\<tau> \<sigma>') (memory (\<tau> \<sigma>') ! i) glb  \<ge>   recoveredGlb \<sigma>'   ) ) "
 using assms
  apply (simp add: TML_Commit_response_def total_wfs_def )
  by (cases "pc \<sigma> t";  simp)






(*********************************mem  0*********************************************)


(*1*)

lemma  recover_surv_le_rec:
 assumes "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
  and " TML_Recover syst   \<sigma> \<sigma>' "
 and "  Recover_inv  syst  ((pc \<sigma>) syst)  \<sigma>"
  and "((pc \<sigma>) syst) \<in> {RecIdle} \<union> recovering "
and "  (  compval (\<tau> \<sigma>) (memory (\<tau> \<sigma>) ! 0) glb = survived_val (\<tau> \<sigma>) glb  \<and> (pc \<sigma> syst = RecIdle  \<longrightarrow>survived_val (\<tau> \<sigma>) glb   \<le>   recoveredGlb \<sigma>  )) "
shows "  (  compval (\<tau> \<sigma>') (memory (\<tau> \<sigma>') ! 0) glb = survived_val (\<tau> \<sigma>') glb  \<and> (pc \<sigma>' syst = RecIdle  \<longrightarrow>survived_val (\<tau> \<sigma>') glb   \<le>   recoveredGlb \<sigma>' )) "
 using assms
  apply (simp add:TML_Recover_def total_wfs_def Recover_inv_def )
  apply (cases "pc \<sigma> syst";   simp add: split if_splits)
  apply (simp add: compval_def comploc_def)
  using survived_val_cas_fail apply presburger
           apply (subgoal_tac " memory (\<tau> \<sigma>) = memory (\<tau> \<sigma>' ) ")
  prefer 2
  using reg_write_mem apply presburger
 apply (simp(no_asm) add: compval_def comploc_def )
  apply (metis assms(6) compval_def survived_val_cas_fail survived_val_preserved_reg_write)
  apply (metis (no_types, lifting) assms(1) assms(2) assms(6) bot_nat_0.extremum cas_fail_crash compval_wr_same last_entry_bounded le_eq_less_or_eq less_nat_zero_code survived_val_preserved_store)
  apply (subgoal_tac "memory (\<tau> \<sigma>') =  memory (\<tau> \<sigma>) ")
          prefer 2
          apply (simp add: step_def)
  apply (metis assms(6) cas_fail_crash flo_crash survived_val_preserved_flushopt)
  apply (subgoal_tac "memory (\<tau> \<sigma>') =  memory (\<tau> \<sigma>) ")
         prefer 2
          apply (simp add: step_def)
  apply (metis mem_sfence)
  apply (metis assms(6) compval_def survived_val_cas_fail survived_val_preserved_sfence)
  apply (metis compval_def survived_val_cas_fail)
  apply (metis assms(6) compval_def ld_step_mem survived_val_cas_fail survived_val_preserved_load)
     apply ( simp add: split: if_split_asm)
  apply (metis compval_def survived_val_cas_fail)
  apply (metis compval_def survived_val_cas_fail)
    apply (intro conjI)
  apply (metis assms(1) assms(2) assms(6) bot_nat_0.extremum bot_nat_0.not_eq_extremum cas_fail_crash compval_wr_same last_entry_bounded less_nat_zero_code survived_val_preserved_store)
    apply (metis le_imp_less_Suc less_or_eq_imp_le survived_val_preserved_store)
  apply (metis assms(1) assms(2) assms(6) bot_nat_0.not_eq_extremum cas_fail_crash compval_wr_same last_entry_bounded le_SucI le_refl less_nat_zero_code survived_val_preserved_store)
  apply (case_tac " log \<sigma> = Map.empty ")
  apply simp
  apply (metis compval_def survived_val_cas_fail)
  apply simp
  by (metis compval_def survived_val_cas_fail)

(*2*)
lemma  begin_surv_le_rec:
 assumes "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
  and "TML_Begin  t1   \<sigma> \<sigma>'"
    and "((pc \<sigma>) t1) \<in> beginning  \<union>{BeginPending,BeginResponding} \<union> {Aborted} "
and "  (  compval (\<tau> \<sigma>) (memory (\<tau> \<sigma>) ! 0) glb = survived_val (\<tau> \<sigma>) glb  \<and> (pc \<sigma> syst = RecIdle  \<longrightarrow>survived_val (\<tau> \<sigma>) glb   \<le>   recoveredGlb \<sigma>  )) "
shows "  (  compval (\<tau> \<sigma>') (memory (\<tau> \<sigma>') ! 0) glb = survived_val (\<tau> \<sigma>') glb  \<and> (pc \<sigma>' syst = RecIdle  \<longrightarrow>survived_val (\<tau> \<sigma>') glb   \<le>   recoveredGlb \<sigma>' )) "
 using assms
  apply (simp add:TML_Begin_def total_wfs_def Begin_inv_def del: comploc_def compval_def )
  apply (cases "pc \<sigma> t1";   simp add: split if_splits)
     apply (metis compval_def survived_val_cas_fail)
    apply (metis assms(5) compval_def ld_step_mem survived_val_cas_fail survived_val_preserved_load)
   apply (case_tac "  (even (regs (\<tau> \<sigma>) t1 DTML.loc)) ")
  apply simp
    apply (metis compval_def survived_val_cas_fail)
  apply simp
  apply (metis compval_def survived_val_cas_fail)

  apply (metis compval_def survived_val_cas_fail)
  by (metis compval_def survived_val_cas_fail)





(*3*)
lemma  read_surv_le_rec:
   assumes "thrdsvars"
   and "total_wfs (\<tau> \<sigma>)"
   and "TML_Read  t1   \<sigma> \<sigma>'"
    and "((pc \<sigma>) t1) \<in> reading \<union>{ReadPending,ReadResponding} \<union> {Aborted} "
      and "Read_inv t1  ((pc \<sigma>) t1) \<sigma>" 
and "  (  compval (\<tau> \<sigma>) (memory (\<tau> \<sigma>) ! 0) glb = survived_val (\<tau> \<sigma>) glb  \<and> (pc \<sigma> syst = RecIdle  \<longrightarrow>survived_val (\<tau> \<sigma>) glb   \<le>   recoveredGlb \<sigma>  )) "
shows "  (  compval (\<tau> \<sigma>') (memory (\<tau> \<sigma>') ! 0) glb = survived_val (\<tau> \<sigma>') glb  \<and> (pc \<sigma>' syst = RecIdle  \<longrightarrow>survived_val (\<tau> \<sigma>') glb   \<le>  recoveredGlb \<sigma>' )) "
  using assms
  apply (simp add:TML_Read_def total_wfs_def Read_inv_def )
  apply (cases "pc \<sigma> t1";   simp add: split if_splits)
  apply (metis compval_def survived_val_cas_fail)
  apply (metis assms(6) cas_fail_crash ld_crash ld_step_mem survived_val_preserved_load)
  apply (metis assms(6) cas_fail_crash)
      apply (case_tac " regs (\<tau> \<sigma>') t1 c1 = Suc 0  ")
  using mem_l_cas_succ_step
  apply (metis (no_types, lifting) One_nat_def assms(6) bot_nat_0.not_eq_extremum compval_def last_entry_bounded le_numeral_extra(3) less_nat_zero_code survived_val_cas_fail survived_val_preserved_cas)
      apply (subgoal_tac " memory (\<tau> \<sigma>) = memory (\<tau> \<sigma>' ) ")
       prefer 2
  apply (metis cas_fail_mem_same cas_lc numeral_1_eq_Suc_0 numerals(1))
  apply (metis assms(6) cas_fail_crash compval_def survived_val_preserved_cas)
  apply (metis assms(6) cas_fail_crash ld_crash ld_step_mem survived_val_preserved_load)
  apply (metis assms(6) cas_fail_crash)
  apply(metis compval_def survived_val_cas_fail)
  apply (unfold compval_def)
  using survived_val_cas_fail by presburger



(*4*)
lemma  crash_surv_le_rec:
assumes  "thrdsvars"
and "TML_Crash  \<sigma> \<sigma>'"
and "  (  compval (\<tau> \<sigma>) (memory (\<tau> \<sigma>) ! 0) glb = survived_val (\<tau> \<sigma>) glb  \<and> (pc \<sigma> syst = RecIdle  \<longrightarrow>survived_val (\<tau> \<sigma>) glb   \<le>   recoveredGlb \<sigma>  )) "
shows "  (  compval (\<tau> \<sigma>') (memory (\<tau> \<sigma>') ! 0) glb = survived_val (\<tau> \<sigma>') glb  \<and> (pc \<sigma>' syst = RecIdle  \<longrightarrow>survived_val (\<tau> \<sigma>') glb   \<le>   recoveredGlb \<sigma>' )) "
  using assms
  by(simp add: TML_Crash_def crash_step_def crash_trans_def compval_def)


(*5*)
lemma write_surv_le_rec:
  assumes "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
  and " Write_inv  t1  ((pc \<sigma>) t1) \<sigma> "
 and "TML_Write  t1   \<sigma> \<sigma>'"
  and " ((pc \<sigma>) t1) \<in> {WritePending, WriteResponding, Aborted} \<union> writing "
and "  (  compval (\<tau> \<sigma>) (memory (\<tau> \<sigma>) ! 0) glb = survived_val (\<tau> \<sigma>) glb  \<and> (pc \<sigma> syst = RecIdle  \<longrightarrow>survived_val (\<tau> \<sigma>) glb   \<le>   recoveredGlb \<sigma>  )) "
shows "  (  compval (\<tau> \<sigma>') (memory (\<tau> \<sigma>') ! 0) glb = survived_val (\<tau> \<sigma>') glb  \<and> (pc \<sigma>' syst = RecIdle  \<longrightarrow>survived_val (\<tau> \<sigma>') glb   \<le>   recoveredGlb \<sigma>' )) "
  using assms
 apply (simp add:TML_Write_def Write_inv_def total_wfs_def )
 apply (cases "pc \<sigma> t1";   simp add: split if_splits)

  apply (metis compval_def survived_val_cas_fail)

  defer
  apply (case_tac "0 < regs (\<tau> \<sigma>') t1 c1 ")
  using mem_l_cas_succ_step 
  apply (metis (no_types, opaque_lifting) Nat.lessE assms(1) assms(2) assms(6) aux bot_nat_0.extremum bot_nat_0.not_eq_extremum cas_fail_crash cas_lc compval_cas_succ_same nat.distinct(1) survived_val_preserved_cas)
 apply (subgoal_tac " memory (\<tau> \<sigma>) = memory (\<tau> \<sigma>' ) ")
       prefer 2
  apply (metis bot_nat_0.not_eq_extremum cas_fail_mem_same)
  apply (metis assms(6) bot_nat_0.not_eq_extremum cas_fail_crash compval_def survived_val_preserved_cas)
  apply (metis assms(6) compval_def reg_write_mem survived_val_cas_fail survived_val_preserved_reg_write)
        apply (case_tac "inLoc \<sigma> t1 \<notin> dom (log \<sigma>)")
  apply simp
  apply (metis compval_def survived_val_cas_fail)
        apply simp
  apply (metis compval_def survived_val_cas_fail)
       apply (metis assms(6) cas_fail_crash ld_crash ld_step_mem survived_val_preserved_load)
  apply (metis compval_def survived_val_cas_fail)
  using mem_l_step
     apply (metis (no_types, opaque_lifting) assms(1) assms(2) assms(6) aux bot_nat_0.extremum bot_nat_0.not_eq_extremum cas_fail_crash compval_wr_same less_nat_zero_code survived_val_preserved_store)
  
    apply (subgoal_tac " memory (\<tau> \<sigma>) =memory (\<tau> \<sigma>')")
  prefer 2
  apply (simp add: step_def)
     apply (metis assms(6) cas_fail_crash flo_crash survived_val_preserved_flushopt)
  apply (metis compval_def survived_val_cas_fail)
  apply (metis compval_def survived_val_cas_fail)
     apply ( simp add: split: if_split_asm)
  apply (metis compval_def survived_val_cas_fail)
  by (metis compval_def survived_val_cas_fail)



 
(*6*)
lemma commit_surv_le_rec:
  assumes "thrdsvars"
  and "total_wfs (\<tau> \<sigma>)"
  and "  Commit_inv  t   ((pc \<sigma>) t) \<sigma>  "
  and "TML_Commit  t   \<sigma> \<sigma>'"
  and " ((pc \<sigma>) t) \<in> {Ready, Aborted} \<union> committing "
and "pc \<sigma> syst = RecIdle"
and " t \<noteq> syst "
and "  (  compval (\<tau> \<sigma>) (memory (\<tau> \<sigma>) ! 0) glb = survived_val (\<tau> \<sigma>) glb  \<and> (pc \<sigma> syst = RecIdle  \<longrightarrow>survived_val (\<tau> \<sigma>) glb   \<le>   recoveredGlb \<sigma>  )) "
shows "  (  compval (\<tau> \<sigma>') (memory (\<tau> \<sigma>') ! 0) glb = survived_val (\<tau> \<sigma>') glb  \<and> (pc \<sigma>' syst = RecIdle  \<longrightarrow>survived_val (\<tau> \<sigma>') glb   \<le>   recoveredGlb \<sigma>' )) "
  using assms
  apply (unfold  total_wfs_def )
  apply (simp add:TML_Commit_def Commit_inv_def  )
  apply (cases "pc \<sigma> t";simp   )

  apply (metis assms(8) cas_fail_crash sfence_crash step_mem_sfence survived_val_preserved_sfence)
  apply (metis compval_def survived_val_cas_fail)
  apply (intro conjI)
  using  mem_l_step
  apply (metis (no_types, opaque_lifting) assms(1) assms(2) assms(8) bot_nat_0.extremum bot_nat_0.not_eq_extremum cas_fail_crash compval_wr_same last_entry_bounded less_nat_zero_code survived_val_preserved_store)
      apply (metis survived_val_preserved_store)
  apply (metis compval_def survived_val_cas_fail)
  by (metis compval_def survived_val_cas_fail)




lemma beginResp_surv_le_rec:
assumes  "thrdsvars"
and "TML_Begin_response t  \<sigma> \<sigma>'"
and "  (  compval (\<tau> \<sigma>) (memory (\<tau> \<sigma>) ! 0) glb = survived_val (\<tau> \<sigma>) glb  \<and> (pc \<sigma> syst = RecIdle  \<longrightarrow>survived_val (\<tau> \<sigma>) glb   \<le>   recoveredGlb \<sigma>  )) "
shows "  (  compval (\<tau> \<sigma>') (memory (\<tau> \<sigma>') ! 0) glb = survived_val (\<tau> \<sigma>') glb  \<and> (pc \<sigma>' syst = RecIdle  \<longrightarrow>survived_val (\<tau> \<sigma>') glb   \<le>   recoveredGlb \<sigma>' )) "
 using assms
  apply (simp add: TML_Begin_response_def total_wfs_def )
  apply (cases "pc \<sigma> t";  simp)
  by blast


lemma readInv_surv_le_rec:
assumes  "thrdsvars"
and "TML_Read_invocation t  \<sigma> \<sigma>'"
  and " Begin_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
and "  (  compval (\<tau> \<sigma>) (memory (\<tau> \<sigma>) ! 0) glb = survived_val (\<tau> \<sigma>) glb  \<and> (pc \<sigma> syst = RecIdle  \<longrightarrow>survived_val (\<tau> \<sigma>) glb   \<le>   recoveredGlb \<sigma>  )) "
shows "  (  compval (\<tau> \<sigma>') (memory (\<tau> \<sigma>') ! 0) glb = survived_val (\<tau> \<sigma>') glb  \<and> (pc \<sigma>' syst = RecIdle  \<longrightarrow>survived_val (\<tau> \<sigma>') glb   \<le>   recoveredGlb \<sigma>' )) "
 using assms
  apply (simp add: TML_Read_invocation_def Begin_invocation_inv_def total_wfs_def )
  apply (cases "pc \<sigma> t";  simp)
  by blast



lemma readResp_surv_le_rec:
assumes  "thrdsvars"
and "TML_Read_response t  \<sigma> \<sigma>'"
and "  (  compval (\<tau> \<sigma>) (memory (\<tau> \<sigma>) ! 0) glb = survived_val (\<tau> \<sigma>) glb  \<and> (pc \<sigma> syst = RecIdle  \<longrightarrow>survived_val (\<tau> \<sigma>) glb   \<le>   recoveredGlb \<sigma>  )) "
shows "  (  compval (\<tau> \<sigma>') (memory (\<tau> \<sigma>') ! 0) glb = survived_val (\<tau> \<sigma>') glb  \<and> (pc \<sigma>' syst = RecIdle  \<longrightarrow>survived_val (\<tau> \<sigma>') glb   \<le>   recoveredGlb \<sigma>' )) "
 using assms
  apply (simp add: TML_Read_response_def total_wfs_def )
   apply (cases "pc \<sigma> t";  simp)
  by blast


lemma writeInv_surv_le_rec:
assumes  "thrdsvars"
and "TML_Write_invocation t  \<sigma> \<sigma>'"
  and " Write_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
and "  (  compval (\<tau> \<sigma>) (memory (\<tau> \<sigma>) ! 0) glb = survived_val (\<tau> \<sigma>) glb  \<and> (pc \<sigma> syst = RecIdle  \<longrightarrow>survived_val (\<tau> \<sigma>) glb   \<le>   recoveredGlb \<sigma>  )) "
shows "  (  compval (\<tau> \<sigma>') (memory (\<tau> \<sigma>') ! 0) glb = survived_val (\<tau> \<sigma>') glb  \<and> (pc \<sigma>' syst = RecIdle  \<longrightarrow>survived_val (\<tau> \<sigma>') glb   \<le>   recoveredGlb \<sigma>' )) "
 using assms
  apply (simp add: TML_Write_invocation_def  total_wfs_def )
  apply (cases "pc \<sigma> t";  simp)
  by blast


lemma writeResp_surv_le_rec:
assumes  "thrdsvars"
and "TML_Write_response t  \<sigma> \<sigma>'"
 and " Write_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
and "  (  compval (\<tau> \<sigma>) (memory (\<tau> \<sigma>) ! 0) glb = survived_val (\<tau> \<sigma>) glb  \<and> (pc \<sigma> syst = RecIdle  \<longrightarrow>survived_val (\<tau> \<sigma>) glb   \<le>   recoveredGlb \<sigma>  )) "
shows "  (  compval (\<tau> \<sigma>') (memory (\<tau> \<sigma>') ! 0) glb = survived_val (\<tau> \<sigma>') glb  \<and> (pc \<sigma>' syst = RecIdle  \<longrightarrow>survived_val (\<tau> \<sigma>') glb   \<le>   recoveredGlb \<sigma>' )) "
 using assms
  apply (simp add: TML_Write_response_def total_wfs_def )
   apply (cases "pc \<sigma> t";  simp)
  by blast


lemma commitInv_surv_le_rec:
assumes  "thrdsvars"
and "TML_Commit_invocation t  \<sigma> \<sigma>'"
  and " Commit_invocation_inv  t  ((pc \<sigma>) t) \<sigma>" 
and "  (  compval (\<tau> \<sigma>) (memory (\<tau> \<sigma>) ! 0) glb = survived_val (\<tau> \<sigma>) glb  \<and> (pc \<sigma> syst = RecIdle  \<longrightarrow>survived_val (\<tau> \<sigma>) glb   \<le>   recoveredGlb \<sigma>  )) "
shows "  (  compval (\<tau> \<sigma>') (memory (\<tau> \<sigma>') ! 0) glb = survived_val (\<tau> \<sigma>') glb  \<and> (pc \<sigma>' syst = RecIdle  \<longrightarrow>survived_val (\<tau> \<sigma>') glb   \<le>   recoveredGlb \<sigma>' )) "
 using assms
  apply (simp add: TML_Commit_invocation_def total_wfs_def )
  apply (cases "pc \<sigma> t";  simp)
  by blast

lemma commitResp_surv_le_rec:
assumes  "thrdsvars"
and "TML_Commit_response t  \<sigma> \<sigma>'"
and "  (  compval (\<tau> \<sigma>) (memory (\<tau> \<sigma>) ! 0) glb = survived_val (\<tau> \<sigma>) glb  \<and> (pc \<sigma> syst = RecIdle  \<longrightarrow>survived_val (\<tau> \<sigma>) glb   \<le>   recoveredGlb \<sigma>  )) "
shows "  (  compval (\<tau> \<sigma>') (memory (\<tau> \<sigma>') ! 0) glb = survived_val (\<tau> \<sigma>') glb  \<and> (pc \<sigma>' syst = RecIdle  \<longrightarrow>survived_val (\<tau> \<sigma>') glb   \<le>   recoveredGlb \<sigma>' )) "
 using assms
  apply (simp add: TML_Commit_response_def total_wfs_def )
  apply (cases "pc \<sigma> t";  simp)
  by blast

(*********************************************************************)









end