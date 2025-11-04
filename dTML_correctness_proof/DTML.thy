(*The DTML implementation*)
theory DTML
imports "pierogi/Proof_Rules"

begin

(* Definition of the datatype for program counters *)
datatype PC =
  NotStarted
  |BeginPending
  | Begin2
  |Begin3
  |BeginResponding
  |CommitPending
  | Commit2
  | Commit3
  | Commit4
  |CommitResponding
  | Committed
  |ReadPending
  |Read1
  | Read2
  | Read3
  | Read4
  | Read5
  |ReadResponding
  |WritePending
  | Write1
  | Write2
  | Write3
  | Write4
  | Write5
  | Write6
  | Write7
  | Write8
  |WriteResponding
  | RecIdle
  | Rec1
  | Rec2
  | Rec3
  | Rec4
  | Rec5
  | Rec6
  |Rec7
  |Rec8
  |Rec9
  | ReadyToRecover
  | Ready
  | Aborted

(* Definition of constants for registers and locations *)
consts glb :: Loc
consts loc :: Reg
consts r1 :: Reg
consts val :: Reg
consts r3 :: Reg
consts c1 :: Reg
consts c2 :: Reg
consts t1 :: TId
consts t2 :: TId

(*
typedef (overloaded) AddrLoc  = "{a:: Loc. a \<noteq> glb }"
by (metis mem_Collect_eq natural.distinct(1) natural_eq_iff)*)


(*the DTMS  state*)
record mp_state =
  pc :: "TId \<Rightarrow> PC"
  \<tau> :: TState
  log :: "Loc \<Rightarrow> Val option "
  writer :: "TId option"
  readAux ::  "TId \<Rightarrow> bool"
  writeAux :: "TId \<Rightarrow> bool "
  recoveredGlb :: "Val"
  inVal :: "TId \<Rightarrow> Val"
  inLoc :: "TId \<Rightarrow> Loc"

(*pc values abbbreviations*)
abbreviation "reading  \<equiv> {Read1,Read2,Read3,Read4,Read5}"
abbreviation "recovering \<equiv> { ReadyToRecover,Rec1, Rec2, Rec3, Rec4, Rec5, Rec6, Rec7, Rec8,Rec9}"
abbreviation "beginning   \<equiv> {BeginPending,  Begin2, Begin3 }"
abbreviation "writing  \<equiv> {Write1, Write2 ,Write3, Write4, Write5, Write6, Write7,Write8 }"
abbreviation "committing  \<equiv> { Commit2, Commit3, Commit4}"


definition
  "thrdsvars  \<equiv>
   loc \<noteq> val \<and>
   loc \<noteq> r3 \<and>
   loc \<noteq> c1 \<and>
   loc  \<noteq> c2 \<and>
   val \<noteq> r3 \<and>
   val \<noteq> c1 \<and>
   val \<noteq> c2 \<and>
   r3 \<noteq> c1 \<and>
   r3 \<noteq> c2 \<and>
   c1 \<noteq> c2 \<and>
   t1 \<noteq> t2 \<and>
   t1 \<noteq> syst \<and>
   t2 \<noteq> syst
"


definition "glb_monotone_inv  ts  \<equiv> (  \<forall> i j  . 0 < j \<and>  j < length(memory ts)  \<and> 0 <  i \<and>  i < length(memory ts)  \<and>  i \<le> j \<and>  (State.loc (memory( ts)!i) ) = glb  \<and>  (State.loc (memory( ts)!j) ) = glb  \<longrightarrow> ((compval ts  (memory( ts)!i) glb ) \<le> (compval ts  (memory( ts)!j) glb ) ))"


definition "glb_monotone_complete_inv ts  \<equiv> (  \<forall> i j  . 0 < j \<and>  j < length(memory ts)  \<and> 0 \<le>  i \<and>  i < length(memory ts)  \<and>  i \<le> j \<and>  comploc ((memory ts)!i) glb = glb     \<and>   comploc ((memory ts)!j) glb = glb      \<longrightarrow> ((compval ts  (memory( ts)!i) glb ) \<le> (compval ts  (memory( ts)!j) glb ) ))"


definition "mem_tml_prop   c a  ts    \<equiv>
(\<forall> i . \<forall> j . i < j \<and> a \<noteq> c \<and>
0 <  i   \<and> j  <  length(memory ts) \<and>
comploc ((memory ts)!i) c = c   \<and>  even ( compval ts ((memory ts)!i) c) \<and>  Msg.loc ((memory ts)!j) = a
\<longrightarrow> ( \<exists>k. k > i \<and>  k < j  \<and>  Msg.loc((memory ts)!k)  = glb \<and> odd (  Msg.val((memory ts)!k))) )
"


definition "mem_tml_prop3 ts    \<equiv>
(\<forall> i . \<forall> j . \<forall>k.  i < j  \<and>
0 < i \<and> i <k \<and> k < j \<and> j <  length(memory ts) \<and>
Msg.loc((memory ts)!i) = glb   \<and>
Msg.loc( (memory ts)!j) = glb  \<and>
compval ts ((memory ts)!i) glb = compval ts ((memory ts)!j) glb
\<longrightarrow>     (Msg.loc((memory ts)!k)  = glb) )
"


definition "mem_tml_prop4 ts    \<equiv>
(\<forall> i . \<forall> j . \<forall>k.  i < j  \<and>
0 \<le>  i \<and> i <k \<and> k < j \<and> j <  length(memory ts) \<and>
comploc ((memory ts)!i) glb = glb   \<and>
comploc ((memory ts)!j) glb = glb    \<and>
compval ts ((memory ts)!i) glb = compval ts ((memory ts)!j) glb
\<longrightarrow>     (Msg.loc((memory ts)!k)  = glb) )
"


(*record update functions*)
definition " pm_inv  \<sigma>  \<equiv> ( \<forall> addr . (( addr \<noteq> glb) \<and> addr \<notin>  dom (log \<sigma>))  \<longrightarrow> [addr]\<^sub>P (\<tau> \<sigma>) =  { lastVal  addr   (\<tau> \<sigma>)  } )"


definition "update_log  l v nlog  \<equiv>  nlog ( l \<mapsto> v)"


definition  "update t nv pcf \<equiv> pcf (t := nv)"


definition "update_an t nv pcf \<equiv> pcf (t := nv)"



definition "get_key m = (SOME k. k \<in> dom m)"

lemma  get_key_in_dom:  "m  \<noteq> Map.empty \<Longrightarrow> get_key m \<in> dom m   "
  apply(simp add: get_key_def)
  by (simp add: some_in_eq)


lemmas mp_sis [simp] =
  update_def
  thrdsvars_def
  update_log_def



(*initial state*)
definition TML_start :: " mp_state \<Rightarrow> bool"
  where
    " TML_start s \<equiv>
(\<forall> t. t \<noteq> syst \<longrightarrow>   pc s t = NotStarted)
\<and> log s = Map.empty
\<and> writer s = None
\<and> start (\<tau> s)
\<and>   (recoveredGlb s = 0 )
\<and> pc s syst  = RecIdle"



(* property: coh x is the lower bound of the observable timestamps for x *)
lemma coh_min_in_ots:
  assumes "  ( \<forall> t. i \<in> OTS ts t l \<longrightarrow> coh ts t l \<le> i) "
    and "vbounded ts"
    and "  mem_structured ts "
    and "    ( \<forall> ti l. comploc ( (memory ts)!(coh ts ti l)) l = l \<and>
last_entry ts l \<in>   OTS ts ti l \<and>
last_entry ts l \<in>   OPTS ts l  \<and>
last_entry ts l \<in>   OATS ts ti l  \<and>
lastVal  l ts  \<in>  [l]\<^sub>ti ts   \<and>
lastVal  l ts  \<in>  [l]\<^sub>P ts \<and>
lastVal  l ts  \<in>   [l]\<^sup>A\<^sub>ti ts) "
    and  " total_OTSF ts "
    and "step t a ts ts'"
  shows "  (\<forall> t. i \<in> OTS ts' t l \<longrightarrow> coh ts' t l \<le> i) "
  using assms
  apply (simp add: step_def)
  apply (cases "a" ; simp)
        apply clarify
        apply (case_tac " ta = t ")
         apply (metis assms(4) assms(6) coh_lc coh_ld_st_dadrr in_mono ld_ots_sub)
        apply (metis assms(6) coh_ld_dif ld_ots_sub subset_iff)
       apply clarify
       apply (case_tac " ta = t ")
        apply (case_tac "  x21 = l ")
         apply (subgoal_tac " ( coh ts' t l =  (length(memory ts') -1)  )")
          prefer 2
  using mem_last_coh[where ts = ts and ts' = ts' and ti = t]
          apply presburger
  using  OTS_lastentry
         apply (metis dual_order.eq_iff singleton_iff)
        apply (subgoal_tac " coh ts' t l = coh ts t l  ")
         prefer 2
         apply (simp add: store_trans_def)
        apply (metis assms(6) st_ots_ni)
       apply (simp add: vbounded_def)
       apply (case_tac "  x21 = l ")
        apply (subgoal_tac "  OTS ts' ta l  = OTS ts ta l \<union>  { length(memory ts')-1} ")
         prefer 2
  using st_ots_dt_lc [where ts = ts and ts' = ts' and t' = t ]
  using assms(2) assms(6) apply blast
        apply (metis OTS_lastentry Un_iff assms(2) assms(6) coh_store_trans less_or_eq_imp_le singletonD st_lastEntry_lc st_ots_lm_lc vbounded_preserved)
       apply (subgoal_tac "  OTS ts' ta l  = OTS ts ta l ")
        prefer 2
  using assms(2) assms(6) st_ots_ni apply blast
       apply (simp add: store_trans_def)
      apply clarify
      apply (subgoal_tac " OTS ts'  ta l  = OTS ts  ta l  ")
       prefer 2
  using assms(6) fl_ots_ni apply presburger
      apply (metis assms(1) coh_fl)
     apply clarify
     apply (subgoal_tac " OTS ts'  ta l  = OTS ts  ta l  ")
      prefer 2
  using assms(6) flo_ots_ni apply presburger
     apply (metis coh_flo)
    apply clarify
    apply (case_tac "ta = t ")
     apply (subgoal_tac "OTS ts' t l   \<subseteq> OTS ts t  l")
      prefer 2
  using assms(6) mf_ots_sub apply presburger
     apply (simp add: mfence_trans_def)
     apply blast
    apply (subgoal_tac "OTS ts' ta l   =  OTS ts ta  l")
     prefer 2
  using assms(6) mf_ots_dt_ni apply blast
    apply (simp add: mfence_trans_def)
   apply clarify
   apply (case_tac "ta = t ")
    apply (simp add: sfence_trans_def)
  using assms(6) sf_ots_ni apply blast
   apply (simp add: sfence_trans_def)
  using assms(6) sf_ots_ni apply blast
  apply clarify
  apply (case_tac " regs ts' t  x74 = 1 ")
   apply (case_tac " ta = t ")
    apply (case_tac "  x71 = l ")
     apply (metis assms(4) assms(6) cas_succ_OTSx_eq_coh_expanded eq_imp_le singletonD)
    apply (subgoal_tac " OTS ts' t l \<subseteq> OTS ts t l  ")
     prefer 2
  using assms(6) cas_ots_daddr_ni apply presburger
  using assms(6) cas_succ_coh_ni total_wfs_def apply auto[1]
   apply (subgoal_tac "ts' = cas_succ_trans t ind x71 x72 x73 x74 nv mnv ts ")
    prefer 2
    apply (metis cas_fail_reg zero_neq_one)
   apply (case_tac   " x71 \<noteq> l ")
    apply (subgoal_tac " OTS ts' ta l= OTS ts ta l  ")
     prefer 2
  using  cas_succ_ots_daddr_dt  apply presburger
    apply (metis assms(6) cas_coh_dt_ni)
   apply (subgoal_tac "  OTS ts' ta l  = OTS ts ta l \<union>  { length(memory ts')-1} ")
    prefer 2
  using cas_ots_dt_lc apply presburger
   apply (subgoal_tac "  coh (ts') ta l =  coh (ts) ta l ")
    prefer 2
  using assms(6) cas_coh_dt_ni apply presburger
   apply (subgoal_tac " vbounded ts' ")
    prefer 2
  using assms(6) vbounded_preserved apply presburger
   apply (unfold  vbounded_def)
   apply (metis Un_iff cas_suc_mem_l less_or_eq_imp_le singletonD)
  apply (subgoal_tac " OTS ts' ta l   \<subseteq> OTS ts ta  l ")
   prefer 2
   apply (metis assms(2) assms(4) assms(6) cas_fail_ots_sub cas_fail_reg cas_suc_reg)
  apply (case_tac " ta \<noteq> t ")
   apply (subgoal_tac " coh ts' ta l  = coh ts ta l  ")
    prefer 2
  using assms(6) cas_coh_dt_ni apply presburger
   apply (metis assms(2) cas_fail_ots_ni cas_suc_reg)
  apply (case_tac" x71 = l ")
  using  cas_fail_coh_lc
   apply (metis assms(2) assms(4) assms(6) cas_fail_reg cas_suc_reg)
  apply (unfold  cas_fail_trans_def)
  by (metis (no_types, lifting) OTSF_def OTS_def mem_Collect_eq)


lemma [simp]: "i \<in>  OTS \<sigma> t l \<longrightarrow> valOf  i l \<sigma> \<in> [l]\<^sub>t \<sigma> "
  by (simp add: valOf_def  survived_val_def  mapval_def)


(*auxiliary lemma*)
lemma fact2 :
  assumes " \<lceil>glb : local1 \<rceil> ts "
    and  "mem_structured ts"
    and "vbounded ts"
    and "  \<forall> ti l. last_entry ts l \<in>   OTS ts ti l "
    and " \<forall> ti l.  lastVal  l ts  \<in>  [glb]\<^sub>ti ts"
    and "  compval ts ( (memory ts)! 0) glb \<noteq> local2  "
    and"   glb_monotone_inv ts "
    and " local2   \<in>  [glb]\<^sub>t ts "
  shows "local2 \<le> local1 "
  using assms
  apply (simp add:  glb_monotone_inv_def )
  apply (subgoal_tac " \<forall> i. i \<in>  OTS ts t glb \<and> i \<noteq> 0  \<longrightarrow>  i \<le>  last_entry ts glb ")
   prefer 2
   apply (subgoal_tac " \<forall> i. i \<in>  OTS ts t glb  \<and> i \<noteq> 0  \<longrightarrow>  i \<in> last_entry_set ts glb ")
    prefer 2
    apply (simp add: last_entry_set_def)
    apply (simp(no_asm) add: OTS_def OTSF_def)
   apply (subgoal_tac "\<forall>i. i  \<in> last_entry_set ts glb\<and> i \<noteq> 0   \<longrightarrow> i \<le>  last_entry ts glb  ")
    prefer 2
    apply (simp add: last_entry_def)
  using  finite_last_entry_set last_entry_in_last_entry_set
    apply (metis Max_ge)
   apply blast
  apply (subgoal_tac " \<exists> j. j \<in>  OTS ts t glb  \<and> j \<noteq>0 \<and> valOf j  glb ts = local2 ")
   prefer 2
   apply(simp add: valOf_def)
   apply (simp add: mapval_def)
   apply (smt (verit, best) assms(6) assms(8) aux gr_zeroI image_iff mapval_def mem_structured_def val_eq_compval)

  apply (subgoal_tac "  \<forall>i. (i \<in> OTS ts t glb \<and> i \<noteq>0  )  \<longrightarrow>  valOf i  glb ts \<le> local1 ")
   prefer 2
   apply (metis assms(1) assms(7) aux comploc_ots glb_monotone_inv_def i_noteqo_loc le_neq_implies_less order_antisym_conv valOf_def)
  by metis


(*part of the DTML read annotation*)
definition "read_pre ts t a \<equiv> even(regs ts t loc)
   \<and> (coh ts t glb) > 0
   \<and> valOf (coh ts t glb) glb ts = regs ts t loc
   \<and>  vrnew  ts  t \<ge> last_entry_lim ts  a (coh  ts  t glb)
   \<and>  vrnew ts t \<ge>  coh ts t a "



(*annotation that holds when a transaction t is in idle state*)
definition " Ready_total \<sigma> t   \<equiv>
(
(  ( odd(regs (\<tau> \<sigma>) t loc)   \<and>  (\<forall>l.[l]\<^sub>t (\<tau> \<sigma>) = {lastVal l  (\<tau> \<sigma>)} ) \<and> writer \<sigma> = Some t  \<and> writeAux \<sigma> t = True \<and>  regs (\<tau> \<sigma>) t loc  = lastVal glb (\<tau> \<sigma>) \<and> pc \<sigma> syst = RecIdle) )
\<or>(  ( even(regs (\<tau> \<sigma>) t loc) \<and> writer \<sigma> \<noteq> Some t \<and> \<not> writeAux \<sigma> t  \<and> pc \<sigma> syst = RecIdle ))
)
\<and>
(
((odd(regs (\<tau> \<sigma>) t loc) \<and> regs (\<tau> \<sigma>) t loc = lastVal glb (\<tau> \<sigma>)   \<and>  (\<forall>l.[l]\<^sub>t (\<tau> \<sigma>) = {lastVal l  (\<tau> \<sigma>)} ) \<and> writer \<sigma> = Some t \<and> writeAux \<sigma> t = True \<and> pc \<sigma> syst = RecIdle  ) \<or>
( even(regs (\<tau> \<sigma>) t loc) \<and> readAux \<sigma> t = False \<and> writeAux \<sigma> t = False \<and> regs (\<tau> \<sigma>) t loc = lastVal glb (\<tau> \<sigma>)\<and>  (\<forall>l.[l]\<^sub>t (\<tau> \<sigma>) = {lastVal l  (\<tau> \<sigma>)} ) \<and> pc \<sigma> syst = RecIdle  ) \<or>
(even(regs (\<tau> \<sigma>) t loc) \<and> readAux \<sigma> t = False \<and> writeAux \<sigma> t = False  \<and> regs (\<tau> \<sigma>) t loc < lastVal glb (\<tau> \<sigma>)\<and> pc \<sigma> syst = RecIdle ) \<or>
( even(regs (\<tau> \<sigma>) t loc) \<and> readAux \<sigma> t = True  \<and> writeAux \<sigma> t = False  \<and> (\<forall>a\<noteq>glb . read_pre (\<tau> \<sigma>)  t ((a) )  ))  \<and> pc \<sigma> syst = RecIdle ))
\<and>
(
(odd (regs (\<tau> \<sigma>) t  loc) \<and> writer \<sigma> = Some t \<and>  (\<forall>l.[l]\<^sub>t (\<tau> \<sigma>) = {lastVal l  (\<tau> \<sigma>)} )  \<and> pc \<sigma> syst = RecIdle
\<and>( \<forall> a. a \<in>  dom (log \<sigma>) \<longrightarrow> [a]\<^sup>A\<^sub>t (\<tau> \<sigma>) =  {lastVal a  (\<tau> \<sigma>)} )   \<and>  regs (\<tau> \<sigma>) t loc = lastVal glb (\<tau> \<sigma>) \<and> writeAux \<sigma> t = True)
\<or>  (even (regs (\<tau> \<sigma>) t  loc) \<and> writeAux \<sigma> t = False \<and> writer \<sigma> \<noteq> Some t  \<and> pc \<sigma> syst = RecIdle  )
)
"


(*DTML inv(Begin) encoding*)
definition   TML_Begin_invocation  ::  "TId \<Rightarrow>  mp_state \<Rightarrow> mp_state \<Rightarrow> bool "
  where
    "    TML_Begin_invocation   t \<sigma> \<sigma>'  \<equiv>
case (pc \<sigma>) t of
NotStarted  \<Rightarrow>(\<tau> \<sigma>) = (\<tau> \<sigma>')  \<and>
pc \<sigma>' =  update t BeginPending (pc \<sigma>) \<and>
log \<sigma>' = log \<sigma> \<and>     writer \<sigma>  = writer \<sigma>' \<and>  readAux \<sigma>  =  readAux \<sigma>'   \<and>  writeAux \<sigma>  =  writeAux \<sigma>'   \<and> recoveredGlb \<sigma> = recoveredGlb \<sigma>'  \<and> pc \<sigma>' syst = RecIdle
\<and> inLoc \<sigma>' = inLoc \<sigma> \<and> inVal \<sigma> = inVal \<sigma>'
|  _ \<Rightarrow> \<sigma> = \<sigma>' "



(*DTML inv(Begin) annotation*)
definition Begin_invocation_inv :: "TId \<Rightarrow> PC  \<Rightarrow> mp_state \<Rightarrow> bool " where
  "  Begin_invocation_inv   t p \<sigma> \<equiv>
(case p  of
NotStarted\<Rightarrow>      writer \<sigma>  \<noteq> Some t \<and>  coh (\<tau> \<sigma>) t glb  = 0 \<and>  vrnew (\<tau> \<sigma>) t   = 0
| BeginPending \<Rightarrow>  writer \<sigma>  \<noteq> Some t \<and>  coh (\<tau> \<sigma>) t glb  = 0 \<and>  vrnew (\<tau> \<sigma>) t   = 0
| _\<Rightarrow> True
)"


(*DTML resp(Begin) encoding*)
definition     TML_Begin_response ::  "TId \<Rightarrow>  mp_state \<Rightarrow> mp_state \<Rightarrow> bool "
  where
    "   TML_Begin_response  t \<sigma> \<sigma>'  \<equiv>
case (pc \<sigma>) t of
BeginResponding \<Rightarrow>  log \<sigma>' = log \<sigma> \<and>  readAux \<sigma>  =  readAux \<sigma>'  \<and> writer \<sigma> = writer \<sigma>' \<and> writeAux \<sigma> = writeAux \<sigma>'  \<and> recoveredGlb \<sigma> = recoveredGlb \<sigma>'  \<and> pc \<sigma>' syst = RecIdle
\<and> inLoc \<sigma>' = inLoc \<sigma> \<and> inVal \<sigma> = inVal \<sigma>' \<and> pc \<sigma>' =  update t Ready (pc \<sigma>) \<and> \<tau> \<sigma> = \<tau> \<sigma>'
|  _ \<Rightarrow> \<sigma> = \<sigma>'    "

(*DTML resp(Begin) annotation*)
definition Begin_Response_inv :: "TId \<Rightarrow> PC  \<Rightarrow> mp_state \<Rightarrow> bool " where
  "  Begin_Response_inv   t p \<sigma> \<equiv>
(case p  of
BeginResponding \<Rightarrow>   Ready_total \<sigma> t
|Ready  \<Rightarrow>   Ready_total \<sigma> t
| _\<Rightarrow> True
)"


(*DTML resp(Begin) encoding*)
definition   TML_Begin ::  "TId \<Rightarrow>  mp_state \<Rightarrow> mp_state \<Rightarrow> bool "
  where
    "   TML_Begin  t \<sigma> \<sigma>'  \<equiv>
case (pc \<sigma>) t of
BeginPending \<Rightarrow>(\<tau> \<sigma>) = (\<tau> \<sigma>')  \<and>
pc \<sigma>' =  update t Begin2 (pc \<sigma>) \<and>
log \<sigma>' = log \<sigma> \<and>      readAux \<sigma>' t = False \<and> ( \<forall>z. z \<noteq>t  \<longrightarrow>  readAux \<sigma> z = readAux \<sigma>' z)    \<and> writer \<sigma>' = writer \<sigma>  \<and>  ( \<forall>z. z \<noteq>t  \<longrightarrow>  writeAux \<sigma> z = writeAux \<sigma>' z) \<and>  writeAux \<sigma>' t = False \<and> recoveredGlb \<sigma> = recoveredGlb \<sigma>'  \<and> pc \<sigma>' syst = RecIdle
\<and> inLoc \<sigma>' = inLoc \<sigma> \<and> inVal \<sigma> = inVal \<sigma>'

|  Begin2\<Rightarrow>(\<tau> \<sigma>) [loc   \<leftarrow> glb ]\<^sub>t (\<tau> \<sigma>')  \<and>
pc \<sigma>' =  update t Begin3 (pc \<sigma>) \<and>
log \<sigma>' = log \<sigma> \<and>  readAux \<sigma>   = readAux \<sigma>' \<and> writer \<sigma>' = writer \<sigma>  \<and> writeAux \<sigma>' = writeAux \<sigma>  \<and> recoveredGlb \<sigma> = recoveredGlb \<sigma>'
\<and> inLoc \<sigma>' = inLoc \<sigma> \<and> inVal \<sigma> = inVal \<sigma>'

|Begin3 \<Rightarrow>  log \<sigma>' = log \<sigma> \<and>  readAux \<sigma>  =  readAux \<sigma>'  \<and> writer \<sigma> = writer \<sigma>' \<and> writeAux \<sigma> = writeAux \<sigma>'
\<and> ( if (even (regs (\<tau> \<sigma>) t  loc )  )
then  (pc \<sigma>' =  update t BeginResponding (pc \<sigma>) \<and> \<tau> \<sigma> = \<tau> \<sigma>' \<and> recoveredGlb \<sigma> = recoveredGlb \<sigma>'\<and> inLoc \<sigma>' = inLoc \<sigma> \<and> inVal \<sigma> = inVal \<sigma>'  )
else  (pc \<sigma>' =  update t  Begin2(pc \<sigma>)  \<and> \<tau> \<sigma> = \<tau> \<sigma>'\<and> recoveredGlb \<sigma> = recoveredGlb \<sigma>'\<and> inLoc \<sigma>' = inLoc \<sigma> \<and> inVal \<sigma> = inVal \<sigma>'  )
 )

|  _ \<Rightarrow> \<sigma> = \<sigma>' "


(*DTML Begin annotation*)
definition Begin_inv :: "TId \<Rightarrow> PC  \<Rightarrow> mp_state \<Rightarrow> bool " where
  "Begin_inv t p \<sigma> \<equiv>
(case p  of
BeginPending \<Rightarrow>    writer \<sigma>  \<noteq> Some t \<and>  coh (\<tau> \<sigma>) t glb  = 0 \<and>  vrnew (\<tau> \<sigma>) t   = 0
| Begin2  \<Rightarrow>  readAux \<sigma> t = False  \<and>  writeAux \<sigma> t = False \<and>  writer \<sigma>  \<noteq> Some t \<and> pc \<sigma> syst = RecIdle

| Begin3  \<Rightarrow> regs (\<tau> \<sigma>) t  loc \<in> [glb]\<^sub>t  (\<tau> \<sigma>)  \<and>  readAux \<sigma> t = False    \<and>  writeAux \<sigma> t = False \<and>  writer \<sigma>  \<noteq> Some t \<and> pc \<sigma> syst = RecIdle \<and>
(even( regs (\<tau> \<sigma>) t  loc) \<longrightarrow> (( regs (\<tau> \<sigma>) t DTML.loc = lastVal glb (\<tau> \<sigma>) \<and> (\<forall>l. [l]\<^sub>t \<tau> \<sigma> = {lastVal l (\<tau> \<sigma>)}) \<or> regs (\<tau> \<sigma>) t DTML.loc < lastVal glb (\<tau> \<sigma>))))


| BeginResponding \<Rightarrow>   Ready_total \<sigma> t

| _\<Rightarrow> True
)"



(*DTML inv(Write) encoding*)
definition   TML_Write_invocation  ::  "TId \<Rightarrow>  mp_state \<Rightarrow> mp_state \<Rightarrow> bool "
  where
    "TML_Write_invocation   t \<sigma> \<sigma>'  \<equiv>
case (pc \<sigma>) t of
Ready  \<Rightarrow> log \<sigma>' = log \<sigma> \<and>  readAux \<sigma>  =  readAux \<sigma>'  \<and> writer \<sigma> = writer \<sigma>' \<and> writeAux \<sigma> = writeAux \<sigma>'  \<and> recoveredGlb \<sigma> = recoveredGlb \<sigma>'  \<and> pc \<sigma>' syst = RecIdle
\<and> inLoc \<sigma>' = inLoc \<sigma> \<and> inVal \<sigma> = inVal \<sigma>' \<and> pc \<sigma>' =  update t WritePending (pc \<sigma>) \<and> \<tau> \<sigma> = \<tau> \<sigma>'


|  _ \<Rightarrow> \<sigma> = \<sigma>' "



(*DTML inv(Write) annotation*)
definition Write_invocation_inv :: "TId \<Rightarrow> PC  \<Rightarrow> mp_state \<Rightarrow> bool " where
  "  Write_invocation_inv   t p \<sigma> \<equiv>
(case p  of
Ready \<Rightarrow>     Ready_total \<sigma> t
| WritePending \<Rightarrow>   Ready_total \<sigma> t

| _\<Rightarrow> True
)"


(*DTML res(Write) encoding*)
definition TML_Write_response ::  "TId \<Rightarrow>  mp_state \<Rightarrow> mp_state \<Rightarrow> bool "
  where
    "   TML_Write_response  t \<sigma> \<sigma>'  \<equiv>
case (pc \<sigma>) t of

WriteResponding \<Rightarrow>  log \<sigma>' = log \<sigma> \<and>  readAux \<sigma>  =  readAux \<sigma>'  \<and> writer \<sigma> = writer \<sigma>' \<and> writeAux \<sigma> = writeAux \<sigma>'  \<and> recoveredGlb \<sigma> = recoveredGlb \<sigma>'  \<and> pc \<sigma>' syst = RecIdle
\<and> inLoc \<sigma>' = inLoc \<sigma> \<and> inVal \<sigma> = inVal \<sigma>' \<and> pc \<sigma>' =  update t Ready (pc \<sigma>) \<and> \<tau> \<sigma> = \<tau> \<sigma>'

|  _ \<Rightarrow> \<sigma> = \<sigma>'    "


(*DTML res(Write) annotation*)
definition Write_Response_inv :: "TId \<Rightarrow> PC  \<Rightarrow> mp_state \<Rightarrow> bool " where
  "  Write_Response_inv   t p \<sigma> \<equiv>
(case p  of

WriteResponding \<Rightarrow>   Ready_total \<sigma> t

|  Ready  \<Rightarrow>   Ready_total \<sigma> t

| _\<Rightarrow> True


)"

(*DTML Write  encoding*)
definition   TML_Write ::  "TId \<Rightarrow> mp_state \<Rightarrow> mp_state \<Rightarrow> bool "
  where
    "TML_Write t \<sigma> \<sigma>'  \<equiv>
case (pc \<sigma>) t of

WritePending  \<Rightarrow> pc \<sigma>' =  update t Write1 (pc \<sigma>)
\<and> (\<exists> a v. a \<noteq> glb \<and> (inLoc \<sigma>')  = update t  a  (inLoc \<sigma>)  \<and> inVal \<sigma>'  = update t  v (inVal \<sigma>)  ) \<and> log \<sigma>' = log \<sigma> \<and>  readAux \<sigma>'  =  readAux \<sigma>  \<and> writer \<sigma> = writer \<sigma>' \<and>  writeAux \<sigma>'  = writeAux \<sigma>
\<and> recoveredGlb \<sigma> = recoveredGlb \<sigma>'\<and> \<tau> \<sigma> = \<tau> \<sigma>'
|
Write1 \<Rightarrow>  if ( even (regs (\<tau> \<sigma>) t  loc) )
then (   pc \<sigma>' =  update t Write2 (pc \<sigma>) \<and> \<tau> \<sigma> = \<tau> \<sigma>' \<and> log \<sigma> = log \<sigma>' \<and> readAux \<sigma>  = readAux \<sigma>'  \<and> writer \<sigma>  = writer \<sigma>'  \<and> writeAux \<sigma>  = writeAux \<sigma>' \<and> recoveredGlb \<sigma> = recoveredGlb \<sigma>'\<and> inLoc \<sigma>' = inLoc \<sigma> \<and> inVal \<sigma> = inVal \<sigma>'   )
else  (pc \<sigma>' =  update t Write4 (pc \<sigma>) \<and> \<tau> \<sigma> = \<tau> \<sigma>'\<and> log \<sigma> = log \<sigma>'\<and> readAux \<sigma>  = readAux \<sigma>'   \<and> writer \<sigma> = writer \<sigma>'  \<and> writeAux \<sigma>  = writeAux \<sigma>'   \<and> recoveredGlb \<sigma> = recoveredGlb \<sigma>'\<and> inLoc \<sigma>' = inLoc \<sigma> \<and> inVal \<sigma> = inVal \<sigma>'  )|

Write2 \<Rightarrow>  (\<tau> \<sigma>) [CAS glb  (regs (\<tau> \<sigma>) t  loc)  ((regs (\<tau> \<sigma>) t  loc) + (Suc 0) )  c1 ]\<^sub>t (\<tau> \<sigma>')  \<and>
( if  (regs (\<tau> \<sigma>') t  c1 = 0)
then ( pc \<sigma>' =  update t Aborted (pc \<sigma>)   \<and> log \<sigma> = log \<sigma>' \<and> writer \<sigma> = writer \<sigma>' \<and> writeAux \<sigma>  = writeAux \<sigma>'  \<and> readAux \<sigma>  = readAux \<sigma>'  \<and>  recoveredGlb \<sigma> = recoveredGlb \<sigma>'\<and> inLoc \<sigma>' = inLoc \<sigma> \<and> inVal \<sigma> = inVal \<sigma>'  )
else ( pc \<sigma>' =  update t  Write3 (pc \<sigma>) \<and>  writer \<sigma>' = Some t \<and>
log \<sigma> = log \<sigma>'    \<and> writeAux  \<sigma>' t = True \<and>  (\<forall> z. z \<noteq> t \<longrightarrow>( writeAux \<sigma>' z = writeAux \<sigma> z))   \<and> readAux \<sigma>  = readAux \<sigma>' \<and>   recoveredGlb \<sigma> = recoveredGlb \<sigma>'\<and> inLoc \<sigma>' = inLoc \<sigma> \<and> inVal \<sigma> = inVal \<sigma>'  ))


|   Write3 \<Rightarrow> pc \<sigma>' =  update t  Write4 (pc \<sigma>) \<and>   (\<tau> \<sigma>') =  update_reg t loc  (regs (\<tau> \<sigma>) t loc + (Suc 0))   (\<tau> \<sigma>) \<and> writer \<sigma> = writer \<sigma>' \<and> writeAux \<sigma>  = writeAux \<sigma>'  \<and> readAux \<sigma>  = readAux \<sigma>'
\<and>   log \<sigma> = log \<sigma>' \<and> recoveredGlb \<sigma> = recoveredGlb \<sigma>'\<and> inLoc \<sigma>' = inLoc \<sigma> \<and> inVal \<sigma> = inVal \<sigma>'


|  Write4 \<Rightarrow>  \<tau> \<sigma> = \<tau> \<sigma>' \<and>   log \<sigma> = log \<sigma>' \<and> readAux \<sigma>  = readAux \<sigma>'  \<and> writer \<sigma> = writer \<sigma>' \<and>  writeAux \<sigma>  = writeAux \<sigma>'  \<and>

( if (inLoc \<sigma>) t \<notin> dom (log \<sigma> )
then  (pc \<sigma>' =  update t Write5 (pc \<sigma>) \<and> recoveredGlb \<sigma> = recoveredGlb \<sigma>'\<and> inLoc \<sigma>' = inLoc \<sigma> \<and> inVal \<sigma> = inVal \<sigma>' )
else  (pc \<sigma>' =  update t Write7(pc \<sigma>) )\<and>  recoveredGlb \<sigma> = recoveredGlb \<sigma>'\<and> inLoc \<sigma>' = inLoc \<sigma> \<and> inVal \<sigma> = inVal \<sigma>'  )|

Write5  \<Rightarrow>    (\<tau> \<sigma>) [r3 \<leftarrow> (inLoc \<sigma>) t]\<^sub>t (\<tau> \<sigma>')    \<and>  writeAux \<sigma>  = writeAux \<sigma>' \<and> log \<sigma> = log \<sigma>'
\<and>  pc \<sigma>' =  update t Write6 (pc \<sigma>)  \<and> readAux \<sigma>  = readAux \<sigma>'    \<and>  writer \<sigma>  = writer \<sigma>'  \<and> recoveredGlb \<sigma> = recoveredGlb \<sigma>'\<and> inLoc \<sigma>' = inLoc \<sigma> \<and> inVal \<sigma> = inVal \<sigma>'  |


Write6  \<Rightarrow>  log \<sigma>' = update_log  ( (inLoc \<sigma>) t)  ((regs (\<tau>  \<sigma>) t r3) )  (log \<sigma>) \<and>  writeAux \<sigma>  = writeAux \<sigma>'
\<and>  pc \<sigma>' =  update t Write7 (pc \<sigma>) \<and> \<tau> \<sigma> = \<tau> \<sigma>' \<and> readAux \<sigma>  = readAux \<sigma>'    \<and>  writer \<sigma>  = writer \<sigma>'  \<and>   recoveredGlb \<sigma> = recoveredGlb \<sigma>'\<and> inLoc \<sigma>' = inLoc \<sigma> \<and> inVal \<sigma> = inVal \<sigma>'  |

Write7 \<Rightarrow>   (\<tau> \<sigma>) [ (inLoc \<sigma>) t := (inVal \<sigma>) t]\<^sub>t (\<tau> \<sigma>')  \<and>  pc \<sigma>' =  update t Write8 (pc \<sigma>) \<and>   log \<sigma> = log \<sigma>'\<and> readAux \<sigma>'  = readAux \<sigma>  \<and>  ( (inLoc \<sigma>) t) \<in> dom (log \<sigma>) \<and>  writeAux \<sigma>  = writeAux \<sigma>'
\<and>  writer \<sigma> = writer \<sigma>'\<and> recoveredGlb \<sigma> = recoveredGlb \<sigma>'\<and> inLoc \<sigma>' = inLoc \<sigma> \<and> inVal \<sigma> = inVal \<sigma>'  |

Write8 \<Rightarrow>   (\<tau> \<sigma>) [flush\<^sub>o ((inLoc \<sigma>) t)]\<^sub>t (\<tau> \<sigma>')  \<and>  pc \<sigma>' =  update t WriteResponding (pc \<sigma>) \<and>   log \<sigma> = log \<sigma>'\<and> readAux \<sigma>  = readAux \<sigma>'  \<and>  writeAux \<sigma>  = writeAux \<sigma>'
\<and>  writer \<sigma> = writer \<sigma>'\<and> recoveredGlb \<sigma> = recoveredGlb \<sigma>'\<and> inLoc \<sigma>' = inLoc \<sigma> \<and> inVal \<sigma> = inVal \<sigma>'  |

_ \<Rightarrow> \<sigma> = \<sigma>'
"

(*DTML Write  annotation*)
definition Write_inv ::  "TId \<Rightarrow> PC \<Rightarrow> mp_state \<Rightarrow> bool " where
  "  Write_inv  t  p \<sigma>  \<equiv>
(case p  of
WritePending  \<Rightarrow> (  Ready_total \<sigma> t )
| Write1 \<Rightarrow> Ready_total \<sigma> t \<and>  glb  \<noteq> (inLoc \<sigma>) t
| Write2  \<Rightarrow>
glb \<noteq> (inLoc \<sigma>) t  \<and>  (even(regs (\<tau> \<sigma>) t loc)  \<and> writer \<sigma> \<noteq> Some t \<and>  \<not> writeAux \<sigma> t  \<and> pc \<sigma> syst = RecIdle )\<and>  (\<forall>a.( a \<in> dom (log \<sigma>) \<and> a \<noteq> (inLoc \<sigma>) t \<and> writer \<sigma> = Some t) \<longrightarrow> [a]\<^sup>A\<^sub>t  \<tau> \<sigma> = {lastVal a (\<tau> \<sigma>)})
| Write3  \<Rightarrow>
( glb \<noteq>  (inLoc \<sigma>) t  \<and>  even(regs (\<tau> \<sigma>) t loc)  \<and>
(\<forall>l.[l]\<^sub>t (\<tau> \<sigma>) = {lastVal l  (\<tau> \<sigma>)} ) \<and> regs (\<tau> \<sigma>) t  c1 = 1   \<and> regs (\<tau> \<sigma>) t loc + (Suc 0) = lastVal glb (\<tau> \<sigma>)   \<and> writer \<sigma> = Some t \<and> writeAux \<sigma> t = True   \<and> pc \<sigma> syst = RecIdle )\<and>  (\<forall>a.( a \<in> dom (log \<sigma>) \<and> a \<noteq> (inLoc \<sigma>) t \<and> writer \<sigma> = Some t) \<longrightarrow> [a]\<^sup>A\<^sub>t  \<tau> \<sigma> = {lastVal a (\<tau> \<sigma>)})
| Write4  \<Rightarrow>  glb \<noteq>  (inLoc \<sigma>) t  \<and>  odd(regs (\<tau> \<sigma>) t loc) \<and>
(\<forall>l.[l]\<^sub>t (\<tau> \<sigma>) = {lastVal l  (\<tau> \<sigma>)} )  \<and> writer \<sigma> = Some t  \<and> writeAux \<sigma> t = True \<and> regs (\<tau> \<sigma>) t loc = lastVal glb (\<tau> \<sigma>)  \<and> pc \<sigma> syst = RecIdle\<and>  (\<forall>a.( a \<in> dom (log \<sigma>) \<and> a \<noteq> (inLoc \<sigma>) t) \<longrightarrow> [a]\<^sup>A\<^sub>t  \<tau> \<sigma> = {lastVal a (\<tau> \<sigma>)})
| Write5  \<Rightarrow>  glb \<noteq>  (inLoc \<sigma>) t  \<and>  odd(regs (\<tau> \<sigma>) t loc)    \<and>
(\<forall>l.[l]\<^sub>t (\<tau> \<sigma>) = {lastVal l  (\<tau> \<sigma>)} )  \<and> writer \<sigma> = Some t  \<and> writeAux \<sigma> t = True \<and>  regs (\<tau> \<sigma>) t loc  = lastVal glb (\<tau> \<sigma>) \<and>  (inLoc \<sigma>) t  \<notin> dom (log \<sigma> )  \<and> pc \<sigma> syst = RecIdle\<and>  (\<forall>a.( a \<in> dom (log \<sigma>) \<and> a \<noteq> (inLoc \<sigma>) t) \<longrightarrow> [a]\<^sup>A\<^sub>t  \<tau> \<sigma> = {lastVal a (\<tau> \<sigma>)})
| Write6  \<Rightarrow>  glb \<noteq>  (inLoc \<sigma>) t  \<and>  odd(regs (\<tau> \<sigma>) t loc)    \<and>
(\<forall>l.[l]\<^sub>t (\<tau> \<sigma>) = {lastVal l  (\<tau> \<sigma>)} )  \<and> writer \<sigma> = Some t  \<and> writeAux \<sigma> t = True \<and>  regs (\<tau> \<sigma>) t loc  = lastVal glb (\<tau> \<sigma>)\<and>  regs (\<tau> \<sigma>) t r3  = lastVal  (inLoc \<sigma> t) (\<tau> \<sigma>)  \<and>  (inLoc \<sigma>) t  \<notin> dom (log \<sigma> )  \<and> pc \<sigma> syst = RecIdle
\<and>  (\<forall>a.( a \<in> dom (log \<sigma>) \<and> a \<noteq> (inLoc \<sigma>) t) \<longrightarrow> [a]\<^sup>A\<^sub>t  \<tau> \<sigma> = {lastVal a (\<tau> \<sigma>)})
| Write7\<Rightarrow>  glb \<noteq>  (inLoc \<sigma>) t  \<and>  odd(regs (\<tau> \<sigma>) t loc)   \<and>
(\<forall>l.[l]\<^sub>t (\<tau> \<sigma>) = {lastVal l  (\<tau> \<sigma>)} ) \<and> writer \<sigma> = Some t  \<and> writeAux \<sigma> t = True \<and>  regs (\<tau> \<sigma>) t loc = lastVal glb (\<tau> \<sigma>)  \<and> pc \<sigma> syst = RecIdle
\<and>  (\<forall>a.( a \<in> dom (log \<sigma>) \<and> a \<noteq> (inLoc \<sigma>) t) \<longrightarrow> [a]\<^sup>A\<^sub>t  \<tau> \<sigma> = {lastVal a (\<tau> \<sigma>)})
| Write8  \<Rightarrow>  glb \<noteq>  (inLoc \<sigma>) t  \<and>  odd(regs (\<tau> \<sigma>) t loc)    \<and>
(\<forall>l.[l]\<^sub>t (\<tau> \<sigma>) = {lastVal l  (\<tau> \<sigma>)} )  \<and> writer \<sigma> = Some t  \<and> writeAux \<sigma> t = True \<and>  regs (\<tau> \<sigma>) t loc  = lastVal glb (\<tau> \<sigma>)  \<and> pc \<sigma> syst = RecIdle
\<and>  (\<forall>a.( a \<in> dom (log \<sigma>) \<and> a \<noteq> (inLoc \<sigma>) t) \<longrightarrow> [a]\<^sup>A\<^sub>t  \<tau> \<sigma> = {lastVal a (\<tau> \<sigma>)})
|   WriteResponding  \<Rightarrow> (  Ready_total \<sigma> t )
| _ \<Rightarrow> True

)"



(*DTML inv(Read) encoding*)
definition   TML_Read_invocation  ::  "TId \<Rightarrow>  mp_state \<Rightarrow> mp_state \<Rightarrow> bool "
  where
    "TML_Read_invocation   t \<sigma> \<sigma>'  \<equiv>
case (pc \<sigma>) t of
Ready  \<Rightarrow> log \<sigma>' = log \<sigma> \<and>  readAux \<sigma>  =  readAux \<sigma>'  \<and> writer \<sigma> = writer \<sigma>' \<and> writeAux \<sigma> = writeAux \<sigma>'  \<and> recoveredGlb \<sigma> = recoveredGlb \<sigma>'  \<and> pc \<sigma>' syst = RecIdle
\<and> inLoc \<sigma>' = inLoc \<sigma> \<and> inVal \<sigma> = inVal \<sigma>' \<and> pc \<sigma>' =  update t ReadPending (pc \<sigma>) \<and> \<tau> \<sigma> = \<tau> \<sigma>'


|  _ \<Rightarrow> \<sigma> = \<sigma>' "


(*DTML inv(Read) annotation*)
definition Read_invocation_inv :: "TId \<Rightarrow> PC  \<Rightarrow> mp_state \<Rightarrow> bool " where
  "  Read_invocation_inv   t p \<sigma> \<equiv>
(case p  of
Ready \<Rightarrow>     Ready_total \<sigma> t
| ReadPending \<Rightarrow>   Ready_total \<sigma> t

| _\<Rightarrow> True
)"


(*DTML res(Read) encoding*)
definition TML_Read_response ::  "TId \<Rightarrow>  mp_state \<Rightarrow> mp_state \<Rightarrow> bool "
  where
    "   TML_Read_response  t \<sigma> \<sigma>'  \<equiv>
case (pc \<sigma>) t of

ReadResponding \<Rightarrow>  log \<sigma>' = log \<sigma> \<and>  readAux \<sigma>  =  readAux \<sigma>'  \<and> writer \<sigma> = writer \<sigma>' \<and> writeAux \<sigma> = writeAux \<sigma>'  \<and> recoveredGlb \<sigma> = recoveredGlb \<sigma>'  \<and> pc \<sigma>' syst = RecIdle
\<and> inLoc \<sigma>' = inLoc \<sigma> \<and> inVal \<sigma> = inVal \<sigma>' \<and> pc \<sigma>' =  update t Ready (pc \<sigma>) \<and> \<tau> \<sigma> = \<tau> \<sigma>'

|  _ \<Rightarrow> \<sigma> = \<sigma>'    "


(*DTML res(Read) annotation*)
definition Read_Response_inv :: "TId \<Rightarrow> PC  \<Rightarrow> mp_state \<Rightarrow> bool " where
  "  Read_Response_inv   t p \<sigma> \<equiv>
(case p  of
ReadResponding \<Rightarrow>   Ready_total \<sigma> t
|  Ready  \<Rightarrow>   Ready_total \<sigma> t
| _\<Rightarrow> True
)"




(*DTML Read encoding*)
definition   TML_Read ::  "TId \<Rightarrow> mp_state \<Rightarrow> mp_state \<Rightarrow> bool "
  where
    "  TML_Read  t  \<sigma> \<sigma>'  \<equiv>
case (pc \<sigma>) t of
ReadPending  \<Rightarrow>  pc \<sigma>' =  update t Read1 (pc \<sigma>)
\<and> (\<exists> a . a \<noteq> glb \<and>  (inLoc \<sigma>')  = update t  a  (inLoc \<sigma>)  )  \<and> inVal \<sigma> = inVal \<sigma>' \<and> \<tau> \<sigma> = \<tau> \<sigma>' \<and> log \<sigma>' = log \<sigma> \<and>  readAux \<sigma>'  =  readAux \<sigma>  \<and> writer \<sigma> = writer \<sigma>' \<and>  writeAux \<sigma>'  = writeAux \<sigma>
\<and> recoveredGlb \<sigma> = recoveredGlb \<sigma>'



|   Read1 \<Rightarrow> (\<tau> \<sigma>) [val   \<leftarrow>  (inLoc \<sigma>) t ]\<^sub>t (\<tau> \<sigma>') \<and>
pc \<sigma>' =  update t Read2 (pc \<sigma>) \<and> log \<sigma>' = log \<sigma> \<and>  readAux \<sigma>'  =  readAux \<sigma>  \<and> writer \<sigma> = writer \<sigma>' \<and>  writeAux \<sigma>'  = writeAux \<sigma>
\<and> recoveredGlb \<sigma> = recoveredGlb \<sigma>'\<and> inLoc \<sigma>' = inLoc \<sigma> \<and> inVal \<sigma> = inVal \<sigma>'   |



Read2 \<Rightarrow>   ( if (even (regs (\<tau> \<sigma>) t loc )  \<and> ( \<not> readAux \<sigma> t)  )
then  (pc \<sigma>' =  update t Read3 (pc \<sigma>) \<and> \<tau> \<sigma> = \<tau> \<sigma>'
 \<and> log \<sigma>' = log \<sigma> \<and>  readAux \<sigma>'  =  readAux \<sigma>  \<and> writer \<sigma> = writer \<sigma>' \<and>  writeAux \<sigma>'  = writeAux \<sigma>  \<and> recoveredGlb \<sigma> = recoveredGlb \<sigma>'\<and> inLoc \<sigma>' = inLoc \<sigma> \<and> inVal \<sigma> = inVal \<sigma>'  )

else  pc \<sigma>' =  update t Read4 (pc \<sigma>)  \<and> \<tau> \<sigma> = \<tau> \<sigma>'
\<and> log \<sigma>' = log \<sigma> \<and>  readAux \<sigma>'  =  readAux \<sigma>  \<and> writer \<sigma> = writer \<sigma>'\<and>  writeAux \<sigma>'  = writeAux \<sigma> \<and> recoveredGlb \<sigma> = recoveredGlb \<sigma>'\<and> inLoc \<sigma>' = inLoc \<sigma> \<and> inVal \<sigma> = inVal \<sigma>'  )|

Read3 \<Rightarrow>   (\<tau> \<sigma>) [CAS glb  (regs (\<tau> \<sigma>) t  loc) ((regs (\<tau> \<sigma>) t loc)) c1 ]\<^sub>t  (\<tau> \<sigma>') \<and>
log \<sigma>' = log \<sigma> \<and> writer \<sigma> = writer \<sigma>' \<and> writeAux \<sigma> = writeAux \<sigma>' \<and>
( if ( (regs (\<tau> \<sigma>') t c1 = 1 )  )
then  (pc \<sigma>' =  update t ReadResponding (pc \<sigma>)  \<and>  readAux \<sigma>' t = True \<and> ( \<forall>z. z \<noteq>t  \<longrightarrow>  readAux \<sigma> z = readAux \<sigma>' z)
\<and> writeAux \<sigma> = writeAux \<sigma>' \<and>
log \<sigma>' = log \<sigma>  \<and> writer \<sigma> = writer \<sigma>'  \<and> recoveredGlb \<sigma> = recoveredGlb \<sigma>'\<and> inLoc \<sigma>' = inLoc \<sigma> \<and> inVal \<sigma> = inVal \<sigma>'  )

else  (pc \<sigma>' =  update t  Aborted (pc \<sigma>) )
\<and> log \<sigma>' = log \<sigma> \<and>  readAux \<sigma>'  =  readAux \<sigma>  \<and> writer \<sigma> = writer \<sigma>'  \<and> writeAux \<sigma> = writeAux \<sigma>'  \<and> recoveredGlb \<sigma> = recoveredGlb \<sigma>'
\<and> inLoc \<sigma>' = inLoc \<sigma> \<and> inVal \<sigma> = inVal \<sigma>'  ) |


Read4 \<Rightarrow>   (\<tau> \<sigma>) [r3   \<leftarrow>   glb ]\<^sub>t (\<tau> \<sigma>') \<and>
pc \<sigma>' =  update t Read5 (pc \<sigma>)
\<and> log \<sigma>' = log \<sigma> \<and>  readAux \<sigma>'  =  readAux \<sigma>  \<and> writer \<sigma> = writer \<sigma>' \<and> writeAux \<sigma> = writeAux \<sigma>' \<and> recoveredGlb \<sigma> = recoveredGlb \<sigma>' \<and> inLoc \<sigma>' = inLoc \<sigma> \<and> inVal \<sigma> = inVal \<sigma>'  |


Read5 \<Rightarrow>   ( if  ( regs (\<tau> \<sigma>) t  r3 =  regs (\<tau> \<sigma>) t  loc )
then  (pc \<sigma>' =  update t (ReadResponding )  (pc \<sigma>)
\<and> log \<sigma>' = log \<sigma> \<and>  readAux \<sigma>'  =  readAux \<sigma>  \<and> writer \<sigma> = writer \<sigma>' \<and> writeAux \<sigma> = writeAux \<sigma>' \<and> (\<tau> \<sigma> = \<tau> \<sigma>' ) \<and> recoveredGlb \<sigma> = recoveredGlb \<sigma>'
\<and> inLoc \<sigma>' = inLoc \<sigma> \<and> inVal \<sigma> = inVal \<sigma>'  )

else  (pc \<sigma>' =  update t Aborted(pc \<sigma>) )
\<and> log \<sigma>' = log \<sigma> \<and>  readAux \<sigma>'  =  readAux \<sigma>  \<and> writer \<sigma> = writer \<sigma>'\<and> writeAux \<sigma>' = writeAux \<sigma>  \<and>(\<tau> \<sigma> = \<tau> \<sigma>' )\<and> recoveredGlb \<sigma> = recoveredGlb \<sigma>'\<and> inLoc \<sigma>' = inLoc \<sigma> \<and> inVal \<sigma> = inVal \<sigma>'   ) |

_ \<Rightarrow> \<sigma> = \<sigma>'
"


(*DTML Read annotation*)
definition Read_inv ::  "TId  \<Rightarrow> PC  \<Rightarrow>  mp_state  \<Rightarrow> bool " where
  "  Read_inv  t p  \<sigma>  \<equiv>

(case p  of
ReadPending  \<Rightarrow> Ready_total \<sigma> t

| Read1 \<Rightarrow> Ready_total \<sigma> t \<and>  glb  \<noteq> (inLoc \<sigma>) t

| Read2  \<Rightarrow>  glb  \<noteq> (inLoc \<sigma>) t \<and>
((odd(regs (\<tau> \<sigma>) t loc)\<and> regs (\<tau> \<sigma>) t loc = lastVal glb (\<tau> \<sigma>)   \<and>  (\<forall>l.[l]\<^sub>t (\<tau> \<sigma>) = {lastVal l  (\<tau> \<sigma>)} ) \<and> writer \<sigma> = Some t \<and> writeAux \<sigma> t = True \<and> regs (\<tau> \<sigma>) t val = lastVal  ((inLoc \<sigma>) t)   (\<tau> \<sigma>) \<and> pc \<sigma> syst = RecIdle  \<and>( \<forall> a. a \<in>  dom (log \<sigma>) \<longrightarrow> [a]\<^sup>A\<^sub>t (\<tau> \<sigma>) =  {lastVal a  (\<tau> \<sigma>)} )  ) \<or>

(even(regs (\<tau> \<sigma>) t loc) \<and> readAux \<sigma> t = False \<and> writeAux \<sigma> t = False\<and> writer \<sigma> \<noteq> Some t \<and> regs (\<tau> \<sigma>) t loc = lastVal glb (\<tau> \<sigma>)  \<and> regs (\<tau> \<sigma>) t val = lastVal  ((inLoc \<sigma>) t)   (\<tau> \<sigma>) \<and> pc \<sigma> syst = RecIdle  ) \<or>
(even(regs (\<tau> \<sigma>) t loc) \<and> readAux \<sigma> t = False \<and> writeAux \<sigma> t = False \<and> writer \<sigma> \<noteq> Some t\<and>regs (\<tau> \<sigma>) t loc < lastVal glb (\<tau> \<sigma>) \<and> pc \<sigma> syst = RecIdle ) \<or>
(even(regs (\<tau> \<sigma>) t loc) \<and> readAux \<sigma> t = True  \<and> writeAux \<sigma> t = False \<and>writer \<sigma> \<noteq> Some t\<and> (\<forall>a\<noteq>glb. read_pre (\<tau> \<sigma>)  t a)  \<and>  regs (\<tau> \<sigma>) t  loc  \<in>  [glb]\<^sub>t (\<tau> \<sigma>) \<and> regs (\<tau> \<sigma>) t val  = valOf (last_entry_lim (\<tau> \<sigma>)  ((inLoc \<sigma>) t)  (coh (\<tau> \<sigma>) t glb))  ((inLoc \<sigma>) t)  (\<tau> \<sigma>) \<and> pc \<sigma> syst = RecIdle   )  \<or>
(even(regs (\<tau> \<sigma>) t loc) \<and> readAux \<sigma> t = True  \<and> writeAux \<sigma> t = False \<and>writer \<sigma> \<noteq> Some t\<and>  regs (\<tau> \<sigma>) t  loc  \<notin>  [glb]\<^sub>t (\<tau> \<sigma>) \<and> pc \<sigma> syst = RecIdle  ) )

|Read3  \<Rightarrow>  glb  \<noteq> (inLoc \<sigma>) t \<and>
(( even(regs (\<tau> \<sigma>) t loc) \<and> readAux \<sigma> t = False  \<and> writeAux \<sigma> t = False \<and>  writer \<sigma> \<noteq> Some t \<and> regs (\<tau> \<sigma>) t loc = lastVal glb (\<tau> \<sigma>) \<and> regs (\<tau> \<sigma>) t val = lastVal  ((inLoc \<sigma>) t)   (\<tau> \<sigma>) \<and> pc \<sigma> syst = RecIdle  ) \<or>
( even(regs (\<tau> \<sigma>) t loc) \<and> readAux \<sigma> t = False  \<and> writeAux \<sigma> t = False \<and>  writer \<sigma> \<noteq> Some t \<and>regs (\<tau> \<sigma>) t loc < lastVal glb (\<tau> \<sigma>) \<and> pc \<sigma> syst = RecIdle  ))



| Read4  \<Rightarrow>  glb  \<noteq> (inLoc \<sigma>) t \<and>
(( odd(regs (\<tau> \<sigma>) t loc)\<and> regs (\<tau> \<sigma>) t loc = lastVal glb (\<tau> \<sigma>)    \<and>  (\<forall>l.[l]\<^sub>t (\<tau> \<sigma>) = {lastVal l  (\<tau> \<sigma>)} ) \<and> writer \<sigma> = Some t \<and> writeAux \<sigma> t = True \<and>   regs (\<tau> \<sigma>) t val = lastVal  ((inLoc \<sigma>) t)   (\<tau> \<sigma>) \<and> pc \<sigma> syst = RecIdle  \<and>( \<forall> a. a \<in>  dom (log \<sigma>) \<longrightarrow> [a]\<^sup>A\<^sub>t (\<tau> \<sigma>) =  {lastVal a  (\<tau> \<sigma>)} )  ) \<or>
(even(regs (\<tau> \<sigma>) t loc) \<and> readAux \<sigma> t = True  \<and> writeAux \<sigma> t = False \<and>  writer \<sigma> \<noteq> Some t\<and>  (\<forall>a\<noteq>glb. read_pre (\<tau> \<sigma>)  t a) \<and>  regs (\<tau> \<sigma>) t  loc  \<in>  [glb]\<^sub>t (\<tau> \<sigma>) \<and>  regs (\<tau> \<sigma>) t val  = valOf (last_entry_lim (\<tau> \<sigma>)  ((inLoc \<sigma>) t)  (coh (\<tau> \<sigma>) t glb))  ((inLoc \<sigma>) t)  (\<tau> \<sigma>) \<and> pc \<sigma> syst = RecIdle )  \<or>
(even(regs (\<tau> \<sigma>) t loc) \<and> readAux \<sigma> t = True  \<and> writeAux \<sigma> t = False\<and>  writer \<sigma> \<noteq> Some t \<and> regs (\<tau> \<sigma>) t  loc  \<notin>  [glb]\<^sub>t (\<tau> \<sigma>) \<and> pc \<sigma> syst = RecIdle )
)



| Read5  \<Rightarrow>  glb  \<noteq> (inLoc \<sigma>) t \<and>
((odd(regs (\<tau> \<sigma>) t loc) \<and> regs (\<tau> \<sigma>) t loc = lastVal glb (\<tau> \<sigma>)    \<and> writer \<sigma> = Some t \<and> writeAux \<sigma> t = True \<and> regs (\<tau> \<sigma>) t val = lastVal  ((inLoc \<sigma>) t)   (\<tau> \<sigma>) \<and> (\<forall>l.[l]\<^sub>t (\<tau> \<sigma>) = {lastVal l  (\<tau> \<sigma>)}) \<and> regs (\<tau> \<sigma>) t  loc = regs (\<tau> \<sigma>) t  r3 \<and> pc \<sigma> syst = RecIdle   \<and>( \<forall> a. a \<in>  dom (log \<sigma>) \<longrightarrow> [a]\<^sup>A\<^sub>t (\<tau> \<sigma>) =  {lastVal a  (\<tau> \<sigma>)} ) ) \<or>

(even(regs (\<tau> \<sigma>) t loc) \<and> readAux \<sigma> t = True  \<and> writeAux \<sigma> t = False \<and> writer \<sigma> \<noteq> Some t\<and> (\<forall>a\<noteq>glb. read_pre (\<tau> \<sigma>)  t  ((a) ))  \<and>  regs (\<tau> \<sigma>) t  loc=  regs (\<tau> \<sigma>) t  r3 \<and>  regs (\<tau> \<sigma>) t val  = valOf (last_entry_lim (\<tau> \<sigma>)  ((inLoc \<sigma>) t)  (coh (\<tau> \<sigma>) t glb))  ((inLoc \<sigma>) t)  (\<tau> \<sigma>)    \<and> pc \<sigma> syst = RecIdle
)

\<or>
(even(regs (\<tau> \<sigma>) t loc) \<and> readAux \<sigma> t = True  \<and> writeAux \<sigma> t = False \<and>writer \<sigma> \<noteq> Some t\<and> regs (\<tau> \<sigma>) t  loc \<noteq> regs (\<tau> \<sigma>) t  r3  \<and> pc \<sigma> syst = RecIdle )
)

|   ReadResponding  \<Rightarrow> Ready_total \<sigma> t

| _ \<Rightarrow> True



)"



(*DTML inv(Commit) encoding*)
definition   TML_Commit_invocation  ::  "TId \<Rightarrow>  mp_state \<Rightarrow> mp_state \<Rightarrow> bool "
  where
    "    TML_Commit_invocation   t \<sigma> \<sigma>'  \<equiv>
case (pc \<sigma>) t of
Ready  \<Rightarrow> log \<sigma>' = log \<sigma> \<and>  readAux \<sigma>  =  readAux \<sigma>'  \<and> writer \<sigma> = writer \<sigma>' \<and> writeAux \<sigma> = writeAux \<sigma>'  \<and> recoveredGlb \<sigma> = recoveredGlb \<sigma>'  \<and> pc \<sigma>' syst = RecIdle
\<and> inLoc \<sigma>' = inLoc \<sigma> \<and> inVal \<sigma> = inVal \<sigma>' \<and> pc \<sigma>' =  update t CommitPending (pc \<sigma>) \<and> \<tau> \<sigma> = \<tau> \<sigma>'


|  _ \<Rightarrow> \<sigma> = \<sigma>' "


(*DTML inv(Commit) annotation*)
definition Commit_invocation_inv :: "TId \<Rightarrow> PC  \<Rightarrow> mp_state \<Rightarrow> bool " where
  "  Commit_invocation_inv   t p \<sigma> \<equiv>
(case p  of
Ready \<Rightarrow>     Ready_total \<sigma> t
| CommitPending \<Rightarrow>   Ready_total \<sigma> t

| _\<Rightarrow> True
)"


(*DTML res(Commit) encoding*)
definition     TML_Commit_response ::  "TId \<Rightarrow>  mp_state \<Rightarrow> mp_state \<Rightarrow> bool "
  where
    "   TML_Commit_response  t \<sigma> \<sigma>'  \<equiv>
case (pc \<sigma>) t of

CommitResponding \<Rightarrow>  log \<sigma>' = log \<sigma> \<and>  readAux \<sigma>  =  readAux \<sigma>'  \<and> writer \<sigma> = writer \<sigma>' \<and> writeAux \<sigma> = writeAux \<sigma>'  \<and> recoveredGlb \<sigma> = recoveredGlb \<sigma>'  \<and> pc \<sigma>' syst = RecIdle
\<and> inLoc \<sigma>' = inLoc \<sigma> \<and> inVal \<sigma> = inVal \<sigma>' \<and> pc \<sigma>' =  update t Committed (pc \<sigma>) \<and> \<tau> \<sigma> = \<tau> \<sigma>'

|  _ \<Rightarrow> \<sigma> = \<sigma>'    "


(*DTML res(Commit) annotation*)
definition Commit_Response_inv :: "TId \<Rightarrow> PC  \<Rightarrow> mp_state \<Rightarrow> bool " where
  "  Commit_Response_inv   t p \<sigma> \<equiv>
(case p  of

_\<Rightarrow> True

)"


(*DTML Commit encoding*)
definition   TML_Commit ::  "TId \<Rightarrow>  mp_state \<Rightarrow> mp_state \<Rightarrow> bool "
  where
    "  TML_Commit t   \<sigma> \<sigma>'  \<equiv>
case (pc \<sigma>) t of

CommitPending  \<Rightarrow>   \<tau> \<sigma>' = \<tau> \<sigma> \<and>  log \<sigma> = log \<sigma>' \<and> writer \<sigma>' = writer \<sigma> \<and>  readAux \<sigma>'  = readAux \<sigma>  \<and>  writeAux \<sigma>'  = writeAux  \<sigma>  \<and>
(  if  odd (regs (\<tau> \<sigma>) t  loc)
then  (pc \<sigma>' =  update t Commit2(pc \<sigma>)  \<and>  recoveredGlb \<sigma>' =  recoveredGlb \<sigma>\<and> inLoc \<sigma>' = inLoc \<sigma> \<and> inVal \<sigma> = inVal \<sigma>'  )
else  (pc \<sigma>' =  update t  CommitResponding (pc \<sigma>)    \<and>  recoveredGlb \<sigma>' =  recoveredGlb \<sigma>\<and> inLoc \<sigma>' = inLoc \<sigma> \<and> inVal \<sigma> = inVal \<sigma>'  ) )|

Commit2 \<Rightarrow>  (\<tau> \<sigma>) [sfence]\<^sub>t (\<tau> \<sigma>')  \<and> pc \<sigma>' =  update t Commit3(pc \<sigma>) \<and> log \<sigma> = log \<sigma>'
\<and> writer \<sigma> = writer \<sigma>' \<and>  readAux \<sigma>  = readAux \<sigma>'  \<and>  writeAux \<sigma>  = writeAux  \<sigma>' \<and>  recoveredGlb \<sigma>' =  recoveredGlb \<sigma>\<and> inLoc \<sigma>' = inLoc \<sigma> \<and> inVal \<sigma> = inVal \<sigma>'  |

Commit3 \<Rightarrow>  log \<sigma>'= Map.empty  \<and>  \<tau> \<sigma>' = \<tau> \<sigma> \<and> pc \<sigma>' =  update t Commit4(pc \<sigma>)
\<and> writer \<sigma> = writer \<sigma>' \<and>  readAux \<sigma>  = readAux \<sigma>'  \<and>  writeAux \<sigma>  = writeAux  \<sigma>' \<and>  recoveredGlb \<sigma>' =  recoveredGlb \<sigma>\<and> inLoc \<sigma>' = inLoc \<sigma> \<and> inVal \<sigma> = inVal \<sigma>'  |

Commit4 \<Rightarrow>   (\<tau> \<sigma>) [ glb := (regs (\<tau> \<sigma>) t  loc + 1)]\<^sub>t (\<tau> \<sigma>') \<and>  log \<sigma> = log \<sigma>' \<and>
pc \<sigma>' =  update t    CommitResponding (pc \<sigma>) \<and>   writer \<sigma>' = None
\<and>  readAux \<sigma>  = readAux \<sigma>'  \<and>  writeAux \<sigma>  = writeAux  \<sigma>'   \<and>  recoveredGlb \<sigma>' =  recoveredGlb \<sigma>\<and> inLoc \<sigma>' = inLoc \<sigma> \<and> inVal \<sigma> = inVal \<sigma>'

|  _ \<Rightarrow> \<sigma> = \<sigma>'
"

(*DTML Commit annotation*)
definition Commit_inv ::  "TId \<Rightarrow> PC \<Rightarrow> mp_state \<Rightarrow> bool " where
  "   Commit_inv  t  p \<sigma>  \<equiv>
case p  of
CommitPending \<Rightarrow>  Ready_total \<sigma> t

|  Commit2 \<Rightarrow>  (odd (regs (\<tau> \<sigma>) t  loc) \<and> writer \<sigma> = Some t \<and>  (\<forall>l.[l]\<^sub>t (\<tau> \<sigma>) = {lastVal l  (\<tau> \<sigma>)} )  \<and> pc \<sigma> syst = RecIdle
\<and>( \<forall> a. a \<in>  dom (log \<sigma>) \<longrightarrow> [a]\<^sup>A\<^sub>t (\<tau> \<sigma>) =  {lastVal a  (\<tau> \<sigma>)} ) \<and>  (regs (\<tau> \<sigma>) t  loc) \<in> [glb]\<^sub>t ( \<tau> \<sigma>)\<and>  regs (\<tau> \<sigma>) t loc = lastVal glb (\<tau> \<sigma>) \<and> writeAux \<sigma> t = True)

|  Commit3 \<Rightarrow>  (odd (regs (\<tau> \<sigma>) t  loc) \<and> writer \<sigma> = Some t  \<and>  (\<forall>l.[l]\<^sub>t (\<tau> \<sigma>) = {lastVal l  (\<tau> \<sigma>)} )  \<and> pc \<sigma> syst = RecIdle
\<and>( \<forall> a. a \<in>  dom (log \<sigma>) \<longrightarrow> [a]\<^sub>P (\<tau> \<sigma>) =  {lastVal a  (\<tau> \<sigma>)} ) \<and>  (regs (\<tau> \<sigma>) t  loc) \<in> [glb]\<^sub>t ( \<tau> \<sigma>) \<and>   regs (\<tau> \<sigma>) t loc = lastVal glb (\<tau> \<sigma>) \<and> writeAux \<sigma> t = True )

|  Commit4 \<Rightarrow>  (odd (regs (\<tau> \<sigma>) t  loc) \<and> writer \<sigma> = Some t  \<and> log \<sigma> = Map.empty  \<and>  (\<forall>l.[l]\<^sub>t (\<tau> \<sigma>) = {lastVal l  (\<tau> \<sigma>)} )  \<and> pc \<sigma> syst = RecIdle
\<and>( \<forall> a. a \<in>  dom (log \<sigma>) \<longrightarrow> [a]\<^sub>P (\<tau> \<sigma>) =  {lastVal a  (\<tau> \<sigma>)} ) \<and>  (regs (\<tau> \<sigma>) t  loc) \<in> [glb]\<^sub>t ( \<tau> \<sigma>) \<and>  regs (\<tau> \<sigma>) t loc = lastVal glb (\<tau> \<sigma>) \<and> writeAux \<sigma> t = True )

| CommitResponding  \<Rightarrow> True


| _ \<Rightarrow> True

"

(*DTML crash encoding*)
definition TML_Crash ::  " mp_state \<Rightarrow> mp_state \<Rightarrow> bool "
  where
    "TML_Crash  \<sigma> \<sigma>'  \<equiv>
writer \<sigma>' = None \<and>
(\<tau> \<sigma>) [CRASH] (\<tau> \<sigma>')\<and>

log \<sigma> = log \<sigma>'  \<and>
pc \<sigma>' =  (\<lambda> t.  if t = syst
then  ReadyToRecover
else  if t \<noteq> syst \<and> (pc \<sigma> t) \<notin> {NotStarted, Aborted, Committed}
then Aborted else (pc \<sigma> t) )

"


(*DTML Recover annotation*)
definition   TML_Recover ::  "TId \<Rightarrow>  mp_state \<Rightarrow> mp_state \<Rightarrow> bool "
  where
    "  TML_Recover t   \<sigma> \<sigma>'  \<equiv>
case (pc \<sigma>) t of
ReadyToRecover \<Rightarrow> (if (log \<sigma> = Map.empty)
then (pc \<sigma>' =  update t Rec6(pc \<sigma>) \<and> \<tau> \<sigma>' = \<tau> \<sigma> \<and> writer \<sigma>' = writer \<sigma>  \<and> readAux \<sigma> = readAux \<sigma>' \<and> writeAux \<sigma> = writeAux \<sigma>' \<and> log \<sigma> = log \<sigma>'  )
else   pc \<sigma>' =  update t Rec1(pc \<sigma>) \<and> \<tau> \<sigma>' = \<tau> \<sigma> \<and> writer \<sigma>' = writer \<sigma> \<and>  readAux \<sigma> = readAux \<sigma>'  \<and> writeAux \<sigma> = writeAux \<sigma>'  \<and> log \<sigma> = log \<sigma>'  )|

Rec1 \<Rightarrow>   (\<tau> \<sigma>') =  update_reg t c2  (get_key (log \<sigma>)) (\<tau> \<sigma>)\<and>   pc \<sigma>' =  update t Rec2(pc \<sigma>) \<and> writer \<sigma>' = writer \<sigma> \<and>  readAux \<sigma> = readAux \<sigma>'   \<and> writeAux \<sigma> = writeAux \<sigma>'  \<and> log \<sigma> = log \<sigma>'  |

Rec2 \<Rightarrow> (\<tau> \<sigma>) [  (regs (\<tau> \<sigma>) t c2)  := the(log \<sigma>  (  regs (\<tau> \<sigma>) t c2  ))]\<^sub>t (\<tau> \<sigma>') \<and> pc \<sigma>' =  update t Rec3(pc \<sigma>) \<and> writer \<sigma>' = writer \<sigma>
\<and>  readAux \<sigma> = readAux \<sigma>'\<and> writeAux \<sigma> = writeAux \<sigma>'  \<and> log \<sigma> = log \<sigma>'  |

Rec3 \<Rightarrow>   (\<tau> \<sigma>) [flush\<^sub>o  (regs (\<tau> \<sigma>) t c2) ]\<^sub>t(\<tau> \<sigma>')  \<and>  pc \<sigma>' =  update t   Rec4 (pc \<sigma>) \<and> writer \<sigma>' = writer \<sigma> \<and>  readAux \<sigma> = readAux \<sigma>' \<and> writeAux \<sigma> = writeAux \<sigma>' \<and> log \<sigma> = log \<sigma>' |

Rec4\<Rightarrow>   (\<tau> \<sigma>) [sfence]\<^sub>t (\<tau> \<sigma>')   \<and>  pc \<sigma>' =  update t  Rec5 (pc \<sigma>) \<and> writer \<sigma>' = writer \<sigma> \<and>  readAux \<sigma> = readAux \<sigma>'\<and> writeAux \<sigma> = writeAux \<sigma>'  \<and> log \<sigma> = log \<sigma>'   |


Rec5\<Rightarrow> log \<sigma>' = (log \<sigma>)(  (regs (\<tau> \<sigma>) t c2) := None)  \<and>  pc \<sigma>' =  update t   ReadyToRecover (pc \<sigma>) \<and> writer \<sigma>' = writer \<sigma> \<and> \<tau> \<sigma> = \<tau>  \<sigma>' \<and>  readAux \<sigma> = readAux \<sigma>' \<and> writeAux \<sigma> = writeAux \<sigma>' |


Rec6 \<Rightarrow> (\<tau> \<sigma>) [c1   \<leftarrow> glb ]\<^sub>t (\<tau> \<sigma>')  \<and>
pc \<sigma>' =  update t Rec7 (pc \<sigma>) \<and>
log \<sigma>' = log \<sigma> \<and>  readAux \<sigma>   = readAux \<sigma>' \<and> writer \<sigma>' = writer \<sigma>  \<and> writeAux \<sigma>' = writeAux \<sigma>
|


Rec7 \<Rightarrow> (if (even(regs (\<tau> \<sigma>) t c1))
then (pc \<sigma>' =  update t Rec8(pc \<sigma>) \<and> \<tau> \<sigma>' = \<tau> \<sigma> \<and> writer \<sigma>' = writer \<sigma>  \<and> readAux \<sigma> = readAux \<sigma>'  \<and> writeAux \<sigma> = writeAux \<sigma>'  \<and> log \<sigma> = log \<sigma>' )
else   pc \<sigma>' =  update t Rec9(pc \<sigma>) \<and> \<tau> \<sigma>' = \<tau> \<sigma> \<and> writer \<sigma>' = writer \<sigma> \<and>  readAux \<sigma> = readAux \<sigma>'   \<and> writeAux \<sigma> = writeAux \<sigma>'  \<and> log \<sigma> = log \<sigma>'  )|


Rec8 \<Rightarrow> (\<tau> \<sigma>) [  glb  :=  Suc( Suc(regs (\<tau> \<sigma>) t c1))  ]\<^sub>t (\<tau> \<sigma>') \<and> pc \<sigma>' =  update t RecIdle(pc \<sigma>) \<and> writer \<sigma>' = writer \<sigma>
\<and>  readAux \<sigma> = readAux \<sigma>'\<and> writeAux \<sigma> = writeAux \<sigma>'  \<and> log \<sigma> = log \<sigma>' \<and>  recoveredGlb \<sigma>' =  Suc( Suc(regs (\<tau> \<sigma>) t c1))  |


Rec9 \<Rightarrow>  (\<tau> \<sigma>) [  glb  :=   Suc(regs (\<tau> \<sigma>) t c1)  ]\<^sub>t (\<tau> \<sigma>') \<and> pc \<sigma>' =  update t RecIdle(pc \<sigma>) \<and> writer \<sigma>' = writer \<sigma>
\<and>  readAux \<sigma> = readAux \<sigma>'\<and> writeAux \<sigma> = writeAux \<sigma>'  \<and> log \<sigma> = log \<sigma>'    \<and>  recoveredGlb \<sigma>' =  Suc(regs (\<tau> \<sigma>) t c1)


|  _ \<Rightarrow> \<sigma> = \<sigma>'
"


(*DTML Recover invocation*)
definition Recover_inv ::  "TId \<Rightarrow> PC \<Rightarrow> mp_state \<Rightarrow> bool " where
  "   Recover_inv  t  p \<sigma>  \<equiv>
case p  of
ReadyToRecover  \<Rightarrow>   (writer \<sigma>  = None) \<and>   ( \<forall> a \<noteq> glb.  [a]\<^sub>t (\<tau> \<sigma>) =  {lastVal a  (\<tau> \<sigma>)} )
\<and>( \<forall> a. a \<in> dom (log \<sigma>) \<longrightarrow> a \<noteq> glb) \<and> (\<forall>i. 0 < i \<and> i < length(memory (\<tau> \<sigma>)) \<longrightarrow>   Msg.loc((memory (\<tau> \<sigma>))!i)  \<noteq> glb )

|  Rec1 \<Rightarrow>  (writer \<sigma>  = None)  \<and>   ( \<forall> a \<noteq> glb.  [a]\<^sub>t (\<tau> \<sigma>) =  {lastVal a  (\<tau> \<sigma>)} )
\<and>( \<forall> a. a \<in> dom (log \<sigma>) \<longrightarrow> a \<noteq> glb) \<and>  (log \<sigma> \<noteq> Map.empty)\<and> (\<forall>i. 0 < i \<and> i < length(memory (\<tau> \<sigma>)) \<longrightarrow>   Msg.loc((memory (\<tau> \<sigma>))!i)  \<noteq> glb )

|  Rec2 \<Rightarrow>   (writer \<sigma>  = None)  \<and>   ( \<forall> a \<noteq> glb.  [a]\<^sub>t (\<tau> \<sigma>) =  {lastVal a  (\<tau> \<sigma>)} ) \<and>regs (\<tau> \<sigma>) t c2\<in> dom (log \<sigma>)
\<and>( \<forall> a. a \<in> dom (log \<sigma>) \<longrightarrow> a \<noteq> glb) \<and>  (log \<sigma> \<noteq> Map.empty)\<and> (\<forall>i. 0 < i \<and> i < length(memory (\<tau> \<sigma>)) \<longrightarrow>   Msg.loc((memory (\<tau> \<sigma>))!i)  \<noteq> glb )

|  Rec3\<Rightarrow>    (writer \<sigma>  = None)  \<and>   ( \<forall> a \<noteq> glb.  [a]\<^sub>t (\<tau> \<sigma>) =  {lastVal a  (\<tau> \<sigma>)} )
\<and>( \<forall> a. a \<in> dom (log \<sigma>) \<longrightarrow> a \<noteq> glb)  \<and>  (log \<sigma> \<noteq> Map.empty)\<and> (\<forall>i. 0 < i \<and> i < length(memory (\<tau> \<sigma>)) \<longrightarrow>   Msg.loc((memory (\<tau> \<sigma>))!i)  \<noteq> glb ) \<and>regs (\<tau> \<sigma>) t c2\<in> dom (log \<sigma>)

| Rec4 \<Rightarrow>    (writer \<sigma>  = None)  \<and>   ( \<forall> a \<noteq> glb.  [a]\<^sub>t (\<tau> \<sigma>) =  {lastVal a  (\<tau> \<sigma>)} )\<and>  [regs (\<tau> \<sigma>) t c2  ]\<^sup>A\<^sub>t (\<tau> \<sigma>) =  {lastVal (regs (\<tau> \<sigma>) t c2)  (\<tau> \<sigma>)}
\<and>( \<forall> a. a \<in> dom (log \<sigma>) \<longrightarrow> a \<noteq> glb) \<and>  (log \<sigma> \<noteq> Map.empty) \<and> (\<forall>i. 0 < i \<and> i < length(memory (\<tau> \<sigma>)) \<longrightarrow>   Msg.loc((memory (\<tau> \<sigma>))!i)  \<noteq> glb ) \<and>regs (\<tau> \<sigma>) t c2\<in> dom (log \<sigma>)

|  Rec5 \<Rightarrow>    (writer \<sigma>  = None)  \<and>   ( \<forall> a \<noteq> glb.  [a]\<^sub>t (\<tau> \<sigma>) =  {lastVal a  (\<tau> \<sigma>)} ) \<and>  [regs (\<tau> \<sigma>) t c2  ]\<^sub>P (\<tau> \<sigma>) =  {lastVal (regs (\<tau> \<sigma>) t c2)  (\<tau> \<sigma>)}
\<and>( \<forall> a. a \<in> dom (log \<sigma>) \<longrightarrow> a \<noteq> glb) \<and>  (log \<sigma> \<noteq> Map.empty)\<and> (\<forall>i. 0 < i \<and> i < length(memory (\<tau> \<sigma>)) \<longrightarrow>   Msg.loc((memory (\<tau> \<sigma>))!i)  \<noteq> glb ) \<and>regs (\<tau> \<sigma>) t c2\<in> dom (log \<sigma>)

|  Rec6 \<Rightarrow>   (writer \<sigma>  = None)  \<and>   ( \<forall> a \<noteq> glb.  [a]\<^sub>t (\<tau> \<sigma>) =  {lastVal a  (\<tau> \<sigma>)} )
\<and> (\<forall>i. 0 < i \<and> i < length(memory (\<tau> \<sigma>)) \<longrightarrow>   Msg.loc((memory (\<tau> \<sigma>))!i)  \<noteq> glb )  \<and> log \<sigma> = Map.empty

|  Rec7 \<Rightarrow>   (writer \<sigma>  = None)  \<and>   ( \<forall> a \<noteq> glb.  [a]\<^sub>t (\<tau> \<sigma>) =  {lastVal a  (\<tau> \<sigma>)} )
\<and> (\<forall>i. 0 < i \<and> i < length(memory (\<tau> \<sigma>)) \<longrightarrow>   Msg.loc((memory (\<tau> \<sigma>))!i)  \<noteq> glb ) \<and> log \<sigma> = Map.empty \<and> regs (\<tau> \<sigma>) t c1 =  survived_val (\<tau> \<sigma>) glb

|  Rec8 \<Rightarrow>    (writer \<sigma>  = None) \<and>   ( \<forall> a \<noteq> glb.  [a]\<^sub>t (\<tau> \<sigma>) =  {lastVal a  (\<tau> \<sigma>)} )
\<and> log \<sigma> = Map.empty  \<and> (\<forall>i. 0 < i \<and> i < length(memory (\<tau> \<sigma>)) \<longrightarrow>   Msg.loc((memory (\<tau> \<sigma>))!i)  \<noteq> glb )\<and>even(regs (\<tau> \<sigma>) t c1) \<and> regs (\<tau> \<sigma>) t c1 =  survived_val (\<tau> \<sigma>) glb

|  Rec9 \<Rightarrow>    (writer \<sigma>  = None)  \<and>   ( \<forall> a \<noteq> glb.  [a]\<^sub>t (\<tau> \<sigma>) =  {lastVal a  (\<tau> \<sigma>)} )
\<and> log \<sigma> = Map.empty  \<and> (\<forall>i. 0 < i \<and> i < length(memory (\<tau> \<sigma>)) \<longrightarrow>   Msg.loc((memory (\<tau> \<sigma>))!i)  \<noteq> glb )  \<and> odd(regs (\<tau> \<sigma>) t c1)  \<and> regs (\<tau> \<sigma>) t c1 =  survived_val (\<tau> \<sigma>) glb

|  RecIdle \<Rightarrow>   t = syst
| _ \<Rightarrow> True
"

(*total  DTML*)
definition" dTML \<sigma> \<sigma>' t  \<equiv>
( t \<noteq> syst \<and>
(  TML_Begin t \<sigma> \<sigma>' \<or>

( TML_Read  t   \<sigma> \<sigma>') \<or>

( TML_Write t   \<sigma> \<sigma>')  \<or>

( TML_Commit  t \<sigma> \<sigma>' )  \<or>

TML_Begin_invocation   t \<sigma> \<sigma>' \<or>

TML_Begin_response   t \<sigma> \<sigma>' \<or>

TML_Read_invocation   t \<sigma> \<sigma>' \<or>

TML_Read_response   t \<sigma> \<sigma>' \<or>

TML_Write_invocation   t \<sigma> \<sigma>' \<or>

TML_Write_response   t \<sigma> \<sigma>' \<or>


TML_Commit_invocation   t \<sigma> \<sigma>' \<or>

TML_Commit_response  t \<sigma> \<sigma>'

)

) \<or>
( t = syst \<and>  TML_Recover  syst \<sigma> \<sigma>') \<or>
TML_Crash   \<sigma> \<sigma>'
"


(*the persistent invanriant of DTML*)
definition "DTML_total_persistent_invariant \<sigma>  \<equiv>
total_wfs  (\<tau> \<sigma>)  
\<and> (glb_monotone_inv (\<tau> \<sigma>)) 
\<and> glb_monotone_complete_inv (\<tau> \<sigma>)
\<and>  (mem_tml_prop3   (\<tau> \<sigma>))
\<and>  (mem_tml_prop4   (\<tau> \<sigma>))
\<and> (\<forall>i t.  i \<in> OTS  (\<tau> \<sigma>) t glb \<longrightarrow> coh  (\<tau> \<sigma>) t glb \<le> i) 
\<and>  (\<forall> n. (0 \<le> n \<and> n  < length (memory (\<tau> \<sigma>))  \<and> comploc ((memory (\<tau> \<sigma>))!n) glb= glb) \<longrightarrow>  (valOf n glb  (\<tau> \<sigma>)) \<le> lastVal glb  (\<tau> \<sigma>) )
\<and>  (  compval (\<tau> \<sigma>) (memory (\<tau> \<sigma>) ! 0) glb = survived_val (\<tau> \<sigma>) glb  \<and> (pc \<sigma> syst = RecIdle  \<longrightarrow>survived_val (\<tau> \<sigma>) glb   \<le>   recoveredGlb \<sigma>  ))
\<and> ( (  \<forall> i   .  (  0 <  i \<and>  i < length(memory (\<tau> \<sigma>)) \<and>  comploc (memory (\<tau> \<sigma>)!i) glb = glb  \<longrightarrow> compval (\<tau> \<sigma>) (memory (\<tau> \<sigma>) ! i) glb  \<ge>   recoveredGlb \<sigma>   ) ))
\<and> (\<forall> a.  mem_tml_prop   glb  a (\<tau> \<sigma>)) 
\<and> (\<forall>  t. (  (   writer \<sigma>  = Some t    \<longrightarrow> \<lceil>glb\<rceil>\<^sub>t (\<tau> \<sigma>) )))
\<and> ( \<forall>t a. t = syst \<or>    writer \<sigma> = Some t \<or>  pc \<sigma> t = Committed  \<or> pc \<sigma> t = CommitResponding \<or> ( ( coh (\<tau> \<sigma>) t a) \<le> vrnew (\<tau> \<sigma>) t) )
\<and> ( \<forall>  t.  ( writer \<sigma> = Some t \<longrightarrow> odd (lastVal glb  (\<tau> \<sigma>)) ))
\<and> ( \<forall>  a.  (a \<in> dom( log \<sigma>)  \<longrightarrow> a \<noteq> glb ))
\<and> (  ( (writer \<sigma> = None \<and>  ((pc \<sigma>) syst) = RecIdle)   \<longrightarrow> ( \<forall> a t. a \<in>  dom (log \<sigma>) \<longrightarrow> [a]\<^sup>A\<^sub>t (\<tau> \<sigma>) =  {lastVal a  (\<tau> \<sigma>)}) )  )
\<and> (pm_inv \<sigma>)
\<and> ((  even (lastVal glb  (\<tau> \<sigma>)) \<and> writer \<sigma> \<noteq> None) \<longrightarrow> pc \<sigma>  (the ( writer \<sigma>) )   \<noteq> Commit4  )
\<and>  (((pc \<sigma>) syst) \<noteq> RecIdle   \<longrightarrow> (\<forall> t  \<noteq> syst.  ((pc \<sigma>) t)   \<in> {PC.NotStarted, PC.Aborted, PC.Committed})  ) 
\<and>  (  pc \<sigma>  syst  = RecIdle \<longrightarrow> (\<forall>t.  (t \<noteq> syst  \<and> ((pc \<sigma>) t \<notin> {PC.NotStarted,PC.Aborted, PC.Committed,PC.Begin2, PC.BeginPending   }) \<longrightarrow>   regs (\<tau> \<sigma>) t loc \<le> lastVal glb  (\<tau> \<sigma>) )))
\<and> ( \<forall>t. t \<noteq> syst \<and>
pc \<sigma> t \<notin> {PC.NotStarted, PC.Aborted, PC.Committed, BeginPending} \<and>
(writeAux \<sigma> t \<or> readAux \<sigma> t) \<longrightarrow>
recoveredGlb \<sigma> \<le> regs (\<tau> \<sigma>) t DTML.loc)
\<and> (\<forall>t. ((pc \<sigma>) t) \<in> {Commit2, Commit3,Commit4,Write3,Write4, Write5, Write6, Write7,Write8} \<longrightarrow> writer \<sigma>  =  Some t ) 
\<and> ( pc \<sigma>  syst  = RecIdle \<longrightarrow> even (recoveredGlb \<sigma> ) )
\<and> (pc \<sigma>  syst  = RecIdle  \<longrightarrow> ( lastVal glb (\<tau> \<sigma>)  \<ge>recoveredGlb \<sigma> )) 
\<and>  (  compval (\<tau> \<sigma>) (memory (\<tau> \<sigma>) ! 0) glb = survived_val (\<tau> \<sigma>) glb  \<and> (pc \<sigma> syst = RecIdle  \<longrightarrow>survived_val (\<tau> \<sigma>) glb   \<le>   recoveredGlb \<sigma> )) 
\<and> ( (  writer \<sigma> = None \<and> pc \<sigma> syst = RecIdle) \<longrightarrow> comploc (memory (\<tau> \<sigma>) ! (length (memory (\<tau> \<sigma>)) - 1)) glb = glb)
"

(*The initial state of DTML implies the persistent invariant*)
lemma start_implies_DTML_total_persistent_invariant :
assumes "TML_start  \<sigma>"
and "total_wfs  (\<tau> \<sigma>)  "
shows "DTML_total_persistent_invariant  \<sigma> "
  using assms 
  apply (simp add: TML_start_def DTML_total_persistent_invariant_def start_def )
  apply (unfold total_wfs_def)
  apply (unfold glb_monotone_inv_def glb_monotone_complete_inv_def   mem_tml_prop3_def  mem_tml_prop4_def  pm_inv_def  )
  apply (intro conjI)
         apply (metis length_Suc_conv list.size(3) not_less_eq)
        apply (metis TML_start_def assms(1) less_nat_zero_code less_one start_size)
       apply (metis TML_start_def assms(1) less_nat_zero_code less_one start_size)
      apply (metis TML_start_def assms(1) less_nat_zero_code less_one start_size)
     apply (metis TML_start_def assms(1) bot_nat_0.extremum_unique lastVal_def singleton_iff st_OTS st_lv valOf_def)
    apply (simp add:  mem_tml_prop_def)
   apply (metis TML_start_def assms(1) lastVal_def st_OPTS st_OTS st_OV_z st_lv)
  by (smt (verit, best) PC.distinct(11) PC.distinct(1273) PC.distinct(13) PC.distinct(1309) PC.distinct(1343) PC.distinct(1375) PC.distinct(1405) PC.distinct(1433) PC.distinct(15) PC.distinct(41) PC.distinct(43) PC.distinct(45) PC.distinct(47) PC.distinct(49) PC.distinct(493) PC.distinct(51) PC.distinct(559) PC.distinct(623))


(*all the program annotations of DTML*)
definition DTML_total_program_annotations ::  "TId \<Rightarrow> PC \<Rightarrow> mp_state \<Rightarrow> bool " where
" DTML_total_program_annotations   t  p cs  \<equiv>
( t \<noteq> syst \<longrightarrow> Begin_inv t  ((pc cs) t) cs)  \<and>
( t \<noteq> syst \<longrightarrow>  Commit_inv t  ((pc cs) t) cs )\<and>
(t= syst \<longrightarrow>  Recover_inv syst    ((pc cs) syst) cs) \<and>
(t \<noteq> syst \<longrightarrow>  ( Read_inv  t   ((pc cs) t)  cs ) )\<and>
( t \<noteq> syst \<longrightarrow> ( (Write_inv  t   ((pc cs) t)  cs))) \<and>
( t \<noteq> syst \<longrightarrow> ( Begin_invocation_inv  t   ((pc cs) t)  cs)) \<and>
( t \<noteq> syst \<longrightarrow> ( Read_invocation_inv  t   ((pc cs) t)  cs)) \<and>
( t \<noteq> syst \<longrightarrow> ( Write_invocation_inv  t   ((pc cs) t)  cs)) \<and>
( t \<noteq> syst \<longrightarrow> ( Commit_invocation_inv  t   ((pc cs) t)  cs)) \<and>
( t \<noteq> syst \<longrightarrow> ( Begin_Response_inv  t   ((pc cs) t)  cs)) \<and>
( t \<noteq> syst \<longrightarrow> ( Read_Response_inv  t   ((pc cs) t)  cs)) \<and>
( t \<noteq> syst \<longrightarrow> ( Write_Response_inv  t   ((pc cs) t)  cs)) \<and>
( t \<noteq> syst \<longrightarrow> ( Commit_Response_inv  t   ((pc cs) t)  cs))
"

(*****************************************************)



(*auxiliary lemmas*)
lemma pc_aux:
  assumes "pc \<sigma>' =  update t k (pc \<sigma>)  "
  shows  " \<forall> j \<noteq> t. ( pc \<sigma>')  j  = (pc \<sigma>)  j  "
  using assms
  by simp

lemma inloc_aux:
  assumes " (inLoc \<sigma>')  = (update t  a  (inLoc \<sigma>))  "
  shows  " \<forall> j \<noteq> t. ((inLoc \<sigma>') j   =  (inLoc \<sigma>) j) "
  using assms
  by simp

lemma inVal_aux:
  assumes " (inLoc \<sigma>')  = (update t  a  (inVal \<sigma>))  "
  shows  " \<forall> j \<noteq> t. ((inLoc \<sigma>') j   =  (inVal \<sigma>) j) "
  using assms
  by simp

lemma recover_not_pc:
  assumes "  ((pc cs) syst) \<notin> {RecIdle } \<union> recovering"
    and "  TML_Recover syst cs cs' "
  shows "cs = cs'"
  using assms
  apply (simp add:  TML_Recover_def)
  by(cases "pc cs syst";  simp)

lemma Begin_pcs:
  assumes "TML_Begin  t   \<sigma> \<sigma>'"
    and "((pc \<sigma>) t) \<in> {PC.BeginPending, PC.BeginResponding } \<union> beginning \<union> {PC.Aborted}"
  shows "((pc \<sigma>') t) \<in> {PC.BeginPending,  PC.BeginResponding  } \<union> {Begin2, Begin3} \<union> {PC.Aborted}"
  using assms
  apply (simp add: TML_Begin_def;simp)
  apply (cases "pc \<sigma> t";   simp  )
  apply (simp add: split if_splits )
  by (metis fun_upd_apply)

lemma Begin_not_pcs:
  assumes "TML_Begin  t   \<sigma> \<sigma>'"
    and "((pc \<sigma>) t) \<notin> {PC.BeginPending, PC.BeginResponding } \<union> beginning \<union> {PC.Aborted}"
  shows "\<sigma> = \<sigma>'"
  using assms
  apply (simp add: TML_Begin_def;simp)
  by  (cases "pc \<sigma> t";   simp  )

lemma Begin_Invocation_pcs:
  assumes "TML_Begin_invocation  t   \<sigma> \<sigma>'"
    and "((pc \<sigma>) t) \<in> {PC.BeginPending, PC.NotStarted } \<union> {PC.Aborted}"
  shows "((pc \<sigma>') t) \<in>  {PC.BeginPending, PC.NotStarted} \<union> {PC.Aborted}"
  using assms
  apply (simp add: TML_Begin_invocation_def;simp)
  by (cases "pc \<sigma> t";   simp  )

lemma Begin_Invocation_not_pcs:
  assumes "TML_Begin_invocation  t   \<sigma> \<sigma>'"
    and "((pc \<sigma>) t) \<notin> {PC.BeginPending,  PC.NotStarted } \<union> {PC.Aborted}"
  shows "\<sigma> = \<sigma>'"
  using assms
  apply (simp add: TML_Begin_invocation_def;simp)
  by  (cases "pc \<sigma> t";   simp  )

lemma Begin_Response_pcs:
  assumes "TML_Begin_response t   \<sigma> \<sigma>'"
    and "((pc \<sigma>) t) \<in> {PC.BeginResponding, PC.Ready } \<union> {PC.Aborted}"
  shows "((pc \<sigma>') t) \<in>  {PC.BeginResponding, PC.Ready} \<union> {PC.Aborted}"
  using assms
  apply (simp add: TML_Begin_response_def;simp)
  by (cases "pc \<sigma> t";   simp  )

lemma Begin_Response_not_pcs:
  assumes "TML_Begin_response t   \<sigma> \<sigma>'"
    and "((pc \<sigma>) t) \<notin> {PC.BeginResponding, PC.Ready } \<union> {PC.Aborted}"
  shows "((pc \<sigma>') t) \<notin>  {PC.BeginResponding, PC.Ready} \<union> {PC.Aborted}"
  using assms
  apply (simp add: TML_Begin_response_def;simp)
  by (cases "pc \<sigma> t";   simp  )

lemma Commit_pcs:
  assumes "TML_Commit  t   \<sigma> \<sigma>'"
    and "((pc \<sigma>) t) \<in> {PC.CommitPending, PC.CommitResponding} \<union> committing \<union> {PC.Aborted}"
  shows "((pc \<sigma>') t) \<in> {PC.CommitPending, PC.CommitResponding} \<union> committing \<union> {PC.Aborted}"
  using assms
  apply (simp add: TML_Commit_def)
  apply (cases "pc \<sigma> t";  simp add: split if_splits  )
  by (metis fun_upd_same)

lemma Commit_not_pcs:
  assumes "TML_Commit  t   \<sigma> \<sigma>'"
    and "((pc \<sigma>) t) \<notin> {PC.CommitPending, PC.CommitResponding} \<union> committing \<union> {PC.Aborted}"
  shows "\<sigma> = \<sigma>'"
  using assms
  apply (simp add: TML_Commit_def)
  by (cases "pc \<sigma> t";  simp add: split if_splits  )

lemma Commit_Invocation_pcs:
  assumes "TML_Commit_invocation  t   \<sigma> \<sigma>'"
    and "((pc \<sigma>) t) \<in>  {PC.CommitPending, PC.Ready } \<union> {PC.Aborted}"
  shows "((pc \<sigma>') t) \<in>  {PC.CommitPending, PC.Ready} \<union> {PC.Aborted}"
  using assms
  apply (simp add: TML_Commit_invocation_def ;simp)
  by (cases "pc \<sigma> t";   simp  )

lemma Commit_Invocation_not_pcs:
  assumes"TML_Commit_invocation  t   \<sigma> \<sigma>'"
    and "((pc \<sigma>) t)\<notin>  {PC.CommitPending, PC.Ready } \<union> {PC.Aborted}"
  shows "\<sigma> = \<sigma>'"
  using assms
  apply (simp add: TML_Commit_invocation_def;simp)
  by  (cases "pc \<sigma> t";   simp  )

lemma Commit_Response_pcs:
  assumes "TML_Commit_response t   \<sigma> \<sigma>'"
    and "((pc \<sigma>) t) \<in> {PC.CommitResponding, PC.Committed } \<union> {PC.Aborted}"
  shows "((pc \<sigma>') t) \<in>  {PC.CommitResponding, PC.Committed} \<union> {PC.Aborted}"
  using assms
  apply (simp add: TML_Commit_response_def;simp)
  by (cases "pc \<sigma> t";   simp  )

lemma Commit_Response_not_pcs:
  assumes "TML_Commit_response t   \<sigma> \<sigma>'"
    and "((pc \<sigma>) t) \<notin> {PC.CommitResponding, PC.Committed } \<union> {PC.Aborted}"
  shows "((pc \<sigma>') t) \<notin>  {PC.CommitResponding, PC.Committed} \<union> {PC.Aborted}"
  using assms
  apply (simp add: TML_Commit_response_def;simp)
  by (cases "pc \<sigma> t";   simp  )

lemma Read_pcs:
  assumes "TML_Read  t  \<sigma> \<sigma>'"
    and "((pc \<sigma>) t) \<in> {PC.ReadPending, PC.ReadResponding} \<union> reading \<union> {PC.Aborted}"
  shows "((pc \<sigma>') t) \<in> {PC.ReadPending, PC.ReadResponding} \<union> reading \<union> {PC.Aborted}"
  using assms
  apply (simp add: TML_Read_def)
  apply (cases "pc \<sigma> t";  simp add: split if_splits  )
    apply ( simp  add: split: if_split_asm)
   apply (metis fun_upd_apply)
  by( simp  add: split: if_split_asm)

lemma Read_not_pcs:
  assumes "TML_Read  t  \<sigma> \<sigma>'"
    and "((pc \<sigma>) t) \<notin> {PC.ReadPending, PC.ReadResponding} \<union> reading \<union> {PC.Aborted}"
  shows "\<sigma> = \<sigma>'"
  using assms
  apply (simp add: TML_Read_def)
  by (cases "pc \<sigma> t";  simp add: split if_splits  )

lemma Read_Invocation_pcs:
  assumes "TML_Read_invocation  t   \<sigma> \<sigma>'"
    and "((pc \<sigma>) t) \<in>  {PC.ReadPending, PC.Ready } \<union> {PC.Aborted}"
  shows "((pc \<sigma>') t) \<in>  {PC.ReadPending, PC.Ready} \<union> {PC.Aborted}"
  using assms
  apply (simp add: TML_Read_invocation_def ;simp)
  by (cases "pc \<sigma> t";   simp  )

lemma  Read_Invocation_not_pcs:
  assumes"TML_Read_invocation  t   \<sigma> \<sigma>'"
    and "((pc \<sigma>) t)\<notin>  {PC.ReadPending, PC.Ready } \<union> {PC.Aborted}"
  shows "\<sigma> = \<sigma>'"
  using assms
  apply (simp add: TML_Read_invocation_def;simp)
  by  (cases "pc \<sigma> t";   simp  )

lemma Read_Response_pcs:
  assumes "TML_Read_response t   \<sigma> \<sigma>'"
    and "((pc \<sigma>) t) \<in> {PC.ReadResponding, PC.Ready } \<union> {PC.Aborted}"
  shows "((pc \<sigma>') t) \<in>  {PC.ReadResponding, PC.Ready} \<union> {PC.Aborted}"
  using assms
  apply (simp add: TML_Read_response_def;simp)
  by (cases "pc \<sigma> t";   simp  )

lemma Read_Response_not_pcs:
  assumes "TML_Read_response t   \<sigma> \<sigma>'"
    and "((pc \<sigma>) t) \<notin> {PC.ReadResponding, PC.Ready } \<union> {PC.Aborted}"
  shows "((pc \<sigma>') t) \<notin>  {PC.ReadResponding, PC.Ready} \<union> {PC.Aborted}"
  using assms
  apply (simp add: TML_Read_response_def;simp)
  by (cases "pc \<sigma> t";   simp  )

lemma Recover_pcs:
  assumes "TML_Recover  syst \<sigma> \<sigma>'"
    and " ((pc \<sigma>) syst) \<in> {RecIdle}\<union> recovering"
  shows " ((pc \<sigma>') syst) \<in> {RecIdle}\<union> recovering"
  using assms
  apply (simp add: TML_Recover_def)
  apply (cases "pc \<sigma> syst";  simp add: split if_splits  )
   apply( simp  add: split: if_split_asm)
  by( simp  add: split: if_split_asm)

lemma Write_pcs:
  assumes "TML_Write  t   \<sigma> \<sigma>'"
    and "((pc \<sigma>) t) \<in> {PC.WritePending, PC.WriteResponding} \<union> writing \<union> {PC.Aborted}"
  shows "((pc \<sigma>') t) \<in> {PC.WritePending, PC.WriteResponding} \<union> writing  \<union> {PC.Aborted}"
  using assms
  apply (simp add: TML_Write_def)
  apply (cases "pc \<sigma> t";  simp add: split if_splits  )
    apply( simp  add: split: if_split_asm)
   apply (metis fun_upd_same gr0I)
  by (metis fun_upd_apply)

lemma Write_not_pcs:
  assumes "TML_Write  t   \<sigma> \<sigma>'"
    and "((pc \<sigma>) t) \<notin> {PC.WritePending, PC.WriteResponding} \<union> writing \<union> {PC.Aborted}"
  shows "\<sigma> = \<sigma>'"
  using assms
  apply (simp add: TML_Write_def)
  by (cases "pc \<sigma> t";  simp add: split if_splits  )

lemma Write_Invocation_pcs:
  assumes "TML_Write_invocation  t   \<sigma> \<sigma>'"
    and "((pc \<sigma>) t) \<in>  {PC.WritePending, PC.Ready } \<union> {PC.Aborted}"
  shows "((pc \<sigma>') t) \<in>  {PC.WritePending, PC.Ready} \<union> {PC.Aborted}"
  using assms
  apply (simp add: TML_Write_invocation_def ;simp)
  by (cases "pc \<sigma> t";   simp  )

lemma  Write_Invocation_not_pcs:
  assumes"TML_Write_invocation  t   \<sigma> \<sigma>'"
    and "((pc \<sigma>) t)\<notin>  {PC.WritePending, PC.Ready } \<union> {PC.Aborted}"
  shows "\<sigma> = \<sigma>'"
  using assms
  apply (simp add: TML_Write_invocation_def;simp)
  by  (cases "pc \<sigma> t";   simp  )

lemma Write_Response_pcs:
  assumes "TML_Write_response t   \<sigma> \<sigma>'"
    and "((pc \<sigma>) t) \<in> {PC.WriteResponding, PC.Ready } \<union> {PC.Aborted}"
  shows "((pc \<sigma>') t) \<in>  {PC.WriteResponding, PC.Ready} \<union> {PC.Aborted}"
  using assms
  apply (simp add: TML_Write_response_def;simp)
  by (cases "pc \<sigma> t";   simp  )

lemma Write_Response_not_pcs:
  assumes "TML_Write_response t   \<sigma> \<sigma>'"
    and "((pc \<sigma>) t) \<notin> {PC.WriteResponding, PC.Ready } \<union> {PC.Aborted}"
  shows "((pc \<sigma>') t) \<notin>  {PC.WriteResponding, PC.Ready} \<union> {PC.Aborted}"
  using assms
  apply (simp add: TML_Write_response_def;simp)
  by (cases "pc \<sigma> t";   simp  )



end






