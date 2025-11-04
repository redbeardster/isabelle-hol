(*The DTMS2 specification*)
theory DTMS2
imports "pierogi/Proof_Rules"
begin

(*DTMS2 pc values*)
datatype TPC =    NotStarted |  Ready |  Aborted | Committed  |BeginPending | BeginResponding | ReadPending |
ReadResponding | WritePending | WriteResponding | CommitPending | CommitResponding 

consts v0 :: "Val"


(*DTMS2 actions*)
datatype TMinstruction =
TMReadInv|
TMRead (lloc:Loc) |
TMReadResp|
TMWriteInv|
TMWrite (sloc: Loc)(sval:Val)|
TMWriteResp|
TMBeginInv|
TMBegin |
TMBeginResp|
TMCommitInv|
TMCommit|
TMCommitResp|
TMCrash |
TMAbort

(*DTMS2 state*)
record tms_state =
tmemory ::  "(Loc \<Rightarrow> Val) list"
beginIndex :: "TId \<Rightarrow> nat"
rdSet :: "TId  \<Rightarrow> Loc \<Rightarrow> Val  option "
wrSet ::  "TId  \<Rightarrow> Loc \<Rightarrow> Val  option "
tpc :: "TId \<Rightarrow> TPC "
valRead ::"TId \<Rightarrow> Val"


(*initial state of DTMS2*)
definition start :: " tms_state \<Rightarrow> bool"
where
"start s \<equiv>
(\<forall> t. tpc s t = NotStarted)
\<and> (\<forall> t. rdSet s t = Map.empty)
\<and> (\<forall> t. wrSet s t = Map.empty)
\<and> tmemory s = [\<lambda> l. v0]"


(*DTMS2 state*)
definition "maxIndex s \<equiv> length( tmemory s)"


(*update functions*)
definition update_partial :: "'a \<Rightarrow> Loc \<Rightarrow> Val \<Rightarrow> ('a \<Rightarrow> Loc \<Rightarrow> Val option) \<Rightarrow> 'a \<Rightarrow> Loc \<Rightarrow> V option"
where
"update_partial t l v p \<equiv> p(t := ((p t) (l := (Some v))))"

definition apply_partial :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b option) \<Rightarrow> 'a \<Rightarrow> 'b"
where
"apply_partial f pf a \<equiv> case pf a of Some b \<Rightarrow> b | None \<Rightarrow> f a"  

abbreviation write_back :: "(Loc \<Rightarrow> Val option) \<Rightarrow> (Loc \<Rightarrow> Val) list \<Rightarrow> (Loc \<Rightarrow> Val) list"  
where
"write_back ws ss \<equiv> append ss [apply_partial ( ( (ss) ! ((length  ss) - 1) )) ws]"


definition update_begin_index :: "TId \<Rightarrow> nat \<Rightarrow>  tms_state \<Rightarrow>  tms_state"
where
"update_begin_index t n s \<equiv> s\<lparr>  beginIndex := (( beginIndex s) (t := n)) \<rparr>"




definition "updateSet (ws :: Loc \<Rightarrow> Val option) l (v::Val) \<equiv> ws(l := (Some v))"

lemmas [simp] = updateSet_def

definition read_consistent :: "(Loc \<Rightarrow> Val) \<Rightarrow> (Loc \<Rightarrow> Val option) \<Rightarrow> bool"              
where
"read_consistent st rs \<equiv>
\<forall> l. case (rs l) of Some v \<Rightarrow> v = st l | None \<Rightarrow> True"

(*validity constraint of DTMS2*)
definition validIndex :: " tms_state \<Rightarrow> TId \<Rightarrow> nat \<Rightarrow> bool"    
where
"validIndex s t n \<equiv>
beginIndex s t \<le> n \<and> n < maxIndex s \<and>
read_consistent (( tmemory s)! n) (rdSet s t)"


(*DTMS2 initial state*)
definition TMS_start :: " tms_state \<Rightarrow> bool"
where
" TMS_start  s \<equiv>
(\<forall> t. tpc s t = NotStarted)\<and>
(\<forall> t. rdSet s t = Map.empty)
\<and> (\<forall> t. wrSet s t = Map.empty)
\<and> tmemory s = [\<lambda> l. 0]"


(*DTMS2 abort transition*)
definition TMAbort_trans :: "TId \<Rightarrow>  tms_state \<Rightarrow> tms_state"
where
"TMAbort_trans  t  \<sigma> \<equiv>

if tpc \<sigma>   t \<notin> { NotStarted, Aborted, Ready, CommitResponding, Committed }
then
\<sigma>\<lparr>  tpc := (tpc \<sigma>)(t := Aborted) \<rparr>
else 
\<sigma>"   


(*DTMS2 inv(begin) transition*)
definition TMBegin_inv_trans :: "TId \<Rightarrow>  tms_state \<Rightarrow> tms_state"
where
"TMBegin_inv_trans  t  \<sigma> \<equiv>    
if tpc \<sigma>   t = NotStarted \<and> t \<noteq> syst
then
\<sigma>\<lparr>  tpc := (tpc \<sigma>)(t := BeginPending) \<rparr>
else 
\<sigma>" 

(*DTMS2 res(begin) transition*)
definition TMBegin_resp_trans :: "TId \<Rightarrow>  tms_state \<Rightarrow> tms_state"
where
"TMBegin_resp_trans  t  \<sigma> \<equiv>    
if tpc \<sigma>   t =  BeginResponding \<and> t \<noteq> syst
then
\<sigma>\<lparr>  tpc := (tpc \<sigma>)(t := Ready) \<rparr>
else 
\<sigma>" 

(*DTMS2 inv(read) transition*)
definition TMRead_inv_trans :: "TId \<Rightarrow>  tms_state \<Rightarrow> tms_state"
where
"TMRead_inv_trans  t  \<sigma> \<equiv>    
if tpc \<sigma>   t = Ready\<and> t \<noteq> syst
then
\<sigma>\<lparr>  tpc := (tpc \<sigma>)(t := ReadPending) \<rparr>
else 
\<sigma>" 

(*DTMS2 res(read) transition*)
definition TMRead_resp_trans :: "TId \<Rightarrow>  tms_state \<Rightarrow> tms_state"
where
"TMRead_resp_trans  t  \<sigma> \<equiv>    
if tpc \<sigma>   t = ReadResponding \<and> t \<noteq> syst
then
\<sigma>\<lparr>  tpc := (tpc \<sigma>)(t := Ready) \<rparr>
else 
\<sigma>" 

(*DTMS2 inv(write) transition*)
definition TMWrite_inv_trans :: "TId \<Rightarrow>  tms_state \<Rightarrow> tms_state"
where
"TMWrite_inv_trans  t  \<sigma> \<equiv>    
if tpc \<sigma>   t = Ready\<and> t \<noteq> syst
then
\<sigma>\<lparr>  tpc := (tpc \<sigma>)(t := WritePending) \<rparr>
else 
\<sigma>" 

(*DTMS2 inv(write) transition*)
definition TMWrite_resp_trans :: "TId \<Rightarrow>  tms_state \<Rightarrow> tms_state"
where
"TMWrite_resp_trans  t  \<sigma> \<equiv>    
if tpc \<sigma>   t = WriteResponding \<and> t \<noteq> syst
then
\<sigma>\<lparr>  tpc := (tpc \<sigma>)(t := Ready) \<rparr>
else 
\<sigma>" 


(*DTMS2 inv(commit) transition*)
definition TMCommit_inv_trans :: "TId \<Rightarrow>  tms_state \<Rightarrow> tms_state"
where
"TMCommit_inv_trans  t  \<sigma> \<equiv>    
if tpc \<sigma>   t = Ready\<and> t \<noteq> syst
then
\<sigma>\<lparr>  tpc := (tpc \<sigma>)(t := CommitPending) \<rparr>
else 
\<sigma>" 

(*DTMS2 res(commit) transition*)
definition TMCommit_resp_trans :: "TId \<Rightarrow>  tms_state \<Rightarrow> tms_state"
where
"TMCommit_resp_trans  t  \<sigma> \<equiv>    
if tpc \<sigma>   t = CommitResponding \<and> t \<noteq> syst
then
\<sigma>\<lparr>  tpc := (tpc \<sigma>)(t := Committed) \<rparr>
else 
\<sigma>" 


(*DTMS2 begin transition*)
definition TMBegin_trans :: "TId \<Rightarrow>  tms_state \<Rightarrow> tms_state"
where
"TMBegin_trans  t  \<sigma> \<equiv>    
if tpc \<sigma>   t = BeginPending \<and> t \<noteq> syst
then
\<sigma>\<lparr>beginIndex := (beginIndex \<sigma> )(t:= (maxIndex \<sigma> -1) ),
     tpc := (tpc \<sigma>)(t := BeginResponding)
\<rparr>
else 
\<sigma>" 


(*DTMS2 write transition*)
definition TMWrite_trans :: "TId \<Rightarrow> Loc \<Rightarrow> Val \<Rightarrow> tms_state \<Rightarrow> tms_state"
where
"TMWrite_trans  t a v  \<sigma> \<equiv>    
if tpc \<sigma>   t = WritePending \<and> t \<noteq> syst
then
\<sigma> \<lparr>  wrSet := (wrSet \<sigma>  )(t := updateSet (wrSet \<sigma>  t) a v),
tpc := (tpc \<sigma> )(t := WriteResponding)\<rparr>
else \<sigma>"


(*DTMS2 commit transition*)
definition "TMCommit_trans  t \<sigma>   \<equiv>                                                      
if tpc \<sigma>  t = CommitPending  \<and> wrSet \<sigma> t = Map.empty \<and> (\<exists> n . validIndex \<sigma> t n  )\<and> t \<noteq> syst
then
\<sigma>\<lparr> tpc := (tpc \<sigma>)(t := CommitResponding) \<rparr>
else
if tpc \<sigma> t =  CommitPending  \<and> read_consistent  (( tmemory \<sigma>)! ((maxIndex \<sigma>) -1) ) (rdSet \<sigma> t) \<and> t \<noteq> syst
then
\<sigma>\<lparr> tpc := (tpc \<sigma>)(t := CommitResponding),
tmemory := write_back (wrSet \<sigma> t) ( tmemory \<sigma>) 
\<rparr>
else 
\<sigma>  "


(*DTMS2 read transition*)
definition "TMRead_trans t a n  \<sigma> \<equiv> 
if tpc \<sigma>   t = ReadPending\<and> t \<noteq> syst \<and> (a \<in> dom (wrSet \<sigma>  t)  \<or> validIndex  \<sigma> t n) 
then
(  let    newSet = if ((a \<notin> dom (wrSet  \<sigma> t))   ) 
then ( ( updateSet (rdSet \<sigma>  t) a (((tmemory \<sigma>)!n)a ) )   )
else (rdSet \<sigma>  t) ;
r = if ((a \<notin> dom (wrSet  \<sigma> t))   ) 
then ( ((tmemory \<sigma>)!n)a )
else (the ( ((wrSet \<sigma>  t)) a)  )

in
\<sigma> \<lparr>  
valRead  :=   (valRead \<sigma>)(t :=  r),
tpc := (tpc \<sigma> )(t := ReadResponding),
rdSet := (rdSet \<sigma>  )(t :=   newSet  )\<rparr>) 

else 
\<sigma>   "

(*DTMS2 crash transition*)
definition TMCrash_trans :: "   tms_state \<Rightarrow> tms_state "
where
" TMCrash_trans   \<sigma> \<equiv> 

\<sigma>\<lparr> tpc := \<lambda> t. if t \<noteq> syst \<and> (tpc \<sigma> t) \<notin> {NotStarted, Aborted, Committed}
    then Aborted else (tpc \<sigma> t),
tmemory := [( tmemory \<sigma>)! ((maxIndex \<sigma>) -1)]  \<rparr>  

"


(*lemma about memory after commit*)
lemma tmem_l_commitWr :
assumes " \<sigma>'  =    \<sigma>\<lparr> tpc := (tpc \<sigma>)(t := CommitResponding),
tmemory := write_back (wrSet \<sigma> t) ( tmemory \<sigma>) 
\<rparr> "
shows " \<forall> i. 0 \<le> i \<and> i < (length (tmemory \<sigma>) )  \<longrightarrow> (tmemory \<sigma> !i = tmemory (\<sigma>') !i) "
using assms
apply (subgoal_tac "  length (tmemory \<sigma>')  =   length (tmemory \<sigma>) + 1 ")
prefer 2
apply (simp add:  apply_partial_def )
apply (simp add:  apply_partial_def )
  by (metis butlast_snoc nth_butlast)

(*lemma about memory after commit*)
lemma tmem_commit_length :
assumes " \<sigma>'  =    \<sigma>\<lparr> tpc := (tpc \<sigma>)(t := CommitResponding),
tmemory := write_back (wrSet \<sigma> t) ( tmemory \<sigma>) 
\<rparr> "
shows  "  length (tmemory \<sigma>')  =   length (tmemory \<sigma>) + 1 " 
using assms
by simp


lemma read_set_Read_from_mem [simp]:
"\<lbrakk>l \<notin> dom (wrSet \<sigma> t); validIndex \<sigma> t n;tpc \<sigma> t = ReadPending; t \<noteq> syst  \<rbrakk>
\<Longrightarrow>
rdSet ( (TMRead_trans  t l n  \<sigma>)) t =
(rdSet \<sigma> t)(l \<mapsto> ((tmemory \<sigma>!n) l))"
by (simp add: TMRead_trans_def apply_partial_def)


(*Step definition*) 
definition tmstep :: "TId \<Rightarrow>TMinstruction \<Rightarrow>  tms_state\<Rightarrow>  tms_state\<Rightarrow> bool "
where
"tmstep t a \<sigma> \<sigma>'  \<equiv>
(case a of
TMBegin    \<Rightarrow> 
\<sigma>'  = TMBegin_trans  t  \<sigma>     |
TMCrash  \<Rightarrow>
\<sigma>'  = TMCrash_trans    \<sigma>        |   
TMWrite  x v  \<Rightarrow> 
\<sigma>'  = TMWrite_trans  t x v  \<sigma> | 
TMCommit  \<Rightarrow> 
\<sigma>'  =  TMCommit_trans  t  \<sigma>   | 
TMRead x \<Rightarrow> 
\<exists>n.  \<sigma>'  =  TMRead_trans  t x n  \<sigma> |
TMAbort \<Rightarrow>
\<sigma>' =  TMAbort_trans t \<sigma> |
TMBeginInv  \<Rightarrow> 
\<sigma>'  =  TMBegin_inv_trans  t  \<sigma>   | 
TMBeginResp  \<Rightarrow> 
\<sigma>'  =  TMBegin_resp_trans  t  \<sigma>   |

TMReadInv  \<Rightarrow> 
\<sigma>'  =  TMRead_inv_trans  t  \<sigma>   | 
TMReadResp  \<Rightarrow> 
\<sigma>'  =  TMRead_resp_trans  t  \<sigma>  |

TMWriteInv  \<Rightarrow> 
\<sigma>'  =  TMWrite_inv_trans  t  \<sigma>   | 
TMWriteResp  \<Rightarrow> 
\<sigma>'  =  TMWrite_resp_trans  t  \<sigma>  |
TMCommitInv  \<Rightarrow> 
\<sigma>'  =  TMCommit_inv_trans  t  \<sigma>   | 
TMCommitResp  \<Rightarrow> 
\<sigma>'  =  TMCommit_resp_trans  t  \<sigma>  


)" 

lemma tmstep_cases:
"tmstep t a \<sigma> \<sigma>'
\<Longrightarrow> 
\<lbrakk>\<And>  n x . \<sigma>' =  TMRead_trans  t x n  \<sigma>   \<and> a = TMRead  x   \<Longrightarrow> P \<sigma> ( TMRead_trans  t x n  \<sigma> )\<rbrakk>
\<Longrightarrow>
\<lbrakk> \<sigma>' = TMCommit_trans t \<sigma> \<and> a = TMCommit

\<Longrightarrow> P \<sigma> ( TMCommit_trans t \<sigma>)\<rbrakk>
\<Longrightarrow>

\<lbrakk>\<And>  x v  . \<sigma>' = TMWrite_trans  t x v  \<sigma>  \<and> a = TMWrite  x v
\<Longrightarrow> P \<sigma> (TMWrite_trans  t x v  \<sigma> )\<rbrakk>
\<Longrightarrow>

\<lbrakk>\<sigma>' =  TMBegin_trans t \<sigma> \<and> a =  TMBegin

\<Longrightarrow> P \<sigma> ( TMBegin_trans t \<sigma>)\<rbrakk>

\<Longrightarrow>  \<lbrakk>\<sigma>' = TMCrash_trans  \<sigma> \<and> a = TMCrash

\<Longrightarrow> P \<sigma> ( TMCrash_trans  \<sigma>)\<rbrakk>

\<Longrightarrow>
\<lbrakk>\<sigma>' = TMAbort_trans t \<sigma> \<and> a = TMAbort

\<Longrightarrow> P \<sigma> ( TMAbort_trans t \<sigma>)\<rbrakk>

\<Longrightarrow>
\<lbrakk> \<sigma>' = TMRead_inv_trans t \<sigma> \<Longrightarrow>
a = TMReadInv \<Longrightarrow> P \<sigma> (TMRead_inv_trans t \<sigma>)\<rbrakk>
\<Longrightarrow> 

\<lbrakk>  \<sigma>' = TMRead_resp_trans t \<sigma> \<Longrightarrow>
a = TMReadResp \<Longrightarrow> P \<sigma> (TMRead_resp_trans t \<sigma>) \<rbrakk>
\<Longrightarrow>
\<lbrakk>  \<sigma>' = TMWrite_inv_trans t \<sigma> \<Longrightarrow>
a = TMWriteInv \<Longrightarrow> P \<sigma> (TMWrite_inv_trans t \<sigma>)  \<rbrakk>

\<Longrightarrow>  \<lbrakk>  \<sigma>' = TMWrite_resp_trans t \<sigma> \<Longrightarrow>
a = TMWriteResp \<Longrightarrow>
P \<sigma> (TMWrite_resp_trans t \<sigma>) \<rbrakk>

\<Longrightarrow>  \<lbrakk>  \<sigma>' = TMBegin_inv_trans t \<sigma> \<Longrightarrow>
a = TMBeginInv \<Longrightarrow>
P \<sigma> (TMBegin_inv_trans t \<sigma>) \<rbrakk>

\<Longrightarrow>  \<lbrakk>  \<sigma>' = TMBegin_resp_trans t \<sigma> \<Longrightarrow>
a = TMBeginResp \<Longrightarrow>
P \<sigma> (TMBegin_resp_trans t \<sigma>) \<rbrakk>

\<Longrightarrow>  \<lbrakk>  \<sigma>' = TMCommit_resp_trans t \<sigma> \<Longrightarrow>
a = TMCommitResp \<Longrightarrow>
P \<sigma> (TMCommit_resp_trans t \<sigma>) \<rbrakk>

\<Longrightarrow>  \<lbrakk>  \<sigma>' = TMCommit_inv_trans t \<sigma> \<Longrightarrow>
a = TMCommitInv \<Longrightarrow>
P \<sigma> (TMCommit_inv_trans t \<sigma>) \<rbrakk>



\<Longrightarrow> P \<sigma> \<sigma>'"
apply (simp add: tmstep_def)
apply(case_tac a)
by  (auto +)


(*DTMS invariant*)
definition tms_inv :: " tms_state  \<Rightarrow> TId \<Rightarrow> bool"
where
"tms_inv \<sigma>  t \<equiv>
( case (tpc \<sigma>) t of 

TPC.Ready  \<Rightarrow> t \<noteq>syst \<and>   beginIndex \<sigma> t < maxIndex \<sigma> 

| TPC.BeginPending  \<Rightarrow> t \<noteq>syst \<and>  rdSet \<sigma> t = Map.empty \<and> wrSet \<sigma> t = Map.empty 

| TPC.BeginResponding  \<Rightarrow> t \<noteq>syst \<and>   beginIndex \<sigma> t < maxIndex \<sigma> 

| TPC.ReadPending  \<Rightarrow> t \<noteq>syst \<and>   beginIndex \<sigma> t < maxIndex \<sigma> 

| TPC.ReadResponding  \<Rightarrow> t \<noteq>syst \<and>   beginIndex \<sigma> t < maxIndex \<sigma> 

| TPC.WritePending  \<Rightarrow> t \<noteq>syst \<and>   beginIndex \<sigma> t < maxIndex \<sigma> 

| TPC.WriteResponding  \<Rightarrow> t \<noteq>syst \<and>   beginIndex \<sigma> t < maxIndex \<sigma> 

| TPC.CommitPending  \<Rightarrow> t \<noteq>syst \<and>   beginIndex \<sigma> t < maxIndex \<sigma> 

| TPC.CommitResponding  \<Rightarrow> t \<noteq>syst \<and>   beginIndex \<sigma> t < maxIndex \<sigma> 

| TPC.NotStarted   \<Rightarrow>  rdSet \<sigma> t = Map.empty \<and> wrSet \<sigma> t = Map.empty 

|_ \<Rightarrow> True

)"


(*The DTMS invariant holds in the intial state of DTMS*)
lemma tms_inv_start:
assumes"   start  \<sigma> "
shows  "\<forall>t.  tms_inv \<sigma>  t "
using assms
by (simp add: tms_inv_def start_def) 



(*Local correctness of DTMS  for t \neq syst*)
lemma tms_inv_self_t:
assumes " tms_inv \<sigma>  t "
and "tmstep t a \<sigma> \<sigma>'"
and " t \<noteq> syst"
and "tmemory \<sigma> \<noteq> [] "
shows  "tms_inv \<sigma>'  t"
apply(rule tmstep_cases)
using assms
apply (simp add: tmstep_def   )
apply clarify
apply (simp add: tms_inv_def TMRead_trans_def  maxIndex_def)
apply (metis (no_types, lifting) TPC.simps(139) assms(1) maxIndex_def tms_inv_def)
apply (simp add: tms_inv_def TMCommit_trans_def  maxIndex_def)
apply (smt (z3) TPC.simps(134) TPC.simps(143) assms(1) less_Suc_eq maxIndex_def tms_inv_def)
apply (simp add: tms_inv_def TMWrite_trans_def  maxIndex_def)
apply (smt (z3) TPC.simps(141) assms(1) maxIndex_def tms_inv_def)
apply (simp add: tms_inv_def TMBegin_trans_def  maxIndex_def)
using assms(1) assms(4) tms_inv_def apply force
apply (simp add: tms_inv_def TMCrash_trans_def  maxIndex_def)
using assms(1) assms(3) tms_inv_def apply fastforce
apply (simp add: tms_inv_def TMAbort_trans_def  maxIndex_def)
apply (simp add: split if_splits)
apply (intro conjI impI)
using assms(1) tms_inv_def apply auto[1]
using assms(1) tms_inv_def apply auto[1]
using assms(3) apply auto[1]
using assms(1) tms_inv_def  
apply (simp add: maxIndex_def)
using assms(1) tms_inv_def 
using assms(3) apply blast
using assms(1) tms_inv_def
apply (simp add: maxIndex_def)
apply (simp add: tms_inv_def TMRead_inv_trans_def  maxIndex_def)
apply (smt (z3) TPC.simps(134) assms(1) maxIndex_def tms_inv_def)
apply (simp add: TMRead_resp_trans_def )
apply (smt (z3) TPC.simps(134) TPC.simps(140) assms(1) fun_upd_same maxIndex_def tms_inv_def tms_state.select_convs(1) tms_state.select_convs(2) tms_state.select_convs(5) tms_state.surjective tms_state.update_convs(5))
apply (simp add: TMWrite_inv_trans_def )
apply (smt (z3) TPC.simps(134) TPC.simps(141) assms(1) fun_upd_same maxIndex_def tms_inv_def tms_state.select_convs(1) tms_state.select_convs(2) tms_state.select_convs(5) tms_state.surjective tms_state.update_convs(5))
apply (simp add: TMWrite_resp_trans_def)
apply (smt (z3) TPC.simps(134) TPC.simps(142) assms(1) fun_upd_same maxIndex_def tms_inv_def tms_state.select_convs(1) tms_state.select_convs(2) tms_state.select_convs(5) tms_state.surjective tms_state.update_convs(5))
apply (simp add: tms_inv_def TMBegin_inv_trans_def maxIndex_def  )
using assms(1) tms_inv_def apply auto[1]
apply (simp add: TMBegin_resp_trans_def)
apply (smt (z3) TPC.simps(134) TPC.simps(138) assms(1) fun_upd_same maxIndex_def tms_inv_def tms_state.select_convs(1) tms_state.select_convs(2) tms_state.select_convs(5) tms_state.surjective tms_state.update_convs(5))
apply (subgoal_tac "  tms_inv \<sigma> t")
prefer 2
apply (simp add: assms(1))
apply (simp add: tms_inv_def TMBegin_inv_trans_def maxIndex_def  )
apply (simp add:  TMCommit_resp_trans_def)
using TMCommit_resp_trans_def apply presburger
apply (simp add: TMCommit_inv_trans_def)
by (smt (z3) TPC.simps(134) TPC.simps(143) assms(1) fun_upd_same maxIndex_def tms_inv_def tms_state.select_convs(1) tms_state.select_convs(2) tms_state.select_convs(5) tms_state.surjective tms_state.update_convs(5))



(*Local correctness of DTMS  for t =  syst*)
lemma tms_inv_self_syst:
assumes " tms_inv \<sigma>  t "
and "tmstep t a \<sigma> \<sigma>'"
and " t = syst"
shows  "tms_inv \<sigma>'  t"
apply(rule tmstep_cases)
using assms
apply (simp add: tmstep_def   )
apply clarify
apply (simp add: tms_inv_def TMRead_trans_def  maxIndex_def)
apply (metis (no_types, lifting) assms(1) maxIndex_def tms_inv_def)
apply (simp add: tms_inv_def TMCommit_trans_def  maxIndex_def)
using assms(1) tms_inv_def apply blast
apply (simp add: tms_inv_def TMWrite_trans_def  maxIndex_def)
apply (metis (no_types, lifting)  assms(1) maxIndex_def tms_inv_def)
apply (simp add: tms_inv_def TMBegin_trans_def  maxIndex_def)
using assms(1) tms_inv_def apply auto[1]
apply (simp add: tms_inv_def TMCrash_trans_def  )
apply (case_tac " t = syst")
apply simp
apply ( cases " tpc \<sigma> syst" ;simp)
using assms(1) tms_inv_def apply force
using assms(1) tms_inv_def apply auto[1]
using assms(1) tms_inv_def apply auto[1] 
using assms(1) tms_inv_def apply auto[1]
using assms(1) tms_inv_def apply auto[1]
using assms(1) tms_inv_def apply auto[1]
using assms(1) tms_inv_def apply auto[1]
using assms(1) tms_inv_def apply auto[1]
using assms(1) tms_inv_def apply auto[1]
using assms(1) tms_inv_def apply auto[1]
using assms(1) tms_inv_def apply auto[1]
apply (simp add: tms_inv_def TMAbort_trans_def  maxIndex_def )
using assms(1) assms(3) tms_inv_def apply fastforce
apply (simp add: TMRead_inv_trans_def)
apply (simp add: assms(1))
apply (simp add: TMRead_resp_trans_def)
apply (simp add: assms(1))
apply (simp add: TMWrite_inv_trans_def)
apply (simp add: assms(1))
apply (simp add: TMWrite_resp_trans_def)
apply (simp add: assms(1))
apply (simp add: TMBegin_inv_trans_def)
apply (simp add: assms(1))
apply (simp add: TMBegin_resp_trans_def)
apply (simp add: assms(1))
apply (simp add: TMCommit_resp_trans_def)
apply (simp add: assms(1))
apply (simp add: TMCommit_inv_trans_def)
by (simp add: assms(1))

(*Local correctness of DTMS*)
lemma tms_inv_self:
assumes " tms_inv \<sigma>  t "
and "tmstep t a \<sigma> \<sigma>'"
and "tmemory \<sigma> \<noteq> [] "
shows  "tms_inv \<sigma>'  t"
using assms
using tms_inv_self_syst tms_inv_self_t by blast

(*Stability check of the DTMS invariant for t = syst*)
lemma tms_inv_self_stable_syst:
assumes " tms_inv \<sigma>  z "
and "tmstep l  a \<sigma> \<sigma>'"
and " l = syst"
and " l \<noteq> z"
shows  "tms_inv \<sigma>'  z"
  apply(rule tmstep_cases)
  using assms
                apply (simp add: tmstep_def   )
               apply clarify
               prefer 5
               apply (simp add: tms_inv_def TMCrash_trans_def  maxIndex_def)
  using assms(1) assms(3) assms(4) tms_inv_def apply fastforce
              apply (simp add: tms_inv_def TMRead_trans_def  maxIndex_def)
  using assms(1) tms_inv_def apply blast
             apply (simp add: tms_inv_def TMCommit_trans_def  maxIndex_def)
  using assms(1) tms_inv_def apply auto[1]
            apply (simp add: tms_inv_def TMWrite_trans_def  maxIndex_def)
  using assms(1) tms_inv_def apply auto[1]
           apply (simp add: tms_inv_def TMBegin_trans_def  maxIndex_def)
  using assms(1) tms_inv_def apply blast
          apply (simp add: TMAbort_trans_def tms_inv_def   maxIndex_def)
          apply (unfold maxIndex_def )
          apply (cases " tpc \<sigma> z"; simp )
  using assms(1) tms_inv_def apply force
                    apply (smt (z3) TPC.simps(134) assms(1) maxIndex_def tms_inv_def tms_state.ext_inject tms_state.surjective tms_state.update_convs(5))
  using assms(1) tms_inv_def apply force
  using assms(3) assms(4) apply blast
  using assms(1) tms_inv_def apply force
                apply (smt (z3) TPC.simps(138) assms(1) maxIndex_def tms_inv_def)
               apply (smt (z3) TPC.simps(139) assms(1) maxIndex_def tms_inv_def tms_state.select_convs(1) tms_state.surjective tms_state.update_convs(5))
              apply (smt (z3) TPC.simps(140) assms(1) maxIndex_def tms_inv_def)
             apply (smt (z3) TPC.simps(141) assms(1) maxIndex_def tms_inv_def)
            apply (smt (z3) TPC.simps(142) assms(1) maxIndex_def tms_inv_def)
           apply (smt (z3) TPC.simps(143) assms(1) maxIndex_def tms_inv_def)
          apply (smt (z3) TPC.simps(144) assms(1) maxIndex_def tms_inv_def)
         apply (simp add:  tms_inv_def)
         apply (smt (z3) TMRead_inv_trans_def assms(1) tms_inv_def)
        apply (simp add:  tms_inv_def) 
  using TMRead_resp_trans_def assms(1) tms_inv_def apply fastforce
  apply (simp add:  tms_inv_def)
  apply (smt (z3) TMWrite_inv_trans_def assms(1) tms_inv_def)
  apply (simp add:  tms_inv_def)
  apply (smt (z3) TMWrite_resp_trans_def assms(1) tms_inv_def)
  apply (simp add:  tms_inv_def)
  apply (smt (z3) TMBegin_inv_trans_def assms(1) tms_inv_def)
  apply (simp add:  tms_inv_def)
  apply (smt (z3) TMBegin_resp_trans_def assms(1) tms_inv_def)
  apply (simp add:  tms_inv_def)
  apply (smt (z3) TMCommit_resp_trans_def assms(1) tms_inv_def)
  apply (simp add:  tms_inv_def)
  by(smt (z3) TMCommit_inv_trans_def assms(1) tms_inv_def)



lemma pc_stable[simp] :
assumes  "tmstep l  a \<sigma> \<sigma>'"
and " l \<noteq> z "
and " a \<noteq>  TMCrash"
and " l \<noteq> syst"
shows  "  tpc \<sigma> z = tpc \<sigma>' z "
  using assms
  apply (simp add: tmstep_def)
  apply (cases "a" ; simp)
  apply (simp add: TMRead_inv_trans_def)
  apply (simp add: TMRead_trans_def)
  apply auto[1]
  apply (simp add: TMRead_resp_trans_def)
  apply (simp add: TMWrite_inv_trans_def)
  apply (simp add: TMWrite_trans_def)
  apply (simp add:  TMWrite_resp_trans_def)
  apply (simp add: TMBegin_inv_trans_def)
  apply (simp add: TMBegin_trans_def)
  apply (simp add: TMBegin_resp_trans_def)
  apply (simp add:TMCommit_inv_trans_def)
  apply (simp add: TMCommit_trans_def)
  apply (simp add: TMCommit_resp_trans_def)
  by (simp add: TMAbort_trans_def)


(*Stability check of the DTMS invariant for t \neq syst*)
lemma tms_inv_self_stable_t:
assumes " tms_inv \<sigma>  z "
and "tmstep l  a \<sigma> \<sigma>'"
and " l \<noteq>  syst"
and "tmemory \<sigma> \<noteq> [] "
and " l \<noteq> z"
shows  "tms_inv \<sigma>'  z"
  apply(rule tmstep_cases)
  using assms
  apply (simp add: tmstep_def   )
  apply clarify
  prefer 5
  apply (simp add: tms_inv_def  maxIndex_def TMCrash_trans_def)
  apply clarify
  apply (case_tac " z \<noteq> syst")
  apply simp
  using assms(1) tms_inv_def apply force
  apply simp
  apply (subgoal_tac "  \<forall> t \<noteq> syst.  tpc \<sigma>' t \<in> {NotStarted  ,Aborted ,Committed  }")
  prefer 2
  apply simp
  apply (cases "  tpc \<sigma> z  "  ;simp add: maxIndex_def )
  using assms(1) tms_inv_def apply auto[1]
  using pc_stable
  apply (smt (z3) TPC.simps(134) assms(1) maxIndex_def tms_inv_def)
  using assms(1) tms_inv_def apply auto[1]
  using pc_stable assms(1) tms_inv_def
  using assms(5) apply fastforce           
  using pc_stable assms(1) tms_inv_def
  using assms(5) apply fastforce           
  using pc_stable assms(1) tms_inv_def
  apply auto[1]     
  using pc_stable assms(1) tms_inv_def
  apply auto[1]   
  using pc_stable assms(1) tms_inv_def
  apply auto[1]   
  using pc_stable assms(1) tms_inv_def
  apply auto[1]   
  using pc_stable assms(1) tms_inv_def
  apply auto[1]   
  using pc_stable assms(1) tms_inv_def
  apply auto[1]   
  using pc_stable assms(1) tms_inv_def
  apply (subgoal_tac " maxIndex \<sigma>'  = maxIndex \<sigma>")
  prefer 2
  apply (simp add: TMRead_trans_def  maxIndex_def )
  apply (subgoal_tac " beginIndex \<sigma>'  z  = beginIndex \<sigma> z")
  prefer 2
  apply (simp add: TMRead_trans_def   )
  apply (subgoal_tac"rdSet \<sigma>' z = rdSet \<sigma> z ")
  prefer 2
  apply (simp add: TMRead_trans_def Let_def )
  using assms(5) apply blast
  apply (subgoal_tac"wrSet \<sigma>' z = wrSet \<sigma> z ")
  prefer 2
  apply (simp add: TMRead_trans_def Let_def )
  apply (subgoal_tac "  tpc \<sigma> z = tpc \<sigma>' z ")
  prefer 2
  apply (simp add: TMRead_trans_def)
  apply (subgoal_tac " tms_inv \<sigma>  z ")
  prefer 2
  apply (simp add: assms(1))
  apply (simp add: tms_inv_def)
  using assms(5) apply blast
  apply metis
  apply (subgoal_tac " maxIndex \<sigma>'  \<ge> maxIndex \<sigma>")
  prefer 2
  apply (simp add: TMCommit_trans_def  maxIndex_def )
  apply (subgoal_tac " beginIndex \<sigma>'  z  = beginIndex \<sigma> z")
  prefer 2
  apply (simp add: TMCommit_trans_def   )
  apply (subgoal_tac"rdSet \<sigma>' z = rdSet \<sigma> z ")
  prefer 2
  apply (simp add: TMCommit_trans_def Let_def )
  apply (subgoal_tac"wrSet \<sigma>' z = wrSet \<sigma> z ")
  prefer 2
  apply (simp add: TMCommit_trans_def Let_def )
  apply (subgoal_tac "  tpc \<sigma> z = tpc \<sigma>' z ")
  prefer 2
  apply (simp add: TMCommit_trans_def)
  using assms(5) apply fastforce
  apply (simp add:   tms_inv_def )
  apply (cases "  tpc (TMCommit_trans l \<sigma>) z  " ;simp)
  using assms(1) tms_inv_def apply force
  using assms(1) tms_inv_def  maxIndex_def 
  apply auto[1]
  using assms(1) tms_inv_def  maxIndex_def 
  apply auto[1]
  using assms(1) tms_inv_def  maxIndex_def 
  apply auto[1]
  using assms(1) tms_inv_def  maxIndex_def 
  apply auto[1]
  using assms(1) tms_inv_def  maxIndex_def 
  apply auto[1]
  using assms(1) tms_inv_def  maxIndex_def 
  apply auto[1]
  using assms(1) tms_inv_def  maxIndex_def 
  apply auto[1]
  using assms(1) tms_inv_def  maxIndex_def 
  apply auto[1]
  using assms(1) tms_inv_def  maxIndex_def 
  apply auto[1]
  apply (subgoal_tac " maxIndex \<sigma>'  = maxIndex \<sigma>")
  prefer 2
  apply (simp add: TMWrite_trans_def  maxIndex_def )
  apply (subgoal_tac " beginIndex \<sigma>'  z  = beginIndex \<sigma> z")
  prefer 2
  apply (simp add: TMWrite_trans_def   )
  apply (subgoal_tac"rdSet \<sigma>' z = rdSet \<sigma> z ")
  prefer 2
  apply (simp add: TMWrite_trans_def Let_def )
  apply (subgoal_tac"wrSet \<sigma>' z = wrSet \<sigma> z ")
  prefer 2
  apply (simp add: TMWrite_trans_def Let_def )
  apply (subgoal_tac "  tpc \<sigma> z = tpc \<sigma>' z ")
  prefer 2
  apply (simp add: TMWrite_trans_def)
  using assms(5) apply fastforce
  apply ( simp add: split: if_split_asm)
  apply auto[1]
  apply (simp add: tms_inv_def ) 
  apply clarify
  apply (cases "  tpc \<sigma>' z " ;simp)
  using assms(1) tms_inv_def 
  using assms(2) assms(3) assms(5) apply auto[1]
  using assms(1) tms_inv_def 
  using assms(2) assms(3) assms(5) apply auto[1]
  using assms(1) tms_inv_def 
  using assms(2) assms(3) assms(5) apply auto[1]
  using assms(1) tms_inv_def 
  using assms(2) assms(3) assms(5) apply auto[1]
  using assms(1) tms_inv_def 
  using assms(2) assms(3) assms(5) apply auto[1]
  using assms(1) tms_inv_def 
  using assms(2) assms(3) assms(5) apply auto[1]
  using assms(1) tms_inv_def 
  using assms(2) assms(3) assms(5) apply auto[1]
  using assms(1) tms_inv_def 
  using assms(2) assms(3) assms(5) apply auto[1]
  using assms(1) tms_inv_def 
  using assms(2) assms(3) assms(5) apply auto[1]
  using assms(1) tms_inv_def 
  using assms(2) assms(3) assms(5) apply auto[1]
  apply (simp add: tms_inv_def TMBegin_trans_def  maxIndex_def)
  apply (cases "  tpc \<sigma> z  "  ;simp add: maxIndex_def )
  using assms(1) assms(5) tms_inv_def apply force
  apply (simp add: split: if_splits)
  apply (subgoal_tac " beginIndex \<sigma>' z = beginIndex \<sigma> z ")
  prefer 2
  using assms(5)  apply simp
  apply (intro conjI impI)
  using assms(5) apply blast
  using assms(1) tms_inv_def apply fastforce
  apply (metis (no_types, lifting) TPC.simps(134) assms(1) maxIndex_def tms_inv_def)
  apply (smt (z3) TPC.simps(134) assms(1) maxIndex_def tms_inv_def)
  using assms(5) apply blast
  using assms(5) apply blast
  using assms(1) assms(5) tms_inv_def apply force
  apply (smt (z3) TPC.simps(138) assms(1) assms(5) maxIndex_def tms_inv_def)
  apply (smt (z3) TPC.simps(139) assms(1) assms(5) maxIndex_def tms_inv_def)
  apply (smt (z3) TPC.simps(140) assms(1) assms(5) maxIndex_def tms_inv_def)
  apply (smt (z3) TPC.simps(141) assms(1) assms(5) maxIndex_def tms_inv_def)
  apply (smt (z3) TPC.simps(142) assms(1) assms(5) maxIndex_def tms_inv_def)
  apply (smt (z3) TPC.simps(143) assms(1) assms(5) maxIndex_def tms_inv_def)
  apply (smt (z3) TPC.simps(144) assms(1) assms(5) maxIndex_def tms_inv_def)
  apply (simp add:    maxIndex_def tms_inv_def  TMAbort_trans_def)
  apply safe
  using assms(5) apply blast
  using assms(5) apply blast
  using assms(5) apply blast
  using assms(5) apply blast
  using assms(5) apply blast
  using assms(5) apply blast
  apply (cases "  tpc \<sigma> z  "  ;simp add: maxIndex_def )
  using assms(1) tms_inv_def apply auto[1]
  using pc_stable
  apply (smt (z3) TPC.simps(134) assms(1) maxIndex_def tms_inv_def)
  using assms(1) tms_inv_def apply auto[1]
  using pc_stable assms(1) tms_inv_def
  apply (simp add: maxIndex_def)
  using pc_stable assms(1) tms_inv_def
  apply (simp add: maxIndex_def)
  using pc_stable assms(1) tms_inv_def
  apply (simp add: maxIndex_def)
  using pc_stable assms(1) tms_inv_def
  apply (simp add: maxIndex_def)
  using pc_stable assms(1) tms_inv_def
  apply (simp add: maxIndex_def)
  using pc_stable assms(1) tms_inv_def
  apply (simp add: maxIndex_def)
  using pc_stable assms(1) tms_inv_def
  apply (simp add: maxIndex_def)
  using assms(1) tms_inv_def apply blast
  using assms(1) tms_inv_def apply blast
  using assms(1) tms_inv_def apply blast
  using assms(1) tms_inv_def apply blast
  using assms(1) tms_inv_def apply blast
  apply (simp add: tms_inv_def TMRead_inv_trans_def  maxIndex_def)
  apply (cases "  tpc \<sigma> z  "  ;simp add: maxIndex_def )
  using assms(1) tms_inv_def apply auto[1]
  using pc_stable
  apply (smt (z3) TPC.simps(134) assms(1) maxIndex_def tms_inv_def)
  using assms(1) tms_inv_def apply auto[1]
  using pc_stable assms(1) tms_inv_def
  using assms(5) apply fastforce           
  using pc_stable assms(1) tms_inv_def
  using assms(5) apply fastforce           
  using pc_stable assms(1) tms_inv_def
  apply (smt (z3) TPC.simps(138) maxIndex_def)         
  using pc_stable assms(1) tms_inv_def
  apply (smt (z3) TPC.simps(139) maxIndex_def)
  using pc_stable assms(1) tms_inv_def
  apply (smt (z3) TPC.simps(140) maxIndex_def)
  using pc_stable assms(1) tms_inv_def
  apply (smt (z3) TPC.simps(141) maxIndex_def)
  using pc_stable assms(1) tms_inv_def
  apply (smt (z3) TPC.simps(142) maxIndex_def)
  using pc_stable assms(1) tms_inv_def
  apply (smt (z3) TPC.simps(143) maxIndex_def)
  using pc_stable assms(1) tms_inv_def
  apply (smt (z3) TPC.simps(144) maxIndex_def)
  apply (simp add: tms_inv_def TMRead_resp_trans_def  maxIndex_def)
  apply (cases "  tpc \<sigma> z  "  ;simp add: maxIndex_def )
  using assms(1) tms_inv_def apply auto[1]
  using pc_stable
  apply (smt (z3) TPC.simps(134) assms(1) maxIndex_def tms_inv_def)
  using assms(1) tms_inv_def apply auto[1]
  using pc_stable assms(1) tms_inv_def
  using assms(5) apply fastforce           
  using pc_stable assms(1) tms_inv_def
  using assms(5) apply fastforce           
  using pc_stable assms(1) tms_inv_def
  apply (smt (z3) TPC.simps(138) maxIndex_def)         
  using pc_stable assms(1) tms_inv_def
  apply (smt (z3) TPC.simps(139) maxIndex_def)
  using pc_stable assms(1) tms_inv_def
  apply (smt (z3) TPC.simps(140) maxIndex_def)
  using pc_stable assms(1) tms_inv_def
  apply (smt (z3) TPC.simps(141) maxIndex_def)
  using pc_stable assms(1) tms_inv_def
  apply (smt (z3) TPC.simps(142) maxIndex_def)
  using pc_stable assms(1) tms_inv_def
  apply (smt (z3) TPC.simps(143) maxIndex_def)
  using pc_stable assms(1) tms_inv_def
  apply (smt (z3) TPC.simps(144) maxIndex_def)
  apply (simp add: tms_inv_def TMWrite_inv_trans_def  maxIndex_def)
  apply (cases "  tpc \<sigma> z  "  ;simp add: maxIndex_def )
  using assms(1) tms_inv_def apply auto[1]
  using pc_stable
  apply (smt (z3) TPC.simps(134) assms(1) maxIndex_def tms_inv_def)
  using assms(1) tms_inv_def apply auto[1]
  using pc_stable assms(1) tms_inv_def
  using assms(5) apply fastforce           
  using pc_stable assms(1) tms_inv_def
  using assms(5) apply fastforce           
  using pc_stable assms(1) tms_inv_def
  apply (smt (z3) TPC.simps(138) maxIndex_def)         
  using pc_stable assms(1) tms_inv_def
  apply (smt (z3) TPC.simps(139) maxIndex_def)
  using pc_stable assms(1) tms_inv_def
  apply (smt (z3) TPC.simps(140) maxIndex_def)
  using pc_stable assms(1) tms_inv_def
  apply (smt (z3) TPC.simps(141) maxIndex_def)
  using pc_stable assms(1) tms_inv_def
  apply (smt (z3) TPC.simps(142) maxIndex_def)
  using pc_stable assms(1) tms_inv_def
  apply (smt (z3) TPC.simps(143) maxIndex_def)
  using pc_stable assms(1) tms_inv_def
  apply (smt (z3) TPC.simps(144) maxIndex_def)
  apply (simp add: tms_inv_def TMWrite_resp_trans_def  maxIndex_def)
  apply (cases "  tpc \<sigma> z  "  ;simp add: maxIndex_def )
  using assms(1) tms_inv_def apply auto[1]
  using pc_stable
  apply (smt (z3) TPC.simps(134) assms(1) maxIndex_def tms_inv_def)
  using assms(1) tms_inv_def apply auto[1]
  using pc_stable assms(1) tms_inv_def
  using assms(5) apply fastforce           
  using pc_stable assms(1) tms_inv_def
  using assms(5) apply fastforce           
  using pc_stable assms(1) tms_inv_def
  apply (smt (z3) TPC.simps(138) maxIndex_def)         
  using pc_stable assms(1) tms_inv_def
  apply (smt (z3) TPC.simps(139) maxIndex_def)
  using pc_stable assms(1) tms_inv_def
  apply (smt (z3) TPC.simps(140) maxIndex_def)
  using pc_stable assms(1) tms_inv_def
  apply (smt (z3) TPC.simps(141) maxIndex_def)
  using pc_stable assms(1) tms_inv_def
  apply (smt (z3) TPC.simps(142) maxIndex_def)
  using pc_stable assms(1) tms_inv_def
  apply (smt (z3) TPC.simps(143) maxIndex_def)
  using pc_stable assms(1) tms_inv_def
  apply (smt (z3) TPC.simps(144) maxIndex_def)
  apply (simp add: tms_inv_def TMBegin_inv_trans_def  maxIndex_def)
  apply (cases "  tpc \<sigma> z  "  ;simp add: maxIndex_def )
  using assms(1) tms_inv_def apply auto[1]
  using pc_stable
  apply (smt (z3) TPC.simps(134) assms(1) assms(5) maxIndex_def tms_inv_def)
  using assms(1) tms_inv_def apply auto[1]
  using pc_stable assms(1) tms_inv_def
  using assms(5) apply fastforce           
  using pc_stable assms(1) tms_inv_def
  using assms(5) apply fastforce           
  using pc_stable assms(1) tms_inv_def
  apply (smt (z3) TPC.simps(138) assms(5) maxIndex_def)
  using pc_stable assms(1) tms_inv_def
  apply (smt (z3) TPC.simps(139) assms(5)  maxIndex_def)
  using pc_stable assms(1) tms_inv_def
  apply (smt (z3) TPC.simps(140)assms(5)  maxIndex_def)
  using pc_stable assms(1) tms_inv_def
  apply (smt (z3) TPC.simps(141)assms(5)  maxIndex_def)
  using pc_stable assms(1) tms_inv_def
  apply (smt (z3) TPC.simps(142)assms(5)  maxIndex_def)
  using pc_stable assms(1) tms_inv_def
  apply (smt (z3) TPC.simps(143)assms(5)  maxIndex_def)
  using pc_stable assms(1) tms_inv_def
  apply (smt (z3) TPC.simps(144) assms(5) maxIndex_def)
  apply (simp add: tms_inv_def TMBegin_resp_trans_def  maxIndex_def)
  apply (cases "  tpc \<sigma> z  "  ;simp add: maxIndex_def )
  using assms(1) tms_inv_def apply auto[1]
  using pc_stable
  apply (smt (z3) TPC.simps(134) assms(1) assms(5) maxIndex_def tms_inv_def)
  using assms(1) tms_inv_def apply auto[1]
  using pc_stable assms(1) tms_inv_def
  using assms(5) apply fastforce           
  using pc_stable assms(1) tms_inv_def
  using assms(5) apply fastforce           
  using pc_stable assms(1) tms_inv_def
  apply (smt (z3) TPC.simps(138) assms(5) maxIndex_def)
  using pc_stable assms(1) tms_inv_def
  apply (smt (z3) TPC.simps(139) assms(5)  maxIndex_def)
  using pc_stable assms(1) tms_inv_def
  apply (smt (z3) TPC.simps(140)assms(5)  maxIndex_def)
  using pc_stable assms(1) tms_inv_def
  apply (smt (z3) TPC.simps(141)assms(5)  maxIndex_def)
  using pc_stable assms(1) tms_inv_def
  apply (smt (z3) TPC.simps(142)assms(5)  maxIndex_def)
  using pc_stable assms(1) tms_inv_def
  apply (smt (z3) TPC.simps(143)assms(5)  maxIndex_def)
  using pc_stable assms(1) tms_inv_def
  apply (smt (z3) TPC.simps(144) assms(5) maxIndex_def)
  apply (simp add: tms_inv_def TMCommit_resp_trans_def maxIndex_def)
  apply (cases "  tpc \<sigma> z  "  ;simp add: maxIndex_def )
  using assms(1) tms_inv_def apply auto[1]
  using pc_stable
  apply (smt (z3) TPC.simps(134) assms(1) assms(5) maxIndex_def tms_inv_def)
  using assms(1) tms_inv_def apply auto[1]
  using pc_stable assms(1) tms_inv_def
  using assms(5) apply fastforce           
  using pc_stable assms(1) tms_inv_def
  using assms(5) apply fastforce           
  using pc_stable assms(1) tms_inv_def
  apply (smt (z3) TPC.simps(138) assms(5) maxIndex_def)
  using pc_stable assms(1) tms_inv_def
  apply (smt (z3) TPC.simps(139) assms(5)  maxIndex_def)
  using pc_stable assms(1) tms_inv_def
  apply (smt (z3) TPC.simps(140)assms(5)  maxIndex_def)
  using pc_stable assms(1) tms_inv_def
  apply (smt (z3) TPC.simps(141)assms(5)  maxIndex_def)
  using pc_stable assms(1) tms_inv_def
  apply (smt (z3) TPC.simps(142)assms(5)  maxIndex_def)
  using pc_stable assms(1) tms_inv_def
  apply (smt (z3) TPC.simps(143)assms(5)  maxIndex_def)
  using pc_stable assms(1) tms_inv_def
  apply (smt (z3) TPC.simps(144) assms(5) maxIndex_def)
  apply (simp add: tms_inv_def TMCommit_inv_trans_def maxIndex_def)
  apply (cases "  tpc \<sigma> z  "  ;simp add: maxIndex_def )
  using assms(1) tms_inv_def apply auto[1]
  using pc_stable
  apply (smt (z3) TPC.simps(134) assms(1) assms(5) maxIndex_def tms_inv_def)
  using assms(1) tms_inv_def apply auto[1]
  using pc_stable assms(1) tms_inv_def
  using assms(5) apply fastforce           
  using pc_stable assms(1) tms_inv_def
  using assms(5) apply fastforce           
  using pc_stable assms(1) tms_inv_def
  apply (smt (z3) TPC.simps(138) assms(5) maxIndex_def)
  using pc_stable assms(1) tms_inv_def
  apply (smt (z3) TPC.simps(139) assms(5)  maxIndex_def)
  using pc_stable assms(1) tms_inv_def
  apply (smt (z3) TPC.simps(140)assms(5)  maxIndex_def)
  using pc_stable assms(1) tms_inv_def
  apply (smt (z3) TPC.simps(141)assms(5)  maxIndex_def)
  using pc_stable assms(1) tms_inv_def
  apply (smt (z3) TPC.simps(142)assms(5)  maxIndex_def)
  using pc_stable assms(1) tms_inv_def
  apply (smt (z3) TPC.simps(143)assms(5)  maxIndex_def)
  using pc_stable assms(1) tms_inv_def
  by(smt (z3) TPC.simps(144) assms(5) maxIndex_def)



(*Stability check of the DTMS invariant*)
lemma tms_inv_stable:
assumes "\<forall>t.  tms_inv \<sigma>  t "
and "tmstep l  a \<sigma> \<sigma>'"
and "tmemory \<sigma> \<noteq> [] "
shows  "\<forall>t.  tms_inv \<sigma>'  t "
using assms
using tms_inv_self tms_inv_self_stable_syst tms_inv_self_stable_t by blast



(* a wrSet property*)
lemma notStarted_wrSet_empty_preserved:
assumes " \<forall> t. tpc \<sigma> t = NotStarted \<longrightarrow>  wrSet \<sigma> t = Map.empty  "
and "tmstep t a \<sigma> \<sigma>'"
shows " \<forall> t. tpc \<sigma>' t = NotStarted \<longrightarrow>  wrSet \<sigma>' t = Map.empty  "
apply(rule tmstep_cases)
using assms
apply (simp add: tmstep_def )
apply clarify
apply (simp add:  TMRead_trans_def Let_def)
apply ( simp add: split: if_split_asm)
using assms(1) apply blast
using assms(1) apply blast
apply (smt (z3) assms(1) fun_upd_triv tms_state.ext_inject tms_state.surjective tms_state.update_convs(3) tms_state.update_convs(5))
apply (simp add:  TMCommit_trans_def)
using assms(1) apply presburger
apply (simp add:  TMWrite_trans_def)
apply (simp add: assms(1))
apply (simp add:  TMBegin_trans_def)
using assms(1) apply blast
apply (simp add:  TMCrash_trans_def)
apply (simp add: assms(1))
apply (simp add:  TMAbort_trans_def)
apply (simp add: assms(1))
apply (simp add:   TMRead_inv_trans_def)
apply (simp add: assms(1))
apply (simp add:    TMRead_resp_trans_def)
apply (simp add: assms(1))
apply (simp add:   TMWrite_inv_trans_def)
apply (simp add: assms(1))
apply (simp add:   TMWrite_resp_trans_def)
apply (simp add: assms(1))
apply (simp add:   TMBegin_inv_trans_def)
apply (simp add: assms(1))
apply (simp add:   TMBegin_resp_trans_def)
apply (simp add: assms(1))
apply (simp add:   TMCommit_resp_trans_def)
apply (simp add: assms(1))
apply (simp add:   TMCommit_inv_trans_def)
by (simp add: assms(1))



lemma  notStarted_wrSet_empty_inv_start:
assumes"   start  \<sigma> "
shows  " \<forall> t. tpc \<sigma> t = NotStarted \<longrightarrow>  wrSet \<sigma> t = Map.empty  "
using assms
by(simp add:  start_def) 





end






