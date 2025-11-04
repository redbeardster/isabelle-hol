(*simulation relation of DTML-DTMS2*)

theory Refinement
imports  DTML  DTMS2
begin

(*auxiliary definition*)
definition write_count :: "nat \<Rightarrow> nat"
where
"write_count n \<equiv> n div 2"


lemma div_mono2:
"(n :: nat) \<le> g \<Longrightarrow> g div 2 < m \<Longrightarrow> n div 2 < m"
by linarith

(*auxiliary definition*)
definition "logical_glb cs \<equiv>
case (writer cs) of
  Some w \<Rightarrow> if (pc cs w =   PC.Commit4 )
                then ( lastVal  glb (\<tau> cs)  + 1) - recoveredGlb  cs  else lastVal  glb (\<tau> cs)  - recoveredGlb  cs 
| None \<Rightarrow> lastVal  glb (\<tau> cs) - recoveredGlb  cs  "


(*auxiliary definition*)
definition tNotCrashed :: " mp_state \<Rightarrow> TId \<Rightarrow> bool"
where 
"tNotCrashed cs t  \<equiv>  (t \<noteq> (syst) \<and>  pc cs t  \<notin>{ PC.NotStarted, PC.Aborted,PC.Committed}   ) "

lemmas tnc_sis [simp] = 
tNotCrashed_def 

(*auxiliary definition*)
definition validity_prop :: "mp_state \<Rightarrow> tms_state  \<Rightarrow> TId \<Rightarrow> bool"
where
"validity_prop  cs as t \<equiv>
   ((read_consistent ( (tmemory  as)! (write_count (regs (\<tau> cs) t  DTML.loc - recoveredGlb  cs ))) (rdSet  as t)))   \<and>( beginIndex as t \<le> write_count (regs (\<tau> cs) t  DTML.loc - recoveredGlb  cs)  )               
"

(*auxiliary definition*)
definition in_flight :: "mp_state \<Rightarrow> tms_state  \<Rightarrow> TId \<Rightarrow> bool"
where
"in_flight  cs as t \<equiv>
    validity_prop  cs as t \<and>
(even ( (regs (\<tau> cs) t  DTML.loc)) \<longleftrightarrow> wrSet as t = Map.empty)
"


lemma loc_zero_read_con:
assumes " rdSet  as t = Map.empty "
shows "read_consistent (nth (tmemory  as) (write_count (regs (\<tau> cs) t  DTML.loc))) (rdSet  as t)"
using assms
by (simp add: read_consistent_def)

lemma loc_zero_read_con2:
assumes " rdSet  as t = Map.empty "
shows "read_consistent (tmemory as !(write_count (regs (\<tau> cs) t  DTML.loc- recoveredGlb cs))) (rdSet  as t)"
using assms
by (simp add: read_consistent_def)


(*auxiliary definition*)
definition writes :: "mp_state \<Rightarrow>tms_state  \<Rightarrow> Loc \<Rightarrow> V option"
where
"writes cs0 as0  \<equiv>
case (writer cs0) of
Some w \<Rightarrow> if (pc cs0 w =  PC.Commit4 )  then Map.empty else wrSet  as0 w
| None \<Rightarrow> Map.empty"


(*Part of the global relation of the simulation relation*)
definition global_rel :: "mp_state \<Rightarrow> tms_state  \<Rightarrow> bool"
where

"global_rel cs0 as0  \<equiv>

(  pc cs0 syst = RecIdle   \<longrightarrow>
(

(     write_count (logical_glb cs0 ) = length (tmemory  as0) - 1)
\<and> 
(  \<forall> l \<noteq> glb . lastVal l (\<tau> cs0)  =  apply_partial ( (tmemory as0) ! ((maxIndex as0) - 1) ) (writes cs0 as0 ) l) ))

\<and>

(  \<forall> l \<noteq> glb.  ( (tmemory as0) ! ((maxIndex as0) - 1) ) l =  (if (log cs0) l = None then (lastVal l (\<tau> cs0))
                      else the ((log cs0) l)))

\<and>

( \<forall>t. t \<noteq> syst \<and> pc cs0 t = PC.NotStarted  \<longrightarrow> tpc as0 t = TPC.NotStarted \<and>
               pc cs0 t = PC.NotStarted   )
"  

(*Part of the global relation of the simulation relation*)
definition "read_prop cs0 as0 \<equiv>
pc cs0 syst = RecIdle   \<longrightarrow>(\<forall> n l. ( n > 0 \<and>n < length (memory (\<tau> cs0))  \<and>  comploc ((memory (\<tau> cs0))!n) glb= glb \<and> l \<noteq> glb) \<longrightarrow> 
((tmemory as0) !(write_count ( (valOf n glb (\<tau> cs0))  - (recoveredGlb  cs0)  ))  ) l = valOf (last_entry_lim (\<tau> cs0) l n) l (\<tau> cs0)  ) "





(*Part of the transaction relation of the simulation relation*)
definition no_read_rdSet_empty :: "mp_state \<Rightarrow> tms_state \<Rightarrow> TId \<Rightarrow> bool"
where
"no_read_rdSet_empty  cs as  t  \<equiv>

( (\<not> readAux cs t \<and>  tNotCrashed cs t \<and>  (\<not> writeAux cs t) )   \<longrightarrow>  rdSet as t = Map.empty )"



(*Part of the transaction relation of the simulation relation*)
definition no_write_wrSet_empty :: "mp_state \<Rightarrow> tms_state \<Rightarrow> TId \<Rightarrow> bool"
where
"no_write_wrSet_empty   cs as  t  \<equiv>

( (\<not> writeAux cs t \<and>  tNotCrashed cs t  )   \<longrightarrow>  wrSet as t = Map.empty )"


(*Part of the transaction relation of the simulation relation*)
definition write_wrSet_notEmpty :: "mp_state \<Rightarrow> tms_state \<Rightarrow> TId \<Rightarrow> bool"
where
"write_wrSet_notEmpty   cs as  t  \<equiv>
( ( writer cs = ( Some t)  \<and>  t\<noteq> syst\<and>
pc cs t  \<notin>{ PC.Write3, PC.Write4,PC.Write5,PC.Write6, PC.Write7 ,  PC.BeginPending }  )   \<longrightarrow>  wrSet as t \<noteq>Map.empty )"


(*Part of the transaction relation of the simulation relation*)
definition read_rdSet_notEmpty :: "mp_state \<Rightarrow> tms_state \<Rightarrow> TId \<Rightarrow> bool"
where
" read_rdSet_notEmpty  cs as  t  \<equiv>
( ( readAux cs t \<and>  tNotCrashed cs t  \<and>  pc cs t  \<noteq> PC.BeginPending  )   \<longrightarrow>  rdSet as t \<noteq>  Map.empty )"


(*Part of the transaction relation of the simulation relation*)
definition  loc_in_wrSet  :: "mp_state \<Rightarrow> tms_state \<Rightarrow> TId \<Rightarrow> bool"
where
" loc_in_wrSet cs as  t  \<equiv>
( \<forall> l \<in>  dom(  (wrSet as t)). (writer cs = Some t \<longrightarrow>  the ( (wrSet as t) l )   =   lastVal l (\<tau> cs)   ) )"


(*Part of the transaction relation of the simulation relation*)
definition  even_loc_wrSet_empty :: "mp_state \<Rightarrow> tms_state \<Rightarrow> TId \<Rightarrow> bool"
where
"even_loc_wrSet_empty   cs as  t  \<equiv>

( ( even( regs (\<tau> cs) t loc)  \<and>  tNotCrashed cs t  )   \<longrightarrow>  wrSet as t = Map.empty )"


(*Part of the transaction relation of the simulation relation*)
definition  odd_loc_wrSet_notEmpty :: "mp_state \<Rightarrow> tms_state \<Rightarrow> TId \<Rightarrow> bool"

where
"odd_loc_wrSet_notEmpty   cs as  t  \<equiv>

( ( odd( regs (\<tau> cs) t loc)  \<and>  tNotCrashed cs t  \<and>
pc cs t  \<notin>{ PC.Write3, PC.Write4,PC.Write5,PC.Write6, PC.Write7 ,  PC.BeginPending,  PC.Begin2,   PC.Begin3 } 
)   \<longrightarrow>  wrSet as t \<noteq> Map.empty )"


(*Final condition of the transaction relation of the simulation relation*)
definition tr_rel  :: "mp_state \<Rightarrow> tms_state  \<Rightarrow> TId \<Rightarrow> bool"
where
"tr_rel   cs as t \<equiv>
( case (pc cs) t of 

PC.Ready  \<Rightarrow>(tpc as) t =  TPC.Ready  \<and>  ( ( ( even(lastVal  glb (\<tau> cs)) \<and> (regs (\<tau> cs) t loc) = lastVal  glb (\<tau> cs)) \<or> readAux cs t  \<or>  writeAux cs t ) \<longrightarrow>
validity_prop  cs as t  )

| PC.WritePending  \<Rightarrow>(tpc as) t =  TPC.WritePending  \<and>  ( ( ( even(lastVal  glb (\<tau> cs)) \<and> (regs (\<tau> cs) t loc) = lastVal  glb (\<tau> cs)) \<or> readAux cs t  \<or>  writeAux cs t ) \<longrightarrow>
validity_prop  cs as t  )

| PC.Write1  \<Rightarrow>(tpc as) t =  TPC.WritePending   \<and>  ( ( ( even(lastVal  glb (\<tau> cs)) \<and> (regs (\<tau> cs) t loc) = lastVal  glb (\<tau> cs)) \<or> readAux cs t  \<or>  writeAux cs t ) \<longrightarrow>
validity_prop  cs as t  )

| PC.Write2  \<Rightarrow> (tpc as) t =   TPC.WritePending   \<and> ( ( (regs (\<tau> cs) t loc) = lastVal  glb (\<tau> cs) \<and> even(regs (\<tau> cs) t loc ) ) \<longrightarrow>
 in_flight  cs as t    \<and> wrSet as t = Map.empty)

| PC.Write3  \<Rightarrow> (tpc as) t =   TPC.WritePending   \<and> validity_prop  cs as t  \<and> wrSet as t = Map.empty
 
| PC.Write4  \<Rightarrow> (tpc as) t =  TPC.WritePending   \<and> validity_prop  cs as t  

| PC.Write5  \<Rightarrow> (tpc as) t =   TPC.WritePending   \<and> validity_prop  cs as t  

| PC.Write6  \<Rightarrow> (tpc as) t =   TPC.WritePending  \<and> validity_prop  cs as t  

| PC.Write7  \<Rightarrow> (tpc as) t =  TPC.WritePending  \<and> validity_prop  cs as t 

| PC.Write8  \<Rightarrow> (tpc as) t =  TPC.WriteResponding  \<and> in_flight  cs as t 

| PC.WriteResponding  \<Rightarrow> (tpc as) t =  TPC.WriteResponding  \<and>  ( ( ( even(lastVal  glb (\<tau> cs)) \<and> (regs (\<tau> cs) t loc) = lastVal  glb (\<tau> cs)) \<or> readAux cs t  \<or>  writeAux cs t ) \<longrightarrow>
validity_prop  cs as t  )

|PC.Aborted \<Rightarrow>  (tpc as) t =   TPC.Aborted

| PC.NotStarted   \<Rightarrow>(tpc as) t = NotStarted\<and>  read_consistent (tmemory as !(write_count (regs (\<tau> cs) t  DTML.loc- recoveredGlb cs))) (rdSet  as t)

| PC.BeginPending   \<Rightarrow>(tpc as) t = BeginPending \<and>  read_consistent (tmemory as !(write_count (regs (\<tau> cs) t  DTML.loc- recoveredGlb cs))) (rdSet  as t)


| PC.Begin2 \<Rightarrow>(tpc as) t =   BeginPending   \<and> read_consistent (tmemory as !(write_count (regs (\<tau> cs) t  DTML.loc- recoveredGlb cs))) (rdSet  as t)

| PC.Begin3 \<Rightarrow>(tpc as) t =   BeginPending \<and>  read_consistent (tmemory as !(write_count (regs (\<tau> cs) t  DTML.loc- recoveredGlb cs))) (rdSet  as t)

|  PC.BeginResponding  \<Rightarrow>(tpc as) t =  TPC.BeginResponding  \<and>  ( ( ( even(lastVal  glb (\<tau> cs)) \<and> (regs (\<tau> cs) t loc) = lastVal  glb (\<tau> cs)) \<or> readAux cs t  \<or>  writeAux cs t ) \<longrightarrow>
validity_prop  cs as t  )

| PC.CommitPending  \<Rightarrow>(tpc as) t =  TPC.CommitPending \<and>  ( ( ( even(lastVal  glb (\<tau> cs)) \<and> (regs (\<tau> cs) t loc) = lastVal  glb (\<tau> cs)) \<or> readAux cs t  \<or>  writeAux cs t ) \<longrightarrow>
validity_prop  cs as t  )

|PC.Commit2 \<Rightarrow>  (tpc as) t =   TPC.CommitPending  \<and> in_flight  cs as t   

|PC.Commit3 \<Rightarrow>  (tpc as) t =   TPC.CommitPending \<and> in_flight  cs as t 

|PC.Commit4 \<Rightarrow>  (tpc as) t =  TPC.CommitResponding

|PC.CommitResponding \<Rightarrow>  (tpc as) t =  TPC.CommitResponding

|PC.Committed \<Rightarrow>  (tpc as) t =  TPC.Committed

|PC.ReadyToRecover \<Rightarrow>  length (tmemory as) = 1 \<and> t = syst

|PC.Rec1 \<Rightarrow>  length (tmemory as) = 1 \<and> t = syst

|PC.Rec2 \<Rightarrow>  length (tmemory as) = 1 \<and> t = syst

|PC.Rec3 \<Rightarrow>  length (tmemory as) = 1 \<and> t = syst \<and> lastVal ( regs (\<tau> cs) t c2)  (\<tau> cs) =  ( (tmemory as) ! ((maxIndex as) - 1) ) (regs (\<tau> cs) t c2)

|PC.Rec4 \<Rightarrow>  length (tmemory as) = 1 \<and> t = syst \<and> lastVal ( regs (\<tau> cs) t c2)  (\<tau> cs)  =  ( (tmemory as) ! ((maxIndex as) - 1) ) (regs (\<tau> cs) t c2)

|PC.Rec5 \<Rightarrow>  length (tmemory as) = 1 \<and> t = syst \<and> lastVal ( regs (\<tau> cs) t c2)  (\<tau> cs)  =  ( (tmemory as) ! ((maxIndex as) - 1) ) (regs (\<tau> cs) t c2)

|PC.Rec6 \<Rightarrow>  length (tmemory as) = 1 \<and> t = syst

|PC.Rec7 \<Rightarrow>  length (tmemory as) = 1 \<and> t = syst

|PC.Rec8 \<Rightarrow>  length (tmemory as) = 1 \<and> t = syst

|PC.Rec9 \<Rightarrow>  length (tmemory as) = 1 \<and> t = syst

|PC.RecIdle \<Rightarrow>  t = syst

| PC.ReadPending  \<Rightarrow>(tpc as) t =  TPC.ReadPending  \<and>  ( ( ( even(lastVal  glb (\<tau> cs)) \<and> (regs (\<tau> cs) t loc) = lastVal  glb (\<tau> cs)) \<or> readAux cs t  \<or>  writeAux cs t ) \<longrightarrow>
validity_prop  cs as t  )

| PC.Read1  \<Rightarrow>(tpc as) t =  TPC.ReadPending  \<and>  ( ( ( even(lastVal  glb (\<tau> cs)) \<and> (regs (\<tau> cs) t loc) = lastVal  glb (\<tau> cs)) \<or> readAux cs t  \<or>  writeAux cs t ) \<longrightarrow>
validity_prop  cs as t  )

|PC.Read2 \<Rightarrow> (tpc as) t =   TPC.ReadPending  \<and> ( ( ( even(lastVal  glb (\<tau> cs)) \<and> (regs (\<tau> cs) t loc) = lastVal  glb (\<tau> cs)) \<or> readAux cs t  \<or>  writeAux cs t ) \<longrightarrow>
in_flight  cs as t  )

|PC.Read3 \<Rightarrow> (tpc as) t =   TPC.ReadPending  \<and>  ( ( ( even(lastVal  glb (\<tau> cs)) \<and> (regs (\<tau> cs) t loc) = lastVal  glb (\<tau> cs)) ) \<longrightarrow>
in_flight  cs as t  ) \<and> (rdSet  as t) = Map.empty

|PC.Read4 \<Rightarrow> (tpc as) t =   TPC.ReadPending  \<and>    in_flight  cs as t   

|PC.Read5 \<Rightarrow> (tpc as) t =   TPC.ReadPending \<and>    in_flight  cs as t 

| PC.ReadResponding  \<Rightarrow>(tpc as) t =  TPC.ReadResponding  \<and>  ( ( ( even(lastVal  glb (\<tau> cs)) \<and> (regs (\<tau> cs) t loc) = lastVal  glb (\<tau> cs)) \<or> readAux cs t  \<or>  writeAux cs t ) \<longrightarrow>
validity_prop  cs as t  )  \<and> regs (\<tau> cs) t val  = valRead  as t
)
"


(*total simulation relation*)
definition f_sim :: "mp_state \<Rightarrow> tms_state \<Rightarrow>  bool"
where 
"f_sim cs as    \<equiv>
global_rel cs as \<and>
(\<forall> t.   no_read_rdSet_empty  cs as  t  \<and>
no_write_wrSet_empty   cs as  t \<and>
write_wrSet_notEmpty   cs as  t \<and>
read_rdSet_notEmpty  cs as  t \<and>
loc_in_wrSet cs as  t  \<and>
even_loc_wrSet_empty   cs as  t  \<and>
odd_loc_wrSet_notEmpty   cs as  t \<and>
tr_rel   cs as t   ) \<and>
read_prop cs as 
"

(*the initial state of DTML and DTMS2 imply the simulation relation*)
lemma Ref_Start:
assumes "thrdsvars" 
and " TML_start cs "
and "(\<forall> \<tau>.   total_wfs  (\<tau> cs))"
and "  TMS_start  as "
shows  "f_sim cs as"  
using assms
apply (simp add: f_sim_def  TML_start_def  TMS_start_def )
apply (intro conjI impI)
apply (simp add: global_rel_def maxIndex_def apply_partial_def writes_def logical_glb_def  write_count_def total_wfs_def)
apply (intro conjI)
apply (metis bits_div_0 lastVal_def st_lv)
apply (metis lastVal_def st_lv)
apply (intro allI conjI)
apply (simp add:  no_read_rdSet_empty_def)
apply (simp add: no_write_wrSet_empty_def)

apply (simp add:  write_wrSet_notEmpty_def)
apply (simp add: read_rdSet_notEmpty_def)  apply metis
apply (simp add:  loc_in_wrSet_def)
apply (simp add:  even_loc_wrSet_empty_def)
apply (simp add:  odd_loc_wrSet_notEmpty_def)
apply blast
apply (unfold tr_rel_def)
apply (smt (z3) PC.simps(1641) PC.simps(1669) diff_zero loc_zero_read_con)
apply (unfold read_prop_def) 
by (metis less_numeral_extra(3) less_one start_size)


lemmas unfold_f_sim  = global_rel_def loc_in_wrSet_def  no_read_rdSet_empty_def  no_write_wrSet_empty_def



end







