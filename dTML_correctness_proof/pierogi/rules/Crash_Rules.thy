theory Crash_Rules
  imports "../State" "../Language"  "../Assertions"  "../Wellformedness"
begin

definition  "select_survived_val \<sigma>  x = (SOME i. i \<in> [x]\<^sub>P \<sigma>)"


definition "crash_trans ts  \<equiv> 
ts\<lparr> vpcommit:=\<lambda>t.\<lambda>l.0, coh:=\<lambda>t.\<lambda>l.0, vpasync:=\<lambda>t.\<lambda>l.0, 
   vrnew:=\<lambda>t.0, vpready:=\<lambda>t.0 ,maxcoh:=\<lambda>t.0,
 regs:=\<lambda>t.\<lambda>r.(SOME v. v \<in> UNIV),
   maxvp:= \<lambda>l.0, 
   survived_val:=\<lambda>l. select_survived_val ts  l,
   memory := [Init_Msg] \<rparr> " 
(* regs:=\<lambda>t.\<lambda>r.(SOME v. v \<in> UNIV),*)



(* Basic lemmas about memory *)
lemma [simp]: "memory (crash_trans ts) = [Init_Msg] "
  by (simp add: crash_trans_def)


(*crash step definition*)
datatype crash_event = Crash

definition crash_step :: "crash_event  \<Rightarrow> TState \<Rightarrow> TState\<Rightarrow> bool "
 where
    " crash_step   b  ts ts'\<equiv>
   (case b of  
         Crash \<Rightarrow> 
           ts'  = crash_trans ts) "
                         
lemma step_crash_cases:
   " crash_step  a  ts ts'
          \<Longrightarrow> 
        \<lbrakk> ts' = crash_trans ts \<and> a = crash  \<Longrightarrow> P ts (crash_trans ts )\<rbrakk>
  \<Longrightarrow> P ts ts'"
  by (metis crash_event.case crash_event.exhaust crash_step_def)


(*crash abbreviation *)
abbreviation crash__abbr:: " TState   \<Rightarrow> TState \<Rightarrow> bool" ("_ [CRASH] _" [100,100])
  where "\<sigma> [CRASH]  \<sigma>' \<equiv> crash_step (Crash) \<sigma> \<sigma>'"


(*check that the wellformedness conditions holds for the crash transition*)
lemma cmem_structured_preserved [simp]:
  assumes "mem_structured ts"
and " crash_step Crash  ts ts' "
  shows "mem_structured ts"
  using  assms by(simp add: mem_structured_def)

lemma cvbounded_preserved[simp]:
  assumes "vbounded ts"
     and " crash_step Crash  ts ts' "
    shows " vbounded ts'"
  using  assms by(simp add: crash_step_def crash_trans_def vbounded_def)

lemma ccoh_loc_rel_preserved[simp]:
 assumes "\<forall>ti l. comploc ( (memory ts)!(coh ts ti l)) l = l"
     and " crash_step Crash  ts ts' "
   shows  "\<forall>ti l. comploc ( (memory ts')!(coh ts' ti l)) l = l"
  using assms
  by (simp add: crash_step_def crash_trans_def)

lemma cOTSF_notempty_preserved[simp]:   
 assumes "mem_structured ts"
and "vbounded ts"
and " (\<forall> nview ti l. OTSF ts ti l nview \<noteq> {})"
 and "crash_step Crash  ts ts'"
and  "\<forall>ti l. comploc ( (memory ts)!(coh ts ti l)) l = l"
shows " (\<forall> nview ti l. OTSF ts' ti l nview \<noteq> {})"
  using assms apply(simp add: crash_step_def crash_trans_def)
  by(simp add: OTSF_def select_survived_val_def notoverwritten_def)


lemma cOTS_notempty_preserved[simp]:
  assumes "mem_structured ts"
 and "vbounded ts"
 and " (\<forall> ti addr. OTS   ts ti  addr \<noteq> {} )" 
 and "crash_step Crash  ts ts'"
 and  "\<forall>ti l. comploc ( (memory ts)!(coh ts ti l)) l = l"
shows " (\<forall> ti addr. OTS ts' ti  addr \<noteq> {} ) "
  using assms apply(simp add: crash_step_def crash_trans_def)
  by (simp add: OTS_def OTSF_def select_survived_val_def notoverwritten_def)


lemma cOV_notempty_preserved[simp]:
 assumes "mem_structured ts"
and "vbounded ts"
  and " (\<forall> ti addr.[addr]\<^sub>ti ts \<noteq> {} )" 
   and "crash_step Crash  ts ts'"
and  "\<forall>ti l. comploc ( (memory ts)!(coh ts ti l)) l = l"
shows " (\<forall> ti addr.[addr]\<^sub>ti ts' \<noteq> {}) "
  using assms
  apply (simp add: mapval_def)
  by (metis Int_Collect all_not_in_conv assms(5) cOTS_notempty_preserved)


lemma  cOPTS_notempty_preserved[simp]:
  assumes "mem_structured ts"
and "vbounded ts"
  and " (\<forall>  addr. OPTS   ts   addr \<noteq> {} )" 
   and "crash_step Crash  ts ts'"
and  "\<forall>ti l. comploc ( (memory ts)!(coh ts ti l)) l = l"
shows " (\<forall>  addr. OPTS ts'   addr \<noteq> {} ) "
  using assms apply(simp add: crash_step_def crash_trans_def)
  by(simp add: OPTS_def select_survived_val_def notoverwritten_def)

lemma  cOPV_notempty_preserved[simp]:
  assumes "mem_structured ts"
and "vbounded ts"
  and " (\<forall>  addr. [addr]\<^sub>P  ts \<noteq> {} )" 
     and "crash_step Crash  ts ts'"
and  "\<forall>ti l. comploc ( (memory ts)!(coh ts ti l)) l = l"
shows " (\<forall>  addr.  [addr]\<^sub>P  ts' \<noteq> {} ) "
  using assms  apply (simp add: mapval_def)
  by (metis Int_Collect assms(5) cOPTS_notempty_preserved equals0I)

lemma cOATS_notempty_preserved[simp]:
  assumes "mem_structured ts"
and "vbounded ts"
  and " (\<forall> ti addr. OATS   ts ti  addr \<noteq> {} )" 
   and "crash_step Crash  ts ts'"
and  "\<forall>ti l. comploc ( (memory ts)!(coh ts ti l)) l = l"
shows " (\<forall> ti addr. OATS ts' ti  addr \<noteq> {} ) "
  using assms apply(simp add: crash_step_def crash_trans_def)
  by(simp add: OATS_def select_survived_val_def notoverwritten_def)

lemma  OAV_notempty_preserved[simp]:
  assumes "mem_structured ts"
and "vbounded ts"
  and " (\<forall>  addr t. [addr]\<^sup>A\<^sub>t  ts \<noteq> {} )" 
   and "crash_step Crash  ts ts'"
and  "\<forall>ti l. comploc ( (memory ts)!(coh ts ti l)) l = l"
shows " (\<forall>  addr t. [addr]\<^sup>A\<^sub>t  ts' \<noteq> {} ) "
  using assms  apply (simp add: mapval_def)
  by (metis (no_types, lifting) assms(5) cOATS_notempty_preserved disjoint_iff_not_equal inf.idem mem_Collect_eq)
(**********************************)



(*rule: If the persistent view of an address x contains only one value before the crash then 
after the crash it will contain this only value*)
lemma opv_ni_s:
  assumes " [x]\<^sub>Pts  = {a}"
and " ts [CRASH] ts' "
shows "  [x]\<^sub>Pts' = {a}"
  using assms
  apply(simp add: crash_step_def total_wfs_def)
  apply (subgoal_tac "  survived_val ts' x = a ")
   prefer 2

  apply (subgoal_tac " select_survived_val ts x = a " )
  prefer 2
   apply (simp add: select_survived_val_def)
   apply (simp add: crash_trans_def)

 apply (subgoal_tac " OPTS ts' x = {0 }" )
   prefer 2
  apply (simp add: OPTS_def notoverwritten_def )
  apply auto[1]
  by (simp add: mapval_def)

(*rule: The value of the last write of a location x does not change after a crash
given that this is the only in the persistent view of x before the crash*)
lemma lv_ni:
  assumes " [x]\<^sub>Pts  = {lastVal x  ts   }"
and " ts [CRASH] ts' "
shows  " lastVal x ts' = lastVal x ts "
  using assms
  apply(simp add:crash_step_def total_wfs_def)
  apply (subgoal_tac "  survived_val ts' x = lastVal x  ts ")
   prefer 2
  apply (subgoal_tac " select_survived_val ts x = lastVal x  ts  " )
  prefer 2
   apply (simp add: select_survived_val_def)
   apply (simp add: crash_trans_def)
  apply (subgoal_tac"   survived_val ts' x = lastVal x ts'") 
  prefer 2 
   apply (simp add: crash_trans_def  )
   apply (subgoal_tac " last_entry_set ts' x = {0} ")
    prefer 2
    apply (simp add: last_entry_set_def)
  apply force
   apply (simp add: lastVal_def last_entry_def )
  by simp


lemma lv_ov_ni:
  assumes " [x]\<^sub>Pts  = {lastVal x  ts   }"
and " ts [CRASH] ts' "
shows  " [x]\<^sub>Pts  = {lastVal x  ts'   } "
  using assms
  using lv_ni by presburger

(*rule: After a crash, the thread view of any thread t for any location x contains only its last written
value*)
lemma ov_lv_lc:
assumes " ts [CRASH] ts' "
shows  "   [y]\<^sub>t ts'  = { lastVal y  ts'  }"
  using assms
 apply (subgoal_tac " length (memory (ts')) = 1 ")
  prefer 2
   apply (simp add: crash_step_def crash_trans_def)
apply (subgoal_tac " last_entry_set ts' y = {0} ")
    prefer 2
   apply (simp add: last_entry_set_def crash_step_def crash_trans_def)
  apply fastforce

  apply (subgoal_tac " last_entry ts' y   = 0 " )
   prefer 2
   apply (simp add: last_entry_def)
  apply (subgoal_tac "  survived_val ts' y = lastVal y  ts' ")
  prefer 2
   apply (simp add: crash_step_def crash_trans_def lastVal_def )

  apply (subgoal_tac "  OTS ts' t y  = {0 } ")
   prefer 2
  apply (simp add: crash_step_def crash_trans_def OTS_def OTSF_def notoverwritten_def)
  apply force
  by (simp add: mapval_def  crash_step_def crash_trans_def)



end

