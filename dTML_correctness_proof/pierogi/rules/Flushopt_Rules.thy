theory Flushopt_Rules

  imports "../State" "../Language"  "../Assertions"  "../Wellformedness"
begin

(* The lemmas that begin with the  comment "rule: __" are the proof rules regarding the flushopt instruction.
   All the other lemmas are auxiliary and are used for proving the proof rules.
   Rules that end with "lc" concern mostly local correctness.
   Rules that end with "ni" concern  mostly  non-interference.
   Rules that end with "gen" concern non-interference and local correctness.
   Rules that end with "rel" concern relations between view sets. *) 

lemma [simp]:
  assumes "mem_structured ts"
  and " i \<in>  OTS ts ti x"
shows " 0 \<le> i  \<and> i < length(memory ts) "
  using assms apply (simp add:  mem_structured_def OTS_def OTSF_def )
  done


lemma [simp]:
  assumes "mem_structured ts"
 and " 0 \<le> i  \<and> i < length(memory ts) "
 and "memory ts ! i = Init_Msg"
shows "i = 0"
  using assms(1)  apply ( unfold  mem_structured_def   )
  apply (subgoal_tac"  length (memory ts) \<noteq>  0 " )
   prefer 2
   apply blast
  using assms(2) assms(3) le_neq_implies_less by blast



lemma flo_oats_ots_rel:
  assumes "mem_structured ts"
  and "vbounded ts"
  and  "step ti ( Flush_opt  x ) ts ts'"
  and " OTS ts  ti  x\<noteq> {}"
 and  "\<forall>ti l. comploc ( (memory ts)!(coh ts ti l)) l = l"
shows "  OATS ts' ti x \<subseteq> OTS ts  ti  x "
using assms 
  apply (simp add: step_def )
  apply (subgoal_tac "\<forall>k.  k \<in> OATS ts' ti x \<longrightarrow> k \<in> OTS ts  ti  x" )
  prefer 2
apply (simp add: OATS_def OTS_def)
  apply (simp add:  OTSF_def notoverwritten_def)
  apply clarify
  apply(intro allI impI conjI, elim conjE)
 apply (subgoal_tac " k = 0")
     prefer 2
     apply auto[1]
    apply simp
 apply (subgoal_tac " coh ts ti x \<le>  vpasync (flush_opt_trans ti x ts) ti x ")
     prefer 2
     apply (simp add: flush_opt_trans_def)
    apply (meson dual_order.strict_trans2 mem_structured_def neq0_conv)
   apply simp
   apply (subgoal_tac " vrnew ts ti \<le>  vpasync ts' ti x")
  prefer 2
   apply (subgoal_tac "  vpasync ts' ti x \<ge> vpready ts ti")
    prefer 2
    apply (simp add: flush_opt_trans_def )
   apply (subgoal_tac " vrnew ts ti \<le> vpready ts ti ")
    prefer 2
  using assms(2) vbounded_def apply blast
      apply linarith
     apply simp
    apply simp
 apply (subgoal_tac " coh ts ti x \<le>  vpasync (flush_opt_trans ti x ts) ti x ")
     prefer 2
     apply (simp add: flush_opt_trans_def)
 apply (subgoal_tac "comploc (( memory ts)! (coh ts ti x)) x = x")
     prefer 2
  using assms(5) apply blast
     apply( elim conjE)
    apply simp
     apply (simp add: mem_structured_def )
    apply (meson le0 leI le_less_trans)
  apply (subgoal_tac " vrnew ts ti \<le>  vpasync ts' ti x")
  prefer 2
   apply (subgoal_tac "  vpasync ts' ti x \<ge> vpready ts ti")
    prefer 2
    apply (simp add: flush_opt_trans_def )
   apply (subgoal_tac " vrnew ts ti \<le> vpready ts ti ")
    prefer 2
  using assms(2) vbounded_def apply blast
      apply linarith
   apply simp
  by (simp add: subsetI) 


(*rule: After a thread t executes a flushopt on address x, the set of its observable asynchronous
values (OAV) of x for t, is a subset of the set of its observable values (OV) *)
lemma flo_oav_ov_rel:
  assumes "mem_structured ts"
  and "vbounded ts"
  and  "step t ( Flush_opt  x ) ts ts'"
  and " OTS ts  t  x\<noteq> {}"
  and  "\<forall>ti l. comploc ( (memory ts)!(coh ts ti l)) l = l"
shows "  [x]\<^sup>A\<^sub>t ts'  \<subseteq>  [x]\<^sub>t ts"
  using assms
 apply (simp add: step_def )
  apply (subgoal_tac " OATS ts' t  x \<subseteq> OTS ts  t  x" )
   prefer 2
  using assms(3) assms(5) flo_oats_ots_rel apply blast
  apply (unfold mapval_def)
  using assms(3) flo_crash by auto



lemma [simp]:
 assumes "mem_structured ts"
and "i = 0"
shows "(memory ts ) ! i =  Init_Msg"
  using assms
  apply (simp add: mem_structured_def vbounded_def )
  done 

lemma vrnew_flo:
 assumes "mem_structured ts"
  and "vbounded ts"
and " ts' = flush_opt_trans t x ts"
shows " vrnew ts' t' =  vrnew ts t'"
  using assms 
  by(simp add: flush_opt_trans_def)

lemma coh_flo:
 assumes "mem_structured ts"
  and "vbounded ts"
and " ts' = flush_opt_trans t x ts"
shows " coh ts' t' y =  coh ts t' y"
 using assms 
  by(simp add: flush_opt_trans_def)
 
lemma mem_flo:
 assumes "mem_structured ts"
  and "vbounded ts"
and " ts' = flush_opt_trans t x ts"
shows " memory ts =  memory ts'"
  using assms 
  by simp

(*rule: After executing a flushopt, the observable  values (OV) for all threads/addresses
remain the same*)
lemma flo_ov_ni: 
  assumes "mem_structured ts"
  and "vbounded ts"
 and  "step t' ( Flush_opt x) ts ts'"
shows "   [y]\<^sub>t ts=  [y]\<^sub>t ts'"
using assms 
  apply (simp add: step_def)
  apply (subgoal_tac " OTS ts t y = OTS ts' t y")
  prefer 2
   apply (subgoal_tac " vrnew ts' t =  vrnew ts t")
    prefer 2
  apply (simp add: vrnew_flo)
  apply (subgoal_tac " coh  ts' t y =  coh  ts t y")
    prefer 2
  using coh_flo apply blast
    apply (subgoal_tac " memory ts = memory ts'")
    prefer 2
  apply simp
   apply (simp add: OTS_def)
   apply (simp add: OTSF_def)
   apply (smt Collect_cong mem_flo notoverwritten_def)
  apply (simp add: mapval_def)
  using assms(3) survived_val_preserved_flushopt by presburger


lemma vpcommit_flo:
 assumes "mem_structured ts"
  and "vbounded ts"
and " ts' = flush_opt_trans t x ts"
shows " vpcommit ts t =  vpcommit ts' t"
  using assms 
  apply (simp add:  flush_opt_trans_def)
  done



lemma vp_commit_flo_gen:
assumes  "mem_structured ts"                                  
and   " ts' = flush_opt_trans t x ts" 
shows " ( \<forall> ti. ( vpcommit ts' ti l =  vpcommit ts ti l)  )"
 using assms
  apply (simp add: flush_opt_trans_def)
  done  


lemma vpasync_flo_daddr:
 assumes "mem_structured ts"
  and "vbounded ts"
and " ts' = flush_opt_trans t x ts"
and " x \<noteq> y"
shows " ( vpasync ts t' y =   vpasync ts' t' y )"
 using assms 
  apply (simp add:  flush_opt_trans_def)
  done


lemma flo_mem: 
assumes  "mem_structured ts"                                  
and " ts' = flush_opt_trans t x ts" 
shows "memory ts = memory ts' "
 using assms
  apply (simp add: flush_opt_trans_def)
  done

lemma maxvp__flo_gen:
 assumes "mem_structured ts"
  and "vbounded ts"
and " ts' = flush_opt_trans t x ts"
shows " (\<forall> t.  maxvp ts t =  maxvp ts' t)"
 using assms 
  apply (simp add:  flush_opt_trans_def)
  done


lemma flo_ots_ni:
  assumes "mem_structured ts"
  and "vbounded ts"
 and  "step t ( Flush_opt x) ts ts'"
shows "    OTS ts t' y  = OTS ts' t' y  "
using assms 
  apply (simp add: step_def)
  apply (subgoal_tac "memory ts = memory ts' ")
  prefer 2
  apply auto[1]
  apply (simp add: OTS_def)
  apply (simp add: OTSF_def notoverwritten_def)
  using coh_flo vrnew_flo by presburger








lemma flo_opts_ni:
  assumes "mem_structured ts"
  and "vbounded ts"
 and  "step t ( Flush_opt x) ts ts'"
shows "    OPTS ts y  = OPTS ts' y  "
using assms 
  apply (simp add: step_def)
  apply (subgoal_tac "memory ts = memory ts' ")
  prefer 2
  apply auto[1]
  apply (subgoal_tac " \<forall> ti.( maxvp ts ti =  maxvp ts' ti) ")
  prefer 2
  using maxvp__flo_gen apply blast
  apply (simp add: OPTS_def)
  by (metis (no_types, lifting) flo_mem notoverwritten_def)

(*rule: After executing a flushopt, the observable persistent  values (OPV) for all addresses
remain the same*)
lemma flo_opv_ni:
  assumes "mem_structured ts"
  and "vbounded ts"
 and  "step t ( Flush_opt x) ts ts'"
shows "   [y]\<^sub>P ts'  =  [y]\<^sub>P ts "
  using assms
  apply (subgoal_tac " OPTS ts y  = OPTS ts' y  ")
   prefer 2
   apply (simp add: flo_opts_ni)
  apply (subgoal_tac " memory ts   = memory ts'  ")
  prefer 2
   apply (simp add: step_def)
  apply (unfold  mapval_def)
  by (metis (no_types, lifting) flo_crash image_cong)



(*rule: flo_oav_ov_rel rule for singleton OV*)
corollary flo_oav_ov_rel_s:
  assumes "mem_structured ts"
  and "vbounded ts"
  and  "step t ( Flush_opt  x ) ts ts'"
  and " OTS ts  t  x\<noteq> {}"
  and  "\<forall>ti l. comploc ( (memory ts)!(coh ts ti l)) l = l"
 and "  [x]\<^sub>t ts = {w} "
 and " (\<forall>  addr t. [addr]\<^sup>A\<^sub>t ts \<noteq> {})"
shows "  [x]\<^sup>A\<^sub>t ts' = {w}"
  using assms
 apply (subgoal_tac "  [x]\<^sup>A\<^sub>t ts' \<noteq> {}")
   prefer 2
  using OAV_notempty_preserved  apply blast
  apply (simp add: step_def )
  by (metis assms(3) assms(5) flo_mem flo_oav_ov_rel subset_singletonD)

lemma flo_oats_sub:
  assumes "mem_structured ts"
  and "vbounded ts"
  and  "step t ( Flush_opt  x ) ts ts'"
shows  "OATS ts' t    x \<subseteq> OATS ts t  x"
  using assms
  apply (simp add: step_def)

  apply (subgoal_tac " memory ts = memory ts' ")
   prefer 2
   apply simp
  apply (subgoal_tac " vpasync ts' t  x \<ge> vpasync ts t x ")
   prefer 2
   apply (simp add: flush_opt_trans_def Let_def)
  apply (simp add: OATS_def )
  by (smt (verit, ccfv_SIG) Collect_mono_iff dual_order.trans flo_mem notoverwritten_def)

(*rule: After a thread t executes a flushopt on x the observable asynchronous values for x might become less.*)
lemma fl_oav_sub:
  assumes "mem_structured ts"
  and "vbounded ts"
  and  "step t ( Flush_opt  x ) ts ts'"
shows  "  [x]\<^sup>A\<^sub>t ts'   \<subseteq>  [x]\<^sup>A\<^sub>t ts"
  using assms
  apply (subgoal_tac " OATS ts' t   x \<subseteq> OATS ts  t  x ")
   prefer 2
   apply (simp add: flo_oats_sub)
 apply (subgoal_tac " memory ts =memory ts' ")
   prefer 2
  apply (simp add: step_def)
  apply (unfold mapval_def)
  by (metis (no_types, lifting) flo_crash image_cong image_mono)

(*rule: The number of writes on address x with value v remain the same after executing a flushopt.*)
lemma  flo_oc_ni : 
  assumes "mem_structured ts"
  and "step t ( Flush_opt y) ts ts'"
  and "vbounded ts"
shows  " \<lparr>x,v\<rparr>  ts' =  \<lparr>x,v\<rparr>  ts "
  using assms
  apply (simp add: step_def)
  apply (simp add:  oc_set_def)
  using assms(2) survived_val_preserved_flushopt by presburger

lemma flo_oats_daddr_ni:
  assumes "mem_structured ts"
  and "vbounded ts"
 and " x \<noteq> y"
  and  "step t ( Flush_opt  x ) ts ts'"
shows  "OATS ts' t'    y = OATS ts t'  y"
  using assms
  apply (simp add: step_def)
 apply (subgoal_tac " memory ts = memory ts' ")
   prefer 2
   apply simp
  apply (subgoal_tac "  vpasync ts t' y =   vpasync ts' t' y")
   prefer 2
  using vpasync_flo_daddr apply blast
  apply (simp add: OATS_def)
  by (metis (no_types, lifting)  flo_mem notoverwritten_def)


(*rule:The set of the asynchronous values for an address y remain the same after a thread executes 
a flushopt on a different address.*)
lemma flo_oav_daddr_ni:
  assumes "mem_structured ts"
  and "vbounded ts"
 and " x \<noteq> y"
  and  "step t' ( Flush_opt  x ) ts ts'"
shows  " [y]\<^sup>A\<^sub>t ts' = [y]\<^sup>A\<^sub>t ts"
  using assms
  apply (subgoal_tac  "OATS ts' t'    y = OATS ts t'  y")
   prefer 2
  apply (simp add: flo_oats_daddr_ni)
  apply (simp add: mapval_def)
 apply (subgoal_tac " memory ts =memory ts' ")
   prefer 2
   apply (simp add: step_def)
  using flo_oats_daddr_ni survived_val_preserved_flushopt by presburger


(*rule: The monotonicity property of glb is preserved after a crash*)
lemma flo_glb_monotonicity_preserved:
 assumes " ( \<forall> i j . ( j \<in> OTS ts ti  glb \<and>  i \<in> OTS ts ti glb \<and>  i \<le> j)  \<longrightarrow> valOf  i glb  ts  \<le> valOf j glb  ts)"
 and "vbounded ts"
and "mem_structured ts"
 and  "step t ( Flush_opt  x ) ts ts'"
shows  " ( \<forall> i j . ( j \<in> OTS ts' ti  glb \<and>  i \<in> OTS ts' ti glb \<and>  i \<le> j)  \<longrightarrow> valOf  i glb  ts'  \<le> valOf j glb  ts')"
  using assms
 apply (subgoal_tac " memory ts = memory ts' ")
   prefer 2
   apply( simp add: step_def)
  apply (subgoal_tac " \<forall> i. valOf  i glb  ts  = valOf  i glb  ts'")
   prefer 2
   apply (metis flo_crash valOf_def)
  apply (subgoal_tac " OTS ts' ti  glb = OTS ts ti  glb")
   prefer 2
  apply( simp add: step_def)
  using assms(4) flo_ots_ni apply blast
  by simp




lemma flo_pm_inv_preserved:
  assumes "mem_structured ts"
  and "vbounded ts"
and   "step t ( Flush_opt  x ) ts ts'"
  and " ( \<forall> addr . ( addr \<noteq> y \<and> addr \<notin> A)  \<longrightarrow> [addr]\<^sub>P ts =  { lastVal  addr  ts  })"
and  "\<forall>ti l. comploc ( (memory ts)!(coh ts ti l)) l = l"
shows "  ( \<forall> addr . ( addr \<noteq> y \<and> addr \<notin> A) \<longrightarrow> [addr]\<^sub>P ts' =  { lastVal  addr  ts'  })  "
 using assms
  apply (subgoal_tac "  \<forall> addr .  [addr]\<^sub>P ts' =  [addr]\<^sub>P ts ")
  prefer 2
  apply (simp add: flo_opv_ni)
  apply (simp add: step_def)
  apply (subgoal_tac "  \<forall> addr . last_entry ts'  addr = last_entry ts  addr")
   prefer 2
   apply (simp add: last_entry_def)
  apply (simp add: last_entry_set_def)
  by (metis assms(3) flo_crash flo_mem lastVal_def)



lemma  flo_wfs_preserved :
  assumes "total_wfs ts"
and   "step t ( Flush_opt  x ) ts ts'"
shows" total_wfs ts'"
  using assms 
  apply (unfold total_wfs_def)
  by (meson OTSF_notempty_preserved coh_loc_rel_preserved le_in_oats le_in_opts le_in_ots lev_in_oav lev_in_opv lev_in_ov mem_structured_preserved total_OTSF_def vbounded_preserved)


lemma  flo_coh_ni :
  assumes  "step t ( Flush_opt  x ) ts ts'"
and " total_wfs ts"
shows"  coh (ts') t' a =  coh (ts) t'  a"
  using assms
  apply (simp add: step_def)
  by (simp add: flush_opt_trans_def)

lemma flo_lastVal_ni :
  assumes  "step t ( Flush_opt  y ) ts ts'"
and " total_wfs ts"
  shows " lastVal x ts' = lastVal x ts " 
  using assms
   apply (subgoal_tac " memory ts' = memory ts ")
  prefer 2
    apply (simp add: step_def)
  apply (simp add: lastVal_def last_entry_def last_entry_set_def )
  using survived_val_preserved_flushopt by force

(*rule: The last entry before the coherence of any location for any thread t' different from t remains the same after t
executes a flushopt*)
lemma flo_le_lim_dt_ni:
assumes "step t ( Flush_opt  y ) ts ts'"
and " total_wfs ts"
and " t \<noteq> t' "
shows " last_entry_lim (ts') b (coh (ts') t' glb) =  last_entry_lim (ts) b (coh (ts) t' glb)"
  using assms
apply (subgoal_tac " memory ts' = memory ts ")
  prefer 2
   apply (simp add: step_def)
  apply (simp add:  last_entry_lim_def last_entry_set_lim_def )
  by (simp add: flo_coh_ni)

(*rule: The above rule lifted to values*)
lemma flo_le_coh_valof_dt_ni:
assumes "step t ( Flush_opt  y ) ts ts'"
and " total_wfs ts"
and " t \<noteq> t' "
shows " valOf (last_entry_lim ts b (coh ts t' glb)) b ts = 
valOf (last_entry_lim ts'  b (coh ts' t' glb)) b ts'"
  using assms
apply (subgoal_tac " memory ts' = memory ts ")
  prefer 2
   apply (simp add: step_def)
  apply (simp add: valOf_def)
  using flo_le_lim_dt_ni survived_val_preserved_flushopt by force

lemma flo_coh_valof_dt_ni:
assumes "step t ( Flush_opt  y ) ts ts'"
and " total_wfs ts"
and " t \<noteq> t' "
shows " valOf (coh ts' t' glb)  b ts' = valOf   (coh ts t' glb) b ts"
  using assms
apply (subgoal_tac " memory ts' = memory ts ")
  prefer 2
   apply (simp add: step_def)
  apply (simp add: valOf_def)
  using flo_coh_ni survived_val_preserved_flushopt by presburger


lemma flo_vrnew_ni:
assumes "step t ( Flush_opt  y ) ts ts'"
and " total_wfs ts"
shows " vrnew ts' t' =   vrnew ts t' "
  using assms
  apply (simp add: step_def)
  by (simp add: flush_opt_trans_def)



lemma  flo_lelim_nle_ni:
   assumes "mem_structured ts"
  and "vbounded ts"
 and "step t ( Flush_opt  y ) ts ts'"
shows "(\<forall> n l. (0 \<le> n \<and> n < length(memory ts' )) \<longrightarrow> valOf (last_entry_lim ts' l n) l (ts')  =    valOf (last_entry_lim ts l n) l ts  ) "
  using assms
  apply (subgoal_tac"memory ts = memory ts' ")
   prefer 2
   apply (simp add: step_def)
  apply (unfold last_entry_lim_def last_entry_set_lim_def)
  by (metis (no_types, lifting) Collect_cong flo_crash valOf_def)


(*All the values of the memory messages remain the same in the post-state of a flushopt*)
lemma  flo_valOf_nle_ni:
   assumes "mem_structured ts"
  and "vbounded ts"
 and "step t ( Flush_opt  y ) ts ts'"
shows "(\<forall> n l. (0 \<le> n \<and> n < length(memory ts' )) \<longrightarrow> valOf (n) l (ts')  =    valOf ( n) l ts  ) "
  using assms
  apply (subgoal_tac"memory ts = memory ts' ")
   prefer 2
   apply (simp add: step_def)
  by (metis flo_crash valOf_def)

lemma  flo_comploc_ni:
   assumes "mem_structured ts"
  and "vbounded ts"
 and "step t ( Flush_opt  y ) ts ts'"
shows "(\<forall> n l. (0 \<le> n \<and> n < length(memory ts' )) \<longrightarrow>  comploc ((memory ts') !n) x  =    comploc ((memory ts) !n) x  )"
  using assms
  by (simp add: step_def)






end