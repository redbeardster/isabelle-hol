theory Sfence_Rules
  imports "../State" "../Language"  "../Assertions"  "../Wellformedness"

begin

(* The lemmas that begin with the  comment "rule: __" are the proof rules regarding the sfence instruction.
   All the other lemmas are auxiliary and are used for proving the proof rules.
   Rules that end with "lc" concern mostly local correctness.
   Rules that end with "ni" concern  mostly  non-interference.
   Rules that end with "gen" concern non-interference and local correctness.
   Rules that end with "rel" concern relations between view sets. *) 

lemma sf_ots_ni:
assumes "mem_structured ts"
and "vbounded ts"
 and  "step t'  (sfence) ts ts'"
shows "   (OTS ts' t y = OTS ts t y)"
 using assms 
    apply (simp add: step_def)
   apply (simp add: OTS_def)
   apply (simp add: OTSF_def)
   apply (subgoal_tac "  coh ts'  t' y =  coh ts  t' y")
    prefer 2
  apply (simp add: sfence_trans_def)
  apply auto[1]
  apply (subgoal_tac "vrnew ts' t = vrnew ts t")
  prefer 2
   apply (simp add: sfence_trans_def)
  apply auto[1]
 apply (subgoal_tac "memory ts'  = memory ts ")
  prefer 2
  apply (simp add: sfence_trans_def)
  apply auto[1]
  apply (simp add: sfence_trans_def notoverwritten_def)
  apply (simp add:  vpcommit_nv_def maxvp_nv_def)
  by force

(*rule: After executing an sfence, the observable  values (OV) for all threads/addresses
remain the same*)
lemma sf_ov_ni:
assumes "mem_structured ts"
and "vbounded ts"
 and  "step t'  (sfence) ts ts'"
shows "   [y]\<^sub>t ts=  [y]\<^sub>t ts'"
 using assms 
  apply (simp add: step_def)
  apply (subgoal_tac "OTS ts' t y = OTS ts t y")
  prefer 2
  using assms(3) sf_ots_ni apply auto[1]
  apply (subgoal_tac " memory ts = memory ts'")
   prefer 2
   apply (simp add: sfence_trans_def)
  apply auto[1]
  apply (simp add: mapval_def )
  by (metis assms(3) survived_val_preserved_sfence)



lemma mem_sfence:
 assumes "mem_structured ts"
  and "vbounded ts"
and " ts' = sfence_trans t nv mnv ts"
shows "memory ts = memory ts' "
  using assms
  apply (simp add: sfence_trans_def)
  done


lemma step_mem_sfence:
 assumes "mem_structured ts"
  and "vbounded ts"
 and  "step t  (sfence) ts ts'"
shows "memory ts = memory ts' "
  using assms
  apply (simp add: step_def)
  using mem_sfence by blast




lemma opts_oats_sf:
 assumes "mem_structured ts"
  and "vbounded ts"
 and  "step t (sfence) ts ts'"
and "OATS ts t  x  \<noteq> {}"
shows " OPTS ts' x \<subseteq> OATS ts t x "
using assms 
  apply (simp add: step_def  vpcommit_nv_def maxvp_nv_def )
  apply (subgoal_tac "\<forall>k.  k \<in> OPTS ts' x \<longrightarrow> k \<in>  OATS ts t x" )
  prefer 2
apply (simp add: OPTS_def OATS_def )
  apply clarify
  apply safe
   apply (subgoal_tac " k = 0 ")
           prefer 2
  using  mem_sfence
             apply (metis antisym_conv3 mem_structured_def not_less0)
  using gr_implies_not0 apply blast

 apply (subgoal_tac " k = 0 ")
           prefer 2
  using  mem_sfence
            apply (metis antisym_conv3 mem_structured_def not_less0)
           apply (subgoal_tac " (vpasync ts t x) \<le> maxvp (sfence_trans t nv mnv ts) x")
            prefer 2
            apply (simp(no_asm) add: sfence_trans_def)
            apply (metis max.cobounded1 max.coboundedI1)
           apply (smt le_trans mem_sfence notoverwritten_def)
          apply auto[1]
         apply auto[1]
        apply auto[1]
       apply (metis mem_sfence)
      apply auto[1]
     apply (metis mem_sfence)
    apply (metis mem_sfence)
  apply (subgoal_tac " (vpasync ts t (loc (memory (sfence_trans t nv mnv ts) ! k)) \<le> 
(maxvp (sfence_trans t nv mnv ts) (loc (memory (sfence_trans t nv mnv ts) ! k))))")
    prefer 2
    apply (simp(no_asm) add: sfence_trans_def)
    apply (metis max.bounded_iff max.cobounded1)

   apply (smt mem_sfence notoverwritten_def order.trans)
  by auto



(*rule: After a thread t executes an sfence, the set of  observable asynchronous
values (OAV) for every address for t, is a subset of its corresponding set of observable values (OV) *)
lemma opv_oav_sf:
 assumes "mem_structured ts"
  and "vbounded ts"
 and  "step t (sfence) ts ts'"
and "OATS ts t  x  \<noteq> {}"
shows "  [x]\<^sub>P ts' \<subseteq>  [x]\<^sup>A\<^sub>t  ts "
  using assms
  apply (subgoal_tac  " OPTS ts' x \<subseteq> OATS ts t x ")
   prefer 2
   apply (simp add: opts_oats_sf)
  apply (subgoal_tac " memory ts = memory ts' ")
   prefer 2
  apply (simp add: step_def)
  apply (meson mem_sfence)
  apply (unfold  mapval_def)
  by (metis (no_types, lifting) image_cong image_mono sfence_crash)


(*rule:  opv_oav_sf for singleton OV  *)
corollary  opv_oav_sf_s:
assumes "mem_structured ts"
  and "vbounded ts"
 and  "step t (sfence) ts ts'"
and "OATS ts t  x  \<noteq> {}"
  and  "\<forall>ti l. comploc ( (memory ts)!(coh ts ti l)) l = l"
 and " (\<forall>  addr . [addr]\<^sub>P ts \<noteq> {})"
and "   [x]\<^sup>A\<^sub>t ts  =  {w}"
shows "  [x]\<^sub>P ts'  =  {w} "
  using assms
apply (subgoal_tac "   [x]\<^sub>P ts' \<noteq> {}")
   prefer 2
  using OPV_notempty_preserved apply blast 
  apply (simp add: step_def )
  by (metis assms(3) opv_oav_sf subset_singletonD)




lemma sf_opts_sub:
  assumes "mem_structured ts"
  and "vbounded ts"
  and  "step t ( sfence ) ts ts'"
shows  "OPTS ts'    x \<subseteq> OPTS ts   x"
  using assms
  apply (simp add: step_def)
  apply (subgoal_tac " memory ts = memory ts' ")
   prefer 2
  using mem_sfence apply blast
  apply (subgoal_tac " maxvp ts' x \<ge> maxvp ts x ")
   prefer 2
   apply (simp add: sfence_trans_def Let_def maxvp_nv_def  vpcommit_nv_def)
  apply fastforce
  apply (simp add: OPTS_def notoverwritten_def)
  by force

(*rule: After executing an  sfence the observable persistent values for any location might become less.*)
lemma sf_opv_sub:
  assumes "mem_structured ts"
  and "vbounded ts"
  and  "step t ( sfence ) ts ts'"
shows  " [x]\<^sub>P ts'   \<subseteq> [x]\<^sub>P ts"
  using assms
  apply (subgoal_tac " OPTS ts'    x \<subseteq> OPTS ts   x ")
   prefer 2
   apply (simp add: sf_opts_sub)
 apply (subgoal_tac " memory ts =memory ts' ")
   prefer 2
   apply (simp add: step_def)
  apply (meson mem_sfence)
  apply (unfold mapval_def)
  by (metis (no_types, lifting) image_cong image_mono sfence_crash)

(*rule: The number of writes on address x with value v remains the same after executing an sfence.*)
lemma  sf_oc_ni : 
  assumes "mem_structured ts"
  and "step t ( sfence) ts ts'"
  and "vbounded ts"
shows  " \<lparr>x,v\<rparr>  ts' =  \<lparr>x,v\<rparr>  ts "
  using assms
  apply (simp add: step_def)
  apply (simp add:  oc_set_def)
  using assms(2) survived_val_preserved_sfence by force

lemma sf_oats_ni:
  assumes "mem_structured ts"
  and "step t ( sfence) ts ts'"
  and "vbounded ts"
shows " OATS ts t' x =  OATS ts' t' x"
  using assms
  apply (simp add: step_def)
  apply (subgoal_tac " memory ts  = memory ts'")
  prefer 2
  using mem_sfence apply blast
  apply (simp add: OATS_def)
  apply (simp add: sfence_trans_def vpcommit_nv_def maxvp_nv_def Let_def)
  by (smt (z3) Collect_cong ext_inject notoverwritten_def surjective update_convs(4) update_convs(5) update_convs(8))


(*rule: An sfence that is executed from a thread t does not affect the set of asynchronous
values that any other thread can observe for any location.*)
lemma sf_oav_ni:
  assumes "mem_structured ts"
  and "step t ( sfence) ts ts'"
  and "vbounded ts"
shows "  [x]\<^sup>A\<^sub>t'  ts =  [x]\<^sup>A\<^sub>t'  ts'"
  using assms
  apply (subgoal_tac  " OATS ts t' x =  OATS ts' t' x")
  prefer 2
   apply (simp add: sf_oats_ni)
  apply (subgoal_tac  " memory ts =  memory ts'")
   prefer 2
  using step_def apply auto[1]
  apply (simp add: mapval_def)
  by (simp add: survived_val_preserved_sfence)



(*rule: The last write of any location y remains the same after an sfence execution*)
lemma sf_last_entry_preserved:
 assumes "mem_structured ts"
 and "vbounded ts"
and "   ts'= sfence_trans ti nv mnv ts"
shows "  last_entry ts'  y = last_entry ts  y"
  using assms
 apply (simp add: last_entry_def)
  apply (subgoal_tac " last_entry_set ts' y = last_entry_set ts y")
   prefer 2
   apply (simp add: last_entry_set_def)
  by simp



lemma sf_pm_inv_preserved:
  assumes "mem_structured ts"
  and "vbounded ts"
  and "step t ( sfence) ts ts'"
  and " ( \<forall> addr . (( addr \<noteq> y)  \<and> addr \<notin> A)  \<longrightarrow> [addr]\<^sub>P ts =  { lastVal  addr  ts  })"
 and "\<forall>  l.   [l]\<^sub>P ts \<noteq> {} "
and  "\<forall>ti l. comploc ( (memory ts)!(coh ts ti l)) l = l" 
shows "  ( \<forall> addr . (( addr \<noteq>y)  \<and> addr \<notin> A )  \<longrightarrow> [addr]\<^sub>P ts' =  { lastVal  addr  ts'  })  "
  using assms
apply (subgoal_tac " \<forall> addr . (( addr \<noteq> y)  \<and> addr \<notin> A)  \<longrightarrow>  [addr]\<^sub>P ts' =  [addr]\<^sub>P ts  ")
   prefer 2
   apply (metis OPV_notempty_preserved assms(1) sf_opv_sub subset_singletonD)

apply (subgoal_tac"  \<forall> addr . (( addr \<noteq> y)  \<and> addr \<notin> A)  \<longrightarrow> lastVal  addr ts = lastVal  addr ts'")
    prefer 2
   apply (subgoal_tac"  \<forall> addr . (( addr \<noteq> y)  \<and> addr \<notin> A)  \<longrightarrow> last_entry ts'  addr = last_entry ts  addr")
    prefer 2
    apply (simp add: step_def)
    apply (meson sf_last_entry_preserved)
   apply (simp add: lastVal_def  )
   apply (subgoal_tac " memory ts = memory ts' ")
    prefer 2
  apply (simp add: step_def)
    apply (meson mem_sfence)
  using survived_val_preserved_sfence apply presburger
  by auto




lemma sf_nlv_ni:
 assumes "mem_structured ts"
 and "vbounded ts"
 and "\<not> \<lceil>glb :l\<rceil> ts"
 and  " ts [sfence]\<^sub>t' ts'"
shows  "\<not> \<lceil>glb :l\<rceil> ts'"
  using assms
  apply (simp add: step_def)
 apply (subgoal_tac "  memory (ts) =  memory (ts') ")
   prefer 2
   apply (simp add: sfence_trans_def)
  apply (metis mem_sfence sfence_trans_def)
  apply simp
  apply (subgoal_tac"  memory (ts) ! last_entry (ts) glb = Init_Msg \<longrightarrow>  memory (ts') ! last_entry (ts') glb = Init_Msg")
   prefer 2
   apply (subgoal_tac " last_entry ts'  l = last_entry ts  l")
    prefer 2
  using sf_last_entry_preserved apply blast
  apply (metis sf_last_entry_preserved)
  by (metis assms(4) sf_last_entry_preserved survived_val_preserved_sfence)




lemma sfence_lastVal_ni :
  assumes "mem_structured ts"
 and "vbounded ts"
 and  " ts [sfence]\<^sub>t' ts'"
shows" \<forall> l ti. lastVal  l ts =  lastVal  l ts' " 
  using assms
  apply (simp add: step_def)
  apply   (simp add: sfence_trans_def lastVal_def last_entry_def last_entry_set_def)
  apply safe
  using assms(3) survived_val_preserved_sfence apply presburger
  apply force
  apply force
  by force


lemma  sf_wfs_preserved :
  assumes "total_wfs ts"
 and  " ts [sfence]\<^sub>t' ts'"
shows" total_wfs ts'"
  using assms 
  apply (unfold total_wfs_def)
  by (meson OTSF_notempty_preserved coh_loc_rel_preserved le_in_oats le_in_opts le_in_ots lev_in_oav lev_in_opv lev_in_ov mem_structured_preserved total_OTSF_def vbounded_preserved)

lemma  sf_coh_ni :
  assumes  " ts [sfence]\<^sub>t ts'"
and " total_wfs ts"
shows"  coh (ts') t' a =  coh (ts) t'  a"
  using assms
  apply (simp add: step_def)
  apply (simp add:sfence_trans_def)
  by fastforce

(*rule: The last entry before any limit  remains the same after t
executes a sfence*)
lemma sf_le_lim_ni :
 assumes "total_wfs ts"
  and  " ts [sfence]\<^sub>t ts'"
shows " last_entry_lim ts' a lim = last_entry_lim ts a lim "
  using assms
  apply (subgoal_tac " memory ts = memory ts' ")
   prefer 2
  apply (simp add: step_mem_sfence total_wfs_def)
  by (simp add: last_entry_lim_def last_entry_set_lim_def)

(*rule: The last entry before the coherence of any location for any thread t' different from t remains the same after t
executes a sfence*)
lemma sf_le_coh_ni:
assumes   " ts [sfence]\<^sub>t ts'"
and " total_wfs ts"
and " t \<noteq> t' "
shows " last_entry_lim (ts') b (coh (ts') t' glb) =  last_entry_lim (ts) b (coh (ts) t' glb)"
  using assms
  by (simp add: sf_coh_ni sf_le_lim_ni)

(*the coherence views for any location of a thread t' different from t  remain the same after t executes an sfence*)
lemma sf_coh_valof_dt_ni:
assumes  " ts [sfence]\<^sub>t ts'" 
and " total_wfs ts"
and " t \<noteq> t' "
shows " valOf (coh ts' t' glb)  b ts' = valOf   (coh ts t' glb) b ts"
  using assms
  apply (unfold total_wfs_def)
  apply (simp add: valOf_def)
  using assms(2) sf_coh_ni step_mem_sfence survived_val_preserved_sfence by presburger

(*the vrnew viewn of a thread t' different from t  remain the same after t executes an sfence*)
lemma sf_vrnew_dt_ni:
assumes  " ts [sfence]\<^sub>t ts'" 
and " total_wfs ts"
and " t \<noteq> t' "
shows " vrnew ts t' =  vrnew ts' t'  "
  using assms
  apply (simp add: step_def )
  apply (simp add: sfence_trans_def Let_def)
  by force











end