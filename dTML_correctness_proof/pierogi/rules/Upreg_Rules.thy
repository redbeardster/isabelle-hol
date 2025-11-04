theory Upreg_Rules
  imports "../State" "../Language"  "../Assertions"  "../Wellformedness"

begin


lemma  reg_write_mem :
  assumes "ts'  =  update_reg ti  r v   ts  "
  shows "memory ts = memory ts' "
  using assms
  by (simp add:  update_reg_def)


lemma reg_write_lc:
  assumes "ts'  =  update_reg ti  r v   ts  "
  shows "regs ts' ti r = v "
  using assms
  by (simp add:  update_reg_def)


lemma reg_write_OTS_ni:
  assumes "ts'  =   update_reg ti  r v   ts  "
  shows "  OTS ts  t x =   OTS ts'  t x  "
  using assms
  by (simp add:  update_reg_def OTS_def OTSF_def notoverwritten_def)







lemma reg_write_OV_ni:
  assumes "ts'  =  update_reg t  r v   ts  "
  shows "  [l]\<^sub>t' ts =  [l]\<^sub>t'  ts' "
  using assms  reg_write_OTS_ni
  apply (unfold mapval_def)
  using reg_write__crash reg_write_mem by presburger



lemma reg_write_lastVal_ni:
  assumes "ts'  =  update_reg t  r v   ts  "
  shows "  lastVal  l ts =  lastVal  l ts' "
  using assms
  by (simp add:  update_reg_def lastVal_def last_entry_def last_entry_set_def )
  


(*lastVal l (\<tau> \<sigma>)*)

lemma reg_OAV_ni:
  assumes "ts'  =  update_reg t  r v   ts  "
  shows "  [l]\<^sup>A\<^sub>t ts =  [l]\<^sup>A\<^sub>t  ts' "
  using assms
  apply (subgoal_tac "   OATS ts  t l =   OATS ts'  t l ")
   prefer 2
  using  reg_write_mem  apply (simp add:  update_reg_def OATS_def notoverwritten_def)
  apply (simp add: mapval_def)
  using reg_write_mem survived_val_preserved_reg_write by presburger

  
lemma reg_write_pm_preserved : 
  assumes "ts'  =   update_reg ti  r v   ts  "
  and " ( \<forall> addr . (( addr \<noteq> y) \<and> addr \<notin> A) \<longrightarrow>  [addr]\<^sub>P ts =  { lastVal  addr  ts  })"
shows "  ( \<forall> addr . (( addr \<noteq> y) \<and> addr \<notin> A)  \<longrightarrow>  [addr]\<^sub>P ts' =  { lastVal  addr  ts'  })  "
  using assms

  apply (subgoal_tac "  \<forall> addr .  OPTS  ts' addr =    OPTS  ts addr ")
   prefer 2
   apply (simp add: update_reg_def OPTS_def notoverwritten_def )

 apply (subgoal_tac "  \<forall> addr . last_entry ts'  addr = last_entry ts  addr")
   prefer 2
   apply (simp add: last_entry_def)
   apply (simp add: last_entry_set_def update_reg_def)
 apply (subgoal_tac "  \<forall> addr .  [addr]\<^sub>P ts' =  [addr]\<^sub>P ts ")
   prefer 2
   apply (unfold mapval_def  )
   apply (simp add:  update_reg_def)
  apply (unfold lastVal_def update_reg_def compval_def )
  by simp

 
lemma reg_write_glb_monotonicity_preserved : 
  assumes "ts'  =   update_reg ti  r v   ts  "
  and "  ( \<forall> i j . ( j \<in> OTS ts ti  glb \<and>  i \<in> OTS ts ti glb \<and>  i \<le> j)  \<longrightarrow> valOf  i glb  ts  \<le> valOf j glb  ts)"
shows "   ( \<forall> i j . ( j \<in> OTS ts' ti  glb \<and>  i \<in> OTS ts' ti glb \<and>  i \<le> j)  \<longrightarrow> valOf  i glb  ts'  \<le> valOf j glb  ts')  "
  using assms
  apply (subgoal_tac " memory ts = memory ts' ")
   prefer 2
   apply (simp add: update_reg_def)
 apply (subgoal_tac " \<forall> i. valOf  i glb  ts  = valOf  i glb  ts'")
   prefer 2
   apply (simp add: valOf_def)
   apply (meson survived_val_preserved_reg_write)
  by (metis reg_write_OTS_ni)


lemma reg_dt_ni:
  assumes "ts'  =  update_reg t  r v   ts  "
and "t \<noteq> t' "
shows " regs ts' t' = regs ts t' "
  using assms
  by (simp add: update_reg_def)

lemma reg_le_ni:
assumes "\<lceil>x\<rceil>\<^sub>t ts"
and  "ts'  =   update_reg t'  r v   ts  "
shows "\<lceil>x\<rceil>\<^sub>t ts' "
  using assms
  apply (subgoal_tac " last_entry ts' x =  last_entry ts x ")
   prefer 2
  apply (subgoal_tac " memory ts' = memory ts ")
  prefer 2
  using reg_write_mem apply fastforce
  apply (simp add: last_entry_def)
   apply (simp add: last_entry_set_def)
  using reg_write_OTS_ni by presburger


lemma  reg_coh_ni :
  assumes  "ts'  =   update_reg t  r v   ts  "
and " total_wfs ts"
shows"  coh (ts') t' a =  coh (ts) t'  a"
  using assms
  by (simp add: update_reg_def)


lemma  reg_vrnew_ni :
  assumes  "ts'  =   update_reg t  r v   ts  "
and " total_wfs ts"
shows"  vrnew (ts') t'  =  vrnew (ts) t'  "
  using assms
  by (simp add: update_reg_def)



(* last_entry_lim (\<tau> \<sigma>') b (coh (\<tau> \<sigma>') t1 glb*)

lemma reg_coh_lim_dt_ni:
  assumes  "ts'  =   update_reg t  r v   ts  "
and " total_wfs ts"
shows " last_entry_lim (ts') b (coh (ts') t' glb) =  last_entry_lim (ts) b (coh (ts) t' glb)"
  using assms
  apply (subgoal_tac"memory ts = memory ts' ")
   prefer 2
  using reg_write_mem apply blast
  apply (unfold last_entry_lim_def last_entry_set_lim_def)
  using reg_coh_ni by presburger



lemma  upreg_lelim_nle_ni:
   assumes "mem_structured ts"
  and "vbounded ts"
  and "ts'  =   update_reg t  r v   ts  "
shows "(\<forall> n l. (0 \<le> n \<and> n < length(memory ts' )) \<longrightarrow> valOf (last_entry_lim ts' l n) l (ts')  =    valOf (last_entry_lim ts l n) l ts  ) "
  using assms
  apply (subgoal_tac"memory ts = memory ts' ")
   prefer 2
  using reg_write_mem apply blast
  apply (unfold last_entry_lim_def last_entry_set_lim_def)
  by (metis (no_types, lifting) Collect_cong reg_write__crash valOf_def)



lemma  upreg_valOf_nle_ni:
   assumes "mem_structured ts"
  and "vbounded ts"
  and "ts'  =   update_reg t  r v   ts  "
shows "(\<forall> n l. (0 \<le> n \<and> n < length(memory ts' )) \<longrightarrow> valOf (n) l (ts')  =    valOf ( n) l ts  ) "
  using assms
  apply (simp add: valOf_def )
  using reg_write_mem survived_val_preserved_reg_write by presburger





lemma  upreg_comploc_ni:
   assumes "mem_structured ts"
  and "vbounded ts"
  and "ts'  =   update_reg t  r v   ts  "
shows "(\<forall> n l. (0 \<le> n \<and> n < length(memory ts' )) \<longrightarrow>  comploc ((memory ts') !n) x  =    comploc ((memory ts) !n) x  )"
  using assms
  apply (simp)
  using reg_write_mem by presburger



























end