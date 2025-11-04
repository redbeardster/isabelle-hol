theory Flush_Rules

  imports "../State" "../Language"  "../Assertions"  "../Wellformedness"

begin

(* The lemmas that begin with the  comment "rule: __" are the proof rules regarding the flush instruction.
   All the other lemmas are auxiliary and are used for proving the proof rules.
   Rules that end with "lc" concern mostly local correctness.
   Rules that end with "ni" concern  mostly  non-interference.
   Rules that end with "gen" concern non-interference and local correctness.
   Rules that end with "rel" concern relations between view sets. *) 

lemma fl_opts_ots_rel:
  assumes "mem_structured ts"
  and "vbounded ts"
  and  "step ti ( Flush  x ) ts ts'"
  and " OTS ts  ti  x\<noteq> {}"
 and  "\<forall>ti l. comploc ( (memory ts)!(coh ts ti l)) l = l"
shows "  OPTS ts' x \<subseteq> OTS ts  ti  x " 
using assms 
  apply (simp add: step_def )
  apply (subgoal_tac "\<forall>k.  k \<in> OPTS ts' x \<longrightarrow> k \<in> OTS ts  ti  x" )
  prefer 2
apply (simp add: OPTS_def OTS_def)
  apply (simp add:  OTSF_def notoverwritten_def)
  apply clarify
  apply(intro allI impI conjI, elim conjE)
    apply (subgoal_tac " k = 0")
     prefer 2
  apply (meson mem_structured_def neq0_conv)
    apply simp
  using assms (5) apply simp
      apply (subgoal_tac " coh ts ti x \<le> maxvp (flush_trans ti x ts) x ")
       prefer 2
       apply (simp add:  vbounded_def)
       prefer 2
       apply (meson le_less_trans mem_structured_def neq0_conv)
      apply (subgoal_tac "  coh ts ti x \<le> maxcoh ts ti")
       prefer 2
       apply blast
      apply (subgoal_tac "  maxcoh ts ti \<le>  maxvp (flush_trans ti x ts) x")
       prefer 2
       apply (simp add: flush_trans_def Let_def)
      apply linarith
     apply (subgoal_tac "  vrnew ts ti \<le> maxvp (flush_trans ti x ts) x")
      prefer 2
      apply (subgoal_tac "vrnew ts ti \<le>  maxcoh ts ti")
       prefer 2
  using assms apply (simp add: vbounded_def)
      apply (subgoal_tac "  maxcoh ts ti \<le> maxvp (flush_trans ti x ts) x")
       prefer 2
       apply (simp add: flush_trans_def Let_def)
      apply linarith
     apply simp
 using assms (5) apply simp
      apply (subgoal_tac " coh ts ti x \<le> maxvp (flush_trans ti x ts) x ")
    prefer 2
    apply (subgoal_tac " coh ts ti x \<le>  maxcoh ts ti")
     prefer 2
  using assms(1) vbounded_def apply blast
  using assms(1)  apply (simp add: flush_trans_def Let_def)
    apply (subgoal_tac "comploc (( memory ts)! (coh ts ti x)) x = x")
     prefer 2
  using assms(5) apply blast
     apply( elim conjE)
    apply simp
     apply (simp add: mem_structured_def )
    apply (meson le0 leI le_less_trans)
   apply (subgoal_tac "  vrnew ts ti \<le> maxvp (flush_trans ti x ts) x")
      prefer 2
      apply (subgoal_tac "vrnew ts ti \<le>  maxcoh ts ti")
       prefer 2
  using assms apply (simp add: vbounded_def)
      apply (subgoal_tac "  maxcoh ts ti \<le> maxvp (flush_trans ti x ts) x")
       prefer 2
       apply (simp add: flush_trans_def Let_def)
      apply linarith
   apply simp
  by (simp add: subsetI)


lemma fl_oats_ots_rel:
  assumes "mem_structured ts"
  and "vbounded ts"
  and  "step ti ( Flush x ) ts ts'"
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
  apply (metis mem_structured_def neq0_conv)
    apply simp
 apply (subgoal_tac " coh ts ti x \<le>  vpasync (flush_trans ti x ts) ti x ")
       prefer 2
       apply (subgoal_tac "  vpasync  (flush_trans ti x ts) ti x \<ge>  maxcoh ts ti")
  prefer 2
        apply (simp add: flush_trans_def Let_def)
       apply (subgoal_tac "coh ts ti x \<le> maxcoh ts ti")
        prefer 2
  using assms(2) vbounded_def apply blast
       apply linarith
      apply (meson dual_order.strict_trans2 mem_structured_def neq0_conv)
  apply simp
  apply (subgoal_tac " vrnew ts ti \<le>  vpasync ts' ti x")
      prefer 2
 apply (subgoal_tac "vrnew ts ti \<le>  maxcoh ts ti")
       prefer 2
  using assms apply (simp add: vbounded_def)
  apply (subgoal_tac "  vpasync  (flush_trans ti x ts) ti x \<ge>  maxcoh ts ti")
  prefer 2
       apply (simp add: flush_trans_def Let_def)
  using dual_order.trans apply blast
  using dual_order.trans apply blast
 apply (subgoal_tac " coh ts ti x \<le>  vpasync (flush_trans ti x ts) ti x ")
     prefer 2
  apply (subgoal_tac "  vpasync  (flush_trans ti x ts) ti x \<ge>  maxcoh ts ti")
  prefer 2
        apply (simp add: flush_trans_def Let_def)
       apply (subgoal_tac "coh ts ti x \<le> maxcoh ts ti")
        prefer 2
  using assms(2) vbounded_def apply blast
  apply linarith
 apply (subgoal_tac "comploc (( memory ts)! (coh ts ti x)) x = x")
     prefer 2
  using assms(5) apply blast
     apply( elim conjE)
    apply simp
     apply (simp add: mem_structured_def )
    apply (meson le0 leI le_less_trans)
   apply (subgoal_tac " vrnew ts ti \<le>  vpasync ts' ti x")
      prefer 2
 apply (subgoal_tac "vrnew ts ti \<le>  maxcoh ts ti")
       prefer 2
  using assms apply (simp add: vbounded_def)
  apply (subgoal_tac "  vpasync  (flush_trans ti x ts) ti x \<ge>  maxcoh ts ti")
  prefer 2
       apply (simp add: flush_trans_def Let_def)
  using dual_order.trans apply blast
  using dual_order.trans apply blast
  by (simp add: subsetI)


lemma fl_opts_sub:
  assumes "mem_structured ts"
  and "vbounded ts"
  and  "step t ( Flush  x ) ts ts'"
shows  "OPTS ts'    x \<subseteq> OPTS ts   x"
  using assms
  apply (simp add: step_def)
  apply (subgoal_tac " memory ts = memory ts' ")
   prefer 2
   apply simp
  apply (subgoal_tac " maxvp ts' x \<ge> maxvp ts x ")
   prefer 2
   apply (simp add: flush_trans_def Let_def)
  apply (simp add: OPTS_def notoverwritten_def)
  by force
 
(*rule: After a thread t executes a flush on address x the observable persistent values for x might become less.*)
lemma fl_opv_sub:
  assumes "mem_structured ts"
  and "vbounded ts"
  and  "step t ( Flush  x ) ts ts'"
shows  " [x]\<^sub>P ts'   \<subseteq> [x]\<^sub>P ts"
  using assms
  apply (subgoal_tac " OPTS ts'    x \<subseteq> OPTS ts   x ")
   prefer 2
   apply (simp add: fl_opts_sub)
 apply (subgoal_tac " memory ts =memory ts' ")
   prefer 2
   apply (simp add: step_def)
  apply (subgoal_tac " \<forall>i.  compval ts (( memory ts)!i) x  =  compval ts' (( memory ts)!i) x ")
   prefer 2
   apply (simp add: compval_def)
   apply (subgoal_tac " survived_val ts x = survived_val ts' x")
    prefer 2
    apply (simp add: step_def)
    apply (simp add: flush_trans_def)
  apply (metis (no_types, lifting) select_convs(9) surjective update_convs(5) update_convs(6) update_convs(8))
  apply simp
  apply (simp add: mapval_def)
  by blast
  


(*rule: After a thread t executes a flush on address x, the set of its observable asynchronous
values (OAV) of  x for t, is a subset of the set of its observable values (OV) *)
lemma fl_oav_ov_rel:
  assumes "mem_structured ts"
  and "vbounded ts"
  and  "step t ( Flush  x ) ts ts'"
  and " OTS ts  t  x\<noteq> {}"
  and  "\<forall>ti l. comploc ( (memory ts)!(coh ts ti l)) l = l"
shows "  [x]\<^sup>A\<^sub>t ts'  \<subseteq>  [x]\<^sub>t ts"
  using assms
 apply (simp add: step_def )
  apply (subgoal_tac " OATS ts' t  x \<subseteq> OTS ts  t  x" )
   prefer 2
  using assms(3) assms(5) fl_oats_ots_rel apply blast
  apply (subgoal_tac " memory ts = memory ts' ")
   prefer 2
   apply (simp add: step_def)
  apply (subgoal_tac " \<forall>i.  compval ts (( memory ts)!i) x  =  compval ts' (( memory ts)!i) x ")
   prefer 2
   apply (subgoal_tac " survived_val ts x = survived_val ts' x")
    prefer 2
    apply (simp add: flush_trans_def)
    apply (metis (no_types, lifting) select_convs(9) surjective update_convs(5) update_convs(6) update_convs(8))
  apply (metis compval_def)
  apply (unfold mapval_def)
  by (metis (no_types, lifting) image_cong image_mono)

lemma [simp]:
 assumes "mem_structured ts"
and "i = 0"
shows "(memory ts ) ! i =  Init_Msg"
  using assms
  apply (simp add: mem_structured_def vbounded_def )
  done 

lemma vrnew_fl:
 assumes "mem_structured ts"
  and "vbounded ts"
and " ts' = flush_trans t x ts"
shows " vrnew ts' t' =  vrnew ts t'"
  using assms 
  apply(simp add: flush_trans_def)
  by (metis (no_types, lifting) ext_inject surjective update_convs(5) update_convs(6) update_convs(8))


lemma coh_fl:
 assumes "mem_structured ts"
  and "vbounded ts"
and " ts' = flush_trans t x ts"
shows " coh ts' t' y =  coh ts t' y"
 using assms 
  apply(simp add: flush_trans_def)
  by (metis (no_types, lifting) ext_inject surjective update_convs(5) update_convs(6) update_convs(8))


lemma mem_fl:
 assumes "mem_structured ts"
  and "vbounded ts"
and " ts' = flush_trans t x ts"
shows " memory ts =  memory ts'"
  using assms 
  by simp


lemma fl_ots_ni:
 assumes "mem_structured ts"
  and "vbounded ts"
 and  "step t' ( Flush x) ts ts'"
shows " OTS ts t y = OTS ts' t y" 
using assms 
  apply (simp add: step_def)
   apply (subgoal_tac " vrnew ts' t =  vrnew ts t")
    prefer 2
  apply (simp add: vrnew_fl)
  apply (subgoal_tac " coh  ts' t y =  coh  ts t y")
    prefer 2
  using coh_fl apply blast
    apply (subgoal_tac " memory ts = memory ts'")
    prefer 2
  apply simp
   apply (simp add: OTS_def)
   apply (simp add: OTSF_def)
  using mem_fl notoverwritten_def by presburger




(*rule: After executing a flush, the observable  values (OV) for all threads/addresses
remain the same*)
lemma fl_ov_ni: 
  assumes "mem_structured ts"
  and "vbounded ts"
 and  "step t' ( Flush x) ts ts'"
shows "   [y]\<^sub>t ts=  [y]\<^sub>t ts'"
 using assms 
  apply (simp add: step_def)
  apply (subgoal_tac " OTS ts t y = OTS ts' t y")
  prefer 2
  using assms(3) fl_ots_ni apply blast
  apply (simp add: mapval_def)
  using assms(3) survived_val_preserved_flush by force
 


lemma fl_opts_daddr_ni: 
  assumes "mem_structured ts"
  and "vbounded ts"
 and "x \<noteq> y"
 and  "step t ( Flush x) ts ts'"
shows " OPTS ts'  y  =  OPTS ts y "
  using assms 
  apply (simp add: step_def)
  apply  (subgoal_tac " maxvp ts' y  = maxvp ts y ")
   prefer 2
   apply (simp add: flush_trans_def)
   apply (smt (z3) ext_inject fun_upd_other surjective update_convs(8))
  apply (unfold OPTS_def)
  by (metis (no_types, lifting)  mem_fl notoverwritten_def)


(*rule: After executing a flush, the observable persistent values (OPV) of addresses 
 different from the newly flushed address remain the same*)
lemma fl_opv_daddr_ni: 
  assumes "mem_structured ts"
  and "vbounded ts"
  and  "x \<noteq> y"
 and  "step t ( Flush x) ts ts'"
shows " [y]\<^sub>P ts=  [y]\<^sub>P ts'"
using assms 
  apply (simp add: step_def)
  apply (simp add: mapval_def)
  using assms(4) fl_opts_daddr_ni survived_val_preserved_flush by presburger


(*rule: After a thread t executes a flush on address x, the set of  observable persistent
values (OPV) of x for t, is a subset of the set of its observable values (OV) *)
lemma fl_opv_ov_rel:
  assumes "mem_structured ts"
  and "vbounded ts"
  and  "step t ( Flush  x ) ts ts'"
  and " OTS ts  t  x\<noteq> {}"
  and  "\<forall>ti l. comploc ( (memory ts)!(coh ts ti l)) l = l"
shows "  [x]\<^sub>P ts'  \<subseteq>  [x]\<^sub>t ts"
using assms 
  apply (simp add: step_def )
  apply (subgoal_tac " OPTS ts' x \<subseteq> OTS ts  t  x" )
  prefer 2
  using assms(3) assms(5) fl_opts_ots_rel apply blast
  apply (subgoal_tac "memory ts = memory ts' ")
   prefer 2
  using mem_fl apply blast
  apply (subgoal_tac " survived_val ts x = survived_val ts' x")
   prefer 2
  using assms(3) survived_val_preserved_flush apply presburger
  apply (unfold mapval_def)
  by (metis (no_types, lifting) assms(3) fl_crash image_cong image_mono)

(*rule:  fl_opv_ov_rel rule for singleton OV set*)
corollary   fl_opv_ov_rel_s:
 assumes "mem_structured ts"
  and "vbounded ts"
  and  "step t ( Flush  x ) ts ts'"
  and " OTS ts  t  x\<noteq> {}" 
  and  "\<forall>ti l. comploc ( (memory ts)!(coh ts ti l)) l = l"
 and "  [x]\<^sub>t ts = {w} "
 and " (\<forall>  addr. [addr]\<^sub>P ts \<noteq> {})"
shows "  [x]\<^sub>P ts' = {w}"
using assms
  apply (subgoal_tac " [x]\<^sub>P ts' \<noteq> {}")
  prefer 2
  using  OPV_notempty_preserved apply blast
  apply (simp add: step_def )
  by (metis assms(3) assms(5) fl_opv_ov_rel mem_fl subset_singletonD)

(*rule:  fl_oav_ov_rel rule for singleton OV set*)
corollary fl_oav_ov_rel_s:
  assumes "mem_structured ts"
  and "vbounded ts"
  and  "step t ( Flush  x ) ts ts'"
  and " OTS ts  t  x\<noteq> {}"
  and  "\<forall>ti l. comploc ( (memory ts)!(coh ts ti l)) l = l"
 and "  [x]\<^sub>t ts = {w} "
 and " (\<forall>  addr t. [addr]\<^sup>A\<^sub>t ts \<noteq> {})"
shows "  [x]\<^sup>A\<^sub>t ts'  =  {w}"
  using assms
apply (subgoal_tac "  [x]\<^sup>A\<^sub>t ts' \<noteq> {}")
   prefer 2
  using OAV_notempty_preserved  apply blast
  apply (simp add: step_def )
  by (metis assms(3) assms(5) fl_oav_ov_rel mem_fl subset_singletonD)

(*rule: After executing a flush, the last store of all addresses 
remain the same*)
lemma fl_ots_lm_ni:
  assumes "mem_structured ts"
  and "vbounded ts"
  and  "step t ( Flush  x ) ts ts'"
(*  and "x \<noteq> y"*)
  and "  \<lceil>y\<rceil>\<^sub>t'  ts "
shows "  \<lceil>y\<rceil>\<^sub>t'  ts'  "
  using assms
  apply (simp add: step_def)
apply (subgoal_tac "  OTS ts' t' y = OTS ts t' y")
   prefer 2
 apply (subgoal_tac " vrnew ts' t =  vrnew ts t")
    prefer 2
  apply (simp add: vrnew_fl)
  apply (subgoal_tac " coh  ts' t y =  coh  ts t y")
    prefer 2
  using coh_fl apply blast
    apply (subgoal_tac " memory ts = memory ts'")
    prefer 2
  apply simp
   apply (simp add: OTS_def)
   apply (simp add: OTSF_def)

  apply (smt (verit, ccfv_SIG) Collect_cong coh_fl mem_fl notoverwritten_def vrnew_fl)
  apply (subgoal_tac " last_entry ts y = last_entry ts' y")
   prefer 2 
   apply (simp add: last_entry_def)
   apply (simp add: last_entry_set_def)
  by auto

lemma   fl_ots_opts_ord:
 assumes "mem_structured ts"
  and "vbounded ts"
  and  "step t ( Flush  x ) ts ts'"
  and " OTS ts  t  x \<noteq> {}" 
  and  "\<forall>ti l. comploc ( (memory ts)!(coh ts ti l)) l = l"
  and "  OTS ts  t'  x = {w} "
  and "  \<lceil>x\<rceil>\<^sub>t' ts"
  and  "\<lceil>FLUSH x\<rceil>\<^sub>t ts " 
shows "   OPTS ts'    x  = {w}"
  using assms
 apply (simp add : step_def)
  apply (simp add : vbounded_def)
   apply (subgoal_tac "  (maxvp ts' x)\<ge> w  ")
    prefer 2
   apply (simp add: flush_trans_def Let_def )
 apply (subgoal_tac " \<nexists> n.( n \<noteq> w \<and> n < length(memory ts') \<and> n \<in>  OPTS ts'  x)")
   prefer 2
   apply clarify
  apply (simp add: last_entry_def)
    apply (simp add: OPTS_def)
   apply (case_tac "n > w")
    apply (subgoal_tac "loc ( (memory ts')! n) \<noteq> x")
     prefer 2
     apply (metis assms(2) last_entry_def last_entry_notoverwritten le_refl mem_fl notoverwritten_def)
    apply (simp(no_asm) split: if_splits)
  prefer 2
  apply (metis assms(2) mem_fl)
    apply (subgoal_tac " w \<ge> 0")
     prefer 2
     apply blast
    apply (metis bot.extremum_strict bot.not_eq_extremum bot_nat_def mem_structured_def)
   apply (case_tac " w = 0")
    apply (metis gr0I)
  apply (unfold notoverwritten_def)
  
   apply (subgoal_tac " memory ts = memory ts'")
  prefer 2
    apply (meson assms(2) mem_fl)
   apply (subgoal_tac "  Max (last_entry_set ts x) < length (memory (flush_trans t x ts))")
    prefer 2
    apply (metis assms(2) last_entry_bounded last_entry_def )
   apply (subgoal_tac " n < Max (last_entry_set ts x)")
    prefer 2 
    apply linarith
   apply (subgoal_tac "  loc (memory ts ! Max (last_entry_set ts x)) = x")
    prefer 2
    apply (subgoal_tac " \<forall> i. i \<in> last_entry_set ts x \<longrightarrow> comploc (memory ts ! i) x = x ")
  prefer 2
     apply (simp(no_asm) add: last_entry_set_def)
    apply (subgoal_tac  "  Max (last_entry_set ts x) \<in> (last_entry_set ts x)")
     prefer 2
     apply (metis assms(2) last_entry_def last_entry_in_last_entry_set)
    apply (subgoal_tac "  comploc (memory ts ! Max (last_entry_set ts x)) x = x")
     prefer 2
     apply meson
 apply (subgoal_tac " Max (last_entry_set ts x) \<noteq> 0")
    prefer 2
     apply blast
  apply (unfold comploc_def)
  apply (subgoal_tac " memory ts ! Max (last_entry_set ts x) \<noteq>
             Init_Msg ") 
     apply meson
    apply (subgoal_tac " Max (last_entry_set ts x) > 0 \<and> Max (last_entry_set ts x) < length(memory ts)")
  prefer 2
     apply (metis not_gr_zero)
    apply (meson mem_structured_def)
   apply (metis)
 apply (subgoal_tac "w \<in>  OPTS ts'    x  ")
   prefer 2
   apply (unfold OPTS_def)
   apply clarify
   apply (rule_tac x=" last_entry ts x " in exI)
   apply (intro conjI)
       apply blast
      apply blast
     apply (metis assms(2) last_entry_bounded mem_fl)
  apply (metis assms(2) last_entry_loc mem_fl)
   apply (simp add: notoverwritten_def)
   apply (meson assms(2) last_entry_notoverwritten notoverwritten_def)
 apply (subgoal_tac " \<forall>k . k \<in>  OPTS ts'    x  \<longrightarrow> k < length(memory ts)")
   prefer 2
   apply (simp add: OPTS_def) 
  apply simp
  by (smt (verit, best) Collect_cong singleton_conv) 


(*rule: Rule regarding flush/store ordering*) 
lemma   fl_ov_opv_ord:
 assumes "mem_structured ts"
  and "vbounded ts"
  and  "step t ( Flush  x ) ts ts'"
  and " OTS ts  t  x \<noteq> {}" 
  and  "\<forall>ti l. comploc ( (memory ts)!(coh ts ti l)) l = l"
   and "  [x]\<^sub>t' ts = {w} "
  and "  \<lceil>x\<rceil>\<^sub>t' ts"
  and  "\<lceil>FLUSH x\<rceil>\<^sub>t ts " 
shows "  [x]\<^sub>P ts'  = {w}"
  using assms
  apply (subgoal_tac "  OTS ts  t'  x =  OPTS ts'  x")
   prefer 2
  using fl_ots_opts_ord apply blast
  apply (simp add: step_def)
 apply (simp add: mapval_def)
  using assms(3) survived_val_preserved_flush by force

(*rule: Rule regarding flush/store ordering *) 
lemma fl_ord_ni:
 assumes "mem_structured ts"
  and "vbounded ts"
  and  "step t' ( Flush  x ) ts ts'"
  and  "\<lceil>FLUSH y\<rceil>\<^sub>t ts "
shows  "\<lceil>FLUSH y\<rceil>\<^sub>t ts' "
  using assms
  apply (simp add: step_def)
 (* apply (simp add: last_entry_def)*)
  apply (subgoal_tac " last_entry ts' y =  last_entry ts y")
  prefer 2
  apply (subgoal_tac " last_entry_set ts' y =  last_entry_set ts y")
   prefer 2
   apply (subgoal_tac " memory ts = memory ts' ")
  prefer 2
  apply (meson mem_fl)
    apply (simp add: last_entry_set_def)
   apply (simp add: last_entry_def)
  apply (subgoal_tac " maxcoh ts t \<le> maxcoh ts' t")
   prefer 2
   apply (simp add: flush_trans_def)
  apply (metis (no_types, lifting) eq_iff ext_inject surjective update_convs(5) update_convs(6) update_convs(8))
  apply (simp add: last_entry_def)

  apply (subgoal_tac " maxvp ts y  \<le> maxvp ts' y")
   prefer 2
   apply (simp add: flush_trans_def Let_def)

  apply (subgoal_tac " vpcommit ts t y \<le> vpcommit ts' t y")
   prefer 2
   apply (simp add: flush_trans_def Let_def)
  by  simp


(*rule: After a thread t executes a flush on y the number of stores on y with value v remains the same.*)
lemma  fl_oc_ni : 
  assumes "mem_structured ts"
  and "step t ( Flush y) ts ts'"
  and "vbounded ts"
shows  " \<lparr>x,v\<rparr> ts' = \<lparr>x,v\<rparr>  ts"
  using assms
  apply (simp add: step_def)
  apply (simp add:  oc_set_def)
  using assms(2) survived_val_preserved_flush by presburger


(*rule: The value of the last write on x remains the same after a flush.*)
lemma fl_lv_lc:
  assumes "mem_structured ts"
 and "vbounded ts"
  and "step t ( Flush y) ts ts'"
shows " \<lceil>x:v\<rceil> ts' =  \<lceil>x:v\<rceil> ts  "
  using assms
  apply (simp add: step_def)
  apply (subgoal_tac " memory ts = memory ts' ")
   prefer 2
  apply auto[1]
  apply (subgoal_tac " last_entry ts x = last_entry ts' x")
   prefer 2
   apply (simp add: last_entry_def)
   apply (simp add: last_entry_set_def)
  using assms(3) survived_val_preserved_flush by presburger



lemma fl_last_entry_init_message_ni:
 assumes "mem_structured ts"
 and "vbounded ts"
and "memory ts ! last_entry ts lx \<noteq> Init_Msg "
 and "step t ( Flush y) ts ts'"
shows "memory ts' ! last_entry ts' lx \<noteq> Init_Msg "
  using assms
  apply (simp add: step_def)
  apply (subgoal_tac " last_entry ts lx = last_entry ts' lx ")
   prefer 2
   apply (simp add: last_entry_def)
   apply (simp add: last_entry_set_def)
  by simp

lemma fl_last_entry_val_ni:
 assumes "mem_structured ts"
 and "vbounded ts"
and "val (memory ts ! last_entry ts lx) = z"
 and "step t ( Flush y) ts ts'"
shows "val (memory ts' ! last_entry ts' lx) = z "
 using assms
  apply (simp add: step_def)
  apply (subgoal_tac " last_entry ts lx = last_entry ts' lx ")
   prefer 2
   apply (simp add: last_entry_def)
   apply (simp add: last_entry_set_def)
 by simp

lemma  fl_wfs_preserved :
  assumes "total_wfs ts"
 and "step t ( Flush y) ts ts'"
shows" total_wfs ts'"
  using assms 
  apply (unfold total_wfs_def)
  by (meson OTSF_notempty_preserved coh_loc_rel_preserved le_in_oats le_in_opts le_in_ots lev_in_oav lev_in_opv lev_in_ov mem_structured_preserved total_OTSF_def vbounded_preserved)





end


