theory Mfence_Rules
  imports "../State" "../Language"  "../Assertions"  "../Wellformedness"

begin

(* The lemmas that begin with the  comment "rule: __" are the proof rules regarding the mfence instruction.
   All the other lemmas are auxiliary and are used for proving the proof rules.
   Rules that end with "lc" concern mostly local correctness.
   Rules that end with "ni" concern  mostly  non-interference.
   Rules that end with "gen" concern non-interference and local correctness.
   Rules that end with "rel" concern relations between view sets. *) 


lemma mem_mf:
 assumes "mem_structured ts"
  and "vbounded ts"
and " ts' = mfence_trans t ts"
shows " memory ts =  memory ts'"
  using assms 
  by simp


lemma   mf_ots_ord:
 assumes "mem_structured ts"
  and "vbounded ts"
  and  "step t ( mfence ) ts ts'"
  and " OTS ts  t  x \<noteq> {}" 
  and  "\<forall>ti l. comploc ( (memory ts)!(coh ts ti l)) l = l"
  and "  OTS ts  t'  x = {w} "
  and "  \<lceil>x\<rceil>\<^sub>t' ts"
  and  "\<lceil>MFENCE x\<rceil>\<^sub>t ts " 
shows "   OTS ts' t   x  = {w}"
  using assms
  apply (simp add: step_def)
 apply (simp add : vbounded_def)
   apply (subgoal_tac "  (vrnew ts' t)\<ge> w  ")
   prefer 2
   apply (simp add:  mfence_trans_def)
 apply (subgoal_tac " \<nexists> n.( n \<noteq> w \<and> n < length(memory ts') \<and> n \<in>  OTS ts' t  x)")
   prefer 2
   apply clarify
  apply (simp add: last_entry_def)
    apply (simp add: OTS_def  OTSF_def  )
 apply (case_tac "n > w")
    apply (subgoal_tac "loc ( (memory ts')! n) \<noteq> x")
     prefer 2
  apply (metis assms(2) last_entry_def last_entry_notoverwritten le_refl mem_mf notoverwritten_def)
   apply (simp(no_asm) split: if_splits)
     prefer 2
     apply (metis assms(2) mem_mf)
    apply (subgoal_tac " w \<ge> 0")
     prefer 2
     apply blast
    apply (metis bot.extremum_strict bot.not_eq_extremum bot_nat_def mem_structured_def)
  apply (case_tac " w = 0")
    apply (metis gr0I)
   apply (unfold notoverwritten_def)
  apply (subgoal_tac " memory ts = memory ts'")
  prefer 2
    apply (meson assms(2) mem_mf)
   apply (subgoal_tac "  Max (last_entry_set ts x) < length (memory (flush_trans t x ts))")
    prefer 2
  apply (metis assms(2) assms(6) assms(7) comploc_def last_entry_bounded last_entry_loc less_nat_zero_code linorder_neqE_nat mem_structured_def singleton_inject)
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
  apply blast
    apply (meson mem_structured_def)
   apply (metis assms(2) last_entry_bounded last_entry_def)
 apply (subgoal_tac "w \<in>  OTS ts' t   x  ")
   prefer 2
   apply (subgoal_tac "  last_entry ts x =  last_entry ts' x ")
    prefer 2
    apply (simp add: last_entry_def)
    apply (simp add: last_entry_set_def)
 apply (unfold  OTS_def)
    apply (unfold  OTSF_def)
    apply clarify
    apply (rule_tac x=" last_entry ts' x" in exI)
    apply (rule conjI)
  apply blast
    apply (subgoal_tac"vbounded ts' ")
     prefer 2
  apply (metis assms(2) assms(3) vbounded_preserved)
    apply (subgoal_tac" mem_structured ts' ")
     prefer 2
  apply (metis assms(3) mem_structured_preserved)
    apply (intro conjI impI)
        prefer 5
  using last_entry_notoverwritten apply blast
       apply blast
  using last_entry_bounded apply blast
     apply (metis last_entry_loc)
    apply (subgoal_tac"notoverwritten ts' (vrnew ts' t) (last_entry ts' x) x")
     prefer 2
  using last_entry_notoverwritten apply blast
    apply (simp add: notoverwritten_def)
apply (subgoal_tac " coh ts' t x  < length(memory ts') ")
     prefer 2
          apply (subgoal_tac "vbounded ts'")
      prefer 2
  apply blast
          apply (unfold vbounded_def)
          apply meson
         apply (subgoal_tac " 0 \<le>  coh ts' t x")
          prefer 2
    apply blast

   apply (smt (z3) assms(2) assms(3) coh_loc_rel_preserved comploc_def dual_order.strict_implies_order dual_order.strict_trans1 mem_mf not_le_imp_less order_refl)
  by blast


(*rule: Rule regarding mfence/store ordering*) 
lemma    mf_ov_ord:
 assumes "mem_structured ts"
  and "vbounded ts"
  and  "step t ( mfence ) ts ts'"
  and " OTS ts  t  x \<noteq> {}" 
  and  "\<forall>ti l. comploc ( (memory ts)!(coh ts ti l)) l = l"
   and "  [x]\<^sub>t' ts = {w} "
  and "  \<lceil>x\<rceil>\<^sub>t' ts"
  and  "\<lceil>MFENCE x\<rceil>\<^sub>t ts" 
shows "  [x]\<^sub>t ts'  = {w}"
  using assms
  apply (subgoal_tac "  OTS ts'  t  x =  OTS ts  t'  x")
   prefer 2
  using mf_ots_ord apply blast
  apply (simp add: step_def)
  apply (unfold mapval_def)
  by (metis (no_types, lifting) assms(3) image_cong mfence_crash)
 

lemma mf_opts_ni:
  assumes "mem_structured ts"
  and "vbounded ts"
  and "step t' ( mfence) ts ts'"
shows " OPTS ts'  y  =  OPTS ts y "
using assms 
  apply (simp add: step_def)
  apply (simp add: OPTS_def)
  apply (subgoal_tac " maxvp ts' y  = maxvp ts y ")
  prefer 2
  apply (simp add :mfence_trans_def Let_def)
 apply (subgoal_tac "memory ts  = memory ts' ")
    prefer 2
  using mem_mf apply blast
  by (metis (no_types, lifting) notoverwritten_def)

lemma mf_ots_dt_ni:
  assumes "mem_structured ts"
  and "vbounded ts"
  and "step t' ( mfence) ts ts'"
and "    t \<noteq> t' "
shows " OTS ts' t  y  =  OTS ts t  y "
using assms 
  apply (simp add: step_def)
  apply (subgoal_tac " vrnew ts t = vrnew ts' t ")
  prefer 2
  apply (simp add: mfence_trans_def)
  apply (subgoal_tac " coh ts t y = coh  ts' t y ")
  prefer 2
  apply (simp add: mfence_trans_def)
  apply (subgoal_tac " memory ts = memory ts' ")
  prefer 2
  using mem_mf apply blast
  apply (simp add: OTS_def OTSF_def)
  using notoverwritten_def by auto













(*rule: After executing an mfence, the observable persistent values (OPV) for all addresses
remain the same*)
lemma mf_opv_ni:
  assumes "mem_structured ts"
  and "vbounded ts"
  and "step t' ( mfence) ts ts'"
shows  "   [y]\<^sub>P ts=  [y]\<^sub>P ts'"
  using assms 
 apply (simp add: step_def)
  apply (subgoal_tac " OPTS ts'  y  =  OPTS ts y")
   prefer 2
  using assms(3) mf_opts_ni apply auto[1]
  apply (subgoal_tac " memory ts = memory ts' ")
   prefer 2
  using mem_mf apply blast
  apply (simp add: mapval_def)
  by (metis assms(3) survived_val_preserved_mfence)


lemma    mf_ots_sub:
 assumes "mem_structured ts"
  and "vbounded ts"
  and  "step t' ( mfence ) ts ts'"
shows  "OTS ts' t x   \<subseteq> OTS ts t  x"
 using assms
 apply (simp add: step_def)
apply (subgoal_tac " memory ts = memory ts' ")
   prefer 2
   apply auto[1]
 apply (subgoal_tac " vrnew ts' t \<ge>  vrnew ts t ")
   prefer 2
   apply (simp add: mfence_trans_def Let_def OTS_def OTSF_def notoverwritten_def)
  apply (subgoal_tac "  coh ts t x  \<le> coh ts' t x ")
   prefer 2
   apply (simp add: mfence_trans_def)
  apply (simp add: OTS_def OTSF_def notoverwritten_def)
  using Collect_mono_iff dual_order.trans by force

(*rule: After executing an mfence the observable values for any location might become less.*)
lemma mf_ov_sub:
  assumes "mem_structured ts"
  and "vbounded ts"
  and  "step t' (mfence ) ts ts'"
shows  "[x]\<^sub>t ts'  \<subseteq> [x]\<^sub>t ts"
 using assms
  apply (subgoal_tac " OTS ts'  t  x \<subseteq> OTS ts t   x ")
   prefer 2
   apply (simp add: mf_ots_sub)
 apply (subgoal_tac " memory ts =memory ts' ")
  prefer 2
  apply (simp add: step_def)
  apply (unfold mapval_def)
  by (metis (no_types, lifting) image_cong image_mono mfence_crash)

(*rule: mf_ov_sub rule for singleton ov set*)
corollary   mf_ots_s : 
  assumes "mem_structured ts"
  and "step t' ( mfence) ts ts'"
 and "vbounded ts"
and "  [y]\<^sub>t ts = {w}"
and "  (\<forall> t addr.  [addr]\<^sub>t ts \<noteq> {} )"
and  "\<forall>ti l. comploc ( (memory ts)!(coh ts ti l)) l = l"
shows "  [y]\<^sub>t ts' = {w}"
  using assms
  apply (subgoal_tac "  [y]\<^sub>t ts' \<noteq> {} ")
   prefer 2
   apply (meson OV_notempty_preserved)
 using mf_ov_sub 
  by (metis subset_singletonD)

(*rule: If the OV set of x for thread t contains only the value of the last write at x, it remains the same after a thread t' executes an mfence. *)
corollary   mf_ots_lm_s : 
  assumes "mem_structured ts"
  and "step t' ( mfence) ts ts'"
  and "vbounded ts"
  and  " \<lceil>x\<rceil>\<^sub>t ts "
  and "  (\<forall> t addr.  OTS ts t addr \<noteq> {} )"
  and  "\<forall>ti l. comploc ( (memory ts)!(coh ts ti l)) l = l"
shows  " \<lceil>x\<rceil>\<^sub>t ts' "
  using assms
  apply (simp add: step_def)
  apply (subgoal_tac "  OTS ts' t x  = {last_entry  ts x }")
   prefer 2
  using  mf_ots_sub 
  apply (metis OTS_notempty_preserved assms(2) assms(6) subset_singleton_iff)
 apply(subgoal_tac" last_entry ts x =  last_entry ts' x")
   prefer 2
   apply (simp add: last_entry_def)
   apply (simp add: last_entry_set_def)
  by force

(*rule: The \<lceil>MFENCE y\<rceil> expression still holds for thread t if another thread executes an mfence.*)
lemma   mf_ots_lm_ord_ni : 
  assumes "mem_structured ts"
  and "step t' ( mfence) ts ts'"
  and "vbounded ts"
  and " t' \<noteq> t"
shows " \<lceil>MFENCE y\<rceil>\<^sub>t ts = \<lceil>MFENCE y\<rceil>\<^sub>t ts'  "
  using assms
  apply (simp add: step_def)
   apply(subgoal_tac" last_entry ts y =  last_entry ts' y")
   prefer 2
   apply (simp add: last_entry_def)
   apply (simp add: last_entry_set_def)
  by  (simp add: mfence_trans_def)


(*rule: The number of writes on address x with value v remain the same after executing an mfence.*)
lemma  mf_oc_ni : 
  assumes "mem_structured ts"
  and "step t ( mfence) ts ts'"
  and "vbounded ts"
shows  " \<lparr>x,v\<rparr>  ts' = \<lparr>x,v\<rparr>  ts"
  using assms
  apply (simp add: step_def)
  apply (simp add:  oc_set_def)
  using assms(2) survived_val_preserved_mfence by presburger


lemma mf_last_entry_in_ots :
  assumes "mem_structured ts"
and "vbounded ts"
  and "step t ( mfence) ts ts'"
 and "\<forall> ti l. comploc ( (memory ts)!(coh ts ti l)) l = l"
shows "  last_entry ts' x \<in> OTS ts' t x "
using assms
 apply (subgoal_tac"vbounded ts' ")
     prefer 2
  using vbounded_preserved apply blast
 apply (subgoal_tac" mem_structured ts' ")
   prefer 2
  using mem_structured_preserved apply blast
  apply (simp add: step_def)
apply (unfold  OTS_def)
    apply (unfold  OTSF_def)
  apply clarify
  apply (rule_tac x=" last_entry ts' x" in exI)
 apply (intro conjI impI)
       prefer 6
 using last_entry_notoverwritten apply blast
       apply blast
      apply linarith
  using last_entry_bounded apply blast
 apply (metis last_entry_loc)
 apply (subgoal_tac"notoverwritten ts' (vrnew ts' t) (last_entry ts' x) x")
     prefer 2
  using last_entry_notoverwritten apply blast
apply (subgoal_tac " coh ts' t x  < length(memory ts') ")
     prefer 2
          apply (subgoal_tac "vbounded ts'")
      prefer 2
  apply blast
          apply (unfold vbounded_def)
          apply meson
         apply (subgoal_tac " 0 \<le>  coh ts' t x")
          prefer 2
   apply blast
 apply (subgoal_tac " \<forall> i. i \<in> last_entry_set ts'  x \<longrightarrow> i \<le> last_entry ts' x")
   prefer 2
   apply (simp add: last_entry_def )
   apply (metis Max.in_idem finite_last_entry_set max_def order_refl)
  apply (subgoal_tac " \<forall> i. 0\<le> i \<and> i < length (memory ts') \<and>  comploc ( memory ts'!i) x = x\<longrightarrow>  i \<in> last_entry_set ts'  x ")
   prefer 2
   apply (simp add: last_entry_set_def)
  using assms(2) assms(3) assms(4) coh_loc_rel_preserved by presburger
 


(*rule: If the expression \<lceil>MFENCE x\<rceil> holds for thread t before executing an mfence, then after executing an mfence
the only observable timestamp for x for thread t  is the last write on x.*)
lemma  mf_ov_lc : 
 assumes "mem_structured ts"
  and "step t ( mfence) ts ts'"
  and "vbounded ts"
 and "  (\<forall> t addr.  OTS ts t addr \<noteq> {} )"
  and  "\<forall>ti l. comploc ( (memory ts)!(coh ts ti l)) l = l"
 and  "\<lceil>MFENCE x\<rceil>\<^sub>t ts " 
shows "   OTS ts' t x  = {last_entry  ts x } " 
  using assms
  apply (simp add: step_def)
apply (simp add : vbounded_def)
   apply (subgoal_tac "  (vrnew ts' t)\<ge> last_entry  ts x  ")
   prefer 2
   apply (simp add:  mfence_trans_def)
 apply (subgoal_tac " \<nexists> n.( n \<noteq> last_entry  ts x \<and> n < length(memory ts') \<and> n \<in>  OTS ts' t  x)")
   prefer 2
   apply clarify
  apply (simp add: last_entry_def)
    apply (simp add: OTS_def  OTSF_def  )
 apply (case_tac "n > last_entry  ts x")
    apply (subgoal_tac "loc ( (memory ts')! n) \<noteq> x")
     prefer 2
  apply (metis assms(3) last_entry_notoverwritten mem_mf nat_less_le notoverwritten_def)
   apply (simp(no_asm) split: if_splits)
     prefer 2
  apply (metis assms(3) mem_mf)
    apply (subgoal_tac "  last_entry  ts x \<ge> 0")
     prefer 2
     apply blast
    apply (metis bot.extremum_strict bot.not_eq_extremum bot_nat_def mem_structured_def)
  apply (case_tac "  last_entry  ts x = 0")
  apply (metis last_entry_def neq0_conv)
   apply (unfold notoverwritten_def)
  apply (subgoal_tac " memory ts = memory ts'")
  prefer 2
    apply (meson assms(2) mem_mf)
   apply (subgoal_tac "  Max (last_entry_set ts x) < length (memory (flush_trans t x ts))")
    prefer 2
  apply (metis assms(3) bot_nat_0.extremum_uniqueI comploc_def last_entry_bounded last_entry_def last_entry_loc le_less linorder_neqE_nat mem_mf mem_structured_def)
   apply (subgoal_tac " n < Max (last_entry_set ts x)")
    prefer 2 
  apply (metis last_entry_def linorder_neqE_nat)
   apply (subgoal_tac "  loc (memory ts ! Max (last_entry_set ts x)) = x")
    prefer 2
    apply (subgoal_tac " \<forall> i. i \<in> last_entry_set ts x \<longrightarrow> comploc (memory ts ! i) x = x ")
  prefer 2
     apply (simp(no_asm) add: last_entry_set_def)
    apply (subgoal_tac  "  Max (last_entry_set ts x) \<in> (last_entry_set ts x)")
     prefer 2
  apply (metis assms(3) last_entry_def last_entry_in_last_entry_set)
    apply (subgoal_tac "  comploc (memory ts ! Max (last_entry_set ts x)) x = x")
     prefer 2
     apply meson
 apply (subgoal_tac " Max (last_entry_set ts x) \<noteq> 0")
    prefer 2
  apply linarith
  apply (unfold comploc_def)
  apply (subgoal_tac " memory ts ! Max (last_entry_set ts x) \<noteq>
             Init_Msg ") 
     apply meson
    apply (subgoal_tac " Max (last_entry_set ts x) > 0 \<and> Max (last_entry_set ts x) < length(memory ts)")
  prefer 2
  apply (metis assms(3) bot.extremum_strict bot_nat_def last_entry_bounded last_entry_def neqE)
    apply (meson mem_structured_def)
  apply (meson assms(3) mem_mf)
 apply (subgoal_tac " last_entry ts x \<in>  OTS ts' t   x  ")
   prefer 2
   apply (subgoal_tac "  last_entry ts x =  last_entry ts' x ")
    prefer 2
  apply (metis assms(3) comploc_def gr_implies_not_zero last_entry_bounded last_entry_def last_entry_loc linorder_neqE_nat mem_structured_def)
 apply (unfold  OTS_def)
    apply (unfold  OTSF_def)
    apply clarify
    apply (rule_tac x=" last_entry ts' x" in exI)
    apply (rule conjI)
  apply blast
    apply (subgoal_tac"vbounded ts' ")
     prefer 2
  apply (metis assms(2) assms(3) vbounded_preserved)
    apply (subgoal_tac" mem_structured ts' ")
     prefer 2
  apply (metis assms(2) mem_structured_preserved)
    apply (intro conjI impI)
        prefer 5
  using last_entry_notoverwritten apply blast
       apply blast
  using last_entry_bounded apply blast
     apply (metis last_entry_loc)
    apply (subgoal_tac"notoverwritten ts' (vrnew ts' t) (last_entry ts' x) x")
     prefer 2
  using last_entry_notoverwritten apply blast
  apply (metis le_trans less_or_eq_imp_le linorder_neqE_nat)
apply (subgoal_tac " coh ts' t x  < length(memory ts') ")
     prefer 2
          apply (subgoal_tac "vbounded ts'")
      prefer 2
  using assms(2) assms(3) vbounded_preserved apply presburger
          apply (unfold vbounded_def)
          apply meson
         apply (subgoal_tac " 0 \<le>  coh ts' t x")
          prefer 2
    apply blast
  apply (metis (no_types, lifting) assms(3) bot_nat_0.extremum_uniqueI comploc_def ex_least_nat_le last_entry_bounded last_entry_def last_entry_loc le_less linorder_neqE_nat mem_structured_def)
 apply (subgoal_tac " last_entry ts x \<in>  OTS ts' t   x  ")
   prefer 2
   apply (subgoal_tac "  last_entry ts x =  last_entry ts' x ")
    prefer 2
  apply (metis OTSF_def OTS_def assms(2) assms(3) assms(5) last_entry_bounded mem_structured_preserved mf_last_entry_in_ots vbounded_preserved)
 apply (unfold  OTS_def)
    apply (unfold  OTSF_def)
    apply clarify
    apply (rule_tac x=" last_entry ts' x" in exI)
    apply (rule conjI)
  apply blast
    apply (subgoal_tac"vbounded ts' ")
     prefer 2
  apply (metis assms(2) assms(3) vbounded_preserved)
    apply (subgoal_tac" mem_structured ts' ")
     prefer 2
  apply (metis assms(2) mem_structured_preserved)
    apply (intro conjI impI)
        prefer 5
  using last_entry_notoverwritten apply blast
       apply blast
  using last_entry_bounded apply blast
     apply (metis last_entry_loc)
    apply (subgoal_tac"notoverwritten ts' (vrnew ts' t) (last_entry ts' x) x")
     prefer 2
  using last_entry_notoverwritten apply blast

   apply (smt (verit, ccfv_SIG) OTSF_def OTS_def assms(2) assms(3) assms(5) mem_Collect_eq mf_last_entry_in_ots)

apply (subgoal_tac " coh ts' t x  < length(memory ts') ")
     prefer 2
          apply (subgoal_tac "vbounded ts'")
      prefer 2
  using assms(2) assms(3) vbounded_preserved apply presburger
          apply (unfold vbounded_def)
          apply meson
         apply (subgoal_tac " 0 \<le>  coh ts' t x")
          prefer 2
   apply blast
  by blast


lemma  mf_wfs_preserved :
  assumes "total_wfs ts"
  and "step t ( mfence) ts ts'"
shows" total_wfs ts'"
  using assms 
  apply (unfold total_wfs_def)
  by (meson OTSF_notempty_preserved coh_loc_rel_preserved le_in_oats le_in_opts le_in_ots lev_in_oav lev_in_opv lev_in_ov mem_structured_preserved total_OTSF_def vbounded_preserved)






end










