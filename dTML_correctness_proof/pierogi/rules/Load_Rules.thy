theory Load_Rules
  imports "../State" "../Language"  "../Assertions"  "../Wellformedness"
begin

(* The lemmas that begin with the  comment "rule: __" are the proof rules regarding the load  instruction.
   All the other lemmas are auxiliary and are used for proving the proof rules.
   Rules that end with "lc" concern mostly local correctness.
   Rules that end with "ni" concern  mostly  non-interference.
   Rules that end with "gen" concern non-interference and local correctness.
   Rules that end with "rel" concern relations between view sets. *) 


lemma mem_ld:
 assumes "mem_structured ts"
  and "vbounded ts"
and " ts' = load_trans t ind x  ts r"
shows " memory ts =  memory ts'"
  using assms 
  by simp

lemma t :
  assumes " a = {x}"
  shows " a \<subseteq> {x,y}"
  using assms
  by simp


(*rule: A thread can only read values at address x that belong to its set of observable values for x (OV)*)
lemma ld_ov_lc:
  assumes "mem_structured ts"
 and "step t ( Load x r) ts ts'"
shows "regs ts' t r \<in> [x]\<^sub>t ts "
  using assms apply (simp add:  step_def load_trans_def Let_def  mem_structured_def  mapval_def )
  apply clarify
  apply (subgoal_tac " ind \<in> OTS ts t x")
   prefer 2
   apply blast
  apply (subgoal_tac " compval ts  ((memory ts)!ind) x \<in> [x]\<^sub>t ts")
   prefer 2
   apply (metis mapval_def rev_image_eqI)
  apply (simp add: load_trans_def)
  by force


lemma coh_lc:
  assumes "mem_structured ts"
 and "vbounded ts"
 and "step t ( Load l r) ts ts'"
 and  "\<forall>ti l. comploc ( (memory ts)!(coh ts ti l)) l = l"
shows " coh ts' t l \<in> OTS ts' t l \<and> (\<forall>i . i \<in> OTS ts' t l \<longrightarrow> coh ts' t l \<le> i)  "
  using assms apply (simp add:  step_def mem_structured_def   )
 apply (intro conjI)
   apply (unfold OTS_def OTSF_def)
   apply clarify
   apply (rule_tac x="  coh ts' t l" in exI)
   apply (intro conjI)
        apply blast
       apply blast
      apply (subgoal_tac " vbounded ts' ")
  prefer 2
  using assms(3) vbounded_preserved apply presburger
      apply (simp add: vbounded_def)
  using assms(1) assms(3) assms(4) coh_loc_rel_preserved apply presburger
    apply blast
   apply (simp add: load_trans_def notoverwritten_def)
  apply (metis leD le_max_iff_disj)
  by fastforce

(*rule: A thread can only read values at address x that belong to its set of observable values for x (OV)*)
lemma ld_ov'_lc:
  assumes "mem_structured ts"
 and "vbounded ts"
 and "step t ( Load x r) ts ts'"
 and  "\<forall>ti l. comploc ( (memory ts)!(coh ts ti l)) l = l"
shows "regs ts' t r \<in> [x]\<^sub>t ts' "
  using assms 
  apply (subgoal_tac "  coh ts' t x \<in> OTS ts' t x ")
   prefer 2
   apply (simp add: coh_lc)
  apply (subgoal_tac " compval ts  ((memory ts')! coh ts' t x) x = regs ts' t r")
   prefer 2
  apply (simp add: step_def load_trans_def Let_def)
   apply force
  apply (simp add: mapval_def )
  using  survived_val_preserved_load
  by (smt (verit, ccfv_SIG) IntI image_iff mem_Collect_eq)

lemma reg_coh_lc:
  assumes "mem_structured ts"
 and "vbounded ts"
 and "step t ( Load x r) ts ts'"
 and  "\<forall>ti l. comploc ( (memory ts)!(coh ts ti l)) l = l"
shows "compval ts'  ((memory ts')! coh ts' t x) x = regs ts' t r "
  using assms
  apply (subgoal_tac "  coh ts' t x \<in> OTS ts' t x ")
   prefer 2
   apply (simp add: coh_lc)
   apply (simp add: step_def load_trans_def Let_def)
  by force



lemma ld_cobts_lc : 
  assumes "mem_structured ts"
  and "step t ( Load x r) ts ts'"
 and "vbounded ts"
 and "   regs ts' t r = v "
  and " x \<noteq> y"
 and  "  COBTS x y v t ts = S "
shows "  OTS ts' t y \<subseteq> S"
  using assms
  apply (simp add: step_def )
  apply clarify
  apply (subgoal_tac "compval ts' (memory ts' ! ind) x = v")
   prefer 2
   apply (simp add: load_trans_def)
  apply (subgoal_tac " OTSF ts t y (compvrnew ts t ind x)   = OTS ts' t y ")
   prefer 2
   apply (subgoal_tac " compvrnew ts t ind x = vrnew ts' t ")
    prefer 2
    apply (simp add: compvrnew_def load_trans_def)
  using max.commute apply blast

  apply (simp add: load_trans_def)
   apply (simp add: OTS_def  mem_structured_def OTSF_def notoverwritten_def )
  apply (simp add: COBTS_def cond_ts_def)
  using assms(2) survived_val_preserved_load by fastforce
   

lemma ld_cobts_lc_aux : 
  assumes "mem_structured ts"
  and "step t ( Load x r) ts ts'"
 and "vbounded ts"
 and "   regs ts' t r = v "
 and  "  COBTS x x v t ts = S "
shows "  OTS ts' t x \<subseteq> S"
  using assms
  apply (simp add: step_def )
  apply clarify
  apply (subgoal_tac "compval ts' (memory ts' ! ind) x = v")
   prefer 2
   apply (simp add: load_trans_def)
  apply (subgoal_tac " OTSF ts t x (compvrnew ts t ind x)   = OTS ts' t x ")
   prefer 2
   apply (subgoal_tac " compvrnew ts t ind x = vrnew ts' t ")
    prefer 2
    apply (simp add: compvrnew_def load_trans_def)
  using max.commute apply blast
    apply (simp add: load_trans_def)
   apply (simp add: OTS_def  mem_structured_def OTSF_def notoverwritten_def )
   apply safe

  apply (metis gr0I le_eq_less_or_eq max.cobounded2 nat_neq_iff)
         apply (metis (no_types, lifting) bot_nat_0.not_eq_extremum eq_imp_le max.coboundedI2)
        apply (metis leI max.cobounded1 max.commute)
  apply (metis bot_nat_0.not_eq_extremum eq_imp_le less_nat_zero_code max.coboundedI2 not_le_imp_less)
  using order.trans apply linarith
     apply (meson le_trans)
  using order.trans apply linarith
  using le_trans apply linarith
 apply (simp add: COBTS_def cond_ts_def)
  using assms(2) survived_val_preserved_load by fastforce

(*rule: Transfer rule for conditional observation*)
lemma ld_cobv_lc : 
  assumes "mem_structured ts"
 and "step t ( Load x r) ts ts'"
 and " \<langle>x  v\<rangle>[y]\<^sub>t  ts = S"
and "vbounded ts"
and  " regs ts' t r = v  "
shows "  [y]\<^sub>t  ts' \<subseteq>  S"
 using assms
  apply (simp add: step_def )
  apply (subgoal_tac "  OTS ts' t y \<subseteq>   COBTS x y v t ts ")
  prefer 2
  using ld_cobts_lc 
   apply (metis assms(2) ld_cobts_lc_aux) 
  apply (unfold mapval_def)

  by (metis (no_types, lifting) assms(2) assms(4) image_cong ld_crash mem_ld subset_image_iff)
(*  by (smt (z3) PowD PowI assms(2) image_Pow_surj image_cong image_iff ld_crash mem_ld) *)



lemma mem_ld_trans :
  assumes " ts' = load_trans t' ind y ts r"
  shows " memory ts = memory ts'"
  using assms 
  by (simp add: load_trans_def)
 

lemma coh_ld :
  assumes " ts' = load_trans t' ind y ts r"
and "t \<noteq> t'"
  shows " coh ts t y = coh ts' t y"
  using assms 
  apply (simp add: load_trans_def)
  done

lemma coh_ld_dif :
  assumes " ts' = load_trans t' ind y ts r"
and "t \<noteq> t'"
and "x \<noteq> y'"
  shows " coh ts t x = coh ts' t x"
  using assms 
  apply (simp add: load_trans_def)
  done
 


lemma ld_ots_ni:
  assumes "mem_structured ts"
  and "vbounded ts"
 and "t \<noteq> t'"
  and "step t' ( Load x r) ts ts'"
shows "   OTS ts t y = OTS ts' t y"
  using assms 
  apply (simp add: step_def)
  apply (subgoal_tac " OTS ts t y = OTS ts' t y")
  prefer 2
  apply (case_tac " x= y")
    apply (simp add: OTS_def  )
    apply (subgoal_tac " vrnew ts t = vrnew ts' t")
     prefer 2
     apply (simp add: load_trans_def)
     apply auto[1]
apply (simp add: OTSF_def)
    apply (subgoal_tac "memory ts = memory ts'")
    prefer 2
  using mem_ld apply blast
  apply (subgoal_tac " coh ts t y =  coh ts' t y")
  prefer 2
     apply (metis coh_ld_dif)
    apply (smt Collect_cong notoverwritten_def)
   apply (simp add: OTS_def)
 apply (subgoal_tac " vrnew ts t = vrnew ts' t")
     prefer 2
     apply (simp add: load_trans_def)
    apply auto[1]
apply (simp add: OTSF_def)
    apply (subgoal_tac "memory ts = memory ts'")
    prefer 2
  using mem_ld apply blast
  apply (subgoal_tac " coh ts t y =  coh ts' t y")
  prefer 2
    apply (metis coh_ld_dif)
  using notoverwritten_def apply presburger
  by auto


(*rule: After a thread t executes a load of address x, the observable values (OV) for x
remain the same for threads different from t.*)
lemma ld_ov_ni:
  assumes "mem_structured ts"
  and "vbounded ts"
 and "t \<noteq> t'"
  and "step t' ( Load x r) ts ts'"
shows "    [y]\<^sub>t ts  =   [y]\<^sub>t ts'"
  using assms 
  apply (simp add: step_def)
  apply (subgoal_tac " OTS ts t y = OTS ts' t y")
   prefer 2
  using assms(4) ld_ots_ni apply blast
  apply (simp add: mapval_def)
  using assms(4) survived_val_preserved_load by force

(*the coherence of the read value is remaining the same or increasing*)
lemma coh_ld_st_sadrr :
   assumes "mem_structured ts"
  and "vbounded ts"
  and "step t ( Load y r) ts ts'"
  shows " coh ts t y  \<le> coh ts' t y"
  using assms 
   apply (simp add: step_def)
  apply (simp add: load_trans_def Let_def)
  apply clarify
  apply (case_tac "ind = coh ts t y")
   apply simp
  apply (simp add: OTS_def)
  apply (simp add: OTSF_def)
  done

(*the coherence view for thread t of any location apart from the one that t reads, remains the same*)
lemma coh_ld_st_dadrr: 
   assumes "mem_structured ts"
  and "vbounded ts"
  and "step t ( Load x r) ts ts'"
   and " x \<noteq> y"
 shows " coh ts t y  = coh ts' t y"
  using assms 
   apply (simp add: step_def)
  apply (simp add: load_trans_def Let_def)
    apply clarify
  apply (case_tac "ind = coh ts t y")
 apply simp
 apply (simp add: OTS_def)
  done

(*the vrnew  view of the thread that performs a load remains the same, or increase*)
lemma vrnew_ld_st_sadrr :
   assumes "mem_structured ts"
  and "vbounded ts"
  and "step t ( Load y r) ts ts'"
shows " vrnew ts t'   \<le> vrnew  ts' t' "
 using assms 
   apply (simp add: step_def)
  apply (simp add: load_trans_def Let_def)
  apply clarify
  apply (case_tac" t  = t' ")
  apply (case_tac "ind = coh ts t y")
  apply simp
  apply (simp add: OTS_def)
  apply (subgoal_tac "  vrnew ts t'   = vrnew  ts' t'")
  prefer 2
  apply (simp add: load_trans_def Let_def)
  by force



(*rule: If a  value k is not included to the observable values (OV) for 
address y  for a thread,it will also not be included after executing a load *)
lemma ld_nov_ni:
  assumes "mem_structured ts"
  and "vbounded ts"
  and "step t' ( Load x r) ts ts'"
  and "  k\<notin>  [y]\<^sub>t ts  "
shows "  k\<notin>  [y]\<^sub>t ts'"
 using assms 
  apply (simp add: step_def)
  apply (case_tac "t = t'")
  prefer 2
  using assms(3) ld_ov_ni apply blast
  apply (subgoal_tac" OTS ts' t' y \<subseteq> OTS ts t' y")
   prefer 2
  apply (case_tac" x = y")
   apply (subgoal_tac " coh ts t' y \<le> coh ts' t' y")
     prefer 2
  using assms(3) coh_ld_st_sadrr apply auto[1]
    apply (subgoal_tac "  vrnew ts t'   \<le> vrnew  ts' t' ")
     prefer 2
  using assms(3) vrnew_ld_st_sadrr apply blast
    apply (simp add: OTS_def )
    apply (simp add: OTSF_def notoverwritten_def )
    apply (subgoal_tac "  memory ts   =  memory  ts' ")
     prefer 2
  using mem_ld apply blast            
    apply clarify
  apply (intro conjI impI)
  apply presburger
  apply linarith
  apply (metis order_trans)
  apply presburger
  apply presburger
  apply linarith
    apply (metis order_trans) 
  apply (subgoal_tac " coh ts t' y = coh ts' t' y")
    prefer 2
  using assms(3) coh_ld_st_dadrr apply auto[1]
 apply (subgoal_tac "  vrnew ts t'   \<le> vrnew  ts' t' ")
    prefer 2
  using assms(3) vrnew_ld_st_sadrr apply auto[1]
  apply (simp add: OTS_def )
    apply (simp add: OTSF_def notoverwritten_def )
    apply (subgoal_tac "  memory ts   =  memory  ts' ")
     prefer 2
  using mem_ld apply blast 
  apply clarify
   apply (intro conjI impI)
         apply presburger
        apply blast
       apply (metis order_trans)
      apply presburger
     apply presburger
    apply linarith
   apply (metis order_trans)
  apply (subgoal_tac " \<forall>i.  i \<notin> OTS ts t' y \<longrightarrow>  i \<notin> OTS ts' t' y ")
  prefer 2
   apply auto[1]
  apply (unfold mapval_def)
  by (smt (z3) assms(3) image_iff ld_crash mem_ld)


corollary   ld_cobts_lc_s : 
  assumes "mem_structured ts"
  and "step t ( Load x r) ts ts'"
 and "vbounded ts"
 and "   regs ts' t r = v "
  and " x \<noteq> y"
 and  "  COBTS x y v t ts = {w} "
and "  (\<forall> ti addr. OTS   ts ti  addr \<noteq> {} )"
and  "\<forall>ti l. comploc ( (memory ts)!(coh ts ti l)) l = l"
shows "  OTS ts' t y = {w}"
 using assms
  apply (simp add: step_def )
  apply (subgoal_tac" OTS ts' t y \<noteq> {}")
  prefer 2
  using OTS_notempty_preserved assms(2) assms(8) apply blast
  using assms(2) ld_cobts_lc by blast

(*rule: Transfer rule for conditional observation when OV is singleton*)
corollary  ld_cobv_lc_s : 
 assumes "mem_structured ts"
 and "step t ( Load x r) ts ts'"
 and " \<langle>x  v\<rangle>[y]\<^sub>t  ts = {w}"
and "vbounded ts"
and " x \<noteq> y"
and  " regs ts' t r = v  "
and  "\<forall>ti l. comploc ( (memory ts)!(coh ts ti l)) l = l"
 and " (\<forall> ti addr.[addr]\<^sub>ti ts \<noteq> {} )" 
shows "  [y]\<^sub>t  ts' =  {w}"
 using assms
  apply (simp add: step_def )
  apply (subgoal_tac" [y]\<^sub>t ts' \<noteq> {}")
  prefer 2
  using OV_notempty_preserved assms(2) assms(7) apply blast
  using assms(2) ld_cobv_lc by blast


lemma ld_ots_sub:
  assumes "mem_structured ts"
  and "vbounded ts"
  and  "step t ( Load  y r ) ts ts'"
shows  "OTS ts' t' x   \<subseteq> OTS ts t'  x"
  using assms
 apply (simp add: step_def)
apply (subgoal_tac " memory ts = memory ts' ")
   prefer 2
   apply auto[1]
 apply (subgoal_tac " vrnew ts' t \<ge>  vrnew ts t ")
   prefer 2
   apply (simp add: load_trans_def Let_def OTS_def OTSF_def notoverwritten_def)
   apply (meson assms(3) vrnew_ld_st_sadrr)
  apply (subgoal_tac "  coh ts t x  \<le> coh ts' t x ")
   prefer 2
  apply (metis assms(3) coh_ld_st_dadrr coh_ld_st_sadrr eq_refl)
  apply (simp add: OTS_def OTSF_def notoverwritten_def)
  apply safe
         apply (metis coh_ld_dif dual_order.trans)
  apply (simp add: load_trans_def split:if_splits)
  apply (metis coh_ld_dif dual_order.trans)
  apply (simp add: load_trans_def split:if_splits)
  using max.coboundedI1 apply blast
  apply blast
  apply (metis max.coboundedI2 max.commute)
  apply blast
  apply blast
  apply blast
  apply (metis coh_ld_dif dual_order.trans)
  apply (simp add: load_trans_def split:if_splits)
  apply (metis coh_ld_dif dual_order.trans)
  by (simp add: load_trans_def split:if_splits)


(*rule: After reading an  address x the observable values for any location might become less.*)
lemma ld_ov_sub:
  assumes "mem_structured ts"
  and "vbounded ts"
  and  "step t ( Load  y r ) ts ts'"
shows  "[x]\<^sub>t' ts'  \<subseteq> [x]\<^sub>t' ts"
 using assms
  apply (subgoal_tac " OTS ts'  t'  x \<subseteq> OTS ts t'   x ")
   prefer 2
   apply (simp add: ld_ots_sub)
 apply (subgoal_tac " memory ts =memory ts' ")
  prefer 2
  apply (simp add: step_def)
  apply (meson mem_ld)
  apply (unfold  mapval_def)
  by (metis (no_types, lifting) image_cong image_mono ld_crash)

(*rule: Same rule for sinlgeton OV. *)
corollary ld_ov_sub_s:
  assumes "mem_structured ts"
  and "vbounded ts"
  and  "step t ( Load  y r ) ts ts'"
and "  [x]\<^sub>t' ts = {w}"
and "  (\<forall> t addr.  [addr]\<^sub>t ts \<noteq> {} )"
and  "\<forall>ti l. comploc ( (memory ts)!(coh ts ti l)) l = l"
shows  "[x]\<^sub>t' ts'  = [x]\<^sub>t' ts"
  using assms
  by (metis OV_notempty_preserved ld_ov_sub subset_singleton_iff)



(*The vpasync view of any address and step remains the same*)
lemma ldstep_vpasync:
assumes "step t' ( Load x r) ts ts'"
shows   " vpasync ts' t y =  vpasync ts t y"
  using assms
  apply (simp add: step_def )
  apply (simp add: load_trans_def)
  by auto

lemma ld_opts_ni:
  assumes "mem_structured ts"
  and "vbounded ts"
  and "step t' ( Load x r) ts ts'"
shows " OPTS ts'  y  =  OPTS ts y "
using assms 
  apply (simp add: step_def)
  apply (simp add: OPTS_def)
  apply (subgoal_tac " maxvp ts' y  = maxvp ts y ")
  prefer 2
  apply (simp add :load_trans_def Let_def)
  using select_convs(8) apply auto[1]
 apply (subgoal_tac "memory ts  = memory ts' ")
    prefer 2
  using mem_ld apply blast
  by (metis (no_types, lifting) notoverwritten_def)

lemma ld_oats_ni:
  assumes "mem_structured ts"
  and "vbounded ts"
  and "step t' ( Load x r) ts ts'"
shows " OATS ts' t  y  =  OATS ts t  y "
using assms 
  apply (simp add: step_def)
  apply (simp add: OATS_def)
  apply (subgoal_tac " vpasync ts' t y =  vpasync ts t y")
  prefer 2
  using assms(3) ldstep_vpasync apply blast
  apply (subgoal_tac "memory ts = memory ts'")
   prefer 2
  using mem_ld apply blast
  by (metis (no_types, lifting)  notoverwritten_def)


(*rule: After executing a load, the observable persistent values (OPV) for all addresses
remain the same.*)
lemma ld_opv_ni:
  assumes "mem_structured ts"
  and "vbounded ts"
  and "step t' ( Load x r) ts ts'"
shows  "   [y]\<^sub>P ts=  [y]\<^sub>P ts'"
  using assms 
 apply (simp add: step_def)
  apply (subgoal_tac " OPTS ts'  y  =  OPTS ts y")
   prefer 2
  using assms(3) ld_opts_ni apply auto[1]
  apply (subgoal_tac " memory ts = memory ts' ")
   prefer 2
  using mem_ld apply blast
  apply (unfold mapval_def)
  using assms(3) ld_crash by force

(*rule: After executing a load, the observable asynchronous values (OAV) for all adresses/threads
remain the same.*)
lemma ld_oav_ni:
  assumes "mem_structured ts"
  and "vbounded ts"
  and "step t' ( Load x r) ts ts'"
shows "   [y]\<^sup>A\<^sub>t ts =  [y]\<^sup>A\<^sub>t ts'"
  using assms
 apply (simp add: step_def)
  apply (subgoal_tac " OATS ts' t  y  =  OATS ts t  y")
   prefer 2
  using assms(3) ld_oats_ni apply auto[1]
  apply (simp add: mapval_def)
  using assms(3) survived_val_preserved_load by force




(*rule: The \<lceil>MFENCE y\<rceil> expression still holds after executing a load.*)
lemma ld_m_ord_ni:
 assumes "mem_structured ts"
  and "vbounded ts"
  and  "step t' ( Load  x r ) ts ts'"
  and "\<lceil>MFENCE y\<rceil>\<^sub>t ts"
shows  "\<lceil>MFENCE y\<rceil>\<^sub>t ts'  "
  using assms
  apply (simp add: step_def) apply (case_tac "t \<noteq> t'")
  apply (subgoal_tac " maxcoh ts' t = maxcoh ts t")
  prefer 2
   apply (simp add: load_trans_def Let_def)
   apply force
apply (subgoal_tac " vrnew ts' t = vrnew ts t")
   prefer 2
 apply (simp add: load_trans_def Let_def)
   apply force
  apply (subgoal_tac " last_entry ts' y = last_entry ts y")
  apply simp
  apply (simp add: last_entry_def)
  apply (simp add: last_entry_set_def)
   apply (metis mem_ld)
  apply (subgoal_tac " maxcoh ts' t \<ge> maxcoh ts t")
  prefer 2
   apply (simp add: load_trans_def Let_def)
  apply force
apply (subgoal_tac " vrnew ts' t \<ge> vrnew ts t")
   prefer 2
 apply (simp add: load_trans_def Let_def)
  using assms(3) vrnew_ld_st_sadrr apply presburger  
  apply (simp add: last_entry_def)
  apply (simp add: last_entry_set_def)
  apply safe
  using dual_order.trans le_max_iff_disj mem_ld by presburger


corollary   ld_ots_s : 
  assumes "mem_structured ts"
  and "step t ( Load x r) ts ts'"
 and "vbounded ts"
and "  [y]\<^sub>t ts = {w}"
and "  (\<forall> t addr.  [addr]\<^sub>t ts \<noteq> {} )"
and  "\<forall>ti l. comploc ( (memory ts)!(coh ts ti l)) l = l"
shows "  [y]\<^sub>t ts' = {w}"
  using assms
  apply (subgoal_tac "  [y]\<^sub>t ts' \<noteq> {} ")
   prefer 2
   apply (meson OV_notempty_preserved)
 using ld_ov_sub 
  using ld_nov_ni by fastforce


(*rule: If the OV set of x contains only the value of the last write at x, it remains the same after executing a load. *)
corollary  ld_ots_lm_s : 
  assumes "mem_structured ts"
  and "step t ( Load y r) ts ts'"
  and "vbounded ts"
  and  " \<lceil>x\<rceil>\<^sub>t' ts "
  and "  (\<forall> t addr.  OTS ts t addr \<noteq> {} )"
  and  "\<forall>ti l. comploc ( (memory ts)!(coh ts ti l)) l = l"
shows  " \<lceil>x\<rceil>\<^sub>t' ts' "
  using assms
  apply (simp add: step_def)
  apply (subgoal_tac "  OTS ts' t' x  = {last_entry  ts x }")
   prefer 2 
  using  ld_ots_sub[where ts=ts and ts'=ts' and t=t] 
  apply (metis OTS_notempty_preserved assms(2) assms(6) subset_singleton_iff)
 apply(subgoal_tac" last_entry ts x =  last_entry ts' x")
   prefer 2
   apply (simp add: last_entry_def)
   apply (simp add: last_entry_set_def)
  apply (metis mem_ld)
  by force


(*rule: The number of writes on address x with value v remain the same after executing a load.*)
lemma  ld_oc_ni : 
  assumes "mem_structured ts"
  and "step t ( Load y r) ts ts'"
  and "vbounded ts"
shows  " \<lparr>x,v\<rparr>  ts' = \<lparr>x,v\<rparr>  ts "
  using assms
  apply (simp add: step_def)
  apply (simp add:  oc_set_def)
  using assms(2) survived_val_preserved_load by fastforce
 


lemma ld_last_entry_in_ots :
  assumes "mem_structured ts"
and "vbounded ts"
 and "step t ( Load x r) ts ts'"
 and  "\<forall>ti l. comploc ( (memory ts)!(coh ts ti l)) l = l"
shows "  last_entry ts' x \<in> OTS ts' t x "
  using assms
  apply (simp add: step_def)
apply (unfold  OTS_def)
    apply (unfold  OTSF_def)
    apply clarify
    apply (rule_tac x=" last_entry ts' x" in exI)
    apply (rule conjI)
  apply blast
    apply (subgoal_tac"vbounded ts' ")
     prefer 2
  using assms(3) vbounded_preserved apply blast
    apply (subgoal_tac" mem_structured ts' ")
     prefer 2
  using assms(3) mem_structured_preserved apply blast
    apply (intro conjI impI)
        prefer 5
  using last_entry_notoverwritten apply blast
       apply blast
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


lemma ld_last_entry :
  assumes "mem_structured ts"
and "vbounded ts"
 and "step t ( Load x r) ts ts'"
shows  " (last_entry ts x)  =  (last_entry ts' x) " 
  using assms
  apply (simp add: step_def)
 apply (simp add: last_entry_def last_entry_set_def )
  by (metis mem_ld)


(*If the OV set for  address x of a thread t' contains only the last write on x and the value of this 
write is v,  and a thread t reads this value on x, then the OV set of x for t after executing the load contains only
the value v. *)
lemma ld_ov_oc_lm_lc :
  assumes "mem_structured ts"
and "vbounded ts"
 and "step t ( Load x r) ts ts'"
and   " \<lparr>x,v\<rparr>  ts = 1"
and  " regs ts' t r = v "
and  " [x]\<^sub>t' ts = {v} "
 and  " \<lceil>x\<rceil>\<^sub>t' ts "
 and  "\<forall>ti l. comploc ( (memory ts)!(coh ts ti l)) l = l"
shows " [x]\<^sub>t  ts' ={v} "
  using assms
 apply (subgoal_tac "  last_entry ts'  x \<in>   OTS ts' t x ")
   prefer 2
  using ld_last_entry_in_ots apply blast
 apply (subgoal_tac "  last_entry ts'  x =   last_entry ts  x ")
   prefer 2
  apply (simp add: ld_last_entry)
  apply (simp add: step_def)
  apply (subgoal_tac " OTS ts' t x  = { last_entry ts  x} ")
  prefer 2
   apply (simp add: OTS_def)
 apply (subgoal_tac " \<nexists> j. ( 0 \<le> j \<and> j < length (memory ts) \<and> compval ts (memory ts ! j) x = v \<and> comploc (memory ts ! j) x = x \<and>( j \<noteq> last_entry ts  x) )")
      prefer 2
    apply simp
    apply (subgoal_tac "comploc (memory ts! (last_entry ts x)) x = x")
     prefer 2
  using last_entry_loc apply blast
     apply (subgoal_tac "compval ts (memory ts! (last_entry ts x)) x  = v")
    prefer 2
     apply (simp add: mapval_def)
     apply fastforce
    apply (simp add:  oc_set_def)
  apply (smt (verit, ccfv_threshold) all_not_in_conv card_1_singleton_iff insert_iff last_entry_bounded mem_Collect_eq)
    apply (elim exE)
    apply (subgoal_tac " ind = last_entry ts  x")
     prefer 2
    apply (simp add: load_trans_def Let_def)
    apply (simp add: OTSF_def)
   apply (subgoal_tac " coh ts' t x =  last_entry ts  x")
  prefer 2
    apply (simp add: load_trans_def Let_def)
   apply (subgoal_tac " \<forall> i.( ( 0 \<le> i \<and> i < length (memory ts')) \<and> comploc (memory ts'!i)  x = x) \<longrightarrow> i \<le> last_entry ts'  x")
    prefer 2
    apply (simp add: last_entry_def)
    apply (simp add: last_entry_set_def)
 apply (unfold OTSF_def)
  apply (smt (verit, ccfv_SIG) Collect_cong le_antisym mem_Collect_eq singleton_iff)
  apply (unfold mapval_def)
  by (metis (no_types, lifting) assms(3) image_empty image_insert ld_crash mem_ld)


(*rule: If there is only one write on x, then this is certainly the last write, and when  a thread t reads it, its view  for x becomes maximal*)
lemma ld_ov_oc_lm_lc_two:
  assumes "mem_structured ts"
and "vbounded ts"
and "total_wfs ts"
 and "step t ( Load x r) ts ts'"
and   " \<lparr>x,v\<rparr>  ts = 1"
and  " regs ts' t r = v "
and  " [x]\<^sub>t' ts = {v} "
 (*d  " \<lceil>x\<rceil>\<^sub>t' ts "*)
 and  "\<forall>ti l. comploc ( (memory ts)!(coh ts ti l)) l = l"
shows " [x]\<^sub>t  ts' ={v} "
  using assms
 apply (subgoal_tac "  last_entry ts'  x \<in>   OTS ts' t x ")
   prefer 2
  using ld_last_entry_in_ots apply blast
 apply (subgoal_tac "  last_entry ts'  x =   last_entry ts  x ")
   prefer 2
  apply (simp add: ld_last_entry)
  apply (simp add: step_def)
   apply (simp add: OTS_def)
 apply (subgoal_tac " \<nexists> j. ( 0 \<le> j \<and> j < length (memory ts) \<and> compval ts (memory ts ! j) x = v \<and> comploc (memory ts ! j) x = x \<and>( j \<noteq> last_entry ts  x) )")
      prefer 2
    apply simp
    apply (subgoal_tac "comploc (memory ts! (last_entry ts x)) x = x")
     prefer 2
  using last_entry_loc apply blast
     apply (subgoal_tac "compval ts (memory ts! (last_entry ts x)) x  = v")
     prefer 2
     apply (simp add: total_wfs_def)
  apply (metis assms(7) compval_def lastVal_def singletonD)

   apply (simp add:  oc_set_def)
  apply (smt (verit, ccfv_threshold) all_not_in_conv card_1_singleton_iff insert_iff last_entry_bounded mem_Collect_eq)
    apply (elim exE)
    apply (subgoal_tac " ind = last_entry ts  x")
     prefer 2
    apply (simp add: load_trans_def Let_def)
    apply (simp add: OTSF_def)
   apply (subgoal_tac " coh ts' t x =  last_entry ts  x")
    prefer 2
   apply (subgoal_tac " \<forall> i.( ( 0 \<le> i \<and> i < length (memory ts')) \<and> comploc (memory ts'!i)  x = x) \<longrightarrow> i \<le> last_entry ts'  x")
    prefer 2
    apply (simp add: last_entry_def)
     apply (simp add: last_entry_set_def)
  apply (smt (verit) assms(4) assms(8) coh_lc coh_loc_rel_preserved last_entry_bounded ld_crash ld_last_entry_in_ots le_0_eq mem_ld nle_le order.strict_trans1 reg_coh_lc)
  apply (subgoal_tac "   \<lceil>x\<rceil>\<^sub>t' ts  ")
    prefer 2
apply (subgoal_tac " \<forall> i.( ( 0 \<le> i \<and> i < length (memory ts')) \<and> comploc (memory ts'!i)  x = x) \<longrightarrow> i \<le> last_entry ts'  x")
    prefer 2
    apply (simp add: last_entry_def)
     apply (simp add: last_entry_set_def)

  apply (subgoal_tac "  compval ts (memory ts ! ( last_entry ts x )) x = v ")
     prefer 2
     apply (metis assms(4) assms(8) ld_crash mem_ld reg_coh_lc)

  apply (subgoal_tac " mapval ts x (OTSF ts t' x (vrnew ts t')) (memory ts) = { compval ts (memory ts ! ( last_entry ts x )) x}  ")
     prefer 2
     apply presburger

    apply(subgoal_tac "\<forall> j. ( 0 \<le> j \<and> j < length (memory ts') \<and> compval ts' (memory ts' ! j) x = v \<and>  comploc (memory ts' ! j) x = x)  \<longrightarrow>  j =  last_entry ts'  x ")
     prefer 2
  apply (metis assms(4) ld_crash mem_ld)
    apply (subgoal_tac "\<forall> i. i \<in>  (OTSF ts t' x (vrnew ts t'))    \<longrightarrow> i  =  last_entry ts  x  ")
     prefer 2
  apply (subgoal_tac   "\<forall> i. i \<in>  (OTSF ts t' x (vrnew ts t')) \<longrightarrow>  ( 0 \<le> i \<and> i < length (memory ts')\<and>  comploc (memory ts ! i) x = x)  ")
      prefer 2
    apply (simp add:  OTSF_def OTS_def  mapval_def)

   apply (subgoal_tac"      mapval ts x (OTSF ts t' x (vrnew ts t')) (memory ts) = { compval ts (memory ts ! ( last_entry ts x )) x   }")
      prefer 2
  apply (metis OTS_def assms(4) assms(7) compval_def mem_ld survived_val_preserved_load)

  apply (subgoal_tac   "\<forall> i. i \<in>  (OTS  ts t' x)  \<longrightarrow>  ( compval ts (memory ts ! i) x \<in>   [x]\<^sub>t' ts ) ") 
      prefer 2
    apply (simp  add:  mapval_def)
        apply (metis OTS_def mem_ld singletonD)
        apply (metis OTS_def card_1_singletonE insert_absorb is_singletonI' is_singleton_altdef singleton_insert_inj_eq' total_wfs_def)
        by (metis OTS_def assms(4) assms(5) assms(8) ld_ov_oc_lm_lc)




(*rule: The value of the last write on x remains the same after a load.*)
lemma st_lv_lc:
  assumes "mem_structured ts"
 and "vbounded ts"
and  "step t ( Load x r) ts ts'"
shows " \<lceil>y:v\<rceil> ts' =  \<lceil>y:v\<rceil> ts  "
  using assms
  apply (simp add: step_def)
  apply (subgoal_tac " memory ts = memory ts' ")
   prefer 2
  using mem_ld_trans apply blast
  apply (subgoal_tac " last_entry ts y = last_entry ts' y")
   prefer 2
   apply (simp add: last_entry_def)
   apply (simp add: last_entry_set_def)
  using assms(3) survived_val_preserved_load by presburger

(*rule: The monotonicity property of glb is preserved after a load*)
lemma ld_glb_monotonicity_preserved:
 assumes " ( \<forall> i j ti. (i \<noteq> 0 \<and> j \<noteq> 0 \<and>  j \<in> OTS ts ti  glb \<and>  i \<in> OTS ts ti glb \<and>  i \<le> j)  \<longrightarrow> valOf  i glb  ts  \<le> valOf j glb  ts)"
 and "vbounded ts"
and "mem_structured ts"
and  "step t ( Load x r) ts ts'"
shows  " ( \<forall> i j ti. (i \<noteq> 0 \<and> j \<noteq> 0 \<and> j \<in> OTS ts' ti  glb \<and>  i \<in> OTS ts' ti glb \<and>  i \<le> j)  \<longrightarrow> valOf  i glb  ts'  \<le> valOf j glb  ts')"
  using assms
 apply (subgoal_tac " memory ts = memory ts' ")
    prefer 2
   apply( simp add: step_def)
   apply (meson mem_ld_trans)
  apply (subgoal_tac " \<forall> i. valOf  i glb  ts  = valOf  i glb  ts'")
   prefer 2
   apply (metis ld_crash valOf_def)
  by (metis ld_ots_sub subsetD)



lemma ld_pm_inv_preserved:
  assumes "mem_structured ts"
  and "vbounded ts"
and  "step t ( Load x r) ts ts'"
  and " ( \<forall> addr . (( addr \<noteq> y) \<and> addr \<notin> A) \<longrightarrow>  [addr]\<^sub>P ts =  { lastVal  addr  ts  })"
and  "\<forall>ti l. comploc ( (memory ts)!(coh ts ti l)) l = l"
shows "  ( \<forall> addr . (( addr \<noteq> y) \<and> addr \<notin> A)  \<longrightarrow>  [addr]\<^sub>P ts' =  { lastVal  addr  ts'  })  "
  using assms                  

  apply (subgoal_tac "  \<forall> addr .  [addr]\<^sub>P ts' =  [addr]\<^sub>P ts ")
   prefer 2
   apply (simp add: ld_opv_ni)
  apply (simp add: step_def)
  apply (subgoal_tac "  \<forall> addr . last_entry ts'  addr = last_entry ts  addr")
   prefer 2
   apply (simp add: last_entry_def)
   apply (simp add: last_entry_set_def)
   apply (metis (no_types, lifting) Collect_cong mem_ld_trans)
  apply (simp add:lastVal_def)
  by (metis assms(3) mem_ld_trans survived_val_preserved_load)


(* The coherence view of an address x, after a thread t reads it, is equal to the timestamp of the message that is loaded*)
lemma ld_vrnew_gr_coh: 
  assumes  "step t ( Load x r) ts ts'"
and "total_wfs ts"
  shows " comploc ((memory ts)!(coh ts' t x))  x = x "
  using assms
  apply (simp add: step_def total_wfs_def)
  apply (simp add: load_trans_def Let_def)
  apply clarify
  apply (subgoal_tac " ind = coh ts' t x")
   prefer 2
   apply simp
apply (unfold OTS_def)
  apply (unfold OTSF_def)
  by (smt (verit, best) comploc_def mem_Collect_eq)

(* The value  of the last write for any address remains the same *)
lemma lastVal_ni: 
  assumes  "step t ( Load x r) ts ts'"
and "total_wfs ts"
  shows "  lastVal y  ts' = lastVal y ts "
  using assms
  apply (simp add: step_def total_wfs_def)
  by (metis assms(1) lastVal_def st_lv_lc)



lemma  ld_wfs_preserved :
  assumes "total_wfs ts"
  and "step t ( Load x r) ts ts'"
shows" total_wfs ts'"
  using assms 
  apply (unfold total_wfs_def)
  by (meson OTSF_notempty_preserved coh_loc_rel_preserved le_in_oats le_in_opts le_in_ots lev_in_oav lev_in_opv lev_in_ov mem_structured_preserved total_OTSF_def vbounded_preserved)


lemma  ld_coh_dt_ni :
  assumes "total_wfs ts"
  and "step t ( Load x r) ts ts'"
and " t \<noteq> t' "
shows"  coh (ts') t' a =  coh (ts) t' a"
  using assms 
   apply (simp add: step_def)
   apply (simp add: load_trans_def Let_def)
  by force

lemma ld_monotone_preserved:
  assumes "  (  \<forall> i j  .0 < j \<and>  j < length(memory ts)  \<and> 0 <  i \<and>  i < length(memory ts)  \<and>  i \<le> j \<and>  (State.loc (memory( ts)!i) ) = glb  \<and>  (State.loc (memory( ts)!j) ) = glb  \<longrightarrow> ((compval ts  (memory( ts)!i) glb ) \<le> (compval ts  (memory( ts)!j) glb ) ))"
 and "vbounded ts"
and "mem_structured ts"
  and "step t ( Load x r) ts ts'"
and " \<forall> ti l. last_entry ts l \<in>   OTS ts ti l "
and " \<forall> ti l. lastVal  l ts  \<in>  [l]\<^sub>ti ts " 
shows   "(  \<forall> i j  . 0 < j \<and>  j < length(memory ts')  \<and> 0 <  i \<and>  i < length(memory ts')  \<and>  i \<le> j \<and>  (State.loc (memory( ts')!i) ) = glb  \<and>  (State.loc (memory( ts')!j) ) = glb  \<longrightarrow> ((compval ts'  (memory( ts')!i) glb ) \<le> (compval ts'  (memory( ts')!j) glb ) ))"
  using assms

  apply (subgoal_tac " memory ts = memory ts' ")
   prefer 2
   apply (simp add: step_def)
   apply (meson mem_ld_trans)
  by (metis ld_crash)



lemma ld_monotone_complete_preserved:
  assumes "  (  \<forall> i j  .0 < j \<and>  j < length(memory ts)  \<and> 0 <  i \<and>  i < length(memory ts)  \<and>  i \<le> j \<and>  comploc ((memory ts)!i )  glb  = glb   \<and>  comploc ((memory ts)!j )  glb  = glb   \<longrightarrow> ((compval ts  (memory( ts)!i) glb ) \<le> (compval ts  (memory( ts)!j) glb ) ))"
 and "vbounded ts"
and "mem_structured ts"
  and "step t ( Load x r) ts ts'"
and " \<forall> ti l. last_entry ts l \<in>   OTS ts ti l "
and " \<forall> ti l. lastVal  l ts  \<in>  [l]\<^sub>ti ts " 
shows   "(  \<forall> i j  . 0 < j \<and>  j < length(memory ts')  \<and> 0 <  i \<and>  i < length(memory ts')  \<and>  i \<le> j \<and>   comploc ((memory ts')!i )  glb  = glb     \<and>    comploc ((memory ts')!j )  glb  = glb    \<longrightarrow> ((compval ts'  (memory( ts')!i) glb ) \<le> (compval ts'  (memory( ts')!j) glb ) ))"
  using assms

  apply (subgoal_tac " memory ts = memory ts' ")
   prefer 2
   apply (simp add: step_def)
   apply (meson mem_ld_trans)
  by (metis ld_crash)




lemma ld_step_mem:
  assumes "vbounded ts"
and "mem_structured ts"
  and "step t ( Load x r) ts ts'"
shows   "memory ts' = memory ts"
  using assms
   apply (simp add: step_def)
  by fastforce

lemma ld_le_lim_ni :
 assumes "total_wfs ts"
  and "step t ( Load x r) ts ts'"
shows " last_entry_lim ts' a lim = last_entry_lim ts a lim "
  using assms
  apply (subgoal_tac " memory ts = memory ts' ")
   prefer 2
  using ld_step_mem total_wfs_def apply auto[1]
  by (simp add: last_entry_lim_def last_entry_set_lim_def)



lemma ld_le_coh_ni:
assumes  "step t ( Load x r) ts ts'"
and " total_wfs ts"
and " t \<noteq> t' "
shows " last_entry_lim (ts') b (coh (ts') t' glb) =  last_entry_lim (ts) b (coh (ts) t' glb)"
  using assms
  by (simp add: ld_coh_dt_ni ld_le_lim_ni)


(*rule: The value of the last entry before the coherence view of any thread t' different to t, for any address b, remains the same after t executes a load*)
lemma ld_le_lim_valof_dt_ni:
assumes  "step t ( Load x r) ts ts'"
and " total_wfs ts"
and " t \<noteq> t' "
shows " valOf ( last_entry_lim (ts') b (coh (ts') t' glb)) b ts' = valOf(  last_entry_lim (ts) b (coh (ts) t' glb)) b ts"
  using assms
  apply (simp add: valOf_def)
  using ld_le_coh_ni ld_step_mem survived_val_preserved_load total_wfs_def by auto




lemma ld_coh_valof_dt_ni:
assumes  "step t ( Load x r) ts ts'"
and " total_wfs ts"
and " t \<noteq> t' "
shows " valOf (coh ts' t' glb)  b ts' = valOf   (coh ts t' glb) b ts"
  using assms
  apply (unfold total_wfs_def)
  apply (simp add: valOf_def)
  using assms(2) ld_coh_dt_ni ld_step_mem survived_val_preserved_load by force



lemma ld_vrnew_dt_ni:
assumes  "step t ( Load x r) ts ts'"
and " total_wfs ts"
and " t \<noteq> t' "
shows " vrnew ts t' =  vrnew ts' t'  "
  using assms
  apply (simp add: step_def )
  apply (simp add: load_trans_def Let_def)
  by fastforce



lemma  ld_lelim_nle_ni:
   assumes "mem_structured ts"
  and "vbounded ts"
  and  "step t ( Load x r) ts ts'"
shows "(\<forall> n l. (0 \<le> n \<and> n < length(memory ts' )) \<longrightarrow> valOf (last_entry_lim ts' l n) l (ts')  =    valOf (last_entry_lim ts l n) l ts  ) "
  using assms
  apply (subgoal_tac"memory ts = memory ts' ")
   prefer 2
  apply (simp add: ld_step_mem)
  apply (unfold last_entry_lim_def last_entry_set_lim_def)
  by (metis (no_types, lifting) Collect_cong ld_crash valOf_def)



lemma  ld_valOf_nle_ni:
   assumes "mem_structured ts"
  and "vbounded ts"
    and  "step t ( Load x r) ts ts'"
shows "(\<forall> n l. (0 \<le> n \<and> n < length(memory ts' )) \<longrightarrow> valOf (n) l (ts')  =    valOf (n) l ts  ) "
  using assms
  apply (simp add: valOf_def )
  using ld_step_mem survived_val_preserved_load by presburger



lemma  ld_comploc_ni:
   assumes "mem_structured ts"
  and "vbounded ts"
    and  "step t ( Load x r) ts ts'"
shows "(\<forall> n l. (0 \<le> n \<and> n < length(memory ts' )) \<longrightarrow>  comploc ((memory ts') !n) x  =    comploc ((memory ts) !n) x  )"
  using assms
  by (simp add: ld_step_mem)


lemma last_entry_last_comp_loc:
assumes " total_wfs ts"
shows " \<forall>  n. n > (last_entry ts  l)\<and> n < length (memory ts ) \<longrightarrow> comploc ((memory ts )!n) l \<noteq> l "
  using assms
  apply (simp add: last_entry_def)
  apply (subgoal_tac " \<forall> i. comploc ((memory ts )!i) l = l \<and> i < length (memory ts ) \<and> 0 \<le> i \<longrightarrow> i \<in> (last_entry_set ts l) ")
   prefer 2
  apply (simp add: last_entry_set_def)
  by (metis add_lessD1 assms dual_order.strict_trans last_entry_def last_entry_notoverwritten lessI less_Suc_eq_le mem_structured_def notoverwritten_def plus_nat.add_0 total_wfs_def)



lemma ld_reg_compval :
  assumes " ts'=  load_trans t ind a (ts) b  "
  shows "  compval ts (memory (ts) ! ind) a  =  regs (ts') t b "
  using assms
  by (simp add: load_trans_def )

lemma ld_ind_eq_coh' :
  assumes " ts'=  load_trans t ind a (ts) b  "
shows " ind  =   coh  ts'  t a"
  using assms
  by(simp add: load_trans_def )


lemma ld_coh_eq_vrnew:
  assumes " ts [loca   \<leftarrow> glb ]\<^sub>t ts'  "
 and "  coh (ts) t glb = vrnew (ts) t"
and "   (\<forall>i.  i \<in> OTS  (ts) t glb \<longrightarrow> coh  (ts) t glb \<le> i) "
shows " coh (ts') t glb = vrnew (ts') t"
  using assms
  apply (simp add: step_def)
  apply (simp add: load_trans_def)
  apply clarify
  apply (case_tac " ind = vrnew (ts) t  ")
   apply (subgoal_tac " vrnew (ts') t =  vrnew (ts) t")
  prefer 2
    apply (smt (z3) TState.ext_inject TState.surjective TState.update_convs(1) TState.update_convs(2) TState.update_convs(3) TState.update_convs(4) TState.update_convs(7) fun_upd_triv max.idem)
   apply simp
  apply (smt (z3) TState.ext_inject TState.surjective TState.update_convs(1) TState.update_convs(2) TState.update_convs(4) TState.update_convs(7) fun_upd_triv)
  apply (subgoal_tac " vrnew (ts') t = ind")
   prefer 2
  apply (subgoal_tac " ind \<ge>  vrnew (ts) t")
    prefer 2
  apply blast
   apply simp
  apply (subgoal_tac " coh (ts') t glb  = ind")
   prefer 2
   apply simp
  by meson



end