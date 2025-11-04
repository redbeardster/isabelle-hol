(*Rules for identifying the acceptable values to be read by read-only transactions*)
theory Read_Rules
imports   inv_rules ld_c
begin



lemma fr:
  assumes "   ( \<exists>\<theta> .0 <\<theta> \<and>  \<theta> > (coh ts t glb )  \<and> \<theta>< length (memory ts' ) \<and>  \<theta> <coh ts' t a  \<and>  Msg.loc((memory ts')!\<theta>)  = glb \<and> odd (  Msg.val((memory ts')!\<theta>)) \<and>
(  \<forall> i. i \<in>  (OTS  ts' t glb) \<longrightarrow> \<theta>  \<le> i) )"
(*and "  f < k"*)
(*and " total_wfs  ts' " *)
 and  "step t ( Load a  val) ts ts'"
 and "a \<noteq> glb" 

and " 0 <  (coh ts t glb )  \<and>   (coh ts t glb ) < length(memory ts')"
(*and " 0 < k \<and>  k < length(memory ts)" *)
and " glb_monotone_inv  ts' "
(*and " odd ( (State.val((memory ( ts))!(k)) ) ) " *)
and "  even (  (State.val((memory ( ts'))!( (coh ts t glb ))) )  ) "

and " total_wfs  ts "

shows " \<forall> n. n \<in>  [glb]\<^sub>t ts'  \<longrightarrow>  (   (State.val((memory ( ts'))!( (coh ts t glb ))) )   <  n)"
  using assms

  apply (subgoal_tac "  total_wfs ts' ")
  prefer 2
  using ld_wfs_preserved apply blast

  apply clarify
 apply (simp add: glb_monotone_inv_def total_wfs_def )
  apply (subgoal_tac " 0 \<notin>  (OTS  ts' t glb)")
   prefer 2
  apply (subgoal_tac "  (State.val((memory ( ts'))!(coh ts t glb)) )  \<le>  (State.val((memory ( ts'))!(\<theta>)) ) ")
    prefer 2
 apply (subgoal_tac "  (State.loc((memory ( ts'))!(coh ts t glb)) ) = glb ")
     prefer 2 

     apply (subgoal_tac "   comploc (memory ts' ! coh ts t  glb) glb = glb " )
      prefer 2
  using coh_ld_st_dadrr comploc_def apply presburger
     apply (meson assms(4) i_noteqo_loc)
  apply (metis assms(4) less_nat_zero_code nat_less_le neq0_conv)
  using assms(4) assms(5)  less_imp_le_nat apply blast
  apply (subgoal_tac " \<forall>x. x \<in> (OTS  ts' t glb) \<longrightarrow>  memory ts' ! x \<noteq> Init_Msg ")
  prefer 2
   apply (unfold mem_structured_def)
   apply (metis aux order_le_imp_less_or_eq)
 apply (subgoal_tac " \<forall> i. i \<in> (OTS  ts' t glb) \<longrightarrow> 0 \<le> i \<and> i < length(memory ts' ) " )
  prefer 2
  apply (simp add: OTS_def)
   apply (simp(no_asm) add: OTSF_def )
  apply (subgoal_tac " \<forall> i. i \<in> (OTS  ts' t glb) \<longrightarrow> 0 < i \<and> i < length(memory ts' ) " )
   prefer 2
   apply (metis bot_nat_0.not_eq_extremum)
  apply (subgoal_tac "  \<forall> i. i \<in> (OTS  ts' t glb) \<longrightarrow> State.val  ((memory ts') !i)  \<in> [glb]\<^sub>t ts' ")
    prefer 2
apply (subgoal_tac "  \<forall> i. i \<in> (OTS  ts' t glb) \<longrightarrow> compval ts' ((memory ts') !i) glb  \<in> [glb]\<^sub>t ts' ")
    prefer 2
     apply (meson opv_opts_rel)
   apply (simp add: compval_def)

apply (subgoal_tac "  \<forall> i. i \<in> (OTS  ts' t glb) \<longrightarrow> comploc  ((memory ts') !i) glb  = glb ")
   prefer 2
   apply (simp add: OTS_def)
   apply (simp(no_asm) add: OTSF_def)
  apply (metis assms(7) coh_ld_st_dadrr le_neq_implies_less order_less_trans total_wfs_def)


apply (subgoal_tac "  \<forall> i. i \<in> (OTS  ts' t glb) \<longrightarrow> Msg.loc ((memory ts') !i)   = glb ")
   prefer 2
  apply (metis comploc_def)

  apply (subgoal_tac "  \<forall>i. i \<in> OTS ts' t glb \<longrightarrow>   State.val  ((memory ts') !\<theta>) \<le>  State.val  ((memory ts') !i)")
   prefer 2
   apply (metis linorder_neqE_nat not_less_zero) 


 apply (subgoal_tac "  \<forall>n. n \<in> [glb]\<^sub>t ts'  \<longrightarrow>   compval ts' ((memory ts') !\<theta>) glb  \<le>  n")
   prefer 2
 


(* apply (subgoal_tac " \<forall>n. n \<in> [glb]\<^sub>t ts'  \<longrightarrow> (\<exists>i. i \<in>  OTS ts' t glb \<and> comploc  ((memory ts') !i) glb  = glb \<and>  compval ts' ((memory ts') !i) glb  = glb)  ")*)
   apply (unfold  mapval_def)

  apply (smt (z3) assms(5) glb_monotone_inv_def image_iff order_less_trans)
  apply (subgoal_tac "compval ts' ((memory ts') !\<theta>) glb  = (State.val ( (memory ts') !\<theta>) ) " )
   prefer 2
  apply (simp(no_asm) add: compval_def)
   apply (subgoal_tac "  \<theta> > 0 " )
    prefer 2
  apply linarith
   apply (subgoal_tac "  memory ts' ! \<theta> \<noteq> Init_Msg  " )
  prefer 2
  apply presburger
  apply blast

  apply (subgoal_tac "  (State.val((memory ( ts'))!( (coh ts t glb ))) )    < compval ts' ((memory ts') !\<theta>) glb  ")
  prefer 2
  apply (metis (no_types, lifting) assms(4) coh_ld_st_dadrr linorder_neqE_nat mem_structured_def nat_less_le not_less_zero)
  by (metis (no_types, lifting) le_antisym le_trans nat_less_le)





lemma fr_gen:
  assumes "   ( \<exists>\<theta> .0 <\<theta> \<and>  \<theta> > (\<phi> )  \<and> \<theta>< length (memory ts' ) \<and>  \<theta> <coh ts' t a  \<and>  Msg.loc((memory ts')!\<theta>)  = glb \<and> odd (  Msg.val((memory ts')!\<theta>)) \<and>
(  \<forall> i. i \<in>  (OTS  ts' t glb) \<longrightarrow> \<theta>  \<le> i) )"
(*and "  f < k"*)
(*and " total_wfs  ts' " *)
 and  "step t ( Load a  val) ts ts'"
 and "a \<noteq> glb" 

and " 0 <  (\<phi> )  \<and>   (\<phi> ) < length(memory ts')"
(*and " 0 < k \<and>  k < length(memory ts)" *)
and " glb_monotone_inv  ts' "
(*and " odd ( (State.val((memory ( ts))!(k)) ) ) " *)
and "  even (  (State.val((memory ( ts'))!( (\<phi> ))) )  ) "

and " total_wfs  ts "
and " comploc (memory ts ! \<phi>) glb = glb"
shows " \<forall> n. n \<in>  [glb]\<^sub>t ts'  \<longrightarrow>  (   (State.val((memory ( ts'))!( (\<phi> ))) )   <  n)"
  using assms

  apply (subgoal_tac "  total_wfs ts' ")
  prefer 2
  using ld_wfs_preserved apply blast

  apply clarify
 apply (simp add: glb_monotone_inv_def total_wfs_def )
  apply (subgoal_tac " 0 \<notin>  (OTS  ts' t glb)")
   prefer 2
 apply (subgoal_tac "  (State.val((memory ( ts'))!(\<phi>)) )  \<le>  (State.val((memory ( ts'))!(\<theta>)) ) ")
    prefer 2
 apply (subgoal_tac "  (State.loc((memory ( ts'))!(\<phi>)) ) = glb ")
     prefer 2 

     apply (subgoal_tac "   comploc (memory ts' ! \<phi>) glb = glb " )
      prefer 2
      apply (subgoal_tac " memory ts = memory ts' ")
       prefer 2
       apply (simp add: step_def)
       apply (meson mem_ld)
  using assms(8) apply presburger

     apply (meson assms(4) i_noteqo_loc)
  apply (metis assms(4) less_nat_zero_code nat_less_le neq0_conv)  
  using assms(4) assms(5)  less_imp_le_nat apply blast
  apply (subgoal_tac " \<forall>x. x \<in> (OTS  ts' t glb) \<longrightarrow>  memory ts' ! x \<noteq> Init_Msg ")
  prefer 2
   apply (unfold mem_structured_def)
   apply (metis aux order_le_imp_less_or_eq)
 apply (subgoal_tac " \<forall> i. i \<in> (OTS  ts' t glb) \<longrightarrow> 0 \<le> i \<and> i < length(memory ts' ) " )
  prefer 2
  apply (simp add: OTS_def)
   apply (simp(no_asm) add: OTSF_def )
  apply (subgoal_tac " \<forall> i. i \<in> (OTS  ts' t glb) \<longrightarrow> 0 < i \<and> i < length(memory ts' ) " )
   prefer 2
   apply (metis bot_nat_0.not_eq_extremum)
  apply (subgoal_tac "  \<forall> i. i \<in> (OTS  ts' t glb) \<longrightarrow> State.val  ((memory ts') !i)  \<in> [glb]\<^sub>t ts' ")
    prefer 2
apply (subgoal_tac "  \<forall> i. i \<in> (OTS  ts' t glb) \<longrightarrow> compval ts' ((memory ts') !i) glb  \<in> [glb]\<^sub>t ts' ")
    prefer 2
     apply (meson opv_opts_rel)
   apply (simp add: compval_def)

apply (subgoal_tac "  \<forall> i. i \<in> (OTS  ts' t glb) \<longrightarrow> comploc  ((memory ts') !i) glb  = glb ")
   prefer 2
  using comploc_ots apply presburger
 
apply (subgoal_tac "  \<forall> i. i \<in> (OTS  ts' t glb) \<longrightarrow> Msg.loc ((memory ts') !i)   = glb ")
   prefer 2
  apply (metis comploc_def)

  apply (subgoal_tac "  \<forall>i. i \<in> OTS ts' t glb \<longrightarrow>   State.val  ((memory ts') !\<theta>) \<le>  State.val  ((memory ts') !i)")
   prefer 2
   apply (metis linorder_neqE_nat not_less_zero) 


 apply (subgoal_tac "  \<forall>n. n \<in> [glb]\<^sub>t ts'  \<longrightarrow>   compval ts' ((memory ts') !\<theta>) glb  \<le>  n")
   prefer 2
 
(* apply (subgoal_tac " \<forall>n. n \<in> [glb]\<^sub>t ts'  \<longrightarrow> (\<exists>i. i \<in>  OTS ts' t glb \<and> comploc  ((memory ts') !i) glb  = glb \<and>  compval ts' ((memory ts') !i) glb  = glb)  ")*)
  apply (unfold  mapval_def)

  apply (smt (z3) assms(5) glb_monotone_inv_def image_iff order_less_trans)
  apply (subgoal_tac "compval ts' ((memory ts') !\<theta>) glb  = (State.val ( (memory ts') !\<theta>) ) " )
   prefer 2
  apply (simp(no_asm) add: compval_def)
   apply (subgoal_tac "  \<theta> > 0 " )
    prefer 2
  apply linarith
   apply (subgoal_tac "  memory ts' ! \<theta> \<noteq> Init_Msg  " )
  prefer 2
  apply presburger
  apply blast
  apply (subgoal_tac " compval ts' ((memory ts') !\<phi>) glb   \<le> compval ts' ((memory ts') !\<theta>) glb  ")
   prefer 2
   apply (unfold step_def)

  apply (smt (z3) assms(4) assms(5) glb_monotone_inv_def instruction.simps(48) less_imp_le_nat less_nat_zero_code mem_ld_trans neq0_conv)
  by (metis (no_types, lifting) assms(2) assms(4) assms(7) ld_wfs_preserved le_antisym le_neq_implies_less le_trans total_wfs_def val_eq_compval)

 

lemmas [simp del] = compval_def comploc_def



lemma ld_last_entry_lim:
 assumes "thrdsvars"
 and "total_wfs ts"
 and  "step t ( Load a  val) ts ts'"
 and "a \<noteq> glb"
and "even (   ( compval ts ((memory ts)!  (coh ts t glb )  ) glb) )  "
and " mem_tml_prop   glb  a (ts) "
and "  vrnew ts' t \<ge>  coh ts' t a "
and " vrnew ts' t \<ge> last_entry_lim ts' a (coh ts t glb) "
and " coh ts t glb > 0"
shows " (coh ts' t a \<noteq> last_entry_lim  ts' a (coh ts t glb ) ) \<longrightarrow> coh ts t glb  \<notin> (OTS  ts' t glb) "
  using assms
 apply (subgoal_tac "  even ( compval ts' ((memory ts')!(coh ts t glb )) glb)" )
   prefer 2
  apply (simp add: step_def compval_def)
      apply (subgoal_tac " memory ts = memory ts' ")
  prefer 2
  using mem_ld_trans apply blast

  apply (metis (full_types) assms(3) survived_val_preserved_load)

   apply (subgoal_tac " \<forall>  i. i \<in> last_entry_set_lim  ts' a (coh ts t glb )   \<longrightarrow> i \<le>   coh ts t glb ")
    prefer 2
   apply (simp add:  last_entry_set_lim_def)

  apply (subgoal_tac " last_entry_lim  ts' a (coh ts t glb )  \<le> (coh ts t glb )  ")
   prefer 2
  using  finite_last_entry_set_lim total_wfs_def 
  using last_entry_lim_in_last_entry_set_lim mem_structured_preserved vbounded_preserved apply blast
  apply (simp add: OTS_def)
  apply (simp add: OTSF_def)
  apply (intro impI conjI)
   apply (case_tac "  coh ts' t a > last_entry_lim ts' a (coh ts t glb)")
    apply (subgoal_tac "   vrnew ts' t  > last_entry_lim ts' a (coh ts t glb)")
  prefer 2
     apply linarith
    apply (subgoal_tac " mem_tml_prop   glb  a (ts') " )
  prefer 2
  using assms(1) ld_mem_inv apply presburger
    apply (subgoal_tac " \<exists>k.  k > (coh ts t glb )  \<and>  k <coh ts' t a  \<and> Msg.loc((memory ts')!k)  = glb ")
     prefer 2
 apply (subgoal_tac "   comploc ((memory ts')!(coh ts t glb )) glb = glb ")
      prefer 2
  using comploc_def 
  apply linarith

     apply (subgoal_tac "  Msg.loc ((memory ts)!(coh ts' t a)) = a ")
      prefer 2
     apply (subgoal_tac " (coh ts' t a) > 0 ")
  prefer 2
       apply linarith
  apply (simp add: total_wfs_def)
  apply (subgoal_tac "  comploc ((memory ts)!(coh ts' t a))  a = a ")
       prefer 2
  using assms(2) ld_vrnew_gr_coh apply presburger
      apply (subgoal_tac " (coh ts' t a) < length(memory ts' ) ")
  prefer 2
  apply (meson assms(2) aux coh_lc total_wfs_def)
  apply (smt (verit, del_insts) assms(2) coh_lc comploc_def i_noteqo_loc last_entry_bounded ld_last_entry ld_last_entry_in_ots le_antisym le_trans less_irrefl_nat less_or_eq_imp_le linorder_neqE_nat)

  apply (subgoal_tac " (coh ts' t a) < length(memory ts' ) ")
  prefer 2
      apply (meson assms(2) aux coh_lc total_wfs_def)
apply (subgoal_tac " 0 \<le>  (coh ts t glb) ")
      prefer 2
      apply blast
 apply (subgoal_tac " total_wfs ts'" )
  prefer 2
  apply (unfold total_wfs_def)
   apply (intro conjI)
  using vbounded_preserved apply blast
  using mem_structured_preserved apply blast
       apply (metis OTSF_notempty_preserved assms(2) total_OTSF_def total_wfs_def)
  apply (meson coh_loc_rel_preserved le_in_oats le_in_opts le_in_ots lev_in_oav lev_in_opv lev_in_ov)
     apply (subgoal_tac " coh ts t glb < coh ts' t a ")
      prefer 2
      apply (subgoal_tac " coh ts' t a < length(memory ts') ")
  prefer 2
  apply blast

apply (subgoal_tac "  comploc ((memory ts)!(coh ts' t a))  a = a ")
       prefer 2
  using assms(2) ld_vrnew_gr_coh apply presburger
  using gr_last_entry_lim total_wfs_def apply presburger
     apply  (unfold  mem_tml_prop_def  )
  apply (subgoal_tac " coh ts t glb <  coh ts' t a \<and>
          a \<noteq> glb \<and>
          0 < coh ts t glb \<and>
          coh ts' t a  < length (memory ts') \<and>
          comploc (memory ts' ! coh ts t glb) glb = glb \<and>
          even (compval ts' (memory ts' ! coh ts t glb) glb) \<and>
          Msg.loc (memory ts' ! coh ts' t a) = a \<longrightarrow>
          (\<exists>k> coh ts t glb . k < coh ts' t a \<and>
                 Msg.loc (memory ts' ! k) = glb \<and>
                 odd (Msg.val (memory ts' ! k)))" )
      prefer 2
      apply presburger
  apply (subgoal_tac " coh ts t glb <  coh ts' t a \<and>
          a \<noteq> glb \<and>
          0 < coh ts t glb \<and>
          coh ts' t a  < length (memory ts') \<and>
          comploc (memory ts' ! coh ts t glb) glb = glb \<and>
          even (compval ts' (memory ts' ! coh ts t glb) glb) \<and>
          Msg.loc (memory ts' ! coh ts' t a) = a")
  prefer 2
      apply (intro conjI)
  apply blast
           apply blast
         apply blast
       apply blast

       apply (metis cas_fail_crash)  
  apply (metis cas_fail_crash)
  apply (metis (no_types, lifting) bot_nat_0.not_eq_extremum i_noteqo_loc less_nat_zero_code total_wfs_def)
     apply blast
    apply (smt (z3) aux coh_lc le_antisym le_trans nat_less_le notoverwritten_def)
   apply (subgoal_tac " coh ts' t a < last_entry_lim ts' a (coh ts t glb)  ")
  prefer 2
    apply linarith
   apply (subgoal_tac " coh ts' t a  \<notin> (OTS  ts' t a) ")
    prefer 2
    apply (unfold OTS_def)
    apply (unfold OTSF_def)
    apply clarify
    apply (subgoal_tac "\<not>  notoverwritten ts' (vrnew ts' t) (coh ts' t a) a ")
     prefer 2
     apply (subgoal_tac "   last_entry_lim ts' a (coh ts t glb) < length (memory ts') \<and>  last_entry_lim ts' a (coh ts t glb) \<le> vrnew ts' t \<and>
 coh ts' t a <  last_entry_lim ts' a (coh ts t glb) \<and>
              Msg.loc (memory ts' !  last_entry_lim ts' a (coh ts t glb)) =  a")
      prefer 2
      apply (intro conjI)
         apply linarith
  apply blast
  apply blast
 apply (subgoal_tac " total_wfs ts'" )
  prefer 2
  apply (unfold total_wfs_def)
   apply (intro conjI)
  using vbounded_preserved 
  apply meson
  using mem_structured_preserved apply meson
    apply (meson OTSF_notempty_preserved total_OTSF_def)
  apply (metis (no_types, lifting) OTS_def coh_loc_rel_preserved lastVal_def le_in_oats le_in_opts le_in_otsf lev_in_oav lev_in_opv opv_opts_rel)
  apply (metis (no_types, lifting) bot_nat_0.not_eq_extremum i_noteqo_loc last_entry_lim_bounded last_entry_lim_loc total_wfs_def)
  apply (metis (no_types, lifting) notoverwritten_def)
  apply blast
  by (metis OTSF_def OTS_def assms(3) coh_lc)



lemma ld_k_exists_coh_gr_le:
 assumes "thrdsvars"
 and "total_wfs ts"
 and  "step t ( Load a  val) ts ts'"
 and "a \<noteq> glb"
and " mem_tml_prop   glb  a (ts) "
and "even (   ( compval ts ((memory ts)!  (coh ts t glb )  ) glb) )  "
and "  coh ts' t a > last_entry_lim  ts' a (coh ts t glb ) "
and "  vrnew ts' t \<ge>  coh ts' t a "
and " vrnew ts' t \<ge> last_entry_lim ts' a (coh ts t glb) "
and "  coh ts t glb > 0"
shows "   ( \<exists>k.  k > (coh ts t glb )  \<and>  k <coh ts' t a  \<and>  Msg.loc((memory ts')!k)  = glb \<and> odd (  Msg.val((memory ts')!k)) ) "
  using assms
 apply (subgoal_tac "  even ( compval ts' ((memory ts')!(coh ts t glb )) glb)" )
   prefer 2
  apply (simp add: step_def compval_def)
      apply (subgoal_tac " memory ts = memory ts' ")
  prefer 2
  using mem_ld_trans apply blast

  apply (metis (full_types) assms(3) survived_val_preserved_load)

   apply (subgoal_tac " \<forall>  i. i \<in> last_entry_set_lim  ts' a (coh ts t glb )   \<longrightarrow> i \<le>   coh ts t glb ")
    prefer 2
   apply (simp add:  last_entry_set_lim_def)

  apply (subgoal_tac " last_entry_lim  ts' a (coh ts t glb )  \<le> (coh ts t glb )  ")
   prefer 2
  using  finite_last_entry_set_lim total_wfs_def  
  apply (metis last_entry_lim_in_last_entry_set_lim mem_structured_preserved vbounded_preserved)
 (*  apply (case_tac "  coh ts' t a > last_entry_lim ts' a (coh ts t glb)") *)
    apply (subgoal_tac "   vrnew ts' t  > last_entry_lim ts' a (coh ts t glb)")
  prefer 2
     apply linarith
    apply (subgoal_tac " mem_tml_prop   glb  a (ts') " )
  prefer 2
  using assms(1) ld_mem_inv apply presburger


(*  apply (subgoal_tac " \<exists>k.  k > (coh ts t glb )  \<and>  k <coh ts' t a  \<and> Msg.loc((memory ts')!k)  = glb \<and> odd (  Msg.val((memory ts')!k)) ")
     prefer 2*)
 apply (subgoal_tac "   comploc ((memory ts')!(coh ts t glb )) glb = glb ")
     prefer 2
 apply (simp add: total_wfs_def) 
  using comploc_def 
  apply (metis coh_ld_st_dadrr coh_loc_rel_preserved)

     apply (subgoal_tac "  Msg.loc ((memory ts)!(coh ts' t a)) = a ")
      prefer 2
     apply (subgoal_tac " (coh ts' t a) > 0 ")
  prefer 2
       apply linarith
  apply (simp add: total_wfs_def)
  apply (subgoal_tac "  comploc ((memory ts)!(coh ts' t a))  a = a ")
       prefer 2
  using assms(2) ld_vrnew_gr_coh apply presburger
      apply (subgoal_tac " (coh ts' t a) < length(memory ts' ) ")
  prefer 2
  apply (meson assms(2) aux coh_lc total_wfs_def)
  apply (smt (verit, del_insts) assms(2) coh_lc comploc_def i_noteqo_loc last_entry_bounded ld_last_entry ld_last_entry_in_ots le_antisym le_trans less_irrefl_nat less_or_eq_imp_le linorder_neqE_nat)

  apply (subgoal_tac " (coh ts' t a) < length(memory ts' ) ")
  prefer 2
      apply (meson assms(2) aux coh_lc total_wfs_def)
apply (subgoal_tac " 0 \<le>  (coh ts t glb) ")
      prefer 2
      apply blast
 apply (subgoal_tac " total_wfs ts'" )
  prefer 2
  apply (unfold total_wfs_def)
   apply (intro conjI)
  using vbounded_preserved apply blast
  using mem_structured_preserved apply blast
       apply (metis OTSF_notempty_preserved assms(2) total_OTSF_def total_wfs_def)
  apply (meson coh_loc_rel_preserved le_in_oats le_in_opts le_in_ots lev_in_oav lev_in_opv lev_in_ov)
     apply (subgoal_tac " coh ts t glb < coh ts' t a ")
      prefer 2
      apply (subgoal_tac " coh ts' t a < length(memory ts') ")
  prefer 2
  apply blast

apply (subgoal_tac "  comploc ((memory ts)!(coh ts' t a))  a = a ")
       prefer 2
  using assms(2) ld_vrnew_gr_coh apply presburger
  using gr_last_entry_lim total_wfs_def apply presburger
     apply  (unfold  mem_tml_prop_def  )
  apply (subgoal_tac " coh ts t glb <  coh ts' t a \<and>
          a \<noteq> glb \<and>
          0 < coh ts t glb \<and>
          coh ts' t a  < length (memory ts') \<and>
          comploc (memory ts' ! coh ts t glb) glb = glb \<and>
          even (compval ts' (memory ts' ! coh ts t glb) glb) \<and>
          Msg.loc (memory ts' ! coh ts' t a) = a \<longrightarrow>
          (\<exists>k> coh ts t glb . k < coh ts' t a \<and>
                 Msg.loc (memory ts' ! k) = glb \<and>
                 odd (Msg.val (memory ts' ! k)))" )
      prefer 2
      apply presburger
  apply (subgoal_tac " coh ts t glb <  coh ts' t a \<and>
          a \<noteq> glb \<and>
          0 < coh ts t glb \<and>
          coh ts' t a  < length (memory ts') \<and>
          comploc (memory ts' ! coh ts t glb) glb = glb \<and>
          even (compval ts' (memory ts' ! coh ts t glb) glb) \<and>
          Msg.loc (memory ts' ! coh ts' t a) = a")
  prefer 2
      apply (intro conjI)
  apply blast
           apply blast
          apply blast
         apply blast
       apply blast
  apply (metis cas_fail_crash)  
  apply (metis (no_types, lifting) bot_nat_0.not_eq_extremum i_noteqo_loc less_nat_zero_code total_wfs_def)
  by blast






lemma ld_coh_le_ots:
 assumes "thrdsvars"
 and "total_wfs ts"
 and  "step t ( Load a  val) ts ts'"
 and "a \<noteq> glb"
and " mem_tml_prop   glb  a (ts') "
and "even (   ( compval ts ((memory ts)!  (coh ts t glb )  ) glb) )  "
and "  coh ts' t a > last_entry_lim  ts' a (coh ts t glb ) "
and "  vrnew ts' t \<ge>  coh ts' t a "
and " vrnew ts' t \<ge> last_entry_lim ts' a (coh ts t glb) "
and " coh ts t glb > 0"
shows "  ( ( \<exists>k.  k > (coh ts t glb )  \<and>  k <coh ts' t a  \<and>  Msg.loc((memory ts')!k)  = glb \<and> odd (  Msg.val((memory ts')!k)) \<and>
(  \<forall> i. i \<in>  (OTS  ts' t glb) \<longrightarrow> k  \<le> i) )) "
  using assms
(*  apply (simp add: total_wfs_def) *)


 apply (subgoal_tac "  even ( compval ts' ((memory ts')!(coh ts t glb )) glb)" )
   prefer 2
  apply (simp add: step_def compval_def)
      apply (subgoal_tac " memory ts = memory ts' ")
  prefer 2
  using mem_ld_trans apply blast

  apply (metis (full_types) assms(3) survived_val_preserved_load)

   apply (subgoal_tac " \<forall>  i. i \<in> last_entry_set_lim  ts' a (coh ts t glb )   \<longrightarrow> i \<le>   coh ts t glb ")
    prefer 2
   apply (simp add:  last_entry_set_lim_def)

  apply (subgoal_tac " last_entry_lim  ts' a (coh ts t glb )  \<le> (coh ts t glb )  ")
   prefer 2
  using  finite_last_entry_set_lim total_wfs_def  
  apply (metis last_entry_lim_in_last_entry_set_lim mem_structured_preserved vbounded_preserved)
 (*  apply (case_tac "  coh ts' t a > last_entry_lim ts' a (coh ts t glb)") *)
    apply (subgoal_tac "   vrnew ts' t  > last_entry_lim ts' a (coh ts t glb)")
  prefer 2
     apply linarith
    apply (subgoal_tac " mem_tml_prop   glb  a (ts') " )
  prefer 2
  using assms(1) ld_mem_inv apply presburger


  apply (subgoal_tac " \<exists>k.  k > (coh ts t glb )  \<and>  k <coh ts' t a  \<and> Msg.loc((memory ts')!k)  = glb \<and> odd (  Msg.val((memory ts')!k)) ")
   prefer 2

 
 apply (subgoal_tac "   comploc ((memory ts')!(coh ts t glb )) glb = glb ")
     prefer 2
 apply (simp add: total_wfs_def) 
  using comploc_def 
  apply (metis coh_ld_st_dadrr coh_loc_rel_preserved)

     apply (subgoal_tac "  Msg.loc ((memory ts)!(coh ts' t a)) = a ")
      prefer 2
     apply (subgoal_tac " (coh ts' t a) > 0 ")
  prefer 2
       apply linarith
  apply (simp add: total_wfs_def)
  apply (subgoal_tac "  comploc ((memory ts)!(coh ts' t a))  a = a ")
       prefer 2
  using assms(2) ld_vrnew_gr_coh apply presburger
      apply (subgoal_tac " (coh ts' t a) < length(memory ts' ) ")
  prefer 2
  apply (meson assms(2) aux coh_lc total_wfs_def)
  apply (smt (verit, del_insts) assms(2) coh_lc comploc_def i_noteqo_loc last_entry_bounded ld_last_entry ld_last_entry_in_ots le_antisym le_trans less_irrefl_nat less_or_eq_imp_le linorder_neqE_nat)

  apply (subgoal_tac " (coh ts' t a) < length(memory ts' ) ")
  prefer 2
      apply (meson assms(2) aux coh_lc total_wfs_def)
apply (subgoal_tac " 0 \<le>  (coh ts t glb) ")
      prefer 2
      apply blast
 apply (subgoal_tac " total_wfs ts'" )
  prefer 2
  apply (unfold total_wfs_def)
   apply (intro conjI)
  using vbounded_preserved apply blast
  using mem_structured_preserved apply blast
       apply (metis OTSF_notempty_preserved assms(2) total_OTSF_def total_wfs_def)
  apply (meson coh_loc_rel_preserved le_in_oats le_in_opts le_in_ots lev_in_oav lev_in_opv lev_in_ov)
     apply (subgoal_tac " coh ts t glb < coh ts' t a ")
      prefer 2
      apply (subgoal_tac " coh ts' t a < length(memory ts') ")
  prefer 2
  apply blast

apply (subgoal_tac "  comploc ((memory ts)!(coh ts' t a))  a = a ")
       prefer 2
  using assms(2) ld_vrnew_gr_coh apply presburger
  using gr_last_entry_lim total_wfs_def apply presburger
     apply  (unfold  mem_tml_prop_def  )
  apply (subgoal_tac " coh ts t glb <  coh ts' t a \<and>
          a \<noteq> glb \<and>
          0 \<le> coh ts t glb \<and>
          coh ts' t a  < length (memory ts') \<and>
          comploc (memory ts' ! coh ts t glb) glb = glb \<and>
          even (compval ts' (memory ts' ! coh ts t glb) glb) \<and>
          Msg.loc (memory ts' ! coh ts' t a) = a \<longrightarrow>
          (\<exists>k> coh ts t glb . k < coh ts' t a \<and>
                 Msg.loc (memory ts' ! k) = glb \<and>
                 odd (Msg.val (memory ts' ! k)))" )
      prefer 2
      apply presburger
  apply (subgoal_tac " coh ts t glb <  coh ts' t a \<and>
          a \<noteq> glb \<and>
          0 \<le> coh ts t glb \<and>
          coh ts' t a  < length (memory ts') \<and>
          comploc (memory ts' ! coh ts t glb) glb = glb \<and>
          even (compval ts' (memory ts' ! coh ts t glb) glb) \<and>
          Msg.loc (memory ts' ! coh ts' t a) = a")
  prefer 2
      apply (intro conjI)
  apply blast
           apply blast
          apply blast
         apply blast
       apply blast
  apply (metis cas_fail_crash)  
  apply (metis (no_types, lifting) bot_nat_0.not_eq_extremum i_noteqo_loc less_nat_zero_code total_wfs_def)
   apply blast 
(*******stop******)
  apply (subgoal_tac " \<exists>k.  k > (coh ts t glb )  \<and>  k < vrnew ts' t   \<and> Msg.loc((memory ts')!k)  = glb \<and> odd (  Msg.val((memory ts')!k))
\<and> (\<forall> j. 0 \<le> j \<and> j < k \<longrightarrow> \<not> notoverwritten ts' (vrnew ts' t)  j  glb) ")
   prefer 2
   apply (unfold notoverwritten_def)

  apply (smt (verit, ccfv_threshold) aux coh_lc le_antisym le_neq_implies_less le_trans less_or_eq_imp_le)

  apply (subgoal_tac " \<exists>k.  k > (coh ts t glb )  \<and>  k <  coh ts' t a    \<and> Msg.loc((memory ts')!k)  = glb \<and> odd (  Msg.val((memory ts')!k))
\<and> (\<forall> j. 0 \<le> j \<and> j < k \<longrightarrow> \<not> notoverwritten ts' (vrnew ts' t)  j  glb) ")
   prefer 2
   apply (unfold notoverwritten_def)
  apply (smt (verit, ccfv_threshold) aux coh_lc le_antisym le_neq_implies_less le_trans less_or_eq_imp_le)

 apply (subgoal_tac " \<exists>k.  k > (coh ts t glb )  \<and>  k <   coh ts' t a     \<and> Msg.loc((memory ts')!k)  = glb \<and> odd (  Msg.val((memory ts')!k))
\<and> (\<forall> j. 0 \<le> j \<and> j < k \<longrightarrow> j \<notin>  (OTS  ts' t glb) )"  )
   prefer 2
 apply (simp add: OTS_def)
   apply (simp add: OTSF_def)
  apply (metis (no_types, lifting)  notoverwritten_def)
  by (metis le_neq_implies_less nat_le_linear zero_le)




lemma ld_coh_noteq_last_entry_lim:
 assumes "thrdsvars"
 and "total_wfs ts"
 and  "step t ( Load a  val) ts ts'"
 and "a \<noteq> glb"
and "even (   ( compval ts ((memory ts)!  (coh ts t glb )  ) glb) )  "
and " (coh ts t glb ) > 0 "
and " mem_tml_prop   glb  a (ts) "
and " glb_monotone_inv  ts' "
and "  vrnew ts' t \<ge>  coh ts' t a " 
and " vrnew ts' t \<ge> last_entry_lim ts' a (coh ts t glb) "
shows " (coh ts' t a \<noteq> last_entry_lim  ts' a (coh ts t glb ) ) \<longrightarrow>  compval ts ((memory ( ts'))!( (coh ts t glb ))) glb  \<notin>  [glb]\<^sub>t ts'  "

  using assms
 apply (subgoal_tac "  even ( compval ts' ((memory ts')!(coh ts t glb )) glb)" )
   prefer 2
  apply (simp add: step_def compval_def)
      apply (subgoal_tac " memory ts = memory ts' ")
  prefer 2
  using mem_ld_trans apply blast

  apply (metis (full_types) assms(3) survived_val_preserved_load)

   apply (subgoal_tac " \<forall>  i. i \<in> last_entry_set_lim  ts' a (coh ts t glb )   \<longrightarrow> i \<le>   coh ts t glb ")
    prefer 2
   apply (simp add:  last_entry_set_lim_def)

  apply (subgoal_tac " last_entry_lim  ts' a (coh ts t glb )  \<le> (coh ts t glb )  ")
   prefer 2
  using  finite_last_entry_set_lim total_wfs_def 
  using last_entry_lim_in_last_entry_set_lim mem_structured_preserved vbounded_preserved apply blast
  apply (simp add: OTS_def)
  apply (simp add: OTSF_def)
  apply (intro impI conjI)
  apply (case_tac "  coh ts' t a > last_entry_lim ts' a (coh ts t glb)")
    apply (subgoal_tac "   vrnew ts' t  > last_entry_lim ts' a (coh ts t glb)")
    prefer 2
     apply linarith
    apply (subgoal_tac " mem_tml_prop   glb  a (ts') " )
  prefer 2
  using assms(1) ld_mem_inv apply presburger
   apply (subgoal_tac " coh ts t glb  \<notin> (OTS  ts' t glb) ")
    prefer 2
  apply (meson assms(1) assms(5) assms(6) ld_last_entry_lim)

  apply (subgoal_tac "   ( \<exists>k.  k > (coh ts t glb )  \<and>  k <coh ts' t a  \<and>  Msg.loc((memory ts')!k)  = glb \<and> odd (  Msg.val((memory ts')!k)) \<and>
(  \<forall> i. i \<in>  (OTS  ts' t glb) \<longrightarrow> k  \<le> i) )")
    prefer 2
  using   ld_coh_le_ots [where a= a and ts = ts and ts' = ts' ]
  using assms(1) assms(5) apply blast


   apply (subgoal_tac " coh ts' t a  < length (memory ts' ) ")
  prefer 2
    apply (simp add: total_wfs_def)
    apply (meson aux coh_lc)
   apply (subgoal_tac " total_wfs ts' ")
    prefer 2
    apply (simp add: total_wfs_def)
    apply (intro conjI )
  using vbounded_preserved apply blast
  using mem_structured_preserved apply blast
  apply (meson OTSF_notempty_preserved total_OTSF_def)
  apply (meson coh_loc_rel_preserved le_in_oats le_in_opts le_in_ots lev_in_oav lev_in_opv lev_in_ov)
  apply (subgoal_tac "   ( \<exists>\<theta> .0 <\<theta> \<and>  \<theta> > (coh ts t glb )  \<and> \<theta>< length (memory ts' ) \<and>  \<theta> <coh ts' t a  \<and>  Msg.loc((memory ts')!\<theta>)  = glb \<and> odd (  Msg.val((memory ts')!\<theta>)) \<and>
(  \<forall> i. i \<in>  (OTS  ts' t glb) \<longrightarrow> \<theta>  \<le> i) )")
    prefer 2

  apply (smt (verit, ccfv_SIG) Suc_lessD less_trans_Suc neq0_conv)

apply (subgoal_tac "  \<forall> n. n \<in>  [glb]\<^sub>t ts'  \<longrightarrow>  (   (State.val((memory ( ts'))!((coh ts t glb))) )   <  n)")
    prefer 2

  apply (subgoal_tac " 0 < coh ts t glb \<and> coh ts t glb < length (memory ts')")
     prefer 2
     apply linarith
    apply (subgoal_tac "  even (Msg.val (memory ts' ! (coh ts t glb)))" )
  prefer 2
   apply (subgoal_tac " memory ts = memory ts' ")
      prefer 2
      apply (simp add: step_def)
  apply (metis mem_ld_trans)
     apply (simp add: compval_def)
     apply ( simp add: split if_splits )
     apply (subgoal_tac " (memory ts' ! (coh ts t glb)  \<noteq> Init_Msg) " )
      prefer 2
apply (elim conjE)
using mem_structured_def
  using total_wfs_def apply blast
  apply meson
  using fr apply blast
   apply (subgoal_tac "0 \<notin>  [glb]\<^sub>t ts'  ")
    prefer 2
    apply blast
  apply (subgoal_tac "   compval ts (memory ts' ! coh ts t glb) glb =
 Msg.val (memory ts' ! coh ts t glb )")
    prefer 2
   apply (subgoal_tac " memory ts = memory ts' ")
      prefer 2
      apply (simp add: step_def)
  apply (metis mem_ld_trans)
     apply (simp add: compval_def)
     apply ( simp add: split if_splits )
     apply (subgoal_tac " (memory ts' ! (coh ts t glb)  \<noteq> Init_Msg) " )
      prefer 2
apply (elim conjE)
using mem_structured_def
  using total_wfs_def
  apply (metis Suc_lessD less_trans_Suc)
   apply simp
 apply (simp add: OTS_def)
  apply (simp add: OTSF_def)
   apply (meson less_irrefl_nat)
 apply (subgoal_tac " coh ts' t a < last_entry_lim ts' a (coh ts t glb)  ")
  prefer 2
    apply linarith
   apply (subgoal_tac " coh ts' t a  \<notin> (OTS  ts' t a) ")
    prefer 2
    apply (unfold OTS_def)
    apply (unfold OTSF_def)
    apply clarify
    apply (subgoal_tac "\<not>  notoverwritten ts' (vrnew ts' t) (coh ts' t a) a ")
     prefer 2
     apply (subgoal_tac "   last_entry_lim ts' a (coh ts t glb) < length (memory ts') \<and>  last_entry_lim ts' a (coh ts t glb) \<le> vrnew ts' t \<and>
 coh ts' t a <  last_entry_lim ts' a (coh ts t glb) \<and>
              Msg.loc (memory ts' !  last_entry_lim ts' a (coh ts t glb)) =  a")
      prefer 2
      apply (intro conjI)
  apply (metis assms(2) assms(3) last_entry_lim_bounded mem_structured_preserved total_wfs_def vbounded_preserved)
  apply blast
  apply blast
 apply (subgoal_tac " total_wfs ts'" )
  prefer 2
  apply (unfold total_wfs_def)
   apply (intro conjI)
  using vbounded_preserved 
  apply meson
  using mem_structured_preserved apply meson
    apply (meson OTSF_notempty_preserved total_OTSF_def)
  apply (metis (no_types, lifting) OTS_def coh_loc_rel_preserved lastVal_def le_in_oats le_in_opts le_in_otsf lev_in_oav lev_in_opv opv_opts_rel)
  apply (metis (no_types, lifting) bot_nat_0.not_eq_extremum i_noteqo_loc last_entry_lim_bounded last_entry_lim_loc total_wfs_def)
  apply (metis (no_types, lifting) notoverwritten_def)
  apply blast
  by (metis OTSF_def OTS_def assms(3) coh_lc)





lemma ld_coh_noteq_last_entry_lim_fin:
 assumes "thrdsvars"
 and "total_wfs ts"
 and  "step t ( Load a  val) ts ts'"
 and "a \<noteq> glb"
and "even (   ( compval ts ((memory ts)!  (coh ts t glb )  ) glb) )  "
and " (coh ts t glb ) > 0 "
and " mem_tml_prop   glb  a (ts) "
and " glb_monotone_inv  ts "
and "  vrnew ts t \<ge>  coh ts t a " 
and " vrnew ts t \<ge> last_entry_lim ts  a (coh ts t glb) "
and " regs  ts t loc =   compval ts ((memory ( ts))!( (coh ts t glb ))) glb "

shows " (coh ts' t a \<noteq> last_entry_lim  ts' a (coh ts' t glb ) ) \<longrightarrow>  regs ts' t  loc  \<notin>  [glb]\<^sub>t ts'  "
  using assms
apply (unfold total_wfs_def)
  apply (subgoal_tac "memory ts' = memory ts ")
  prefer 2
  using ld_step_mem apply presburger

  apply (subgoal_tac " glb_monotone_inv  ts'")
   prefer 2
   apply (unfold  glb_monotone_inv_def)
   apply (metis ld_crash)
  apply (subgoal_tac " coh ts' t glb = coh ts t glb ")
   prefer 2
  using coh_ld_st_dadrr apply presburger
  apply (subgoal_tac " vrnew ts' t \<ge>  coh ts' t a ")
   prefer 2
  using ld_coh_lt_vrew_simp  
  using assms(2) apply presburger
  apply (subgoal_tac " vrnew ts' t \<ge> last_entry_lim ts' a (coh ts t glb) ")
   prefer 2
  using Load_Rules.vrnew_ld_st_sadrr assms(2) ld_le_lim_ni le_trans apply presburger
  apply (subgoal_tac "  regs ts' t  loc =  regs ts t  loc ")
   prefer 2
   apply (simp add: step_def)
  apply (metis assms(3) reg_same_ld_dt)
   by (metis assms(2) glb_monotone_inv_def ld_coh_noteq_last_entry_lim)



end






