(*Showing local correctness of the DTML Begin annotation*)
theory Begin
imports "../DTML" 

begin

lemma ld_coh_le_vrew:
assumes "ts [r   \<leftarrow> a ]\<^sub>t ts'"
and " ( (coh ts t b \<le> vrnew ts  t) ) "
and "total_wfs ts"
shows   "  (  (coh ts' t b  \<le> vrnew ts' t) ) "
  using assms
  apply (case_tac " a = b ")
   apply (simp add:  step_def)
   apply (simp add: load_trans_def  Let_def)
   apply clarify
   apply (subgoal_tac "  coh ts' t a \<le> vrnew ts' t" )
    prefer 2
    apply (case_tac "  ind \<noteq> coh ts  t a ")
     apply (subgoal_tac "  (coh ts' t a ) = ind")
      prefer 2
      apply simp
     apply ( simp  add: split: if_split_asm)
    apply ( simp  add: split: if_split_asm)
   apply blast
  apply (unfold total_wfs_def)
  by (metis Load_Rules.vrnew_ld_st_sadrr assms(1) coh_ld_st_dadrr dual_order.trans)

(*add: replace_append*)

(*del: comploc_def compval_def*)

(*auxiliary lemma*)
lemma  ld_begin_lv1 :
assumes " (\<tau> \<sigma>) [loc   \<leftarrow> glb ]\<^sub>t (\<tau> \<sigma>')  "
and " t \<noteq> syst"
and " total_wfs (\<tau> \<sigma>) "
and"   glb_monotone_complete_inv  (\<tau> \<sigma>) " 
and " mem_tml_prop4 (\<tau> \<sigma>)  "
and " (writer \<sigma> = None ) "
and "  (\<forall> n. (0 \<le> n \<and> n  < length (memory (\<tau> \<sigma>))  \<and> comploc ((memory (\<tau> \<sigma>))!n) glb= glb) \<longrightarrow>  (valOf n glb  (\<tau> \<sigma>)) \<le> lastVal glb  (\<tau> \<sigma>) )"
and   " \<forall>  t.  ( writer \<sigma> = Some t \<longrightarrow> odd (lastVal glb  (\<tau> \<sigma>)) )"
and  " \<forall>t. (writer \<sigma> = None \<and>   pc \<sigma> syst = RecIdle  )  \<longrightarrow> (  (comploc ((memory (\<tau> \<sigma>))!  (length( memory (\<tau> \<sigma>))-1)  ) glb  )      = glb) " 
and "  (  compval (\<tau> \<sigma>) (memory (\<tau> \<sigma>) ! 0) glb = survived_val (\<tau> \<sigma>) glb ) "
and "  pc \<sigma> syst = RecIdle "
shows  "  (\<forall> n. (0  \<le> n \<and> n  < length (memory (\<tau> \<sigma>))  \<and> comploc ((memory (\<tau> \<sigma>))!n) glb= glb \<and>
      compval (\<tau> \<sigma>) (memory (\<tau> \<sigma>) ! n) glb  =  lastVal glb  (\<tau> \<sigma>) ) \<longrightarrow>
(\<nexists> j. j \<ge>n  \<and> j < length (memory (\<tau> \<sigma>)) \<and> comploc ((memory (\<tau> \<sigma>))!j) glb \<noteq> glb)    ) "
  using assms
  apply (unfold total_wfs_def)
  apply (simp  add: step_def  )
  apply (subgoal_tac "  (length( memory (\<tau> \<sigma>))-1)      =  (last_entry (\<tau> \<sigma>)  glb)   ")
   prefer 2
   apply (simp add:  last_entry_def)
   apply (subgoal_tac "  (length( memory (\<tau> \<sigma>))-1)  \<in> last_entry_set (\<tau> \<sigma>) glb ")
    prefer 2
    apply (simp add: last_entry_set_def)
    apply (metis diff_Suc_less gr0I gr_implies_not_zero last_entry_bounded)
  using  finite_last_entry_set last_entry_in_last_entry_set 
   apply (metis Max.coboundedI One_nat_def Suc_diff_1 last_entry_bounded last_entry_def le_less_Suc_eq less_nat_zero_code neq0_conv)
  apply (subgoal_tac "  (\<forall> n. (0  \<le> n \<and> n \<le>  (last_entry (\<tau> \<sigma>)  glb)  \<and>   Msg.loc (memory (\<tau> \<sigma>) ! n)  = glb \<and>
      compval (\<tau> \<sigma>) (memory (\<tau> \<sigma>) ! n) glb  =  lastVal glb  (\<tau> \<sigma>) ) \<longrightarrow>
(\<nexists> j. j \<ge>n \<and> j < length (memory (\<tau> \<sigma>))  \<and>  Msg.loc (memory (\<tau> \<sigma>) ! j)   \<noteq> glb)    ) ")
   prefer 2
   apply (unfold  mem_tml_prop4_def)
   apply clarify
   apply (subgoal_tac "  last_entry (\<tau> \<sigma>)  glb  < length (memory (\<tau> \<sigma>) ) ")
    prefer 2
    apply (metis last_entry_bounded)
   apply (smt (z3) Nat.lessE One_nat_def comploc_def diff_Suc_1 i_noteqo_loc lastVal_def le_neq_implies_less not_less_eq zero_less_Suc)
  apply clarify
  apply (subgoal_tac " memory  (\<tau> \<sigma>) = memory (\<tau> \<sigma>') ")
   prefer 2
  using mem_ld_trans apply presburger
  apply safe
   apply (unfold  mem_structured_def)
   apply (smt (z3) Nat.lessE One_nat_def assms(10) comploc_def diff_Suc_1 diff_less lastVal_def le_less_Suc_eq le_numeral_extra(3) neq0_conv)
  by (metis Suc_diff_1 Suc_leI Suc_le_mono compval_def le0 length_greater_0_conv)


corollary ld_ind_eq_coh_tml :
assumes " \<tau> \<sigma>' = \<tau> \<sigma>
\<lparr>vrnew := (vrnew (\<tau> \<sigma>))
(t := max (vrnew (\<tau> \<sigma>) t) (if ind \<noteq> coh (\<tau> \<sigma>) t glb then ind else vrnew (\<tau> \<sigma>) t)),
vpready := (vpready (\<tau> \<sigma>))
(t := max (vpready (\<tau> \<sigma>) t) (if ind \<noteq> coh (\<tau> \<sigma>) t glb then ind else vrnew (\<tau> \<sigma>) t)),
maxcoh := (maxcoh (\<tau> \<sigma>))(t := max (maxcoh (\<tau> \<sigma>) t) ind),
coh := (coh (\<tau> \<sigma>))(t := (coh (\<tau> \<sigma>) t)(glb := ind)),
regs := (regs (\<tau> \<sigma>))
(t := (regs (\<tau> \<sigma>) t)
(DTML.loc :=
if memory (\<tau> \<sigma>) ! ind = Init_Msg then survived_val (\<tau> \<sigma>) glb
else Msg.val (memory (\<tau> \<sigma>) ! ind)))\<rparr> "
shows "  ind  =   coh  ( \<tau> \<sigma>')  t glb"
  using assms
  by simp


corollary  ld_reg_compval_tml:
assumes "    \<tau> \<sigma>' = \<tau> \<sigma>
\<lparr>vrnew := (vrnew (\<tau> \<sigma>))
(t := max (vrnew (\<tau> \<sigma>) t) (if ind \<noteq> coh (\<tau> \<sigma>) t glb then ind else vrnew (\<tau> \<sigma>) t)),
vpready := (vpready (\<tau> \<sigma>))
(t := max (vpready (\<tau> \<sigma>) t) (if ind \<noteq> coh (\<tau> \<sigma>) t glb then ind else vrnew (\<tau> \<sigma>) t)),
maxcoh := (maxcoh (\<tau> \<sigma>))(t := max (maxcoh (\<tau> \<sigma>) t) ind),
coh := (coh (\<tau> \<sigma>))(t := (coh (\<tau> \<sigma>) t)(glb := ind)),
regs := (regs (\<tau> \<sigma>))
(t := (regs (\<tau> \<sigma>) t)
(DTML.loc :=
if memory (\<tau> \<sigma>) ! ind = Init_Msg then survived_val (\<tau> \<sigma>) glb
else Msg.val (memory (\<tau> \<sigma>) ! ind)))\<rparr>  "
shows "  compval  (\<tau> \<sigma>)  (memory  (\<tau> \<sigma>) ! ind) glb =  regs  (\<tau> \<sigma>')  t  DTML.loc  "
  using assms ld_reg_compval
  by (smt (verit) TState.unfold_congs(1) TState.unfold_congs(2) TState.unfold_congs(3) TState.unfold_congs(4) TState.unfold_congs(7) compval_def load_trans_def)

(*auxiliary lemma*)
lemma beg_load_ind_case:
assumes "  \<forall> j. j > 0 \<and>  j  < length (memory (\<tau> \<sigma>'))  \<longrightarrow> j \<notin>     OTS (\<tau>  \<sigma>') t l   "
and "  OTS (\<tau>  \<sigma>') t l \<noteq> {} "
and " \<forall> i. i \<in>  OTS (\<tau>  \<sigma>') t l \<longrightarrow> 0 \<le> i \<and> i < length (memory (\<tau> \<sigma>')) " 
shows "  OTS (\<tau>  \<sigma>') t l = {0}   "
  using assms
  by (metis insertCI not_gr_zero subset_iff subset_singletonD)

(*auxiliary lemma*)
lemma  ld_begin_lv_writer_none :
assumes " (\<tau> \<sigma>) [loc   \<leftarrow> glb ]\<^sub>t (\<tau> \<sigma>')  "
and " t \<noteq> syst"
and " total_wfs (\<tau> \<sigma>) "
and"   glb_monotone_complete_inv  (\<tau> \<sigma>) "
and " mem_tml_prop4 (\<tau> \<sigma>)  "
and " (writer \<sigma> = None ) "
and "  (\<forall> n. (0 \<le> n \<and> n  < length (memory (\<tau> \<sigma>))  \<and> comploc ((memory (\<tau> \<sigma>))!n) glb= glb) \<longrightarrow>  (valOf n glb  (\<tau> \<sigma>)) \<le> lastVal glb  (\<tau> \<sigma>) )"
and   " \<forall>  t.  ( writer \<sigma> = Some t \<longrightarrow> odd (lastVal glb  (\<tau> \<sigma>)) )"
and "  (  compval (\<tau> \<sigma>) (memory (\<tau> \<sigma>) ! 0) glb = survived_val (\<tau> \<sigma>) glb ) " 
and  " \<forall>t. (writer \<sigma> = None \<and>   pc \<sigma> syst = RecIdle  )  \<longrightarrow> (  (comploc ((memory (\<tau> \<sigma>))!  (length( memory (\<tau> \<sigma>))-1)  ) glb  )      = glb) "  
and "  pc \<sigma> syst = RecIdle "
and "   coh (\<tau> \<sigma>) t glb  \<le>  vrnew (\<tau> \<sigma>) t "
shows " regs (\<tau> \<sigma>') t DTML.loc = lastVal glb (\<tau> \<sigma>') \<and>
(\<forall>l. [l]\<^sub>t \<tau> \<sigma>' = {lastVal l (\<tau> \<sigma>')}) \<or>  regs (\<tau> \<sigma>') t DTML.loc < lastVal glb (\<tau> \<sigma>')"
  using assms (1,3)
  apply (unfold total_wfs_def)
  apply (case_tac " lastVal glb  (\<tau> \<sigma>')  =  regs (\<tau> \<sigma>' ) t loc ")
   apply (simp  add: step_def  )
   apply (simp add: load_trans_def Let_def   )
   apply clarify
   apply (subgoal_tac "  coh (\<tau> \<sigma>') t glb  \<le>  vrnew (\<tau> \<sigma>') t  ")
    prefer 2
  using assms(1) assms(12) assms(3) ld_coh_le_vrew le_eq_less_or_eq apply blast
   apply (subgoal_tac " coh (\<tau> \<sigma>') t glb = ind ")
    prefer 2
  using  ld_ind_eq_coh_tml [where \<sigma> = \<sigma> and \<sigma>'  = \<sigma>' ]
    apply (metis assms(12))
   apply (subgoal_tac "  (vrnew (\<tau> \<sigma>') t)  \<ge> ind ")
    prefer 2
    apply blast
   apply (subgoal_tac "    compval (\<tau> \<sigma>) (memory (\<tau> \<sigma>) ! ind) glb  =  lastVal glb  (\<tau> \<sigma>) ")
    prefer 2
    apply (subgoal_tac "  compval  (\<tau> \<sigma>)  (memory  (\<tau> \<sigma>) ! ind) glb =  regs  (\<tau> \<sigma>')  t  DTML.loc  ")
  using ld_reg_compval_tml
     apply (metis assms(1) assms(3) lastVal_ni)
  using ld_reg_compval_tml apply blast
   apply (subgoal_tac "    (\<forall> n. (0  \<le> n \<and> n  < length (memory (\<tau> \<sigma>))  \<and> comploc ((memory (\<tau> \<sigma>))!n) glb= glb \<and>
      compval (\<tau> \<sigma>) (memory (\<tau> \<sigma>) ! n) glb  =  lastVal glb  (\<tau> \<sigma>) ) \<longrightarrow>
(\<nexists> j. j \<ge>n  \<and> j < length (memory (\<tau> \<sigma>)) \<and> comploc ((memory (\<tau> \<sigma>))!j) glb \<noteq> glb))    ")
    prefer 2
  using  ld_begin_lv1[where \<sigma>= \<sigma> and t =t and \<sigma>' = \<sigma>' ]
  using assms(1) assms(10) assms(11) assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) assms(9) apply blast
   apply (case_tac " l \<noteq> glb") (**************1************)
    apply (case_tac " ind = 0 ") (**************2************)
     apply (subgoal_tac "    compval (\<tau> \<sigma>') (memory (\<tau> \<sigma>') ! 0) glb  =  lastVal glb  (\<tau> \<sigma>') ")
      prefer 2
      apply (metis assms(1) assms(3) lastVal_ni ld_crash ld_step_mem)

     apply (subgoal_tac "  comploc ((memory (\<tau> \<sigma>'))!0) glb= glb  ")
      prefer 2
      apply (metis assms(1) comploc_ots ld_step_mem)
     apply (subgoal_tac "    (\<forall> n. (0  \<le> n \<and> n  < length (memory (\<tau> \<sigma>'))  \<and> comploc ((memory (\<tau> \<sigma>'))!n) glb= glb \<and>
      compval (\<tau> \<sigma>') (memory (\<tau> \<sigma>') ! n) glb  =  lastVal glb  (\<tau> \<sigma>') ) \<longrightarrow>
(\<nexists> j. j \<ge>n  \<and> j < length (memory (\<tau> \<sigma>')) \<and> comploc ((memory (\<tau> \<sigma>'))!j) glb \<noteq> glb))    ")
      prefer 2
      apply (metis assms(1) aux bot_nat_0.extremum comploc_ots ld_step_mem)
     apply (subgoal_tac "( \<forall> j. j > 0 \<and>  j  < length (memory (\<tau> \<sigma>'))  \<longrightarrow> j \<notin>     OTS (\<tau>  \<sigma>') t l )  ")
      prefer 2
      apply (metis assms(1) aux comploc_ots i_noteqo_loc ld_step_mem)
     apply (subgoal_tac " OTS (\<tau>  \<sigma>') t l = {0}   ")
      prefer 2
      apply (subgoal_tac " total_wfs ( \<tau> \<sigma>')")
       prefer 2
       apply (metis assms(1) assms(3) ld_wfs_preserved)
      apply (subgoal_tac " OTS (\<tau>  \<sigma>') t l \<noteq> {}   ")
       prefer 2
  using total_wfs_def 
       apply (metis emptyE)
      apply (subgoal_tac " \<forall> i. i \<in>  OTS (\<tau>  \<sigma>') t l \<longrightarrow> 0 \<le> i \<and> i < length (memory (\<tau> \<sigma>')) ")
       prefer 2
       apply (metis aux)
      apply (metis beg_load_ind_case)
  using mapval_def
     apply (metis assms(1) assms(3) bot_nat_0.not_eq_extremum image_empty image_insert lastVal_def last_entry_bounded ld_wfs_preserved mem_structured_preserved total_wfs_def vbounded_preserved)
    apply (unfold  mapval_def)
    apply (subgoal_tac " \<forall>i . i \<ge>   (vrnew (\<tau> \<sigma>') t) \<and> i < length (memory (\<tau> \<sigma>')) \<longrightarrow>  comploc ((memory (\<tau> \<sigma>'))!i) glb = glb ")
     prefer 2
     apply (smt (z3) assms(1) aux bot_nat_0.not_eq_extremum comploc_ots ld_step_mem le_trans)
    apply (subgoal_tac " \<forall>i . i \<ge>   (vrnew (\<tau> \<sigma>') t) \<and> i < length (memory (\<tau> \<sigma>')) \<longrightarrow>  comploc ((memory (\<tau> \<sigma>'))!i) l \<noteq> l ")
     prefer 2
  using comploc_def mem_structured_def
     apply (metis assms(1) bot_nat_0.extremum_uniqueI mem_structured_preserved zero_less_iff_neq_zero)
    apply (subgoal_tac " last_entry (\<tau> \<sigma>')  l \<le>  (vrnew (\<tau> \<sigma>') t) ")
     prefer 2
     apply (simp(no_asm) add: last_entry_def )
     apply (subgoal_tac " \<forall>i . i \<ge>   (vrnew (\<tau> \<sigma>') t) \<and> i < length (memory (\<tau> \<sigma>')) \<longrightarrow> i \<notin>  (last_entry_set (\<tau> \<sigma>') l)  ")
      prefer 2
      apply (subgoal_tac "\<forall> i. i \<in>  (last_entry_set (\<tau> \<sigma>') l)  \<longrightarrow>  comploc ((memory (\<tau> \<sigma>'))!i) l  = l   ")
       prefer 2
       apply (smt (z3) last_entry_set_def mem_Collect_eq)
      apply (metis assms(1) assms(8) bot_nat_0.extremum_uniqueI compval_def ld_step_mem less_nat_zero_code loc_eq_comploc nat_neq_iff valOf_def)
  using  finite_last_entry_set  last_entry_in_last_entry_set
     apply (metis assms(1) last_entry_bounded last_entry_def mem_structured_preserved nat_le_linear vbounded_preserved)
    apply (subgoal_tac "  (OTS  (\<tau> \<sigma>')  t l) =  {(last_entry (\<tau>  \<sigma>') l) } ")
     prefer 2
     apply (subgoal_tac " (last_entry (\<tau>  \<sigma>') l) \<in>   (OTS  (\<tau> \<sigma>')  t l) ")
      prefer 2
      apply (metis assms(1) assms(3) ld_wfs_preserved total_wfs_def)

     apply (subgoal_tac" \<forall>  n. n < (last_entry (\<tau>  \<sigma>') l) \<longrightarrow>n \<notin>    (OTS  (\<tau> \<sigma>')  t l) ")
      prefer 2
  apply (subgoal_tac" \<forall>  n. n < (last_entry (\<tau>  \<sigma>') l) \<longrightarrow>\<not>    notoverwritten (\<tau> \<sigma>') (vrnew (\<tau> \<sigma>') t) n  l   ")
  prefer 2
  apply (simp(no_asm) add: notoverwritten_def)
  apply (metis assms(1) aux bot_nat_0.not_eq_extremum comploc_ots i_noteqo_loc ld_step_mem less_nat_zero_code)
  apply (simp(no_asm) add: OTS_def OTSF_def) 
  apply meson
  apply (subgoal_tac" \<forall>  n. n > (last_entry (\<tau>  \<sigma>') l) \<longrightarrow>n \<notin>    (OTS  (\<tau> \<sigma>')  t l) ")
  prefer 2
  apply (subgoal_tac" \<forall>  n. n > (last_entry (\<tau>  \<sigma>') l)\<and> n < length (memory (\<tau> \<sigma>')) \<longrightarrow> comploc ((memory (\<tau> \<sigma>'))!n) l \<noteq> l  ")
  prefer 2
  using  last_entry_last_comp_loc 
  using assms(1) assms(3) ld_wfs_preserved apply presburger
  apply (simp(no_asm) add: OTS_def OTSF_def) 
  apply (metis comploc_def)
  apply (subgoal_tac "\<forall>n. n \<in>   OTS (\<tau> \<sigma>') t l \<longrightarrow> n = last_entry (\<tau> \<sigma>') l  ")
  prefer 2
  apply (meson linorder_neqE_nat)
  apply (metis empty_iff insertI1 subsetI subset_singleton_iff)
  apply (simp(no_asm) add: mapval_def lastVal_def) 
  apply (smt (z3) Int_empty_left Int_insert_left_if0 Int_insert_left_if1 Un_commute Un_empty_right image_empty image_insert mem_Collect_eq)
  apply (subgoal_tac "\<forall>n. n \<in>   OTS (\<tau> \<sigma>') t l \<longrightarrow>    compval (\<tau> \<sigma>') (memory (\<tau> \<sigma>') ! n) glb  =  lastVal glb  (\<tau> \<sigma>') ")
  prefer 2
  apply (subgoal_tac "(\<forall>i . i \<in> OTS  (\<tau> \<sigma>') t l \<longrightarrow> coh  (\<tau> \<sigma>') t l \<le> i) ") 
  prefer 2
  apply (metis assms(1) assms(3) coh_lc total_wfs_def)
  apply (subgoal_tac "  ind  =   coh  (\<tau> \<sigma>') t l")
  prefer 2
  apply (metis ld_ind_eq_coh_tml)
  apply (subgoal_tac "  \<forall> i. i \<in>  OTS (\<tau> \<sigma>)  t glb \<longrightarrow> 0 \<le> i  \<and> i < length (memory (\<tau> \<sigma>))  ")
  prefer 2
  using aux apply presburger
  apply (smt (z3) assms(1) assms(3) assms(4) assms(7) aux comploc_ots glb_monotone_complete_inv_def gr0I lastVal_ni ld_step_mem ld_valOf_nle_ni le_antisym valOf_def)
  apply safe
  apply (smt (z3) antisym_conv2 assms(1) assms(3) assms(4) assms(7) aux coh_lc comploc_ots glb_monotone_complete_inv_def lastVal_ni ld_step_mem ld_valOf_nle_ni le_antisym max.absorb2 max_def total_wfs_def valOf_def)
  apply (subgoal_tac " memory (\<tau> \<sigma> ) = memory (\<tau> \<sigma>') ")
  prefer 2
  using assms(1) ld_step_mem apply presburger
  apply (subgoal_tac "  total_wfs (\<tau> \<sigma>' ) ")
  prefer 2
  using assms(1) assms(3) ld_wfs_preserved apply presburger
  apply (smt (verit, ccfv_SIG) assms(3) image_eqI lastVal_def lastVal_ni ld_last_entry total_wfs_def)
  apply (smt (verit) assms(7) aux coh_lc coh_loc_rel_preserved lastVal_def ld_crash ld_last_entry ld_step_mem le_neq_implies_less reg_coh_lc valOf_def)
  using assms
  apply (smt (verit) aux bot_nat_0.extremum_uniqueI coh_lc comploc_ots glb_monotone_complete_inv_def lastVal_def ld_crash ld_last_entry_in_ots ld_step_mem le_neq_implies_less reg_coh_lc)
  by (metis lev_in_ov mapval_def)

(*auxiliary lemma*)
lemma  ld_begin_lv2 :
assumes " (\<tau> \<sigma>) [loc   \<leftarrow> glb ]\<^sub>t (\<tau> \<sigma>')  "
and " t \<noteq> syst"
and " total_wfs (\<tau> \<sigma>) "
and"   glb_monotone_complete_inv  (\<tau> \<sigma>) "
and " mem_tml_prop4 (\<tau> \<sigma>)  "
and "  (\<forall> n. (0 \<le> n \<and> n  < length (memory (\<tau> \<sigma>))  \<and> comploc ((memory (\<tau> \<sigma>))!n) glb= glb) \<longrightarrow>  (valOf n glb  (\<tau> \<sigma>)) \<le> lastVal glb  (\<tau> \<sigma>) )"
and "  (  compval (\<tau> \<sigma>) (memory (\<tau> \<sigma>) ! 0) glb = survived_val (\<tau> \<sigma>) glb ) " 
and   " \<forall>  t.  ( writer \<sigma> = Some t \<longrightarrow> odd (lastVal glb  (\<tau> \<sigma>)) )"
and  " \<forall>t. (writer \<sigma> = None \<and>   pc \<sigma> syst = RecIdle  )  \<longrightarrow> (  (comploc ((memory (\<tau> \<sigma>))!  (length( memory (\<tau> \<sigma>))-1)  ) glb  )      = glb) "   (*proved 1610*)
and "  pc \<sigma> syst = RecIdle "
and "   coh (\<tau> \<sigma>) t glb  \<le>  vrnew (\<tau> \<sigma>) t "
shows "even (regs (\<tau> \<sigma>') t DTML.loc) \<longrightarrow> ( regs (\<tau> \<sigma>') t DTML.loc = lastVal glb (\<tau> \<sigma>') \<and>
(\<forall>l. [l]\<^sub>t \<tau> \<sigma>' = {lastVal l (\<tau> \<sigma>')}) \<or>  regs (\<tau> \<sigma>') t DTML.loc < lastVal glb (\<tau> \<sigma>'))"
using assms
  apply (case_tac  " (writer \<sigma> = None ) " )
  using  ld_begin_lv_writer_none [where \<sigma> = \<sigma> and t = t and  \<sigma>' = \<sigma>'] 
  apply (metis option.discI)
  apply (subgoal_tac "even (regs (\<tau> \<sigma>') t DTML.loc) \<longrightarrow>  ( regs (\<tau> \<sigma>') t DTML.loc \<noteq> lastVal glb (\<tau> \<sigma>'))  ")
  prefer 2
  apply (metis lastVal_ni not_None_eq)
  apply (unfold valOf_def total_wfs_def)
  by (smt (z3) assms(3) aux bot_nat_0.extremum coh_lc lastVal_ni ld_crash ld_step_mem ld_vrnew_gr_coh le_neq_implies_less reg_coh_lc)



(*DTML Begin annotation is locally correct*)
lemma Begin_local:
assumes "thrdsvars"
and " t \<noteq> syst"
and " total_wfs (\<tau> \<sigma>) "
and"   glb_monotone_complete_inv  (\<tau> \<sigma>) " (*persistent invariant*)
and " mem_tml_prop4 (\<tau> \<sigma>)  "  (*persistent invariant*)
and "  (\<forall> n. (0 \<le> n \<and> n  < length (memory (\<tau> \<sigma>))  \<and> comploc ((memory (\<tau> \<sigma>))!n) glb= glb) \<longrightarrow>  (valOf n glb  (\<tau> \<sigma>)) \<le> lastVal glb  (\<tau> \<sigma>) )" (*persistent invariant*)
and   " \<forall>  t.  ( writer \<sigma> = Some t \<longrightarrow> odd (lastVal glb  (\<tau> \<sigma>)) )" (*persistent invariant*)
and "  (  compval (\<tau> \<sigma>) (memory (\<tau> \<sigma>) ! 0) glb = survived_val (\<tau> \<sigma>) glb ) "  (*persistent invariant*)
and  " \<forall>t. (writer \<sigma> = None \<and>   pc \<sigma> syst = RecIdle  )  \<longrightarrow> (  (comploc ((memory (\<tau> \<sigma>))!  (length( memory (\<tau> \<sigma>))-1)  ) glb  ) = glb) "   (*persistent invariant*) 
and "   (\<forall>i.  i \<in> OTS  (\<tau> \<sigma>) t glb \<longrightarrow> coh  (\<tau> \<sigma>) t glb \<le> i) " (*well formedness condtion*)
and   " \<forall>  t.  ( writer \<sigma> = Some t \<longrightarrow> odd (lastVal glb  (\<tau> \<sigma>)) )" (*persistent invariant*)
and " \<forall>t a. t = syst \<or> (writer \<sigma> = Some t)  \<or>    pc \<sigma> t = Committed \<or> pc \<sigma> t = CommitResponding \<or>   ( ( coh (\<tau> \<sigma>) t a) \<le> vrnew (\<tau> \<sigma>) t) " (*persistent invariant*)
and "Begin_inv t  ((pc \<sigma>) t) \<sigma>" 
and "TML_Begin  t   \<sigma> \<sigma>'"
shows "Begin_inv t  ((pc \<sigma>') t) \<sigma>'" 
  using assms
  apply (simp add:TML_Begin_def Begin_inv_def total_wfs_def   )
  apply (cases "pc \<sigma> t";simp  )
  apply (metis fun_upd_other)
  apply (intro conjI)
  using assms(3) ld_ov'_lc total_wfs_def apply blast
  apply (subgoal_tac "  coh (\<tau> \<sigma>) t glb \<le> vrnew (\<tau> \<sigma>) t ")
  prefer 2
  apply (metis PC.distinct(171) PC.distinct(173))
  using  ld_begin_lv2[where t = t and \<sigma>= \<sigma> and \<sigma>' =\<sigma>']
  using assms(3) assms(6) assms(8) assms(9) apply presburger
  apply (case_tac "  even (regs (\<tau> \<sigma>) t DTML.loc) ")
  apply simp
  apply (simp add: Ready_total_def)
  by simp


(*DTML intial state implies the  Begin annotation*)
lemma BeginInv_start:
assumes "total_wfs (\<tau> \<sigma>)"   
and "thrdsvars"
and "TML_start \<sigma>"
shows " \<forall>t \<noteq> syst. Begin_inv t  ((pc \<sigma>) t) \<sigma>"
using assms 
by (simp add: TML_start_def start_def Begin_inv_def mapval_def OTS_def st_OTSF )  




end

