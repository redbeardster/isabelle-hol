theory CAS_Rules
  imports "../State" "../Language"  "../Assertions"  "../Wellformedness"
begin

(* The lemmas that begin with the  comment "rule: __" are the proof rules regarding the CAS instruction.
   All the other lemmas are auxiliary and are used for proving the proof rules.
   Rules that end with "lc" concern mostly local correctness.
   Rules that end with "ni" concern  mostly  non-interference.
   Rules that end with "gen" concern non-interference and local correctness.
   Rules that end with "rel" concern relations between view sets. *) 

(*rule: If the value of the last write on x is different from v1 the CAS fails and so r = 0.*)
lemma cas_nlv_lc:
  assumes "mem_structured ts"
 and "vbounded ts"
and " step t ( CAS x  v1 v2 r) ts ts' "
and "   \<lceil>x:v3\<rceil> ts "
and "v1 \<noteq> v3"
shows "     regs ts' t r = 0 "
  using assms
  apply (simp add: step_def)
  apply (simp add:  cas_fail_trans_def)
  by force

(* If CAS succeeds   r = 1.*)
lemma cas_suc_reg:
assumes " ts' =   cas_succ_trans t ind x v1 v2 r nv1 nv2  ts "
 and "vbounded ts"
 and "mem_structured ts"
shows "  regs ts' t r = 1 "
  using assms
  by (simp add:  cas_succ_trans_def)


lemma cas_suc_loc:
 assumes   " ts' =   cas_succ_trans t ind x v1 v2 r nv1 nv2 ts "
 shows "loc ((memory (ts'))! (length(memory ts)) )   = x "
  using assms
  by (simp add: step_def)

lemma cas_suc_mem_l:
 assumes   " ts' =   cas_succ_trans t ind x v1 v2 r  nv1 nv2 ts "
 shows "(length( memory (ts'))-1) =  (length( memory (ts))) "
  using assms
  by (simp add: step_def)




(* If CAS fais  r = 0.*)
lemma cas_fail_reg:
assumes " ts' =   cas_fail_trans t ind x v1 v2 r   ts "
 and "vbounded ts"
 and "mem_structured ts"
shows "  regs ts' t r = 0 "
  using assms
  by (simp add:  cas_fail_trans_def)


lemma mem_l_cas_succ_step:
  assumes  " step t ( CAS x  v1 v2 r) ts ts' "
and  "regs ts' t r = 1 "
 and "vbounded ts"
 and "mem_structured ts"
    shows "(\<forall>i.(i\<ge>0\<and>i<length(memory ts)) \<longrightarrow> ( memory ts)!i =( memory ts')!i) "
  using assms
  apply (simp add:  step_def )
  by (metis cas_fail_reg le0 mem_l_casucc n_not_Suc_n)

lemma mem_length_cas_succ_step:
  assumes  " step t ( CAS x  v1 v2 r) ts ts' "
and  "regs ts' t r = 1 "
 and "vbounded ts"
 and "mem_structured ts"
    shows "length (memory ts' ) = length(memory ts) + 1 "
  using assms
  apply (simp add:  step_def )
  apply clarify
  apply (subgoal_tac "  ts' = cas_succ_trans t ind x v1 v2 r  nv mnv ts")
   prefer 2
  using cas_fail_reg apply auto[1]
  by simp


(*rule: If CAS on x  succeeds, last entry' x  is |M|-1*)
lemma cas_succ_lastentry:
  assumes "mem_structured ts"
 and "vbounded ts"
 and " ts' =   cas_succ_trans t ind x v1 v2  nv mnv r ts"
shows  " last_entry ts' x = length(memory ts')-1"
  using assms
  apply (subgoal_tac "  comploc ((memory ts') !(length(memory ts')-1)) x = x")
  prefer 2
    apply (simp add: store_trans_def)
   apply (subgoal_tac "( length(memory ts')-1 )\<in> last_entry_set ts' x")
    prefer 2
    apply (simp add: last_entry_set_def)
   apply (subgoal_tac " \<forall>i. (i \<in> last_entry_set ts' x) \<longrightarrow> i \<le> (length(memory ts')-1)")
    prefer 2
    apply (simp add: last_entry_set_def)
   apply (simp add: last_entry_def )
   apply (subgoal_tac" finite (last_entry_set ts' x )")
    prefer 2
  apply (simp add: last_entry_set_def)
  using Max_eqI by auto[1]


(*rule: If the CAS succeeds then the value of the last write on x becomes v2.*)
lemma cas_succ_lv_lc:
  assumes "mem_structured ts"
 and "vbounded ts"
and " step t ( CAS x  v1 v2 r) ts ts' "
and "    regs ts' t r = 1 "
shows "     \<lceil>x:v2\<rceil> ts' "
  using assms
  apply (simp add: step_def)
  apply clarify
  apply (subgoal_tac " ts' =   cas_fail_trans t ind x v1 v2 r ts \<longrightarrow>  regs ts' t r = 0 ")
   prefer 2
   apply (simp add: cas_fail_trans_def)
  apply (subgoal_tac " ts' \<noteq>    cas_fail_trans t ind x v1 v2 r ts" )
   prefer 2
   apply linarith
  apply (subgoal_tac " \<lceil>x:v1\<rceil> ts \<and>  ind = last_entry ts x")
   prefer 2
   apply (metis compval_def)
  apply (subgoal_tac  " ts' =    cas_succ_trans t ind x v1 v2 r  nv mnv ts")
   prefer 2
   apply presburger
  apply (subgoal_tac " last_entry ts' x = length(memory ts')-1") 
   prefer 2
   apply (meson cas_succ_lastentry)
  by simp

lemma [simp]:  " ts' =   cas_succ_trans t ind x v1 v2 r  nv mnv ts \<longrightarrow>  regs ts' t r = 1 "
  by (simp add: cas_succ_trans_def)

lemma [simp]: " ts' =   cas_fail_trans t ind x v1 v2 r ts \<longrightarrow>  regs ts' t r = 0 "
  by (simp add: cas_fail_trans_def)



(*rule: After thread t executes CAS, either r =1 and the value of last write on x becomes v1, or r=0.*)
lemma cas_lc:
  assumes "mem_structured ts"
 and "vbounded ts"
and " step t ( CAS x  v1 v2 r) ts ts' "
shows "    ( \<lceil>x:v2\<rceil> ts' \<and>  regs ts' t r = 1 ) \<or>  regs ts' t r= 0   "
  using assms
 apply (simp add: step_def)
  apply clarify
  apply (subgoal_tac " regs ts' t r = 1 \<longrightarrow> ts' = cas_succ_trans t ind x v1 v2 r  nv mnv ts")
   prefer 2
   apply auto[1]
  apply  (subgoal_tac " regs ts' t r = 1 \<longrightarrow>   \<lceil>x:v2\<rceil> ts'")
  prefer 2
  using assms(3) cas_succ_lv_lc apply blast
 apply (subgoal_tac " regs ts' t r = 0 \<longrightarrow> ts' = cas_fail_trans t ind x v1 v2 r ts")
   prefer 2
   apply auto[1]
  by (metis One_nat_def cas_fail_reg cas_suc_reg compval_def)



lemma cas_ots_lastentry:
 assumes  "mem_structured ts"
and "  ts' = cas_succ_trans ti ind x v1 v2 r  nv mnv ts "
shows " OTS ts' ti x = { length(memory ts')-1} "
using assms 
  apply(simp add:  mem_structured_def   OTS_def OTSF_def cas_succ_trans_def notoverwritten_def
  )
 apply (case_tac " 0 \<notin> OTS ts' ti x" )
   prefer 2
  using  assms   apply (simp add: OTS_def OTSF_def notoverwritten_def )
  using assms   apply  (subgoal_tac" ( coh ts' ti x > 0 )" )
    prefer 2
apply simp
  apply clarsimp
  by(auto simp add: split: Msg.split)



lemma cas_succ_ov_lc:
 assumes "mem_structured ts"
 and "vbounded ts"
 and " ts' = cas_succ_trans ti ind x v1 v2 r  nv mnv ts "
shows "  [x]\<^sub>ti ts' = {v2}"
  using assms 
  apply (subgoal_tac " OTS ts' ti x = { length(memory ts')-1}")
   prefer 2
  using cas_ots_lastentry apply blast
  by (simp add: mapval_def)


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



lemma cas_succ_ots_daddr_st:
assumes "mem_structured ts"
and "vbounded ts"
and " ts' = cas_succ_trans t' ind lx v1 v2 r nv mnv ts "
and " lx \<noteq> y "
shows " OTS ts' t y \<subseteq> OTS ts t y"
  using assms
 apply (subgoal_tac "  coh ts'  t y =  coh ts  t y")
    prefer 2
  apply (simp add: cas_succ_trans_def)

 apply (subgoal_tac "  vrnew ts  t \<le>  vrnew ts'  t ")
  prefer 2
     apply (simp add: cas_succ_trans_def)
    apply (simp add: OTS_def)
    apply (simp add: OTSF_def)
    apply (simp add: notoverwritten_def)
    apply safe
                  apply (metis Msg.sel(1) less_antisym nth_append_length)
  apply (metis bot.extremum_strict bot.extremum_unique bot_nat_def less_SucE mem_l mem_structured_def not_less_iff_gr_or_eq store_add)
                apply (metis Msg.sel(1) not_less_less_Suc_eq nth_append_length)
  apply (metis Msg.sel(1) bot.extremum bot_nat_def less_SucE mem_l nth_append_length store_add)
  apply (metis bot_nat_0.extremum le_trans less_eq_Suc_le mem_l not_le_imp_less not_less_iff_gr_or_eq store_add)
           apply (metis Msg.distinct(1) less_antisym nth_append_length)

(*  apply (metis (no_types, opaque_lifting) bot.extremum bot_nat_def dual_order.strict_trans le_trans less_not_refl mem_l not_less_less_Suc_eq store_add)*)

  apply (metis bot.extremum bot_nat_def dual_order.strict_trans le_trans less_not_refl mem_l not_less_less_Suc_eq store_add)
(*  apply (smt (z3) le_0_eq le_imp_less_Suc le_trans less_imp_le_nat mem_l nat_le_linear store_add)
  apply (metis (no_types, hide_lams) bot_nat_0.extremum le_trans less_eq_Suc_le mem_l not_le_imp_less not_less_iff_gr_or_eq store_add)*)
           apply (metis Msg.distinct(1) less_SucE nth_append_length)
  apply (metis Msg.distinct(1) less_SucE less_nat_zero_code mem_l not_le_imp_less nth_append_length store_add)
  apply (metis bot.extremum bot_nat_def length_append_singleton mem_structured_def store_add store_wfs verit_comp_simplify1(3) verit_la_disequality)
        apply (metis Msg.sel(1) less_antisym nth_append_length)
  apply (metis bot_nat_0.extremum le_trans less_eq_Suc_le mem_l not_le_imp_less not_less_iff_gr_or_eq store_add)
  apply (metis Msg.sel(1) less_antisym nth_append_length)
     apply (metis Msg.sel(1) bot.extremum bot_nat_def less_SucE mem_l nth_append_length store_add)
  by (metis (no_types) bot.extremum bot_nat_def dual_order.strict_trans le_trans less_not_refl mem_l not_less_less_Suc_eq store_add)


lemma cas_succ_ov_daddr_st:
assumes "mem_structured ts"
and "vbounded ts"
and " ts' = cas_succ_trans t' ind lx v1 v2 r  nv mnv ts "
and " lx \<noteq> y "
shows " [y]\<^sub>t ts'  \<subseteq> [y]\<^sub>t ts"
  using assms
  apply (subgoal_tac "  survived_val ts y = survived_val ts' y")
   prefer 2
  using survived_val_cas_succ apply blast
  apply (subgoal_tac " OTS ts' t y \<subseteq> OTS ts t y ")
   prefer 2
   apply (simp add: cas_succ_ots_daddr_st)
 apply (subgoal_tac " mapval ts y  (OTS ts t y)  (memory ts') = mapval ts y (OTS ts t y) (memory ts )")
 prefer 2
    apply (subgoal_tac "\<forall> i. i \<in> (OTS ts t y) \<longrightarrow> i < length (memory ts)")
    prefer 2
    apply (simp add: OTS_def)
   apply (unfold mapval_def )
  using mem_l_casucc apply auto[1]
  apply (simp )
  using Un_Int_assoc_eq by blast
 



lemma cas_succ_ots_daddr_dt:
assumes "mem_structured ts"
and "vbounded ts"
and " ts' = cas_succ_trans t' ind lx v1 v2 r  nv mnv ts "
and " lx \<noteq> y "
and "t \<noteq> t' "
shows " OTS ts' t y =  OTS ts t y"
  using assms
 apply (subgoal_tac "  coh ts'  t y =  coh ts  t y")
    prefer 2
  apply (simp add: cas_succ_trans_def)
 apply (subgoal_tac "  vrnew ts  t =  vrnew ts'  t ")
  prefer 2
    apply (simp add: cas_succ_trans_def)
   apply (subgoal_tac " (\<forall>i.(i\<ge>0\<and>i<length(memory ts)) \<longrightarrow> ( memory ts)!i =( memory ts')!i) ")
    prefer 2
  using mem_l_casucc apply blast
   apply (subgoal_tac" length( memory ts) \<notin>  OTS ts' t y")
  prefer 2
 apply (simp add: OTS_def)
    apply (simp add: OTSF_def)
  apply (simp add: OTS_def)
   apply (simp add: OTSF_def)
  apply (simp add: notoverwritten_def)
  apply safe
  apply (simp_all)
                      apply (metis Msg.sel(1) not_less_less_Suc_eq nth_append_length)                 
                      apply (metis Msg.sel(1) not_less_less_Suc_eq nth_append_length)
  apply (metis Msg.sel(1) less_Suc_eq nth_append_length)                 
                      apply (metis Msg.discI not_less_less_Suc_eq nth_append_length)
  using less_Suc_eq apply blast
                      apply (metis Msg.distinct(1) less_antisym nth_append_length)
                      apply (metis Msg.discI less_Suc_eq nth_append_length)
                     apply (metis Msg.sel(1) not_less_less_Suc_eq nth_append_length)             
                   apply (metis Msg.sel(1) not_less_less_Suc_eq nth_append_length)
                  apply (metis Msg.sel(1) less_Suc_eq nth_append_length)  
            apply (metis Msg.sel(1) less_Suc_eq nth_append_length)       
          apply (metis Msg.sel(1) less_Suc_eq nth_append_length) 
     apply (metis Msg.sel(1) less_Suc_eq nth_append_length)
  by (metis Msg.sel(1) less_Suc_eq nth_append_length)


lemma cas_succ_ov_daddr_dt:
assumes "mem_structured ts"
and "vbounded ts"
and " ts' = cas_succ_trans t' ind lx v1 v2 r  nv mnv ts "
and " lx \<noteq> y "
and " t \<noteq> t'"
shows " [y]\<^sub>t ts'  = [y]\<^sub>t ts"
  using assms
  apply (subgoal_tac "OTS ts' t y =  OTS ts t y ")
   prefer 2
  using cas_succ_ots_daddr_dt apply blast
   apply (subgoal_tac " mapval ts y (OTS ts t y)  (memory ts') = mapval ts y (OTS ts t y) (memory ts )")
 prefer 2
    apply (subgoal_tac "\<forall> i. i \<in> (OTS ts t y) \<longrightarrow> i < length (memory ts)")
    prefer 2
    apply (simp add: OTS_def)
  apply (unfold mapval_def )
  using mem_l apply auto[1]
  apply simp
  using survived_val_cas_succ by presburger


lemma cas_ots_dt_lc:
  assumes "mem_structured ts"
and "vbounded ts"
 and " ts' = cas_succ_trans t' ind x v1 v2 r  nv mnv ts "
and " t \<noteq> t'"
shows " OTS ts' t x  = OTS ts t x \<union>  { length(memory ts')-1} "
 using assms
  apply (subgoal_tac "  coh ts t  x = coh ts' t x")
  prefer 2
  apply (simp add: cas_succ_trans_def)
  apply (subgoal_tac "  vrnew ts t  = vrnew  ts' t ")
   prefer 2
  apply (simp add: cas_succ_trans_def)
  apply (subgoal_tac "  memory ts'  =  memory ts  @ [msg x v2 t'] ")
   prefer 2
   apply auto[1] 
  apply (simp add: OTS_def)
  apply (simp add: OTSF_def)
  apply safe
                     apply (simp_all)
  apply (metis bot.extremum_unique bot.not_eq_extremum bot_nat_def less_SucE mem_l mem_structured_def store_add)
                   apply (simp add: mem_l)
                  apply (simp add: notoverwritten_def)
  apply (metis bot_nat_0.extremum_uniqueI le_imp_less_Suc less_imp_le_nat mem_l nat_le_linear store_add)
                 apply (simp add: notoverwritten_def)
  apply (metis bot_nat_0.extremum_uniqueI le_imp_less_Suc less_imp_le_nat mem_l nat_le_linear store_add)
                apply (metis bot_nat_0.extremum_uniqueI less_SucE mem_l nat_le_linear store_add)
  apply (metis bot_nat_0.extremum_uniqueI less_SucE mem_l nat_le_linear store_add)
              apply (simp add: notoverwritten_def)
  apply (metis bot_nat_0.extremum_uniqueI le_imp_less_Suc less_imp_le_nat mem_l nat_le_linear store_add)
             apply (simp add: mem_l)
  apply (simp add: notoverwritten_def)
  apply (metis bot_nat_0.extremum_uniqueI le_imp_less_Suc less_imp_le_nat mem_l nat_le_linear store_add)
           apply(simp add: vbounded_def)     
           apply (metis nat_less_le)
          apply(simp add: vbounded_def) 
          apply (simp add: notoverwritten_def)
         apply (simp add: notoverwritten_def)
  apply (metis bot.extremum bot_nat_def mem_l store_add)
  apply (metis bot.extremum bot_nat_def mem_l store_add)

     apply (simp add: notoverwritten_def)
 apply (subgoal_tac " vrnew ts t <  (length (memory ts))")
        prefer 2
        apply(simp add: vbounded_def)
        apply metis
apply (subgoal_tac " vrnew ts t <  Suc(length (memory ts))")
        prefer 2
        apply linarith
       apply simp
       apply (subgoal_tac " \<forall>i.  i \<le> vrnew ts t \<and>  xa < i \<longrightarrow>   loc (memory ts ! i) \<noteq> loc (memory ts ! xa)")
        prefer 2
        apply auto[1]
       apply (simp add: nth_append)
      apply (simp add: notoverwritten_def)
 apply (subgoal_tac " vrnew ts t <  (length (memory ts))")
        prefer 2
        apply(simp add: vbounded_def)
        apply metis
apply (subgoal_tac " vrnew ts t <  Suc(length (memory ts))")
        prefer 2
       apply linarith
      apply (simp add: nth_append)
 apply (simp add: notoverwritten_def)
 apply (subgoal_tac " vrnew ts t <  (length (memory ts))")
        prefer 2
        apply(simp add: vbounded_def)
      apply metis
     apply (simp add: nth_append)
  apply (simp add: notoverwritten_def)
 apply (subgoal_tac " vrnew ts t <  (length (memory ts))")
        prefer 2
        apply(simp add: vbounded_def)
     apply metis
    apply (simp add: nth_append)
 apply (simp add: notoverwritten_def)
 apply (subgoal_tac " vrnew ts t <  (length (memory ts))")
        prefer 2
        apply(simp add: vbounded_def)
      apply metis
     apply (simp add: nth_append)
  apply (simp add: notoverwritten_def)
 apply (subgoal_tac " vrnew ts t <  (length (memory ts))")
        prefer 2
        apply(simp add: vbounded_def)
     apply metis
  apply (simp add: nth_append)
 apply (simp add: notoverwritten_def)
 apply (subgoal_tac " vrnew ts t <  (length (memory ts))")
        prefer 2
        apply(simp add: vbounded_def)
      apply metis
  by (simp add: nth_append)

lemma cas_oats_dt_lc:
  assumes "mem_structured ts"
and "vbounded ts"
 and " ts' = cas_succ_trans t' ind x v1 v2 r nv mnv ts "
and " t \<noteq> t'"
shows " OATS ts' t x  = OATS ts t x \<union>  { length(memory ts')-1} "
  using assms


  apply (subgoal_tac "  coh ts t  x = coh ts' t x")
  prefer 2
  apply (simp add: cas_succ_trans_def)
  apply (subgoal_tac "  vpasync ts t x  = vpasync  ts' t x ")
   prefer 2
  apply (simp add: cas_succ_trans_def)

  apply (subgoal_tac "  vrnew ts t  = vrnew  ts' t ")
   prefer 2
  apply (simp add: cas_succ_trans_def)
  apply (subgoal_tac "  memory ts'  =  memory ts  @ [msg x v2 t'] ")
   prefer 2
   apply auto[1] 
  apply (simp add: OATS_def)
  apply safe
                     apply (simp_all)
  apply (metis not_less_less_Suc_eq nth_append)
  apply (metis less_SucE nth_append)
                 apply (unfold notoverwritten_def)
  apply (metis (no_types, lifting) One_nat_def le_zero_eq length_Cons length_append length_append_singleton length_s less_Suc_eq list.size(3) mem_l_casucc nat_le_linear)
  apply (metis One_nat_def add_Suc_right append.right_neutral length_append length_s less_Suc_eq list.size(3) mem_l_casucc zero_le)
  apply (metis less_SucE nth_append)
  apply (metis not_less_less_Suc_eq nth_append)
  using dual_order.strict_trans mem_l_casucc apply auto[1]
  apply (metis not_less_less_Suc_eq nth_append)
  using dual_order.strict_trans mem_l_casucc apply auto[1]
  apply (simp add: discrete)
  apply (simp add: nth_append)
  apply (simp add: nth_append)
        apply (simp add: vbounded_def)
        apply (metis leD less_Suc_eq mem_l store_add zero_le)
        apply (simp add: vbounded_def)
  apply (metis leD less_Suc_eq nth_append)
  apply (metis nth_append)
     apply (metis nth_append)
        apply (simp add: vbounded_def)
  apply (metis leD less_Suc_eq mem_l store_add zero_le)
   apply (simp add: nth_append)
        apply (simp add: vbounded_def)
  by (metis leD less_Suc_eq nth_append)



lemma  cas_succ_ov_dt_lc:
  assumes "mem_structured ts"
  and "vbounded ts"
  and "t \<noteq> t'"
 and " ts' = cas_succ_trans t' ind x v1 v2 r  nv mnv ts "
shows "  [x]\<^sub>t ts'  =  [x]\<^sub>t ts  \<union> {v2}"
  using assms
   apply (subgoal_tac  " OTS ts' t x  = OTS ts t x \<union>  { length(memory ts')-1} ")
  prefer 2
   apply (simp add: cas_ots_dt_lc)
  apply (subgoal_tac " mapval ts x (OTS ts t x)  (memory ts') = mapval ts x (OTS ts t x) (memory ts )")
 prefer 2
    apply (subgoal_tac "\<forall> i. i \<in> (OTS ts t x) \<longrightarrow> i < length (memory ts)")
    prefer 2
    apply (simp add: OTS_def)
  apply (unfold mapval_def )
  using mem_l apply auto[1]
  apply simp
  using survived_val_cas_succ by presburger


lemma  cas_succ_oav_dt_lc:
  assumes "mem_structured ts"
  and "vbounded ts"
  and "t \<noteq> t'"
 and " ts' = cas_succ_trans t' ind x v1 v2 r  nv mnv ts "
shows "  [x]\<^sup>A\<^sub>t ts'  =  [x]\<^sup>A\<^sub>t ts  \<union> {v2}"
  using assms
   apply (subgoal_tac  " OATS ts' t x  = OATS ts t x \<union>  { length(memory ts')-1} ")
   prefer 2
  using cas_oats_dt_lc apply blast

   apply (simp add: cas_ots_dt_lc)
  apply (subgoal_tac " mapval ts x (OATS ts t x)  (memory ts') = mapval ts x (OATS ts t x) (memory ts )")
 prefer 2
    apply (subgoal_tac "\<forall> i. i \<in> (OATS ts t x) \<longrightarrow> i < length (memory ts)")
    prefer 2
    apply (simp add: OATS_def)
  apply (unfold mapval_def )
  using mem_l apply auto[1]
  apply simp
  using survived_val_cas_succ by presburger




lemma cas_fail_ots_ni:
  assumes "mem_structured ts"
  and "vbounded ts"
 and "t \<noteq> t'"
 and " ts' = cas_fail_trans t' ind x v1 v2 r  ts "
shows "  OTS ts t y = OTS ts' t y   "
  using assms 
 apply (case_tac " x= y")
    apply (simp add: OTS_def  )
    apply (subgoal_tac " vrnew ts t = vrnew ts' t")
     prefer 2
     apply (simp add: cas_fail_trans_def)
apply (simp add: OTSF_def)
    apply (subgoal_tac "memory ts = memory ts'")
    prefer 2
  apply simp
  apply (subgoal_tac " coh ts t y =  coh ts' t y")
  prefer 2
      apply (simp add: cas_fail_trans_def)
    apply (smt Collect_cong notoverwritten_def)
   apply (simp add: OTS_def)
 apply (subgoal_tac " vrnew ts t = vrnew ts' t")
     prefer 2
      apply (simp add: cas_fail_trans_def)
apply (simp add: OTSF_def)
    apply (subgoal_tac "memory ts = memory ts'")
    prefer 2
  apply simp
  apply (subgoal_tac " coh ts t y =  coh ts' t y")
  prefer 2
   apply (simp add: cas_fail_trans_def)
  using notoverwritten_def by presburger




lemma cas_fail_ov_ni:
  assumes "mem_structured ts"
  and "vbounded ts"
 and "t \<noteq> t'"
 and " ts' = cas_fail_trans t' ind x v1 v2 r ts "
shows "    [y]\<^sub>t ts  =   [y]\<^sub>t ts'"
  using assms 
apply (subgoal_tac " OTS ts t y = OTS ts' t y")
  prefer 2
  apply (simp add: cas_fail_ots_ni)
  apply simp
  apply (simp add: mapval_def)
  by (meson survived_val_cas_fail)


lemma coh_cas_fail_st_dadrr :
  assumes "mem_structured ts"
  and "vbounded ts"
  and " ts' = cas_fail_trans t  ind x v1 v2 r ts "
   and " x \<noteq> y"
 shows " coh ts t y  = coh ts' t y"
  using assms 
  by (simp add:  cas_fail_trans_def Let_def)



lemma cas_ots_daddr_ni:
  assumes "mem_structured ts"
 and "vbounded ts"
and " step t' ( CAS y  v1 v2 r) ts ts' "
and " x \<noteq> y"
shows " OTS ts' t x \<subseteq> OTS ts t x "
 using assms
 apply (simp add: step_def)
  apply clarify
  apply (case_tac "  ts' = cas_succ_trans t' ind y v1 v2 r  nv mnv ts")
  apply simp
 apply (case_tac "t = t'")
   prefer 2
   apply (metis cas_succ_ots_daddr_dt)
  apply (metis assms(2) cas_succ_ots_daddr_st subsetD) 
 apply (case_tac "t = t'")
   prefer 2
  using cas_fail_ots_ni apply blast
apply (subgoal_tac " coh ts t x \<le> coh ts' t x")
    prefer 2
    apply (simp add: cas_fail_trans_def Let_def)
 apply clarify
  apply (case_tac "ind = coh ts t x")
   apply simp
  apply (simp add: OTS_def)
    apply (simp add: OTSF_def)
 apply (subgoal_tac "  vrnew ts t   \<le> vrnew  ts' t ")
    prefer 2
     apply (simp add:  cas_fail_trans_def Let_def)
    apply (elim conjE)
    apply (simp add: notoverwritten_def)
apply (subgoal_tac "  vrnew ts t   \<le> vrnew  ts' t ")
    prefer 2
    apply (simp add:  cas_fail_trans_def Let_def)
apply (simp add: OTS_def )
  by (simp add: OTSF_def notoverwritten_def )


(*rule: After thread t executes a CAS on y,the observable values of any other address for t might become less.*)
lemma cas_ov_daddr_ni:
  assumes "mem_structured ts"
 and "vbounded ts"
and " step t' ( CAS y  v1 v2 r) ts ts' "
and " x \<noteq> y"
shows " [x]\<^sub>t ts' \<subseteq> [x]\<^sub>t ts "
 using assms
 apply (simp add: step_def)
  apply clarify
  apply (case_tac "  ts' = cas_succ_trans t' ind y v1 v2 r  nv mnv ts")
  apply simp
 apply (case_tac "t = t'")
    prefer 2
    apply (subgoal_tac " [x]\<^sub>t ts' = [x]\<^sub>t ts")
     prefer 2
  using cas_succ_ov_daddr_dt apply presburger
    apply (simp add: mapval_def)
  apply (metis (no_types, lifting) UnE UnI1 UnI2)
   apply (subgoal_tac " [x]\<^sub>t ts' \<subseteq> [x]\<^sub>t ts")
    prefer 2
  using cas_succ_ov_daddr_st apply presburger
  apply (simp add: mapval_def)
   apply (meson UnE in_mono)
 apply (case_tac "t = t'")
   prefer 2
  using cas_fail_ov_ni apply blast

 apply (subgoal_tac" OTS ts' t x \<subseteq> OTS ts t x")
   prefer 2
apply (subgoal_tac " coh ts t x \<le> coh ts' t x")
    prefer 2
    apply (simp add: cas_fail_trans_def Let_def)
 apply clarify
  apply (case_tac "ind = coh ts t x")
   apply simp
  apply (simp add: OTS_def)
    apply (simp add: OTSF_def)
 apply (subgoal_tac "  vrnew ts t   \<le> vrnew  ts' t ")
    prefer 2
     apply (simp add:  cas_fail_trans_def Let_def)
    apply (elim conjE)
    apply (simp add: notoverwritten_def)
apply (subgoal_tac "  vrnew ts t   \<le> vrnew  ts' t ")
    prefer 2
    apply (simp add:  cas_fail_trans_def Let_def)
apply (simp add: OTS_def )
   apply (simp add: OTSF_def notoverwritten_def )
  apply (subgoal_tac "  memory ts   =  memory  ts' ")
    prefer 2
   apply simp
  apply (subgoal_tac " survived_val ts x = survived_val ts' x   ")
  prefer 2
  using assms(3) survived_val_preserved_cas apply blast
  apply (unfold  mapval_def)
  apply simp
  by blast

(*rule:  cas_ov_daddr_ni for singleton OV set*)
corollary  cas_ov_daddr_ni_s:
  assumes "mem_structured ts"
 and "vbounded ts"
and " step t' ( CAS y  v1 v2 r) ts ts' "
and " x \<noteq> y"
and " [x]\<^sub>t ts =  {w}"
and "  (\<forall> t addr.  [addr]\<^sub>t ts \<noteq> {} )"
and  "\<forall>ti l. comploc ( (memory ts)!(coh ts ti l)) l = l"
shows " [x]\<^sub>t ts' = [x]\<^sub>t ts "
  using assms
  by (metis OV_notempty_preserved cas_ov_daddr_ni subset_singleton_iff)

(*rule: cas on x does not impact the thread view for any other address apart from x*)
lemma cas_nov_daddr_ni:
  assumes "mem_structured ts"
 and "vbounded ts"
and " step t' ( CAS y  v1 v2 r) ts ts' "
and " v3 \<notin>[x]\<^sub>t ts "
and " x \<noteq> y"
shows "v3 \<notin>[x]\<^sub>t ts' "
  using assms
 apply (simp add: step_def)
  apply clarify
  apply (case_tac "  ts' = cas_succ_trans t' ind y v1 v2 r nv mnv ts")
  apply simp
 apply (case_tac "t = t'")
    prefer 2
    apply (subgoal_tac " [x]\<^sub>t ts' = [x]\<^sub>t ts")
     prefer 2
  apply (metis assms(5) cas_succ_ov_daddr_dt)
    apply (simp add: mapval_def)
  apply (metis (no_types, lifting) UnE UnI1 UnI2)
   apply (subgoal_tac " [x]\<^sub>t ts' \<subseteq> [x]\<^sub>t ts")
    prefer 2
  using cas_succ_ov_daddr_st apply presburger
  apply (simp add: mapval_def)
   apply (meson UnE in_mono)
 apply (case_tac "t = t'")
   prefer 2
  using cas_fail_ov_ni apply blast

 apply (subgoal_tac" OTS ts' t x \<subseteq> OTS ts t x")
   prefer 2
apply (subgoal_tac " coh ts t x \<le> coh ts' t x")
    prefer 2
    apply (simp add: cas_fail_trans_def Let_def)
 apply clarify
  apply (case_tac "ind = coh ts t x")
   apply simp
  apply (simp add: OTS_def)
    apply (simp add: OTSF_def)
 apply (subgoal_tac "  vrnew ts t   \<le> vrnew  ts' t ")
    prefer 2
     apply (simp add:  cas_fail_trans_def Let_def)
    apply (elim conjE)
    apply (simp add: notoverwritten_def)
apply (subgoal_tac "  vrnew ts t   \<le> vrnew  ts' t ")
    prefer 2
    apply (simp add:  cas_fail_trans_def Let_def)
apply (simp add: OTS_def )
   apply (simp add: OTSF_def notoverwritten_def )
  apply (subgoal_tac "  memory ts   =  memory  ts' ")
    prefer 2
   apply simp
 apply (subgoal_tac " \<forall>i.  i \<notin> OTS ts t' x \<longrightarrow>  i \<notin> OTS ts' t' x ")
  prefer 2
  apply blast
  apply (unfold mapval_def)
  using assms(3) cas_ov_daddr_ni mapval_def by blast


(*rule: cas on x does not impact the thread view for any other address apart from x*)
lemma cas_nov_lc:
  assumes "mem_structured ts"
 and "vbounded ts"
and " step t' ( CAS x  v1 v2 r) ts ts' "
and " v3 \<notin>[x]\<^sub>t ts "
and "v2 \<noteq> v3"
shows "v3 \<notin>[x]\<^sub>t ts' "
  using assms
  apply (simp add: step_def)
  apply clarify
  apply (case_tac "  ts' = cas_succ_trans t' ind x v1 v2 r  nv mnv ts")
  apply (metis UnE cas_succ_ov_dt_lc cas_succ_ov_lc singletonD)
  apply simp
 apply (case_tac "t = t'")
   prefer 2
   apply (subgoal_tac " [x]\<^sub>t ts = [x]\<^sub>t ts'")
    prefer 2
  using cas_fail_ov_ni apply blast
   apply (subgoal_tac "  v3 \<notin>[x]\<^sub>t ts'")
    prefer 2
    apply blast
   apply simp
 apply (subgoal_tac" OTS ts' t' x \<subseteq> OTS ts t' x")
   prefer 2
apply (subgoal_tac " coh ts t' x \<le> coh ts' t' x")
    prefer 2
    apply (simp add: cas_fail_trans_def Let_def)
 apply clarify
  apply (case_tac "ind = coh ts t' x")
   apply simp
  apply (simp add: OTS_def)
    apply (simp add: OTSF_def)
 apply (subgoal_tac "  vrnew ts t'   \<le> vrnew  ts' t' ")
    prefer 2
    apply (simp add:  cas_fail_trans_def Let_def)
 apply (simp add: OTS_def )
   apply (simp add: OTSF_def notoverwritten_def )
  apply (subgoal_tac "  memory ts   =  memory  ts' ")
    prefer 2
    apply simp
 apply clarify
   apply (intro conjI impI)
         apply presburger
        apply (meson dual_order.trans)
       apply (metis dual_order.trans)
      apply blast
     apply blast
    apply (meson dual_order.trans)
   apply (meson dual_order.trans)
  apply (subgoal_tac " \<forall>i.  i \<notin> OTS ts t' x \<longrightarrow>  i \<notin> OTS ts' t' x ")
  prefer 2
   apply auto[1]
  apply (unfold mapval_def)
  apply (subgoal_tac"  survived_val ts x = survived_val ts' x ")
   prefer 2
  using survived_val_cas_fail apply presburger
  by auto

(*rule: If the  value of the last write on x is v3 and a thread t executes CAS x  v1 v2 r, and v3 different to v1, the value
of the last write on x remains the same.*)
lemma cas_fail_lv_ni:
  assumes "mem_structured ts"
 and "vbounded ts"
and "  \<lceil>x:v3\<rceil> ts "
and " v3 \<noteq> v1 "
and " step t ( CAS x  v1 v2 r) ts ts' "
shows "     \<lceil>x:v3\<rceil> ts' "
  using assms
  apply (simp add: step_def)
  apply clarify
  apply (subgoal_tac " ts' = cas_fail_trans t ind x v1 v2 r ts")
   prefer 2
   apply simp
  apply simp
  apply (subgoal_tac " memory ts = memory ts'")
   prefer 2
   apply simp
  apply (simp(no_asm) add: last_entry_def)
  apply (simp(no_asm) add: last_entry_set_def)
  using survived_val_cas_fail by presburger


(*rule: If the  value of the last write on x is v3 and a thread t' executes CAS x  v1 v2 r, and v3 different to v1, and v4 is
not in the observable values of x for thread t, then after the execution of the CAS, v4 is still not in  the observable values of x for thread t'.*)
lemma cas_fail_nov_ni:
  assumes "mem_structured ts"
 and "vbounded ts"
and "  \<lceil>x:v3\<rceil> ts "
and " v4 \<notin>[x]\<^sub>t ts "
and " v3 \<noteq> v1 "
and " step t' ( CAS x  v1 v2 r) ts ts' "
shows  " v4 \<notin>[x]\<^sub>t ts' "
  using assms
 apply (simp add: step_def)
  apply clarify
  apply (subgoal_tac " ts' = cas_fail_trans t ind x v1 v2 r ts")
   prefer 2
  apply (metis cas_fail_ov_ni)
   apply simp
 apply (case_tac "t = t'")
   prefer 2
   apply (subgoal_tac " [x]\<^sub>t ts = [x]\<^sub>t ts'")
    prefer 2
  using cas_fail_ov_ni apply blast
   apply (subgoal_tac "  v4 \<notin>[x]\<^sub>t ts'")
    prefer 2
    apply blast
   apply simp
 apply (subgoal_tac" OTS ts' t' x \<subseteq> OTS ts t' x")
   prefer 2
apply (subgoal_tac " coh ts t' x \<le> coh ts' t' x")
    prefer 2
    apply (simp add: cas_fail_trans_def Let_def)
  apply (case_tac "ind = coh ts t' x")
   apply simp
  apply (simp add: OTS_def)
    apply (simp add: OTSF_def)
 apply (subgoal_tac "  vrnew ts t'   \<le> vrnew  ts' t' ")
    prefer 2
    apply (simp add:  cas_fail_trans_def Let_def)
 apply (simp add: OTS_def )
   apply (simp add: OTSF_def notoverwritten_def )
  apply (subgoal_tac "  memory ts   =  memory  ts' ")
    prefer 2
     apply simp
    apply clarify
   apply (intro conjI impI)
         apply presburger
        apply (meson dual_order.trans)
       apply (metis dual_order.trans)
      apply blast
     apply blast
    apply (meson dual_order.trans)
   apply (meson dual_order.trans)
  apply (subgoal_tac " \<forall>i.  i \<notin> OTS ts t' x \<longrightarrow>  i \<notin> OTS ts' t' x ")
  prefer 2
   apply auto[1]
  apply (unfold mapval_def)
  apply (subgoal_tac " \<forall>i .  compval ts (( memory ts)!i) x  =  compval ts' (( memory ts)!i) x")
   prefer 2
  using cas_fail_crash apply presburger
  by (metis (no_types, lifting) image_cong image_mono subset_iff)


(*rule: If the value of the last write on x is v3 and a thread t executes  CAS x  v1 v2 r then the value of the last write on x
either remains the same or becomes v2.*)
lemma cas_possible_lv_lc:
  assumes "mem_structured ts"
 and "vbounded ts"
and "  \<lceil>x:v3\<rceil> ts "
and " step t ( CAS x  v1 v2 r) ts ts' "
shows "  \<lceil>x:v2\<rceil> ts' \<or>  \<lceil>x:v3\<rceil> ts'  "
  using assms
  apply (simp add: step_def)
  apply clarify
apply (case_tac " ts' = cas_succ_trans t ind x v1 v2 r  nv mnv ts")
  apply (metis assms(4) cas_lc cas_suc_reg compval_def zero_neq_one)
  apply simp
 apply (subgoal_tac " memory ts = memory ts'")
   prefer 2
   apply simp
  apply (subgoal_tac " last_entry ts x = last_entry ts' x")
   prefer 2
   apply (simp(no_asm) add: last_entry_def)
   apply (simp(no_asm) add: last_entry_set_def)
   apply presburger
  using survived_val_cas_fail by presburger


lemma cas_fail_opts_ni :
 assumes "mem_structured ts"
 and "vbounded ts"
and " ts' = cas_fail_trans t ind x v1 v2 r ts"
(*and " x \<noteq> y"*)
shows " OPTS ts'  y =  OPTS ts  y"
  using assms

  apply (subgoal_tac " maxvp ts y = maxvp  ts' y ")
  prefer 2
  apply (simp add:cas_fail_trans_def Let_def)

   apply (subgoal_tac " memory ts = memory ts' ")
  prefer 2
  apply simp
  by (simp add: OPTS_def notoverwritten_def)


(*rule: In case a cas fails the persistent view for all addresses remain the same.*)
lemma cas_fail_opv_ni:
 assumes "mem_structured ts"
 and "vbounded ts"
and " step t' ( CAS x  v1 v2 r) ts ts' "
and " regs ts' t' r = 0"
shows  "[y]\<^sub>P ts' = [y]\<^sub>P ts"
  using assms
  apply (simp add: step_def)
  apply clarify
  apply (subgoal_tac " ts' = cas_fail_trans t' ind x v1 v2 r  ts")
  prefer 2
  apply (metis cas_suc_reg zero_neq_one)
  apply (simp add: mapval_def)
  using assms(3) cas_fail_opts_ni survived_val_preserved_cas by presburger



lemma ca_succ_opts_daddr_sub: 
  assumes "mem_structured ts"
  and "vbounded ts"
 and "x \<noteq> y"
and " step t ( CAS x  v1 v2 r) ts ts' "
and " regs ts' t r = 1"
shows " OPTS ts'  y  \<subseteq>  OPTS ts y "
using assms 
  apply (simp add: step_def)
  apply clarify
  apply (subgoal_tac"   ts' = cas_succ_trans t ind x v1 v2 r nv mnv ts  ")
  prefer 2
  apply (simp add:cas_succ_trans_def  cas_fail_trans_def Let_def )
  apply (metis cas_fail_reg cas_fail_trans_def n_not_Suc_n)
  apply (simp add: OPTS_def)
  apply (simp add: notoverwritten_def)
  apply (subgoal_tac " maxvp ts' y \<ge>  maxvp ts y")
  prefer 2
  apply (simp add:  cas_succ_trans_def)
  apply (metis max.orderI max.right_idem maxvp_nv_def)
apply (subgoal_tac " (\<forall>i.(i\<ge>0\<and>i<length(memory ts)) \<longrightarrow> ( memory ts)!i =( memory ts')!i) ")
  prefer 2
  using assms(4) assms(5) mem_l_cas_succ_step apply presburger
   apply (subgoal_tac" length( memory ts) \<notin>  OPTS ts'  y")
  prefer 2
   apply (simp add: OPTS_def)
  apply clarify
  apply safe
  apply (metis Msg.distinct(1) Msg.sel(1) less_antisym nth_append_length)
  apply (metis canonically_ordered_monoid_add_class.lessE le_trans less_add_Suc1 mem_l store_add zero_le)
  apply (metis Msg.distinct(1) Msg.sel(1) less_antisym nth_append_length)
  apply (metis Msg.distinct(1) Msg.sel(1) le0 less_antisym mem_l nth_append_length store_add)
  apply (metis le0 le_trans less_Suc_eq mem_l store_add)
  apply (metis assms(5) cas_fail_reg zero_neq_one)
  apply (metis assms(5) cas_fail_reg zero_neq_one)
  apply (metis assms(5) cas_fail_reg zero_neq_one)
  apply (metis assms(5) cas_fail_reg zero_neq_one)
  apply (metis assms(5) cas_fail_reg zero_neq_one)
  apply (metis assms(5) cas_fail_reg zero_neq_one)
  apply (metis assms(5) cas_fail_reg zero_neq_one)
  apply (metis assms(5) cas_fail_reg zero_neq_one)
  apply (metis assms(5) cas_fail_reg zero_neq_one)
  by (metis assms(5) cas_fail_reg zero_neq_one)


lemma cas_opts_ni:
 assumes "mem_structured ts"
 and "vbounded ts"
and " step t ( CAS x  v1 v2 r) ts ts' "
and " x \<noteq> y"
shows " OPTS ts'  y \<subseteq> OPTS ts  y"
  using assms
  apply (simp add: step_def)
  apply clarify
  apply (case_tac " ts' = cas_fail_trans t ind x v1 v2 r ts")
  using cas_fail_opts_ni apply blast
  by (metis assms(3) ca_succ_opts_daddr_sub cas_suc_reg in_mono)


(*rule: An execution of CAS on address x can reduce the observable  persistent values of any other address.*)
lemma cas_opv_ni:
 assumes "mem_structured ts"
 and "vbounded ts"
and " step t ( CAS x  v1 v2 r) ts ts' "
and " x \<noteq> y"
shows "[y]\<^sub>P ts' \<subseteq>[y]\<^sub>P ts"
  using assms
  apply (subgoal_tac " OPTS ts'  y \<subseteq>  OPTS ts  y")
  prefer 2
   apply (simp add: cas_opts_ni)
  apply (case_tac "  regs ts' t r = 0")
  using cas_fail_opv_ni apply blast
  apply (simp add: step_def)
  apply clarify
  apply (subgoal_tac " ts' = cas_succ_trans t ind x v1 v2 r nv mnv ts ")
   prefer 2
  apply (metis bot_nat_0.not_eq_extremum cas_fail_reg)
  apply (subgoal_tac" survived_val ts y = survived_val ts' y")
   prefer 2
  using assms(3) survived_val_preserved_cas apply blast
  apply (subgoal_tac " \<forall> x. compval ts (memory ts ! x) y = compval ts' (memory ts ! x) y")
   prefer 2
    apply (metis compval_def)
 apply (subgoal_tac " mapval ts' y (OPTS ts'  y)  (memory ts')\<subseteq>  mapval ts y (OPTS ts y) (memory ts )")
 prefer 2
    apply (subgoal_tac "\<forall> i. i \<in> (OPTS ts  y) \<longrightarrow> i < length (memory ts)")
    prefer 2
    apply (simp add: OPTS_def)
  apply (subgoal_tac " length ( memory ts')  =length ( memory ts) + 1")
    prefer 2
  using length_s apply presburger
  apply (subgoal_tac  "(\<forall>i.(i\<ge>0\<and>i<length(memory ts)) \<longrightarrow> ( memory ts)!i =( memory ts')!i)")
  prefer 2
  using mem_l_casucc apply blast
  apply (subgoal_tac" survived_val ts y = survived_val ts' y")
   prefer 2
  using assms(3) survived_val_preserved_cas apply blast
   apply (simp add:  mapval_def)
  using Int_Un_distrib2 image_mono le_supI1 le_supI2 subset_Un_eq apply blast
  by blast

 


lemma cas_succ_last_entry_in_ots :
  assumes "mem_structured ts"
and "vbounded ts"
and " step t ( CAS lx  v1 v2 r) ts ts' "
and " regs ts' t r = 1"
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
  apply clarify
  apply (subgoal_tac  "  ts' = cas_succ_trans t ind lx v1 v2 r  nv mnv  ts ")
   prefer 2
   apply (metis cas_fail_reg n_not_Suc_n)
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
  using assms(2) assms(3) assms(5) coh_loc_rel_preserved by presburger


lemma cas_fail_last_entry_in_ots :
  assumes "mem_structured ts"
and "vbounded ts"
and " step t ( CAS lx  v1 v2 r) ts ts' "
and " regs ts' t r = 0"
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
  apply clarify
  apply (subgoal_tac  "  ts' = cas_fail_trans t ind lx v1 v2 r ts ")
   prefer 2
   apply (metis cas_suc_reg zero_neq_one)
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
  using assms(2) assms(3) assms(5) coh_loc_rel_preserved by presburger

(*rule: In case a cas succeed the last .*)
lemma last_entry_succ_daddr_preserved:
 assumes "mem_structured ts"
 and "vbounded ts"
and " x \<noteq> y"
and "  ts' = cas_succ_trans t ind x v1 v2 r  nv mnv ts"
shows "  last_entry ts'  y = last_entry ts  y"
  using assms
  apply (subgoal_tac " (\<forall>i.(i\<ge>0\<and>i<length(memory ts)) \<longrightarrow> ( memory ts)!i =( memory ts')!i) ")
   prefer 2
  using mem_l_casucc apply blast
  apply (simp add: last_entry_def)
  apply (subgoal_tac " last_entry_set ts' y = last_entry_set ts y")
   prefer 2
   apply (subgoal_tac " length(memory ts) \<notin> last_entry_set ts' y")
    prefer 2
    apply (simp add: last_entry_set_def)
   apply (simp add: last_entry_set_def)
  using less_Suc_eq apply force
  by simp


lemma last_entry_fail_daddr_preserved:
 assumes "mem_structured ts"
 and "vbounded ts"
and " x \<noteq> y"
and "  ts' = cas_fail_trans t ind x v1 v2 r ts"
shows "  last_entry ts'  y = last_entry ts  y"
  using assms 
 apply (subgoal_tac "memory ts = memory ts' ")
   prefer 2
  apply (simp add: cas_fail_trans_def)
  by(simp add: last_entry_def last_entry_set_def)



lemma cas_sv_lc:
 assumes "mem_structured ts"
 and "vbounded ts"
and " step t ( CAS x  v1 v2 r) ts ts' "
shows "    ( [x]\<^sub>t ts'  = {v2}  \<and>  regs ts' t r = 1 ) \<or>  regs ts' t r= 0   "
  using assms
  apply (simp add: step_def)
  apply clarify
  apply (case_tac "  ts' = cas_succ_trans t ind x v1 v2 r  nv mnv ts")
  using One_nat_def cas_suc_reg cas_succ_ov_lc apply presburger
  by simp


lemma cas_sv_lc_2:
 assumes "mem_structured ts"
 and "vbounded ts"
and " step t ( CAS x  v1 v2 r) ts ts' "
and "  regs ts' t r= 1 "
shows "    [x]\<^sub>t ts'  = {v2}   "
 using assms
  apply (simp add: step_def)
  by (metis assms(3) assms(4) cas_sv_lc zero_neq_one)






lemma cas_lv_ots_daddr_lc:
  assumes "mem_structured ts"
 and "vbounded ts"
and " x \<noteq> y"
and " OTS ts t' y  = {w} "
and " step t ( CAS x  v1 v2 r) ts ts' "
 and "\<forall> ti l. comploc ( (memory ts)!(coh ts ti l)) l = l"
 and "  \<lceil>y\<rceil>\<^sub>t' ts"
shows "    (  OTS ts' t y  = {w}  \<and>  regs ts' t r = 1 ) \<or>  regs ts' t r= 0   "
  using assms
  apply (simp add: step_def)
  apply clarify
  apply (subgoal_tac " vbounded ts' ")
   prefer 2
  using assms(5) vbounded_preserved apply blast
 apply (subgoal_tac " maxcoh ts t < length (memory ts)")
   prefer 2
   apply (simp add: vbounded_def)
 apply (subgoal_tac " vrnew ts t < length (memory ts)")
      prefer 2
   apply (simp add: vbounded_def)
  apply (subgoal_tac "  regs ts' t r = 1  \<or>   regs ts' t r= 0 ")
   prefer 2
   apply (metis assms(5) cas_lc)
 apply (case_tac "  regs ts' t r = 1 ")
    apply (subgoal_tac"  ts' = cas_succ_trans t ind x v1 v2 r  nv mnv ts")
    prefer 2
    apply (metis cas_fail_reg zero_neq_one)
 apply (subgoal_tac "  last_entry ts'  y \<in>   OTS ts' t y ")
    prefer 2
  using assms(5) assms(6) cas_succ_last_entry_in_ots apply blast
 apply (subgoal_tac "  last_entry ts'  y =   last_entry ts  y ")
    prefer 2
    apply (metis last_entry_succ_daddr_preserved)
(* apply (subgoal_tac " OTS ts' t y  = { last_entry ts  y} ")*)
  apply (subgoal_tac " vrnew ts' t  = length (memory ts)")
     prefer 2
    apply (simp add:  cas_succ_trans_def)
(* apply (subgoal_tac " \<nexists> n.( n \<noteq> last_entry ts  y \<and>0 \<le> n \<and> n < length(memory ts') \<and> n \<in>  OTS ts' t y)")  *)
 apply (subgoal_tac " \<forall> n.( n \<noteq> last_entry ts'  y \<and>0 \<le> n \<and> n < length(memory ts') \<longrightarrow> n \<notin>  OTS ts' t y)") 
   prefer 2
    apply clarify
    apply (simp add: last_entry_def)
    apply (simp add: OTS_def)
    apply (simp add: OTSF_def)
  apply (case_tac "n > last_entry ts'  y")
  (*  apply (subgoal_tac " comploc ( (memory ts')! n) y \<noteq> y")
      prefer 2*)
apply (subgoal_tac " \<forall> j. ( 0 \<le> j \<and> j < length (memory ts')  \<and> comploc (memory ts' ! j) y = y) \<longrightarrow> j \<in>  last_entry_set  ts'  y")
      prefer 2
       apply (simp add: last_entry_set_def)
    apply (subgoal_tac " \<forall> i. i \<in>  last_entry_set  ts'  y \<longrightarrow> i \<le>  last_entry ts'  y")
      prefer 2
      apply (subgoal_tac " last_entry_set ts' y \<noteq> {}")
       prefer 2
       apply (metis cas_succ_wfs last_entry_set_not_empty)
 apply (subgoal_tac " finite ( last_entry_set ts' y )")
       prefer 2
        apply (metis finite_last_entry_set)
       apply (metis Max_ge last_entry_def)
      apply (subgoal_tac "(n >  last_entry ts'  y \<and>  0 \<le> n \<and> n < length (memory ts')) \<longrightarrow> ( comploc (memory ts' ! n) y \<noteq> y)")
       prefer 2
       apply (metis le_antisym nat_less_le)
     apply (subgoal_tac "(n >  last_entry ts'  y \<and>  0 \<le> n \<and> n < length (memory ts'))  \<longrightarrow> n \<notin>  OTS ts' t y   ")
      prefer 2
      apply (simp add: OTS_def)
     apply (simp add: OTSF_def)
    apply (subgoal_tac " n \<noteq>  last_entry ts'  y ")
     prefer 2
  apply (metis last_entry_def)
    apply (subgoal_tac "(n <  last_entry ts'  y \<and>  0 \<le> n \<and> n < length (memory ts')) \<longrightarrow> ( \<not> notoverwritten ts'  (length (memory ts)) n y)")
     prefer 2
     apply (subgoal_tac " \<exists> j.( n < j \<and> j \<le> length (memory ts)) \<and>  ( comploc (memory ts' ! j) y = y)")
  prefer 2
      apply clarify
      apply (rule_tac x=" last_entry ts' y " in exI)
      apply (intro conjI)
        apply (meson nat_neq_iff)
       apply (metis last_entry_def not_le_imp_less not_less_eq)
      apply (meson cas_succ_wfs last_entry_loc)

     apply (simp add: notoverwritten_def)
  apply (metis (no_types, lifting) last_entry_bounded last_entry_def last_entry_succ_daddr_preserved less_Suc_eq_0_disj less_Suc_eq_le linorder_neqE_nat mem_l mem_structured_def store_add)
    apply (simp add: OTS_def)
   apply (subgoal_tac "  OTS ts' t y = {last_entry ts' y}")
    prefer 2
    apply (subgoal_tac " \<forall>i. i \<in> OTS ts' t y \<longrightarrow>   0 \<le> i \<and> i < length (memory ts')")
  prefer 2
    apply (simp add: OTS_def)
     apply (simp add: OTSF_def)
    apply blast
   apply (metis One_nat_def)
  by (metis less_numeral_extra(3))


(*rule: Given x different to y, if thread's t view of y is the
 last write on y  and  the value of this write is v  then after executing the CAS  either the CAS succeeds, so r=1  and t's  view of y becomes v or the CAS fails and r=0.*)
lemma cas_lv_daddr_lc:
  assumes "mem_structured ts"
 and "vbounded ts"
and " x \<noteq> y"
and " \<lceil>y, v\<rceil>\<^sub>t'  ts "
and " step t ( CAS x  v1 v2 r) ts ts' "
 and "\<forall> ti l. comploc ( (memory ts)!(coh ts ti l)) l = l"
shows "    ( [y]\<^sub>t  ts' = {v}  \<and>  regs ts' t r = 1 ) \<or>  regs ts' t r= 0   "   
  using assms
  apply (subgoal_tac "  ( ( OTS ts' t y  =  OTS ts t' y)  \<and>  regs ts' t r = 1 ) \<or>  regs ts' t r= 0 ")
   prefer 2
   apply (metis cas_lv_ots_daddr_lc)
  apply (simp add: step_def)
  apply clarify
 apply (subgoal_tac "  regs ts' t r = 1  \<or>   regs ts' t r= 0 ")
   prefer 2
   apply (metis assms(5) cas_lc)
 apply (case_tac "  regs ts' t r = 1 ")
    apply (subgoal_tac"  ts' = cas_succ_trans t ind x v1 v2 r  nv mnv ts")
    prefer 2
    apply (metis cas_fail_reg zero_neq_one)
 apply (subgoal_tac " mapval ts y (OTS ts  t'  y)  (memory ts') = mapval ts y (OTS ts t'  y) (memory ts )")
 prefer 2
    apply (subgoal_tac "\<forall> i. i \<in> (OTS ts t'  y) \<longrightarrow> i < length (memory ts)")
    prefer 2
     apply (metis last_entry_bounded singleton_iff)
  apply simp
    apply (unfold  mapval_def)
    apply (subgoal_tac " survived_val ts' y = survived_val ts y") 
     prefer 2
     apply (metis survived_val_cas_succ)
  apply (metis (no_types, lifting) image_cong nth_append singletonD)

    apply (subgoal_tac " \<forall>x. compval ts (memory ts ! x) y = compval ts' (memory ts ! x) y")
     prefer 2
    apply (metis compval_def survived_val_cas_succ)
  using assms(5) survived_val_preserved_cas apply auto[1]
  by (metis less_numeral_extra(3))



 


 
lemma cas_fail_ots__sub:
  assumes "mem_structured ts"
  and "vbounded ts"
and "  ts' = cas_fail_trans t ind x v1 v2 r ts "
and "y \<noteq> x" 
shows  "OTS ts' t' y   \<subseteq> OTS ts t'  y"
  using assms
apply (subgoal_tac " memory ts = memory ts' ")
   prefer 2
   apply auto[1]
 apply (subgoal_tac " vrnew ts t'  \<ge> vrnew ts t'  ")
    prefer 2
   apply (simp add: cas_fail_trans_def)
   apply (simp add: OTS_def )
   apply (simp add: OTSF_def )
  apply (simp add: notoverwritten_def)
  apply safe
         apply (simp add: cas_fail_trans_def split:if_splits)
        apply (simp add: cas_fail_trans_def split:if_splits)
       apply (simp add: cas_fail_trans_def split:if_splits)
      apply (simp add: cas_fail_trans_def split:if_splits)
  using le_max_iff_disj apply auto[1]
       apply blast
      apply blast
     apply (simp add: cas_fail_trans_def split:if_splits)
    apply (simp add: cas_fail_trans_def split:if_splits)
   apply (simp add: cas_fail_trans_def split:if_splits)
  by (simp add: cas_fail_trans_def split:if_splits)


(*rule: The value of the last write on y remains the same after executing a CAS on a different address.*)
lemma cas_ots_lm_ni:
  assumes "mem_structured ts"
  and "vbounded ts"
and " step t ( CAS x  v1 v2 r) ts ts' "
  and "x \<noteq> y"
  and "  \<lceil>y\<rceil>\<^sub>t'  ts "
and "\<forall> ti l.  OTS  ts ti  l \<noteq> {}"
and  "\<forall>ti l. comploc ( (memory ts)!(coh ts ti l)) l = l"
shows "  \<lceil>y\<rceil>\<^sub>t'  ts'  "
  using assms
  apply (simp add: step_def)
  apply clarify
  apply(case_tac " ts' =  cas_succ_trans t ind x v1
            v2 r  nv mnv ts")
  apply (subgoal_tac " last_entry ts y = last_entry ts' y") 
   prefer 2
  using last_entry_succ_daddr_preserved apply force
   apply (subgoal_tac" OTS ts' t' y \<subseteq>  OTS ts t' y ")
    prefer 2
    apply (metis cas_succ_ots_daddr_dt cas_succ_ots_daddr_st dual_order.eq_iff)
   apply (metis OTS_notempty_preserved assms(3) assms(7) subset_singletonD)
  apply (subgoal_tac " memory ts = memory ts'")
  prefer 2
  apply simp
 apply (subgoal_tac " last_entry ts y = last_entry ts' y") 
   prefer 2
   apply  (simp add: last_entry_def)
   apply  (simp add: last_entry_set_def)
  apply (subgoal_tac" OTS ts' t' y \<subseteq>  OTS ts t' y ")
   prefer 2
   apply (metis cas_fail_ots__sub)
  by (metis OTS_notempty_preserved assms(3) assms(7) subset_singletonD)




lemma valRule [simp] : "i \<in>  OTS \<sigma> t l \<longrightarrow> valOf  i l \<sigma> \<in> [l]\<^sub>t \<sigma> "
  by (simp add: valOf_def  survived_val_def  mapval_def)


lemma  cas_ots_lm_succ:
assumes " step t ( CAS glb  v1 v2 r) ts ts'"
and "vbounded ts"
and "mem_structured ts"
and " \<lceil>glb\<rceil>\<^sub>t ts"
and " \<lceil>glb:v1\<rceil> ts"
shows  "  regs ts' t r = 1 "
  using assms
  apply (simp add: step_def)
  by fastforce


lemma cas_succ_valOf_dt_ni:
assumes "vbounded ts" 
and "mem_structured ts"
and " ts' =  cas_succ_trans t ind glb v1  v2 r nv mnv  ts"
shows "\<forall> i.  i \<in> OTS ts ti glb \<longrightarrow>  ( valOf  i glb  ts  = valOf  i glb  ts' )"
  using assms
  apply (subgoal_tac " (\<forall>i.(i\<ge>0\<and>i<length(memory ts)) \<longrightarrow> ( memory ts)!i =( memory ts')!i) ")
   prefer 2
  using mem_l_casucc apply blast
  by  (simp add: valOf_def cas_succ_trans_def)



lemma cas_succ_read_glb_monotone_preserved_aux:
  assumes "  (  \<forall> i j  .0 < j \<and>  j < length(memory ts)  \<and> 0 <  i \<and>  i < length(memory ts)  \<and>  i \<le> j \<and>  (State.loc (memory( ts)!i) ) = glb  \<and>  (State.loc (memory( ts)!j) ) = glb  \<longrightarrow> ((compval ts  (memory( ts)!i) glb ) \<le> (compval ts  (memory( ts)!j) glb ) ))"
 and "vbounded ts"
and "  \<lceil>glb : v1 \<rceil> ts "
and "mem_structured ts"
and  "ts' = cas_succ_trans t (last_entry ts glb) glb v1  v1 r nv mnv ts "
and " \<forall> ti l. last_entry ts l \<in>   OTS ts ti l "
and " \<forall> ti l. lastVal  l ts  \<in>  [l]\<^sub>ti ts " 
shows   "(  \<forall> i j  . 0 < j \<and>  j < length(memory ts')  \<and> 0 <  i \<and>  i < length(memory ts')  \<and>  i \<le> j \<and>  (State.loc (memory( ts')!i) ) = glb  \<and>  (State.loc (memory( ts')!j) ) = glb  \<longrightarrow> ((compval ts'  (memory( ts')!i) glb ) \<le> (compval ts'  (memory( ts')!j) glb ) ))"
 using assms
apply (subgoal_tac "  valOf (last_entry  ts  glb)  glb  ts = v1")
   prefer 2
   apply (simp add: valOf_def)
apply (subgoal_tac "   last_entry  ts' glb =  length (memory ts) ")
   prefer 2
   apply (subgoal_tac "  length (memory ts) =  length (memory ts') -1 ")
    prefer 2
    apply (simp add: cas_succ_trans_def)
  using cas_succ_lastentry apply presburger
  apply (subgoal_tac "  valOf (last_entry  ts'  glb)  glb  ts' = v1")
   prefer 2
  apply (simp add: cas_succ_trans_def  valOf_def )
apply (subgoal_tac " (\<forall>i.(i>0\<and>i<length(memory ts)) \<longrightarrow> ( memory ts)!i =( memory ts')!i) ")
   prefer 2
  using mem_l_casucc 
  using nat_less_le apply presburger
apply (subgoal_tac " \<forall> i .(i>0\<and>i<length(memory ts)) \<longrightarrow>  ( valOf  i glb  ts  = valOf  i glb  ts' )")
   prefer 2
   apply (simp add: valOf_def)
  using survived_val_cas_succ apply presburger
apply (subgoal_tac "  \<forall>  j . (  (0 < j \<and>  j < length(memory ts)  \<and> comploc ((memory ts)!j) glb = glb)   \<longrightarrow>  valOf  j  glb  ts  \<le>  v1 ) ")
   prefer 2  
apply (subgoal_tac " \<forall> j . (0 < j \<and>  j < length(memory ts)  \<and> comploc ((memory ts)!j) glb = glb)  \<longrightarrow>  j \<le> last_entry  ts  glb  ")
   prefer 2
    apply (subgoal_tac "\<forall> j .(0 <  j \<and>  j < length(memory ts)  \<and> comploc ((memory ts)!j) glb = glb)  \<longrightarrow>  j \<in> last_entry_set ts glb")
  prefer 2
     apply (simp add: last_entry_set_def)
     apply metis
    apply (subgoal_tac "\<forall> i. i \<in>  last_entry_set ts glb \<longrightarrow> i \<le>  last_entry  ts  glb  ")
     prefer 2
  apply (simp add: last_entry_def)
  using  finite_last_entry_set    apply (metis Max_ge)
    apply metis
  apply (metis dual_order.eq_iff last_entry_bounded last_entry_loc loc_eq_comploc nat_less_le valOf_def zero_less_iff_neq_zero)
apply (subgoal_tac "  \<forall>  j . (  (0 < j \<and>  j < length(memory ts')  \<and> comploc ((memory ts')!j) glb = glb)   \<longrightarrow>  valOf  j  glb  ts'  \<le>  Suc v1 ) ")
   prefer 2
apply (subgoal_tac " \<forall> j . (0 < j \<and>  j < length(memory ts')  \<and> comploc ((memory ts')!j) glb = glb)  \<longrightarrow>  j \<le> last_entry  ts'  glb  ")
   prefer 2
    apply (subgoal_tac "\<forall> j .(0 < j \<and>  j < length(memory ts')  \<and> comploc ((memory ts')!j) glb = glb)  \<longrightarrow>  j \<in> last_entry_set ts' glb")
  prefer 2
     apply (simp add: last_entry_set_def)
    apply (subgoal_tac "\<forall> i. i \<in>  last_entry_set ts'  glb \<longrightarrow> i \<le>  last_entry  ts'  glb  ")
     prefer 2
  apply (simp add: last_entry_def)
  using  finite_last_entry_set    apply (metis Max_ge)
    apply metis
  apply (metis le_SucI le_less)

  apply (subgoal_tac " (\<forall> i j  .( 0 < j \<and>  j < length(memory ts') \<and> 0 < i \<and>  i < length(memory ts') \<and>  i \<le> j \<and> comploc ((memory ts')!i) glb = glb \<and> comploc ((memory ts')!j) glb = glb  ) \<longrightarrow>
            ( valOf  i glb ts'  \<le> valOf j glb  ts')  )")
   prefer 2
  apply (intro allI impI)
   apply (case_tac"  j < length (memory ts) \<and>  i < length (memory ts) ")

  apply (metis loc_eq_comploc valOf_def)
   apply (subgoal_tac " length (memory ts') = length (memory ts) + 1 ")
  prefer 2
    apply simp
   apply (metis Suc_eq_plus1 diff_is_0_eq nat_neq_iff not_less_eq_eq zero_less_diff)
  by (smt (verit, best) assms(4) cas_succ_wfs loc_eq_comploc order_le_less_trans valOf_def)




lemma cas_succ_read_glb_monotone_preserved_complete_aux:
  assumes "  (  \<forall> i j  .0 < j \<and>  j < length(memory ts)  \<and> 0 \<le>  i \<and>  i < length(memory ts)  \<and>  i \<le> j \<and>  comploc ((memory ts')!i) glb = glb  \<and>   comploc ((memory ts')!j) glb = glb  \<longrightarrow> ((compval ts  (memory( ts)!i) glb ) \<le> (compval ts  (memory( ts)!j) glb ) ))"
 and "vbounded ts"
and "  \<lceil>glb : v1 \<rceil> ts "
and "mem_structured ts"
and  "ts' = cas_succ_trans t (last_entry ts glb) glb v1  v1 r  nv mnv ts "
and " \<forall> ti l. last_entry ts l \<in>   OTS ts ti l "
and " \<forall> ti l. lastVal  l ts  \<in>  [l]\<^sub>ti ts " 
shows   "(  \<forall> i j  . 0 < j \<and>  j < length(memory ts')  \<and> 0 \<le>  i \<and>  i < length(memory ts')  \<and>  i \<le> j \<and>   comploc ((memory ts')!i) glb = glb  \<and>  comploc ((memory ts')!j) glb = glb  \<longrightarrow> ((compval ts'  (memory( ts')!i) glb ) \<le> (compval ts'  (memory( ts')!j) glb ) ))"
 using assms
apply (subgoal_tac "  valOf (last_entry  ts  glb)  glb  ts = v1")
   prefer 2
   apply (simp add: valOf_def)

apply (subgoal_tac "   last_entry  ts' glb =  length (memory ts) ")
   prefer 2
   apply (subgoal_tac "  length (memory ts) =  length (memory ts') -1 ")
    prefer 2
    apply (simp add: cas_succ_trans_def)
  using cas_succ_lastentry apply presburger
  apply (subgoal_tac "  valOf (last_entry  ts'  glb)  glb  ts' = v1")
   prefer 2
  apply (simp add: cas_succ_trans_def  valOf_def )
apply (subgoal_tac " (\<forall>i.(i\<ge> 0\<and>i<length(memory ts)) \<longrightarrow> ( memory ts)!i =( memory ts')!i) ")
   prefer 2
  using mem_l_casucc 
  
  using nat_less_le apply presburger
apply (subgoal_tac " \<forall> i .(i\<ge>0\<and>i<length(memory ts)) \<longrightarrow>  ( valOf  i glb  ts  = valOf  i glb  ts' )")
   prefer 2
   apply (simp add: valOf_def)
  using survived_val_cas_succ apply presburger
apply (subgoal_tac "  \<forall>  j . (  (0 \<le> j \<and>  j < length(memory ts)  \<and> comploc ((memory ts)!j) glb = glb)   \<longrightarrow>  valOf  j  glb  ts  \<le>  v1 ) ")
   prefer 2  
apply (subgoal_tac " \<forall> j . (0 \<le> j \<and>  j < length(memory ts)  \<and> comploc ((memory ts)!j) glb = glb)  \<longrightarrow>  j \<le> last_entry  ts  glb  ")
   prefer 2
    apply (subgoal_tac "\<forall> j .(0 \<le>  j \<and>  j < length(memory ts)  \<and> comploc ((memory ts)!j) glb = glb)  \<longrightarrow>  j \<in> last_entry_set ts glb")
  prefer 2
     apply (simp add: last_entry_set_def)
     apply metis
    apply (subgoal_tac "\<forall> i. i \<in>  last_entry_set ts glb \<longrightarrow> i \<le>  last_entry  ts  glb  ")
     prefer 2
  apply (simp add: last_entry_def)
  using  finite_last_entry_set    apply (metis Max_ge)
    apply metis
  apply (metis dual_order.eq_iff last_entry_bounded last_entry_loc loc_eq_comploc nat_less_le valOf_def zero_less_iff_neq_zero)
apply (subgoal_tac "  \<forall>  j . (  (0 \<le> j \<and>  j < length(memory ts')  \<and> comploc ((memory ts')!j) glb = glb)   \<longrightarrow>  valOf  j  glb  ts'  \<le>  Suc v1 ) ")
   prefer 2
apply (subgoal_tac " \<forall> j . (0 \<le> j \<and>  j < length(memory ts')  \<and> comploc ((memory ts')!j) glb = glb)  \<longrightarrow>  j \<le> last_entry  ts'  glb  ")
   prefer 2
    apply (subgoal_tac "\<forall> j .(0 \<le> j \<and>  j < length(memory ts')  \<and> comploc ((memory ts')!j) glb = glb)  \<longrightarrow>  j \<in> last_entry_set ts' glb")
  prefer 2
     apply (simp add: last_entry_set_def)
    apply (subgoal_tac "\<forall> i. i \<in>  last_entry_set ts'  glb \<longrightarrow> i \<le>  last_entry  ts'  glb  ")
     prefer 2
  apply (simp add: last_entry_def)
  using  finite_last_entry_set    apply (metis Max_ge)
    apply metis

  apply (metis le_SucI nat_le_linear nless_le)

  apply (subgoal_tac " (\<forall> i j  .( 0 < j \<and>  j < length(memory ts') \<and> 0 \<le> i \<and>  i < length(memory ts') \<and>  i \<le> j \<and> comploc ((memory ts')!i) glb = glb \<and> comploc ((memory ts')!j) glb = glb  ) \<longrightarrow>
            ( valOf  i glb ts'  \<le> valOf j glb  ts')  )")
   prefer 2
  apply (intro allI impI)
   apply (case_tac"  j < length (memory ts) \<and>  i < length (memory ts) ")
  apply (metis bot_nat_0.extremum valOf_def)
   apply (subgoal_tac " length (memory ts') = length (memory ts) + 1 ")
  prefer 2
    apply simp
   apply (metis Suc_eq_plus1 diff_is_0_eq nat_neq_iff not_less_eq_eq zero_less_diff)
  by (smt (verit, best) assms(4) cas_succ_wfs loc_eq_comploc order_le_less_trans valOf_def)


lemma cas_succ_glb_monotone_preserved_aux:
  assumes "  (  \<forall> i j  .0 < j \<and>  j < length(memory ts)  \<and> 0 <  i \<and>  i < length(memory ts)  \<and>  i \<le> j \<and>  (State.loc (memory( ts)!i) ) = glb  \<and>  (State.loc (memory( ts)!j) ) = glb  \<longrightarrow> ((compval ts  (memory( ts)!i) glb ) \<le> (compval ts  (memory( ts)!j) glb ) ))"
 and "vbounded ts"
and "  \<lceil>glb : v1 \<rceil> ts "
and "mem_structured ts"
and  "ts' = cas_succ_trans t (last_entry ts glb) glb v1 (Suc v1) r  nv mnv ts "
and " \<forall> ti l. last_entry ts l \<in>   OTS ts ti l "
and " \<forall> ti l. lastVal  l ts  \<in>  [l]\<^sub>ti ts " 
shows   "(  \<forall> i j  . 0 < j \<and>  j < length(memory ts')  \<and> 0 <  i \<and>  i < length(memory ts')  \<and>  i \<le> j \<and>  (State.loc (memory( ts')!i) ) = glb  \<and>  (State.loc (memory( ts')!j) ) = glb  \<longrightarrow> ((compval ts'  (memory( ts')!i) glb ) \<le> (compval ts'  (memory( ts')!j) glb ) ))"
 using assms
apply (subgoal_tac "  valOf (last_entry  ts  glb)  glb  ts = v1")
   prefer 2
   apply (simp add: valOf_def)

apply (subgoal_tac "   last_entry  ts' glb =  length (memory ts) ")
   prefer 2
   apply (subgoal_tac "  length (memory ts) =  length (memory ts') -1 ")
    prefer 2
    apply (simp add: cas_succ_trans_def)
  using cas_succ_lastentry apply presburger
  apply (subgoal_tac "  valOf (last_entry  ts'  glb)  glb  ts' = Suc v1")
   prefer 2
  apply (simp add: cas_succ_trans_def  valOf_def )
apply (subgoal_tac " (\<forall>i.(i>0\<and>i<length(memory ts)) \<longrightarrow> ( memory ts)!i =( memory ts')!i) ")
   prefer 2
  using mem_l_casucc 
  
  using nat_less_le apply presburger
apply (subgoal_tac " \<forall> i .(i>0\<and>i<length(memory ts)) \<longrightarrow>  ( valOf  i glb  ts  = valOf  i glb  ts' )")
   prefer 2
   apply (simp add: valOf_def)
  using survived_val_cas_succ apply presburger
apply (subgoal_tac "  \<forall>  j . (  (0 < j \<and>  j < length(memory ts)  \<and> comploc ((memory ts)!j) glb = glb)   \<longrightarrow>  valOf  j  glb  ts  \<le>  v1 ) ")
   prefer 2  
apply (subgoal_tac " \<forall> j . (0 < j \<and>  j < length(memory ts)  \<and> comploc ((memory ts)!j) glb = glb)  \<longrightarrow>  j \<le> last_entry  ts  glb  ")
   prefer 2
    apply (subgoal_tac "\<forall> j .(0 <  j \<and>  j < length(memory ts)  \<and> comploc ((memory ts)!j) glb = glb)  \<longrightarrow>  j \<in> last_entry_set ts glb")
  prefer 2
     apply (simp add: last_entry_set_def)
     apply metis
    apply (subgoal_tac "\<forall> i. i \<in>  last_entry_set ts glb \<longrightarrow> i \<le>  last_entry  ts  glb  ")
     prefer 2
  apply (simp add: last_entry_def)
  using  finite_last_entry_set    apply (metis Max_ge)
    apply metis
  apply (metis dual_order.eq_iff last_entry_bounded last_entry_loc loc_eq_comploc nat_less_le valOf_def zero_less_iff_neq_zero)
apply (subgoal_tac "  \<forall>  j . (  (0 < j \<and>  j < length(memory ts')  \<and> comploc ((memory ts')!j) glb = glb)   \<longrightarrow>  valOf  j  glb  ts'  \<le>  Suc v1 ) ")
   prefer 2
apply (subgoal_tac " \<forall> j . (0 < j \<and>  j < length(memory ts')  \<and> comploc ((memory ts')!j) glb = glb)  \<longrightarrow>  j \<le> last_entry  ts'  glb  ")
   prefer 2
    apply (subgoal_tac "\<forall> j .(0 < j \<and>  j < length(memory ts')  \<and> comploc ((memory ts')!j) glb = glb)  \<longrightarrow>  j \<in> last_entry_set ts' glb")
  prefer 2
     apply (simp add: last_entry_set_def)
    apply (subgoal_tac "\<forall> i. i \<in>  last_entry_set ts'  glb \<longrightarrow> i \<le>  last_entry  ts'  glb  ")
     prefer 2
  apply (simp add: last_entry_def)
  using  finite_last_entry_set    apply (metis Max_ge)
    apply metis
  apply (metis   le_Suc_eq nat_less_le)
  apply (subgoal_tac " (\<forall> i j  .( 0 < j \<and>  j < length(memory ts') \<and> 0 < i \<and>  i < length(memory ts') \<and>  i \<le> j \<and> comploc ((memory ts')!i) glb = glb \<and> comploc ((memory ts')!j) glb = glb  ) \<longrightarrow>
            ( valOf  i glb ts'  \<le> valOf j glb  ts')  )")
   prefer 2
  apply (intro allI impI)
   apply (case_tac"  j < length (memory ts) \<and>  i < length (memory ts) ")

  apply (metis loc_eq_comploc valOf_def)
   apply (subgoal_tac " length (memory ts') = length (memory ts) + 1 ")
  prefer 2
    apply simp
   apply (metis Suc_eq_plus1 diff_is_0_eq nat_neq_iff not_less_eq_eq zero_less_diff)
  by (smt (verit, best) assms(4) cas_succ_wfs loc_eq_comploc order_le_less_trans valOf_def)





lemma cas_succ_glb_monotone_complete_preserved_aux:
  assumes "  (  \<forall> i j  .0 < j \<and>  j < length(memory ts)  \<and> 0 \<le>  i \<and>  i < length(memory ts)  \<and>  i \<le> j \<and>  comploc ((memory ts)!j) glb = glb   \<and>  comploc ((memory ts)!i) glb = glb   \<longrightarrow> ((compval ts  (memory( ts)!i) glb ) \<le> (compval ts  (memory( ts)!j) glb ) ))"
 and "vbounded ts"
and "  \<lceil>glb : v1 \<rceil> ts "
and "mem_structured ts"
and  "ts' = cas_succ_trans t (last_entry ts glb) glb v1 (Suc v1) r  nv mnv ts "
(*and "  \<lceil>glb\<rceil>\<^sub>t ts "*)
and " \<forall> ti l. last_entry ts l \<in>   OTS ts ti l "
and " \<forall> ti l. lastVal  l ts  \<in>  [l]\<^sub>ti ts " 
shows   "(  \<forall> i j  . 0 < j \<and>  j < length(memory ts')  \<and> 0 \<le>  i \<and>  i < length(memory ts')  \<and>  i \<le> j \<and>   comploc ((memory ts')!j) glb = glb    \<and>   comploc ((memory ts')!i) glb = glb    \<longrightarrow> ((compval ts'  (memory( ts')!i) glb ) \<le> (compval ts'  (memory( ts')!j) glb ) ))"
 using assms
apply (subgoal_tac "  valOf (last_entry  ts  glb)  glb  ts = v1")
   prefer 2
   apply (simp add: valOf_def)
apply (subgoal_tac "   last_entry  ts' glb =  length (memory ts) ")
   prefer 2
   apply (subgoal_tac "  length (memory ts) =  length (memory ts') -1 ")
    prefer 2
    apply (simp add: cas_succ_trans_def)
  using cas_succ_lastentry apply presburger
  apply (subgoal_tac "  valOf (last_entry  ts'  glb)  glb  ts' = Suc v1")
   prefer 2
  apply (simp add: cas_succ_trans_def  valOf_def )
apply (subgoal_tac " (\<forall>i.(i \<ge>0\<and>i<length(memory ts)) \<longrightarrow> ( memory ts)!i =( memory ts')!i) ")
   prefer 2
  using mem_l_casucc 
  using nat_less_le apply presburger
apply (subgoal_tac " \<forall> i .(i\<ge>0\<and>i<length(memory ts)) \<longrightarrow>  ( valOf  i glb  ts  = valOf  i glb  ts' )")
   prefer 2
   apply (simp add: valOf_def)
  using survived_val_cas_succ apply presburger
apply (subgoal_tac "  \<forall>  j . (  (0 \<le> j \<and>  j < length(memory ts)  \<and> comploc ((memory ts)!j) glb = glb)   \<longrightarrow>  valOf  j  glb  ts  \<le>  v1 ) ")
   prefer 2  
apply (subgoal_tac " \<forall> j . (0 \<le> j \<and>  j < length(memory ts)  \<and> comploc ((memory ts)!j) glb = glb)  \<longrightarrow>  j \<le> last_entry  ts  glb  ")
   prefer 2
    apply (subgoal_tac "\<forall> j .(0 \<le>  j \<and>  j < length(memory ts)  \<and> comploc ((memory ts)!j) glb = glb)  \<longrightarrow>  j \<in> last_entry_set ts glb")
  prefer 2
     apply (simp add: last_entry_set_def)
     apply metis
    apply (subgoal_tac "\<forall> i. i \<in>  last_entry_set ts glb \<longrightarrow> i \<le>  last_entry  ts  glb  ")
     prefer 2
  apply (simp add: last_entry_def)
  using  finite_last_entry_set    apply (metis Max_ge)
    apply metis
  apply (metis dual_order.eq_iff last_entry_bounded last_entry_loc loc_eq_comploc nat_less_le valOf_def zero_less_iff_neq_zero)
apply (subgoal_tac "  \<forall>  j . (  (0 \<le> j \<and>  j < length(memory ts')  \<and> comploc ((memory ts')!j) glb = glb)   \<longrightarrow>  valOf  j  glb  ts'  \<le>  Suc v1 ) ")
   prefer 2
apply (subgoal_tac " \<forall> j . (0 \<le> j \<and>  j < length(memory ts')  \<and> comploc ((memory ts')!j) glb = glb)  \<longrightarrow>  j \<le> last_entry  ts'  glb  ")
   prefer 2
    apply (subgoal_tac "\<forall> j .(0 \<le> j \<and>  j < length(memory ts')  \<and> comploc ((memory ts')!j) glb = glb)  \<longrightarrow>  j \<in> last_entry_set ts' glb")
  prefer 2
     apply (simp add: last_entry_set_def)
    apply (subgoal_tac "\<forall> i. i \<in>  last_entry_set ts'  glb \<longrightarrow> i \<le>  last_entry  ts'  glb  ")
     prefer 2
  apply (simp add: last_entry_def)
  using  finite_last_entry_set    apply (metis Max_ge)
    apply metis
  apply (metis   le_Suc_eq nat_less_le)
  apply (subgoal_tac " (\<forall> i j  .( 0 < j \<and>  j < length(memory ts') \<and> 0 \<le> i \<and>  i < length(memory ts') \<and>  i \<le> j \<and> comploc ((memory ts')!i) glb = glb \<and> comploc ((memory ts')!j) glb = glb  ) \<longrightarrow>
            ( valOf  i glb ts'  \<le> valOf j glb  ts')  )")
   prefer 2
  apply (intro allI impI)
   apply (case_tac"  j < length (memory ts) \<and>  i < length (memory ts) ")

  apply (metis bot_nat_0.extremum valOf_def)
   apply (subgoal_tac " length (memory ts') = length (memory ts) + 1 ")
  prefer 2
    apply simp
   apply (metis Suc_eq_plus1 diff_is_0_eq nat_neq_iff not_less_eq_eq zero_less_diff)
  by (smt (verit, best) assms(4) cas_succ_wfs loc_eq_comploc order_le_less_trans valOf_def)




(*rule: The monotonicity property of glb is preserved after a successful   cas of the form: cas glb v v+1*)
lemma cas_succ_glb_monotone_preserved:
  assumes "  (  \<forall> i j  .0 < j \<and>  j < length(memory ts)  \<and> 0 <  i \<and>  i < length(memory ts)  \<and>  i \<le> j \<and>  (State.loc (memory( ts)!i) ) = glb  \<and>  (State.loc (memory( ts)!j) ) = glb  \<longrightarrow> ((compval ts  (memory( ts)!i) glb ) \<le> (compval ts  (memory( ts)!j) glb ) ))"
 and "vbounded ts"
and "  \<lceil>glb :  (regs ts t r) \<rceil> ts "
and "mem_structured ts"
and  "ts'  =
       cas_succ_trans t  (last_entry ts glb)  glb (regs ts t r)
        (Suc (regs ts t r)) c1  nv mnv ts"
(*and "  \<lceil>glb\<rceil>\<^sub>t ts "*)
and " \<forall> ti l. last_entry ts l \<in>   OTS ts ti l "
and " \<forall> ti l. lastVal  l ts  \<in>  [l]\<^sub>ti ts " 
shows   "(  \<forall> i j  . 0 < j \<and>  j < length(memory ts')  \<and> 0 <  i \<and>  i < length(memory ts')  \<and>  i \<le> j \<and>  (State.loc (memory( ts')!i) ) = glb  \<and>  (State.loc (memory( ts')!j) ) = glb  \<longrightarrow> ((compval ts'  (memory( ts')!i) glb ) \<le> (compval ts'  (memory( ts')!j) glb ) ))"
  using assms
   using  cas_succ_glb_monotone_preserved_aux [where ts = ts and ts' = ts'  and glb = glb and t = t ]
   by blast



(*rule: The monotonicity property of glb is preserved after a successful cas of the form: cas glb v v+1, including also the initial message*)
lemma cas_succ_glb_monotone_complete_preserved:
  assumes "  (  \<forall> i j  .0 < j \<and>  j < length(memory ts)  \<and> 0 \<le>  i \<and>  i < length(memory ts)  \<and>  i \<le> j \<and> comploc ((memory ts)!i) glb = glb   \<and>  comploc ((memory ts)!j) glb = glb   \<longrightarrow> ((compval ts  (memory( ts)!i) glb ) \<le> (compval ts  (memory( ts)!j) glb ) ))"
 and "vbounded ts"
and "  \<lceil>glb :  (regs ts t r) \<rceil> ts "
and "mem_structured ts"
and  "ts'  =
       cas_succ_trans t  (last_entry ts glb)  glb (regs ts t r)
        (Suc (regs ts t r)) c1  nv mnv ts"
(*and "  \<lceil>glb\<rceil>\<^sub>t ts "*)
and " \<forall> ti l. last_entry ts l \<in>   OTS ts ti l "
and " \<forall> ti l. lastVal  l ts  \<in>  [l]\<^sub>ti ts " 
shows   "(  \<forall> i j  . 0 < j \<and>  j < length(memory ts')  \<and> 0 \<le>  i \<and>  i < length(memory ts')  \<and>  i \<le> j \<and>   comploc ((memory ts')!i) glb = glb   \<and>  comploc ((memory ts')!j) glb = glb   \<longrightarrow> ((compval ts'  (memory( ts')!i) glb ) \<le> (compval ts'  (memory( ts')!j) glb ) ))"
  using assms
   using  cas_succ_glb_monotone_complete_preserved_aux [where ts = ts and ts' = ts'  and glb = glb and t = t ]
   by blast


(*rule: The monotonicity property of glb is preserved after a successful cas of the form: cas glb v v*)
lemma cas_succ_read_glb_monotone_preserved:
  assumes "  (  \<forall> i j  .0 < j \<and>  j < length(memory ts)  \<and> 0 <  i \<and>  i < length(memory ts)  \<and>  i \<le> j \<and>  (State.loc (memory( ts)!i) ) = glb  \<and>  (State.loc (memory( ts)!j) ) = glb  \<longrightarrow> ((compval ts  (memory( ts)!i) glb ) \<le> (compval ts  (memory( ts)!j) glb ) ))"
 and "vbounded ts"
and "  \<lceil>glb :  (regs ts t r) \<rceil> ts "
and "mem_structured ts"
and  "ts'  =
       cas_succ_trans t  (last_entry ts glb)  glb (regs ts t r)
        ((regs ts t r)) c1  nv mnv ts"
(*and "  \<lceil>glb\<rceil>\<^sub>t ts "*)
and " \<forall> ti l. last_entry ts l \<in>   OTS ts ti l "
and " \<forall> ti l. lastVal  l ts  \<in>  [l]\<^sub>ti ts " 
shows   "(  \<forall> i j  . 0 < j \<and>  j < length(memory ts')  \<and> 0 <  i \<and>  i < length(memory ts')  \<and>  i \<le> j \<and>  (State.loc (memory( ts')!i) ) = glb  \<and>  (State.loc (memory( ts')!j) ) = glb  \<longrightarrow> ((compval ts'  (memory( ts')!i) glb ) \<le> (compval ts'  (memory( ts')!j) glb ) ))"
  using assms
   using  cas_succ_read_glb_monotone_preserved_aux [where ts = ts and ts' = ts'  and glb = glb and t = t ]
   by blast

(*rule: The monotonicity property of glb is preserved after a successful cas of the form: cas glb v v, including also the initial message*)
lemma cas_succ_read_glb_monotone_complete_preserved:
  assumes "  (  \<forall> i j  .0 < j \<and>  j < length(memory ts)  \<and> 0 \<le>  i \<and>  i < length(memory ts)  \<and>  i \<le> j \<and>  comploc ((memory ts)!i) glb = glb \<and>    comploc ((memory ts)!j) glb = glb     \<longrightarrow> ((compval ts  (memory( ts)!i) glb ) \<le> (compval ts  (memory( ts)!j) glb ) ))"
 and "vbounded ts"
and "  \<lceil>glb :  (regs ts t r) \<rceil> ts "
and "mem_structured ts"
and  "ts'  =
       cas_succ_trans t  (last_entry ts glb)  glb (regs ts t r)
        ((regs ts t r)) c1  nv mnv ts"
(*and "  \<lceil>glb\<rceil>\<^sub>t ts "*)
and " \<forall> ti l. last_entry ts l \<in>   OTS ts ti l "
and " \<forall> ti l. lastVal  l ts  \<in>  [l]\<^sub>ti ts " 
shows   "(  \<forall> i j  . 0 < j \<and>  j < length(memory ts')  \<and> 0 \<le>  i \<and>  i < length(memory ts')  \<and>  i \<le> j \<and>   comploc ((memory ts')!i) glb = glb \<and>    comploc ((memory ts')!j) glb = glb    \<longrightarrow> ((compval ts'  (memory( ts')!i) glb ) \<le> (compval ts'  (memory( ts')!j) glb ) ))"
  using assms
   using  cas_succ_read_glb_monotone_preserved_complete_aux [where ts = ts and ts' = ts'  and glb = glb and t = t ]
   by (smt (z3) le_eq_less_or_eq mem_l_casucc)




(*rule: The monotonicity property of glb is preserved after a failed  cas*)
lemma cas_fail_read_glb_monotone_preserved_aux:
  assumes "  (  \<forall> i j  .0 < j \<and>  j < length(memory ts)  \<and> 0 <  i \<and>  i < length(memory ts)  \<and>  i \<le> j \<and>  (State.loc (memory( ts)!i) ) = glb  \<and>  (State.loc (memory( ts)!j) ) = glb  \<longrightarrow> ((compval ts  (memory( ts)!i) glb ) \<le> (compval ts  (memory( ts)!j) glb ) ))"
 and "vbounded ts"
and "mem_structured ts"
and " step t ( CAS x  v1 v2 r) ts ts' "
and "regs ts' t r  = 0"
shows   "(  \<forall> i j  . 0 < j \<and>  j < length(memory ts')  \<and> 0 <  i \<and>  i < length(memory ts')  \<and>  i \<le> j \<and>  (State.loc (memory( ts')!i) ) = glb  \<and>  (State.loc (memory( ts')!j) ) = glb  \<longrightarrow> ((compval ts'  (memory( ts')!i) glb ) \<le> (compval ts'  (memory( ts')!j) glb ) ))"
  using assms
  apply (subgoal_tac " memory ts = memory ts' ")
   prefer 2
   apply (simp add: step_def)
  apply clarify
   apply (subgoal_tac "  ts' = cas_fail_trans t ind x v1 v2 r ts  ")
  prefer 2
    apply (metis cas_suc_reg zero_neq_one)
  apply (simp add:  cas_fail_trans_def)
  by (metis mem_structured_preserved val_eq_compval)


(*rule: The monotonicity property of glb is preserved after a failed cas, including also the initial message*)
lemma cas_fail_read_glb_monotone_complete_preserved_aux:
  assumes "  (  \<forall> i j  .0 < j \<and>  j < length(memory ts)  \<and> 0 \<le>  i \<and>  i < length(memory ts)  \<and>  i \<le> j \<and>   comploc ((memory ts)!i) glb = glb  \<and>    comploc ((memory ts)!j) glb = glb   \<longrightarrow> ((compval ts  (memory( ts)!i) glb ) \<le> (compval ts  (memory( ts)!j) glb ) ))"
 and "vbounded ts"
and "mem_structured ts"
and " step t ( CAS x  v1 v2  r) ts ts' "
and "regs ts' t r  = 0"
shows   "(  \<forall> i j  . 0 < j \<and>  j < length(memory ts')  \<and> 0 \<le>  i \<and>  i < length(memory ts')  \<and>  i \<le> j \<and>    comploc ((memory ts')!i) glb = glb \<and>    comploc ((memory ts')!j) glb = glb  \<longrightarrow> ((compval ts'  (memory( ts')!i) glb ) \<le> (compval ts'  (memory( ts')!j) glb ) ))"
  using assms
  apply (subgoal_tac " memory ts = memory ts' ")
   prefer 2
   apply (simp add: step_def)
  apply clarify
   apply (subgoal_tac "  ts' = cas_fail_trans t ind x v1 v2 r ts  ")
  prefer 2
    apply (metis cas_suc_reg zero_neq_one)
   apply (simp add:  cas_fail_trans_def)
  apply simp
  using survived_val_preserved_cas
  by (smt (z3))


lemma cas_lastEntry:
 assumes " step t ( CAS glb  v1 v2 r) ts ts'"
 and "vbounded ts"
and " \<forall> l ti. last_entry ts l \<in>   OTS ts ti l "
and "mem_structured ts"
and  "\<forall>ti l. comploc ( (memory ts)!(coh ts ti l)) l = l"
shows  "  ( OTS ts' t x = {last_entry ts' x}  \<and>  regs ts' t  r = 1)  \<or>  regs ts' t  r = 0 "
  using assms
  apply (simp add: step_def)
apply (subgoal_tac " \<forall> i. i \<in> last_entry_set ts'  x \<longrightarrow> i \<le> last_entry ts' x")
   prefer 2
   apply (simp add: last_entry_def) 
   apply (subgoal_tac " last_entry_set ts' x  \<noteq> {} ")
  prefer 2
  using assms(1) last_entry_set_not_empty mem_structured_preserved vbounded_preserved apply blast
  apply (simp add: finite_last_entry_set)
  apply clarify
  apply (case_tac " ts' =
           cas_succ_trans t ind glb v1 v2 r  nv mnv ts")
   apply (case_tac " x = glb")
  apply (subgoal_tac "  OTS ts' t x = { length(memory ts')-1}" )
  prefer 2
  apply (meson cas_ots_lastentry)
  using One_nat_def cas_suc_reg cas_succ_lastentry apply presburger
   apply (subgoal_tac " ( vrnew ts' t  =  (length(memory ts) )  ) ")
    prefer 2
    apply(simp add: vbounded_def  cas_succ_trans_def )
   apply (subgoal_tac" last_entry ts' x \<in>  OTS ts' t x")
  prefer 2
  using OTS_def assms(1) assms(5) le_in_otsf apply presburger 
   defer
   apply (subgoal_tac "  last_entry ts'  x \<in>   OTS ts' t x " )
    prefer 2
  using assms(1) assms(5) le_in_ots apply blast
   apply (subgoal_tac " \<forall>i .  x= comploc ((memory ts')!i) x \<and>  (i < length (memory ts')) \<longrightarrow> i \<le> last_entry ts'  x ")
    prefer 2
  apply simp
 apply (subgoal_tac " \<forall>t.   x= comploc ((memory ts')!t) x \<and>  (t < length (memory ts'))  \<longrightarrow> t \<in> last_entry_set ts'  x")
   prefer 2
     apply (simp add: last_entry_set_def )
   apply simp 
 apply (subgoal_tac " \<forall>i . x= comploc ((memory ts')!i) x \<and>  (i < length (memory ts')) \<longrightarrow> i \<le> last_entry ts'  x ")
   prefer 2
  apply (metis assms(1) assms(2) assms(4) bot_nat_0.extremum bot_nat_def comploc_def diff_is_0_eq' dual_order.strict_trans1 last_entry_notoverwritten le_neq_implies_less less_nat_zero_code linorder_not_less mem_structured_def mem_structured_preserved notoverwritten_def pinf(4) sup.strict_coboundedI2 sup_idem vbounded_preserved zero_less_diff)
 apply (subgoal_tac " \<forall>t. x= comploc ((memory ts')!t) x \<and>  (t < length (memory ts'))  \<longrightarrow> t \<in> last_entry_set ts'  x")
   prefer 2
   apply (simp add: last_entry_set_def )
  apply (simp add: OTS_def)
  apply (simp add: OTSF_def notoverwritten_def)
  apply safe
  apply (metis assms(2) assms(4) diff_self_eq_0 dual_order.irrefl last_entry_succ_daddr_preserved le0 less_SucE less_Suc_eq_le less_imp_diff_less mem_l mem_structured_def nat_neq_iff store_add)
            apply (metis Msg.discI le_eq_less_or_eq less_Suc_eq_le less_nat_zero_code linorder_neqE_nat mem_l mem_structured_def nth_append_length store_add)
  apply (metis assms(2) assms(4) diff_self_eq_0 dual_order.irrefl last_entry_succ_daddr_preserved le0 less_SucE less_Suc_eq_le less_imp_diff_less mem_l mem_structured_def nat_neq_iff store_add)
  apply (metis assms(4) cas_fail_reg cas_suc_reg zero_neq_one)
         apply (metis Msg.discI le_eq_less_or_eq less_Suc_eq_le less_nat_zero_code linorder_neqE_nat mem_l mem_structured_def nth_append_length store_add)
        apply (metis cas_fail_reg cas_suc_reg zero_neq_one)
  apply (metis Msg.discI le_eq_less_or_eq less_Suc_eq_le less_nat_zero_code linorder_neqE_nat mem_l mem_structured_def nth_append_length store_add)
      apply (metis cas_fail_reg cas_suc_reg zero_neq_one)
  apply (metis Msg.discI le_eq_less_or_eq less_Suc_eq_le less_nat_zero_code linorder_neqE_nat mem_l mem_structured_def nth_append_length store_add)
    apply meson
   apply meson
   by meson
  

lemma cas_lastVal:
 assumes " step t ( CAS glb  v1 v2 r) ts ts'"
 and "vbounded ts"
and "mem_structured ts"
and " \<forall> l ti. last_entry ts l \<in>   OTS ts ti l "
and  "\<forall>ti l. comploc ( (memory ts)!(coh ts ti l)) l = l"
shows  "  ([l]\<^sub>t ts' = {lastVal l  ts'} \<and>  regs ts' t r = 1)  \<or>  regs ts' t r = 0 "
  using assms
 apply (subgoal_tac " survived_val ts' l = survived_val ts l") 
     prefer 2
   apply (simp add: survived_val_preserved_cas)
  apply (subgoal_tac "  ( OTS ts' t l= {last_entry ts' l}  \<and>  regs ts' t  r = 1)  \<or>  regs ts' t  r = 0 ")
   prefer 2
  apply (meson cas_lastEntry)
 apply (simp add: step_def)
  apply clarify
 apply (subgoal_tac "  regs ts' t r = 1  \<or>   regs ts' t r= 0 ")
   prefer 2
  apply linarith
apply (case_tac "  regs ts' t r = 1 ")
    apply (subgoal_tac"  ts' = cas_succ_trans t ind glb v1 v2 r  nv mnv ts")
    prefer 2
    apply (metis cas_fail_reg zero_neq_one)
 apply (simp add: lastVal_def)
   apply (simp add: mapval_def)
  by simp

(*lemmas [simp del] = compval_def*)


lemma aux : shows "  \<forall> i. i \<in>  OTS ts t glb \<longrightarrow> 0 \<le> i  \<and> i < length (memory ts) "
  apply (simp add: OTS_def)
  by (simp add: OTSF_def)


 (*rule: All the last writes of addresses different from x remain the same after the execution of a cas of the form cas x v1 v2*)
lemma cas_le_daddr:
assumes "mem_structured ts"
and "vbounded ts"
and  " step t ( CAS glb  v1 v2 r) ts ts'" 
shows "  \<forall>l. l \<noteq> glb \<longrightarrow> lastVal l ts' = lastVal l ts"
  using assms
  apply (simp add: step_def)
  apply (subgoal_tac " \<forall>l. l \<noteq> glb \<longrightarrow>  last_entry ts'  l = last_entry ts  l")
   prefer 2
  apply (metis last_entry_fail_daddr_preserved last_entry_succ_daddr_preserved)

  apply clarify
apply (case_tac " ts' =cas_succ_trans t ind glb v1
            v2 r  nv mnv ts")
  apply (metis bot_nat_0.extremum compval_def lastVal_def last_entry_bounded last_entry_succ_daddr_preserved mem_l_casucc survived_val_cas_succ)
(*  apply (metis assms(1) assms(2) bot_nat_0.extremum compval_def lastVal_def last_entry_bounded mem_l_casucc survived_val_cas_succ)*)
  apply (unfold lastVal_def) 
  apply simp
  using survived_val_cas_fail 
  using last_entry_fail_daddr_preserved by presburger
 

lemma cas_succ_oats_daddr_ni:
  assumes "mem_structured ts"
 and "vbounded ts"
 and " ts' =   cas_succ_trans t ind x v1 v2 r  nv mnv ts"
and " l \<noteq> x"
(*and " t \<noteq> t' "*)
shows" OATS ts' t' l =  OATS ts t' l"
  using assms
  apply (simp add:OATS_def )
  apply (subgoal_tac "vpasync ts' t' l = vpasync ts t' l ")
  prefer 2
   apply (simp add:  cas_succ_trans_def)
  apply (subgoal_tac " (comploc  ((memory ts')!length (memory ts)) l)  = x ")
   prefer 2
   apply simp
  apply (subgoal_tac " length (memory ts) \<notin>  OATS ts' t' l")
   prefer 2
   apply (simp add: OATS_def)
    apply (subgoal_tac " (\<forall>i.(i\<ge>0\<and>i<length(memory ts)) \<longrightarrow> ( memory ts)!i =( memory ts')!i) ")
    prefer 2
  using mem_l_casucc apply blast
  apply safe
                      apply (metis Msg.sel(1) less_SucE nth_append_length)
  apply (metis Msg.sel(1) less_SucE less_eq_nat.simps(1) mem_l nth_append_length store_add)
                      apply (metis Msg.sel(1) less_SucE nth_append_length)
                      apply (metis Msg.sel(1) le0 less_antisym mem_l nth_append_length store_add)
                      apply (simp add: notoverwritten_def)
                      apply (metis Msg.discI less_SucE nth_append_length)
                      apply (simp add: notoverwritten_def)
                      apply (metis Msg.discI less_SucE nth_append_length)
  apply (metis Msg.distinct(1) le0 less_antisym mem_l nth_append_length store_add)
                      apply (simp add: notoverwritten_def)
                     apply (metis Msg.sel(1) less_SucE nth_append_length)
                    apply (simp add: notoverwritten_def)
                   apply (metis Msg.sel(1) less_SucE nth_append_length)
                  apply (simp add: notoverwritten_def)
  apply (metis Msg.sel(1) less_Suc_eq nth_append_length)
                 apply (simp add: notoverwritten_def)
                apply linarith
               apply (metis bot.extremum bot_nat_def mem_l store_add)
  using less_SucI apply blast
             apply simp
  apply (simp add: notoverwritten_def)
            apply (metis Msg.sel(1) less_Suc_eq nth_append_length)
           apply linarith
          apply (simp add: notoverwritten_def)
          apply (metis Msg.sel(1) less_Suc_eq nth_append_length)
  using less_SucI apply blast
        apply (metis bot.extremum bot_nat_def mem_l store_add)
       apply simp
  using less_SucI apply blast
  apply (simp add: notoverwritten_def)
     apply (metis Msg.sel(1) less_Suc_eq nth_append_length)
  using less_SucI apply blast
   apply (metis bot.extremum bot_nat_def mem_l store_add)
  apply (simp add: notoverwritten_def)
  by (metis Msg.sel(1) less_Suc_eq nth_append_length)




lemma cas_fail_oats_daddr_ni:
  assumes "mem_structured ts"
 and "vbounded ts"
and " ts' =   cas_fail_trans t' ind x v1 v2 r ts "
(*and " l \<noteq> x"*)
shows" OATS ts' t l =  OATS ts t l"
  using assms
  apply (subgoal_tac "vpasync ts' t l = vpasync ts t l ")
  prefer 2
   apply (simp add:  cas_fail_trans_def)
  by(simp add: OATS_def notoverwritten_def)

lemma cas_fail_oav_ni_step:
  assumes "mem_structured ts"
 and "vbounded ts"
and " step t ( CAS x  v1 v2 r) ts ts'"
and " regs ts' t r = 0 "
shows" OATS ts' t' l =  OATS ts t' l"
  using assms
  apply (simp add: step_def)
  apply clarify
  apply (subgoal_tac "  ts' = cas_fail_trans t ind x v1 v2 r ts")
  prefer 2
   apply (metis cas_suc_reg zero_neq_one)
  using cas_fail_oats_daddr_ni by presburger



 (*rule: The asynchronous view of all addresses remain the same after a failed cas*)
lemma cas_fail_oav_ni:
  assumes "mem_structured ts"
 and "vbounded ts"
and " step t' ( CAS x  v1 v2 r) ts ts'"
and " regs ts' t' r = 0 "
shows" [l]\<^sup>A\<^sub>t  ts' =  [l]\<^sup>A\<^sub>t  ts"
  using assms
  apply (simp add: step_def)
  apply clarify
  apply (subgoal_tac "  ts' = cas_fail_trans t' ind x v1 v2 r ts")
  prefer 2
  apply (metis cas_suc_reg zero_neq_one)
  apply (subgoal_tac " OATS ts' t l =  OATS ts t l")
   prefer 2
  using cas_fail_oats_daddr_ni apply presburger
  apply (simp add : mapval_def)
  using assms(3) survived_val_preserved_cas by presburger



(*rule: The asynchronous view of x for t is updated to include v2 after a successful cas executed by a different thread from t,  of the form: cas x v1 v2*)
lemma  cas_succ_step_oav_dt_lc:
  assumes "mem_structured ts"
  and "vbounded ts"
  and "t \<noteq> t'"
and " step t' ( CAS x  v1 v2 r) ts ts'"
and " regs ts' t' r = 1 "
shows "  [x]\<^sup>A\<^sub>t ts'  =  [x]\<^sup>A\<^sub>t ts  \<union> {v2}"
  using assms
  apply (simp add: step_def)
  apply clarify
  apply (subgoal_tac "  ts' = cas_succ_trans t' ind x v1 v2 r  nv mnv ts  ")
  prefer 2
  apply (metis assms(5) cas_fail_reg zero_neq_one)
  using cas_succ_oav_dt_lc by force

(*rule: *)
lemma cas_dt_ni :
  assumes "mem_structured ts"
 and "vbounded ts"
and " u \<in> [l]\<^sub>t  ts"
and " step t1 ( CAS x  v1 v2 r) ts ts'"
and " t \<noteq> t1"
shows" u \<in> [l]\<^sub>t  ts'"
  using assms
  apply (simp add: step_def)
  apply clarify
  apply (case_tac "  ts' =
   cas_succ_trans t1 ind x v1 v2 r  nv mnv ts")
  apply (metis UnCI assms(1) assms(2) assms(3) cas_succ_ov_daddr_dt cas_succ_ov_dt_lc)
  using cas_fail_ov_ni by blast

(*rule: If the thread view of x is maximal for after a failed  cas on x executed by a different thread from t, it remains maximal*)
lemma cas_fail_lastVal_dt_ni :
  assumes "mem_structured ts"
 and "vbounded ts"
and " \<forall>l. [l]\<^sub>t ts = {lastVal l ts}"
and " step t' ( CAS x  v1 v2 r) ts ts'"
and " regs ts' t'  r = 0"
and "t \<noteq> t' "
 and " \<forall> l ti. lastVal  l ts  \<in>  [l]\<^sub>ti ts  " 
shows" \<forall>l. [l]\<^sub>t ts' = {lastVal l ts'}"
  using assms
  apply (simp add: step_def)
  apply clarify
  apply (subgoal_tac "ts' = cas_fail_trans t' ind x v1 v2 r ts")
   prefer 2
  apply (metis cas_suc_reg zero_neq_one)
  apply (subgoal_tac " \<forall>l. [l]\<^sub>t ts' = [l]\<^sub>t ts ")
   prefer 2
  using cas_fail_ov_ni apply presburger
  apply (subgoal_tac "memory ts = memory ts' ")
   prefer 2
   apply (simp add: cas_fail_trans_def )
  apply (subgoal_tac " lastVal l ts= lastVal l ts'")
   prefer 2
apply (subgoal_tac "  last_entry_set ts' l =  last_entry_set ts l ")
    prefer 2
  apply (simp(no_asm) add: last_entry_set_def)
  apply presburger

apply (subgoal_tac "  last_entry ts' l =  last_entry ts l ")
    prefer 2
  apply (simp(no_asm) add: last_entry_def)
  apply presburger
  apply (metis cas_fail_crash lastVal_def)
  by presburger

(*rule: If the thread view of x is maximal for thread t, after a failed cas on x executed by a different thread from t, it remains maximal*)
lemma cas_succ_glb_gr_lc:
  assumes "step t ( CAS glb (regs ts t l)  (Suc(regs ts t l))  r) ts ts'"
 and "vbounded ts"
and "mem_structured ts"
and " \<forall> l ti. last_entry ts l \<in>   OTS ts ti l "
and  "\<forall>ti l. comploc ( (memory ts)!(coh ts ti l)) l = l"
and" regs ts' t r > 0"
shows  "(regs ts' t l) \<le>  lastVal glb ts' "
  using assms
  apply (simp add: step_def)
  apply clarify
  apply (subgoal_tac" ts' = cas_succ_trans t ind glb (regs ts t l) (Suc (regs ts t l)) r  nv mnv ts")
   prefer 2
   apply (metis cas_fail_reg less_not_refl3)
  by (metis One_nat_def Suc_n_not_le_n assms(1) cas_suc_reg cas_succ_lv_lc lastVal_def less_eq_Suc_le nat_le_linear reg_same_CAS_dr zero_less_Suc)
 

(*rule: The values of the last writes for all addresses in memory remain the same after a failed cas*)
lemma cas_fail_lastVal_ni :
  assumes "mem_structured ts"
 and "vbounded ts"
and " step t' ( CAS x  v1 v2 r) ts ts'"
and " regs ts' t'  r = 0"
shows" \<forall> l ti. lastVal  l ts =  lastVal  l ts' " 
  using assms
  apply (simp add: step_def)
  apply clarify 
  apply (subgoal_tac"  ts' = cas_fail_trans t' ind x v1 v2 r ts")
  prefer 2
   apply (metis cas_suc_reg zero_neq_one)
  by (simp add: cas_fail_trans_def lastVal_def last_entry_def last_entry_set_def)




lemma cas_fail_mem_same:
 assumes   " step t ( CAS x  v1 v2 r) ts ts'"
 and "mem_structured ts"
 and "vbounded ts"
 and " regs ts' t  r = 0"
 shows " memory ts = memory ts' "
  using assms
apply (simp add: step_def)
  apply clarify 
 apply (subgoal_tac"  ts' = cas_fail_trans t ind x v1 v2 r ts")
   prefer 2
  apply (metis cas_suc_reg zero_neq_one)
  by (simp add: cas_fail_trans_def)


lemma cas_fail_ots_sub:
  assumes "mem_structured ts"
  and "vbounded ts"
and "\<forall> ti l.  last_entry ts l \<in>   OTS ts ti l"
and  "\<forall>ti l. comploc ( (memory ts)!(coh ts ti l)) l = l"
and "regs ts' t  r = 0"
and   "step t ( CAS x  v1 v2 r) ts ts'" 

shows  "OTS ts' t' y   \<subseteq> OTS ts t'  y"
  using assms
  apply (simp add: step_def)
  apply clarify
  apply (subgoal_tac "   ts' = cas_fail_trans t ind x v1 v2 r ts ")
  prefer 2
   apply (metis cas_suc_reg zero_neq_one)

  apply (case_tac " t = t' ")
apply (subgoal_tac " coh ts t y \<le> coh ts' t  y")
    prefer 2
    apply (simp add: cas_fail_trans_def Let_def)
  apply (case_tac "ind = coh ts t y")
   apply simp
  apply (simp add: OTS_def)
    apply (simp add: OTSF_def)
 apply (subgoal_tac "  vrnew ts t   \<le> vrnew  ts' t ")
    prefer 2
    apply (simp add:  cas_fail_trans_def Let_def)
 apply (simp add: OTS_def )
  apply (simp add: OTSF_def notoverwritten_def )
  by (metis cas_fail_ots_ni)




lemma cas_le_ni:
  assumes "mem_structured ts"
  and "vbounded ts"
and " step t ( CAS x  v1 v2 r) ts ts' "
  and "  \<lceil>y\<rceil>\<^sub>t  ts "
and  "\<forall>ti l. comploc ( (memory ts)!(coh ts ti l)) l = l"
and "\<forall> ti l.  last_entry ts l \<in>   OTS ts ti l"
and  "\<forall>ti l. comploc ( (memory ts)!(coh ts ti l)) l = l"
shows "  \<lceil>y\<rceil>\<^sub>t  ts'  "
  using assms
  apply (case_tac " x \<noteq> y")
  using cas_ots_lm_ni 
  apply (metis insert_absorb insert_not_empty) 

  apply (simp add: step_def)
  apply clarify
   apply (case_tac " ts' =  cas_fail_trans t (last_entry ts y) y v1 v2 r ts")

   apply (subgoal_tac " regs ts' t  r = 0 ")
    prefer 2
    apply simp
  apply (metis assms(3) assms(5) cas_fail_ots_sub doubleton_eq_iff insert_absorb le_in_ots subset_singletonD)

 apply (subgoal_tac " regs ts' t  r = 1 ")
    prefer 2
   apply simp
  by (metis assms(3) assms(5) cas_lastEntry le_zero_eq not_one_le_zero)
 

lemma cas_fail_diff_lv:
  assumes "mem_structured ts"
  and "vbounded ts"
and " step t ( CAS x  v1 v2 r) ts ts' "
and " (lastVal x  ts) \<noteq> v1 "
shows " regs ts' t r = 0 "
  using assms
  apply (simp add: step_def lastVal_def)
  apply clarify
  apply (subgoal_tac "  ts' = cas_fail_trans t ind x v1 v2 r ts")
  prefer 2
  apply auto[1]
  using cas_fail_reg by blast


lemma  cas_wfs_preserved :
  assumes "total_wfs ts"
 and " step t ( CAS x  v1 v2 r) ts ts' "
shows" total_wfs ts'"
  using assms 
  apply (unfold total_wfs_def)
  by (meson OTSF_notempty_preserved coh_loc_rel_preserved le_in_oats le_in_opts le_in_ots lev_in_oav lev_in_opv lev_in_ov mem_structured_preserved total_OTSF_def vbounded_preserved)


lemma cas_ots_daddr_dt:
assumes "mem_structured ts"
and "vbounded ts"
and  " step t ( CAS x  v1 v2 r) ts ts'"
and " x \<noteq> y "
and "t \<noteq> t' "
shows " OTS ts' t' y =  OTS ts t' y"
  using assms
  apply (simp add: step_def)
  apply clarify
  apply (case_tac " ts' = cas_succ_trans t ind x v1 v2 r  nv mnv ts")
   apply (simp add: cas_succ_ots_daddr_dt)
  by (metis cas_fail_ots_ni)


(*Lemmas regarding the coherence and vrnew  view*) 

lemma  cas_coh_dt_ni :
 assumes " step t ( CAS x  v1 v2 r) ts ts' "
and " t \<noteq> t' "
shows"  coh (ts') t' a =  coh (ts) t' a"
  using assms
   apply (simp add: step_def)

  apply clarify

   apply (case_tac " ts' = cas_succ_trans t ind x v1 v2 r nv mnv ts")
   apply (simp add:  cas_succ_trans_def)
  by (simp add:  cas_fail_trans_def)


lemma  cas_coh_st_ni :
  assumes " step t ( CAS x  v1 v2 r) ts ts' "
and " total_wfs ts"
and" (regs ts' t r =  0) "
and " a \<noteq> x"
shows"  coh (ts') t a =  coh (ts) t  a"
  using assms
  apply (simp add: step_def)
  apply clarify
  apply (subgoal_tac "   ts' = cas_fail_trans t ind x v1 v2 r ts")
  prefer 2
  apply auto[1]
  by (simp add: cas_fail_trans_def)


lemma  cas_succ_coh_ni :
  assumes " step t ( CAS x  v1 v2 r) ts ts' "
and " total_wfs ts"
and" (regs ts' t r =  1) "
and " a \<noteq> x"
shows"  coh (ts') t' a =  coh (ts) t'  a"
  using assms
  apply (simp add: step_def)
  apply clarify
  apply (subgoal_tac " ts' = cas_succ_trans t ind x v1 v2 r  nv mnv ts")
  prefer 2
  apply auto[1]
  by (simp add: cas_succ_trans_def)


lemma  cas_succ_gr_z :
  assumes " step t ( CAS x  v1 v2 r) ts ts' "
and " total_wfs ts"
and" (regs ts' t r =  1) "
shows"  coh (ts') t x >0"
  using assms
 apply (simp add: step_def)
  apply clarify
  apply (subgoal_tac " ts' = cas_succ_trans t ind x v1 v2 r  nv mnv ts")
  prefer 2
   apply auto[1]
  apply (unfold total_wfs_def)
  apply (subgoal_tac "mem_structured ts' ")
   prefer 2
  using cas_succ_wfs apply presburger
  apply (subgoal_tac "coh (ts') t x =  length (memory ts)")
   prefer 2
  apply (simp add: cas_succ_trans_def)
  by (metis bot_nat_0.not_eq_extremum last_entry_bounded less_nat_zero_code)


lemma  cas_succ_lastentry_gr_vrnew :
  assumes " step t ( CAS x  v1 v2 r) ts ts' "
and " total_wfs ts"
and" (regs ts' t r =  1) "
shows"  last_entry_lim (ts') a (coh (ts') t x) \<le> vrnew (ts') t  "
  using assms
 apply (simp add: step_def)
  apply clarify
  apply (subgoal_tac " ts' = cas_succ_trans t ind x v1 v2 r  nv mnv ts")
  prefer 2
   apply auto[1]

 apply (subgoal_tac "vrnew (ts') t  =  length (memory ts)")
   prefer 2
   apply (simp add: cas_succ_trans_def)
   apply (subgoal_tac " (maxcoh ts t) \<le> (length (memory ts) ) ")
  prefer 2
    apply (unfold total_wfs_def)
    apply (unfold vbounded_def)
  using nat_less_le apply blast
  apply (metis max.absorb2 max.absorb3)

  apply (subgoal_tac "   last_entry_lim (ts') a (coh (ts') t x) < length (memory ts' ) ")
   prefer 2
  apply (metis assms(1) assms(2) cas_succ_wfs last_entry_lim_bounded total_wfs_def vbounded_preserved)

  apply (subgoal_tac " length (memory ts' ) = length (memory ts)  +1 ")
  prefer 2
   apply (simp add: cas_succ_trans_def)
  by linarith


lemma  cas_succ_valoflex_eq_v2 :
  assumes " step t ( CAS x  v1 v2 r) ts ts' "
and " total_wfs ts"
and" (regs ts' t r =  1) "
shows"  valOf (coh ts' t x) x ts' = v2 "
  using assms
 apply (simp add: step_def)
  apply clarify
  apply (subgoal_tac " ts' = cas_succ_trans t ind x v1 v2 r  nv mnv ts")
  prefer 2
   apply auto[1]
  by (simp add: valOf_def  cas_succ_trans_def)


lemma cas_succ_OTSx_eq_coh:
 assumes " step t ( CAS x  v1 v2 r) ts ts' "
and " total_wfs ts"
and" (regs ts' t r =  1) "
shows " OTS ts' t x  = { coh ts' t x  }" 
  using assms
 apply (simp add: step_def)
  apply clarify
  apply (subgoal_tac " ts' = cas_succ_trans t ind x v1 v2 r  nv mnv ts")
  prefer 2
   apply auto[1]
  apply (subgoal_tac " coh ts'  t x = length(memory ts')-1 ") 
  prefer 2
   apply (simp add:  cas_succ_trans_def)
  by (metis assms(2)  cas_ots_lastentry length_tl total_wfs_def)
lemma cas_succ_vnrew_eq_length:
 assumes " step t ( CAS x  v1 v2 r) ts ts' "
and " total_wfs ts"
and" (regs ts' t r =  1) "
shows " coh ts' t s   \<le> vrnew ts' t" 
  using assms
  apply (unfold total_wfs_def)
  apply (unfold vbounded_def)
  apply (simp add: step_def) 
   apply clarify
  apply (subgoal_tac " ts' = cas_succ_trans t ind x v1 v2 r  nv mnv ts")
  prefer 2
   apply auto[1]
  apply (subgoal_tac " vrnew ts' t = length (memory ts ) ")
   prefer 2
   apply (simp add: cas_succ_trans_def)
   apply (subgoal_tac " (maxcoh ts t) < length (memory ts )  ")
  prefer 2
   apply blast
  apply (subgoal_tac " (vrnew ts t) < length (memory ts )  ")
  prefer 2
   apply blast
  apply simp
  apply (subgoal_tac "coh ts' t s  < length (memory ts' ) ")
   prefer 2
   apply (subgoal_tac " vbounded ts' ")
    prefer 2
  using assms(1) assms(2) total_wfs_def vbounded_preserved apply blast
   apply (simp add: vbounded_def)
  apply (subgoal_tac " length (memory ts') = length (memory ts) +1 ")
  prefer 2
   apply(simp add: cas_succ_trans_def)
  by simp


lemma cas_succ_OTSx_eq_coh_expanded:
 assumes " step t ( CAS x  v1 v2 r) ts ts' "
and "vbounded ts"
and "  mem_structured ts "
and "    ( \<forall> ti l. comploc ( (memory ts)!(coh ts ti l)) l = l \<and>
           last_entry ts l \<in>   OTS ts ti l \<and>
           last_entry ts l \<in>   OPTS ts l  \<and>
           last_entry ts l \<in>   OATS ts ti l  \<and>
           lastVal  l ts  \<in>  [l]\<^sub>ti ts   \<and>
           lastVal  l ts  \<in>  [l]\<^sub>P ts \<and>
            lastVal  l ts  \<in>   [l]\<^sup>A\<^sub>ti ts) " 
and  " total_OTSF ts "
and" (regs ts' t r =  1) "
shows " OTS ts' t x  = { coh ts' t x  }" 
  using assms
  using cas_succ_OTSx_eq_coh total_wfs_def by presburger
 



lemma cas_suc_compval:
assumes "mem_structured ts"
and "vbounded ts"
and " ts' = cas_succ_trans t  ind x v1 v2 r  nv mnv ts "
shows "compval ts'  (memory ts'!(length(memory ts)))  x  = v2 "
  using assms
  by (simp add: cas_succ_trans_def)



lemma cas_succ_add:
 " memory ( cas_succ_trans t  ind x v1 v2 r  nv mnv ts ) = memory ts @ [msg x v2 t]"
  apply ( simp add: store_trans_def )
  done


lemma cas_fail_lastVal_same:
 assumes " step t ( CAS x  v1 v2 r) ts ts' "
and " total_wfs ts"
and" (regs ts' t r =  0) "
shows " lastVal x ts' = lastVal x ts " 
  using assms
  apply (simp add: step_def)
  apply clarify
  apply (subgoal_tac "  ts' = cas_fail_trans t ind x v1 v2 r ts ")
  prefer 2
   apply fastforce
  apply (unfold lastVal_def)
  apply (subgoal_tac "memory ts = memory ts' ")
   prefer 2
  using assms(1) assms(3) cas_fail_mem_same total_wfs_def apply blast
  by (metis assms(1) assms(2) assms(3) cas_fail_lastVal_ni lastVal_def total_wfs_def valOf_def)



lemma cas_le_lim_dt_ni:
assumes " step t ( CAS x  v1 v2 r) ts ts' "
and " total_wfs ts"
and " t \<noteq> t' "
shows " last_entry_lim (ts') b (coh (ts') t' glb) =  last_entry_lim (ts) b (coh (ts) t' glb)"
  using assms
  apply (unfold total_wfs_def)
  apply (simp add: step_def)
  apply clarify
  apply (case_tac" ts' =  cas_succ_trans t ind x
            v1 v2 r nv mnv ts")
  apply (subgoal_tac "  length (memory ts ) =  length (memory ts' ) - 1 ")
    prefer 2
   apply (simp add:  cas_succ_trans_def Let_def )
  apply (subgoal_tac " memory ts' = memory ts @ [msg x v2 t]")
  prefer 2
    apply simp
   apply (subgoal_tac " (coh (ts') t' glb) = (coh (ts) t' glb)")
  prefer 2
  using assms(1) cas_coh_dt_ni apply blast
   apply (subgoal_tac " \<forall>i. 0 \<le> i \<and> i < length (memory ts ) \<longrightarrow> (memory ts)!i = (memory ts')!i ")
  prefer 2
    apply (metis assms(1) cas_fail_mem_same cas_lc mem_l_cas_succ_step)

   apply (subgoal_tac " (coh (ts') t' glb) <  length (memory ts )")
    prefer 2
  apply (subgoal_tac " vbounded ts' ")
  prefer 2
  using assms(1) vbounded_preserved apply presburger
  apply (unfold vbounded_def)
  apply metis
   apply (unfold   last_entry_lim_def)
  apply (simp(no_asm) add: last_entry_set_lim_def)
   apply (subgoal_tac " mem_structured ts' ")
    prefer 2
  using cas_succ_wfs apply presburger
   apply (unfold  mem_structured_def)
  apply (smt (z3) Collect_cong Suc_diff_1 length_greater_0_conv less_Suc0 less_Suc_eq less_Suc_eq_le not_less_eq)
  apply (subgoal_tac " memory ts = memory ts' ")
   prefer 2
   apply simp
  apply (simp(no_asm) add: last_entry_set_lim_def)
  using assms(1) cas_coh_dt_ni by presburger


lemma cas_le_lim_valof_dt_ni:
assumes " step t ( CAS x  v1 v2 r) ts ts' "
and " total_wfs ts"
and " t \<noteq> t' "
shows " valOf ( last_entry_lim (ts') b (coh (ts') t' glb)) b ts' = valOf(  last_entry_lim (ts) b (coh (ts) t' glb)) b ts"
  using assms
  apply (simp add: valOf_def)
  by (smt (verit, best) cas_fail_mem_same cas_lc cas_le_lim_dt_ni last_entry_lim_bounded le0 mem_l_cas_succ_step survived_val_preserved_cas total_wfs_def)



lemma cas_coh_valof_dt_ni:
assumes " step t ( CAS x  v1 v2 r) ts ts' "
and " total_wfs ts"
and " t \<noteq> t' "
shows " valOf (coh ts' t' glb)  b ts' = valOf   (coh ts t' glb) b ts"
  using assms
  apply (unfold total_wfs_def)
  apply (subgoal_tac " (coh ts t' glb)  = (coh ts' t' glb)  ")
  prefer 2
  apply (simp add: cas_coh_dt_ni)
 apply (subgoal_tac " \<forall>i. 0 \<le> i \<and> i < length (memory ts ) \<longrightarrow> (memory ts)!i = (memory ts')!i ")
  prefer 2
  apply (metis assms(1) cas_fail_mem_same cas_lc mem_l_cas_succ_step total_wfs_def)

 apply (unfold vbounded_def)
   apply (subgoal_tac " (coh (ts) t' glb) <  length (memory ts )")
   prefer 2
  apply blast
  apply (simp add: valOf_def)
  using survived_val_preserved_cas by presburger



lemma cas_vrnew_dt_ni:
assumes " step t ( CAS x  v1 v2 r) ts ts' "
and " total_wfs ts"
and " t \<noteq> t' "
shows " vrnew ts t' =  vrnew ts' t'  "
  using assms
  apply (simp add: step_def total_wfs_def)
  apply clarify
  apply (case_tac "  ts' =
           cas_succ_trans t ind x v1 v2
            r  nv mnv ts")
   apply (simp add:  cas_succ_trans_def )
  by (simp add:  cas_fail_trans_def )


lemma cas_succ_eq:
  assumes " step t ( CAS x  v1 v2 r) ts ts' "
and" total_wfs ts"
and"  (regs ts' t r =  1)  "
shows"lastVal x ts = v1"
  using assms
  apply (unfold total_wfs_def)
  apply (simp add: step_def)
  apply clarify
  apply (subgoal_tac" ts' = cas_succ_trans t ind x v1 v2 r  nv mnv ts ")
   prefer 2
  apply (metis assms(3) cas_fail_reg zero_neq_one)
  apply (simp add: lastVal_def)
  by (metis assms(3) cas_fail_reg zero_neq_one)



lemma cas_fail_coh_st_dadrr: 
   assumes "mem_structured ts"
  and "vbounded ts"
  and " step t ( CAS x  v1 v2 r) ts ts' "
and"  (regs ts' t r = 0)  "
   and " x \<noteq> y"
 shows " coh ts t y  = coh ts' t y"
  using assms 
  apply (simp add: step_def)
  apply clarify
  apply (subgoal_tac " ts' = cas_fail_trans t ind x v1 v2 r ts ")
  prefer 2
   apply (metis cas_suc_reg zero_neq_one)
  using coh_cas_fail_st_dadrr by blast


lemma vrnew_ld_st_sadrr :
   assumes "mem_structured ts"
  and "vbounded ts"
  and " step t ( CAS x  v1 v2 r) ts ts' "
and"  (regs ts' t r = 0)  "
shows " vrnew ts t' \<le> vrnew  ts' t' "
  using assms 
    apply (simp add: step_def)
  apply clarify
  apply (subgoal_tac " ts' = cas_fail_trans t ind x v1 v2 r ts ")
  prefer 2
   apply (metis cas_suc_reg zero_neq_one)
  apply (case_tac" t  = t' ")
  apply (case_tac "ind = coh ts t x")
  apply simp
  apply (simp add: OTS_def)
  apply (subgoal_tac "  vrnew ts t'   = vrnew  ts' t'")
  prefer 2
     apply (simp add: cas_fail_trans_def Let_def)
  apply auto[1]
   apply (simp add: cas_fail_trans_def Let_def)
  by (simp add: cas_fail_trans_def Let_def)





lemma cas_succ_lv_lim_eq_lv  :
   assumes "mem_structured ts"
  and "vbounded ts"
  and " step t ( CAS x  v1 v2 r) ts ts' "
and"  (regs ts' t r = 1)  "
shows "  (last_entry_lim (ts') l (length (memory ts)) )   =  last_entry (ts') l    "
  using assms 
    apply (simp add: step_def)
  apply clarify
  apply (subgoal_tac " ts' = cas_succ_trans t ind x v1 v2 r  nv mnv ts ")
  prefer 2
   apply (metis assms(4) cas_fail_reg zero_neq_one)
  apply (subgoal_tac " length (memory ts' ) = length (memory ts) + 1 ")
   prefer 2
   apply simp
 apply (subgoal_tac " \<forall>i. 0 \<le> i \<and> i < length (memory ts ) \<longrightarrow> (memory ts)!i = (memory ts')!i ")
  prefer 2
  using mem_l_casucc apply blast


  apply (case_tac " x = l ")
   apply (subgoal_tac "  (last_entry_lim (ts') l (length (memory ts)) )  =  (length (memory ts))  ")
  prefer 2
  apply (unfold last_entry_lim_def )
    apply (subgoal_tac " length (memory ts) \<in>  (last_entry_set_lim ts' l (length (memory ts)))")
     prefer 2
     apply (subgoal_tac " comploc (memory ts' !  (length (memory ts))) l = l ")
      prefer 2
  using cas_suc_loc comploc_def apply presburger
  apply (simp add:  last_entry_set_lim_def )
  using last_entry_set_lim_not_empty  last_entry_lim_bounded finite_last_entry_set_lim
  apply (metis Max_ge add.right_neutral add_Suc_right assms(3) assms(4) last_entry_lim_def le_less_Suc_eq mem_structured_preserved vbounded_preserved)
   apply (subgoal_tac " last_entry ts' l =  (length (memory ts)) ")
  prefer 2

   apply (subgoal_tac " length (memory ts) \<in>  (last_entry_set ts' l )")
     prefer 2
     apply (subgoal_tac " comploc (memory ts' !  (length (memory ts))) l = l ")
      prefer 2
  using cas_suc_loc comploc_def apply presburger
  apply (simp add:  last_entry_set_def )
  apply (metis Nat.add_0_right One_nat_def add_Suc_right cas_succ_lastentry diff_Suc_Suc minus_nat.diff_0)
   apply linarith
  apply (subgoal_tac " last_entry ts' l = last_entry ts l ")
   prefer 2
  using last_entry_succ_daddr_preserved apply presburger
  apply (subgoal_tac " (last_entry_set_lim ts' l (length (memory ts)))  =
(last_entry_set_lim ts l (length (memory ts)))  ")
   prefer 2
  apply (subgoal_tac " comploc (memory ts' !  (length (memory ts))) l \<noteq>  l ")
    prefer 2
  apply (metis assms(3) cas_suc_loc last_entry_bounded less_add_one less_nat_zero_code loc_eq_comploc mem_structured_preserved not_gr_zero)
   apply (unfold last_entry_set_lim_def)
  apply (metis (no_types, lifting) Suc_eq_plus1 le_imp_less_Suc nat_less_le)
  apply (unfold last_entry_def last_entry_set_def)
  using Suc_eq_plus1 less_Suc_eq_le by presburger


lemma cas_succ_lv_lim_eq_lv_val  :
   assumes "mem_structured ts"
  and "vbounded ts"
  and " step t ( CAS x  v1 v2 r) ts ts' "
and"  (regs ts' t r = 1)  "
shows " valOf   (last_entry_lim (ts') l (length (memory ts)) ) l  ts'    =  lastVal l ts'  "
  using assms
  apply (subgoal_tac "  (last_entry_lim (ts') l (length (memory ts)) )   =  last_entry (ts') l  ")
   prefer 2  apply (simp add: cas_succ_lv_lim_eq_lv)
  by (simp add: valOf_def lastVal_def)



lemma  cas_succ_lelim_daddr_ni:
   assumes "mem_structured ts"
  and "vbounded ts"
  and " step t ( CAS x  v1 v2 r) ts ts' "
and"  (regs ts' t r = 0)  "
shows "(\<forall> n l. (0 \<le> n \<and> n < length(memory ts' )) \<longrightarrow> valOf (last_entry_lim ts' l n) l (ts')  =    valOf (last_entry_lim ts l n) l ts  ) "
  using assms
  apply (subgoal_tac " memory ts = memory ts' ")
   prefer 2
  using cas_fail_mem_same apply blast
  apply (simp add:last_entry_lim_def last_entry_set_lim_def valOf_def )
  by (simp add: survived_val_preserved_cas)


lemma  cas_succ_lelim_nle_ni:
   assumes "mem_structured ts"
  and "vbounded ts"
  and " step t ( CAS x  v1 v2 r) ts ts' "
and"  (regs ts' t r = 1)  "
shows "(\<forall> n l. (0 \<le> n \<and> n < length(memory ts )) \<longrightarrow> valOf (last_entry_lim ts' l n) l (ts')  =    valOf (last_entry_lim ts l n) l ts  ) "
  using assms
  apply (simp add: step_def)
  apply clarify
  apply (subgoal_tac " ts' = cas_succ_trans t ind x v1 v2 r  nv mnv ts ")
  prefer 2
   apply (metis assms(4) cas_fail_reg zero_neq_one)
  apply (subgoal_tac " length (memory ts' ) = length (memory ts) + 1 ")
   prefer 2
   apply simp
 apply (subgoal_tac " \<forall>i. 0 \<le> i \<and> i < length (memory ts ) \<longrightarrow> (memory ts)!i = (memory ts')!i ")
  prefer 2
  using mem_l_casucc apply blast
  apply clarify
  apply (subgoal_tac " last_entry_lim ts l n = last_entry_lim ts' l n ")
   prefer 2
   apply (unfold last_entry_lim_def)
   apply (simp add: last_entry_set_lim_def)
  apply (metis (no_types, lifting) Collect_cong le_imp_less_Suc less_Suc_eq not_less_eq not_less_less_Suc_eq)
  apply (simp add: valOf_def)
  by (metis assms(3) last_entry_lim_bounded last_entry_lim_def survived_val_preserved_cas)


lemma  cas_succ_valOf_nle_ni:
   assumes "mem_structured ts"
  and "vbounded ts"
  and " step t ( CAS x  v1 v2 r) ts ts' "
and"  (regs ts' t r = 1)  "
shows "(\<forall> n l. (0 \<le> n \<and> n < length(memory ts )) \<longrightarrow> valOf (n) l (ts')  =    valOf ( n) l ts  ) "
  using assms
  apply (simp add: step_def)
  apply clarify
  apply (subgoal_tac " ts' = cas_succ_trans t ind x v1 v2 r  nv mnv ts ")
  prefer 2
   apply (metis assms(4) cas_fail_reg zero_neq_one)
  apply (subgoal_tac " length (memory ts' ) = length (memory ts) + 1 ")
   prefer 2
   apply simp
 apply (subgoal_tac " \<forall>i. 0 \<le> i \<and> i < length (memory ts ) \<longrightarrow> (memory ts)!i = (memory ts')!i ")
  prefer 2
  using mem_l_casucc apply blast
  apply (simp add: valOf_def)
  using assms(3) survived_val_preserved_cas by presburger
 

lemma  cas_succ_valOf_le_lvx:
   assumes "mem_structured ts"
  and "vbounded ts"
  and " step t ( CAS x  v1 v2 r) ts ts' "
and"  (regs ts' t r = 1)  "
shows "(  valOf (length (memory ts)) x (ts')   = lastVal x (ts') ) "
  using assms
     apply (simp add: valOf_def lastVal_def)
     apply (subgoal_tac "  last_entry (ts') x =  length (memory (ts)) ")
  prefer 2
      apply (simp add: step_def)
      apply (metis One_nat_def cas_fail_reg cas_suc_mem_l cas_succ_lastentry zero_neq_one)
  by  presburger



(*  regs (\<tau> \<sigma>') t PTML2.loc \<in> [glb]\<^sub>t \<tau> \<sigma>'*)

lemma  cas_succ_v2_in_x:
   assumes "total_wfs ts"
  and " step t ( CAS x  v1 v2 r) ts ts' "
and"  (regs ts' t r = 1)  "
shows " v2 \<in> [x]\<^sub>t ts' "
  using assms
  apply (unfold total_wfs_def)
  using cas_sv_lc_2 by blast



lemma cas_fail_coh_lc:
  assumes "mem_structured ts"
 and "vbounded ts"
  and " step t ( CAS x  v1 v2 r) ts ts' "
and"  (regs ts' t r = 0)  "
 and  "\<forall>ti l. comploc ( (memory ts)!(coh ts ti l)) l = l"
shows " coh ts' t x \<in> OTS ts' t x \<and> (\<forall>i . i \<in> OTS ts' t x \<longrightarrow> coh ts' t x \<le> i)  "
  using assms apply (simp add:  step_def mem_structured_def   )
 apply (intro conjI)
   apply (unfold OTS_def OTSF_def)
   apply clarify
   apply (rule_tac x="  coh ts' t x" in exI)
   apply (intro conjI)
        apply blast
       apply blast
      apply (subgoal_tac " vbounded ts' ")
  prefer 2
  using assms(3) vbounded_preserved apply presburger
      apply (simp add: vbounded_def)
  using assms(1) assms(3) assms(4) coh_loc_rel_preserved
  apply (metis assms(5))
    apply blast
   apply (subgoal_tac " ts' = cas_fail_trans t ta x v1 v2 r ts ")
  prefer 2
  apply (metis assms(1) cas_suc_reg zero_neq_one)

   apply (simp add: cas_fail_trans_def  notoverwritten_def Let_def)
apply safe
          apply (simp_all)
  by (metis assms(1) assms(4) cas_suc_reg zero_neq_one)



lemma cas_dt_ov_ni :
  assumes "mem_structured ts"
 and "vbounded ts"
and " step t1 ( CAS x  v1 v2 r) ts ts'"
and " regs ts' t1 r = 0 "
and " t \<noteq> t1"
shows" [l]\<^sub>t  ts' =  [l]\<^sub>t  ts"
  using assms
  apply (simp add: step_def)
  apply clarify
  apply (subgoal_tac " ts' =
           cas_fail_trans t1 ind x v1 v2 r ts ")
   prefer 2
  apply (metis cas_suc_reg zero_neq_one)
  using cas_fail_ov_ni by blast

lemma cas_oav_daddr_ni:
  assumes "mem_structured ts"
 and "vbounded ts"
and " step t ( CAS x  v1 v2 r) ts ts'"
and " l \<noteq> x"
shows" [l]\<^sup>A\<^sub>t'  ts' =  [l]\<^sup>A\<^sub>t'  ts"
  using assms 
   apply ( case_tac " regs ts' t r = 0 ")
  using cas_fail_oav_ni apply blast

   apply (simp add: step_def)
  apply clarify
  apply (subgoal_tac "  ts' = cas_succ_trans t ind x v1 v2 r  nv mnv ts ")
  prefer 2
   apply (metis cas_fail_reg less_not_refl3)

  apply (subgoal_tac "  OATS ts' t' l =  OATS ts t' l ")
   prefer 2
  using cas_succ_oats_daddr_ni apply presburger
  apply (unfold mapval_def)
  apply (subgoal_tac " (\<forall>i.(i\<ge>0\<and>i<length(memory ts)) \<longrightarrow> ( memory ts)!i =( memory ts')!i) ")
  prefer 2
  using mem_l_casucc apply presburger
  by (smt (verit) OATS_def assms(3) compval_def image_cong mem_Collect_eq survived_val_preserved_cas)


lemma cas_ov_daddr_dt_ni:
  assumes "mem_structured ts"
 and "vbounded ts"
and " step t ( CAS x  v1 v2 r) ts ts'"
and " l \<noteq> x"
and " t \<noteq> t' "
shows" [l]\<^sub>t'  ts' =  [l]\<^sub>t'  ts"
  using assms 
   apply ( case_tac " regs ts' t r = 0 ")
  using cas_dt_ov_ni apply presburger
  using cas_dt_ni cas_ov_daddr_ni by blast


lemma cas_ov_daddr_dt_sx_ni:
  assumes "total_wfs ts "
and " step t ( CAS x  v1 v1 r) ts ts'"
and " t \<noteq> t' "
shows" [l]\<^sub>t'  ts' =  [l]\<^sub>t'  ts"
  using assms 
  apply (unfold total_wfs_def)
   apply ( case_tac " regs ts' t r = 0 ")
  using cas_dt_ov_ni apply presburger

   apply (case_tac " x = l ")
    apply (subgoal_tac "  [l]\<^sub>t'  ts'  = [l]\<^sub>t'  ts  \<union> {v1} ")
     prefer 2
  using cas_succ_ov_dt_lc step_def apply auto[1]

     apply (subgoal_tac "   \<lceil>l:v1\<rceil> ts'")
  prefer 2
  apply (meson cas_lc)
     apply (simp add: step_def)
  apply clarify
  apply (subgoal_tac "ts'= cas_succ_trans t ind l v1 v1 r  nv mnv ts ")
  prefer 2
      apply fastforce
     apply (subgoal_tac "   \<lceil>l:v1\<rceil> ts")
      prefer 2
  apply (metis assms(2) cas_fail_diff_lv lastVal_def less_numeral_extra(3))
  apply (smt (verit, ccfv_threshold) insert_absorb lastVal_def)
  using cas_ov_daddr_dt_ni by presburger



end