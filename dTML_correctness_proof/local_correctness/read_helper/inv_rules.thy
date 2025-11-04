(*Lemmas that help in proving  parts of the persistent invariant that concern the DTML Read operation*)
theory inv_rules
  imports "../../DTML" 

begin


lemma sfence_mem_inv:
  assumes "thrdsvars"
  and "total_wfs (ts)"
 and  "step t (sfence) ts ts'"
and " mem_tml_prop    c  n  (ts) "
shows  " mem_tml_prop    c  n  (ts')"
 using assms
  apply (simp add:  mem_tml_prop_def step_def total_wfs_def)

  apply (subgoal_tac " memory (ts) = memory (ts' ) ")
   prefer 2
  apply (metis mem_sfence)
  using assms(3) survived_val_preserved_sfence 
  by (smt (verit, best))





lemma sfence_mem_inv3:
  assumes "thrdsvars"
  and "total_wfs (ts)"
 and  "step t (sfence) ts ts'"
and " mem_tml_prop3   ts "
shows  " mem_tml_prop3   ts'"
 using assms
  apply (simp add:   step_def total_wfs_def)
  apply (subgoal_tac " memory (ts) = memory (ts' ) ")
  prefer 2
  apply (metis mem_sfence)
  apply (unfold mem_tml_prop3_def)
  by (metis assms(3) sfence_crash)



lemma sfence_mem_inv4:
  assumes "thrdsvars"
  and "total_wfs (ts)"
 and  "step t (sfence) ts ts'"
and " mem_tml_prop4   ts "
shows  " mem_tml_prop4   ts'"
 using assms
  apply (simp add:   step_def total_wfs_def)
  apply (subgoal_tac " memory (ts) = memory (ts' ) ")
  prefer 2
  apply (metis mem_sfence)
  apply (unfold mem_tml_prop4_def)
  by (metis assms(3) sfence_crash)



lemma flo_mem_inv:
  assumes "thrdsvars"
  and "total_wfs (ts)"
 and  "ts [flush\<^sub>o a]\<^sub>t ts'"
and " mem_tml_prop    c  n  (ts) "
shows  " mem_tml_prop    c  n  (ts')"

 using assms
  apply (simp add:  mem_tml_prop_def step_def total_wfs_def)
  apply (subgoal_tac " memory (ts) = memory (ts' ) ")
   prefer 2
  using flo_mem apply presburger
  apply (subgoal_tac " \<forall> z. survived_val ts z = survived_val ts' z")
   prefer 2
  using assms(3) survived_val_preserved_flushopt apply presburger
  by (smt (verit, ccfv_SIG))





lemma flo_mem_inv3:
  assumes "thrdsvars"
  and "total_wfs (ts)"
  and  "ts [flush\<^sub>o a]\<^sub>t ts'"
and " mem_tml_prop3   ts "
shows  " mem_tml_prop3   ts'"
 using assms
  apply (simp add:   step_def total_wfs_def)
  apply (subgoal_tac " memory (ts) = memory (ts' ) ")
  prefer 2
  using flo_mem apply blast
  apply (unfold mem_tml_prop3_def)
  by (metis assms(3) flo_crash)



lemma flo_mem_inv4:
  assumes "thrdsvars"
  and "total_wfs (ts)"
  and  "ts [flush\<^sub>o a]\<^sub>t ts'"
and " mem_tml_prop4   ts "
shows  " mem_tml_prop4   ts'"
 using assms
  apply (simp add:   step_def total_wfs_def)
  apply (subgoal_tac " memory (ts) = memory (ts' ) ")
  prefer 2
  using flo_mem apply blast
  apply (unfold mem_tml_prop4_def)
  by (metis assms(3) flo_crash)









lemma ld_mem_inv:
  assumes "thrdsvars"
  and "total_wfs (ts)"
 and  "ts  [r \<leftarrow> x]\<^sub>t  ts'"
and " mem_tml_prop    c  n  (ts) "
shows  " mem_tml_prop    c  n  (ts')"
 using assms
  apply (simp add:  mem_tml_prop_def step_def total_wfs_def)
  apply (subgoal_tac " memory (ts) = memory (ts' ) ")
   prefer 2
  apply (metis mem_ld_trans)
 apply (subgoal_tac " \<forall> z. survived_val ts z = survived_val ts' z")
  prefer 2
  using assms(3) survived_val_preserved_load apply presburger
  by auto





lemma ld_mem_inv3:
  assumes "thrdsvars"
  and "total_wfs (ts)"
 and  "ts  [r \<leftarrow> x]\<^sub>t  ts'"
and " mem_tml_prop3   ts "
shows  " mem_tml_prop3   ts'"
 using assms
  apply (simp add:   step_def total_wfs_def)
  apply (subgoal_tac " memory (ts) = memory (ts' ) ")
  prefer 2
  using mem_ld_trans apply blast
  apply (unfold mem_tml_prop3_def)
  by (metis assms(3) ld_crash)



lemma ld_mem_inv4:
  assumes "thrdsvars"
  and "total_wfs (ts)"
 and  "ts  [r \<leftarrow> x]\<^sub>t  ts'"
and " mem_tml_prop4   ts "
shows  " mem_tml_prop4   ts'"
 using assms
  apply (simp add:   step_def total_wfs_def)
  apply (subgoal_tac " memory (ts) = memory (ts' ) ")
  prefer 2
  using mem_ld_trans apply blast
  apply (unfold mem_tml_prop4_def)
  by (metis assms(3) ld_crash)









lemma loc_wr_same:
  assumes "thrdsvars"
  and "total_wfs (ts)"
 and  "step t ( Store x v) ts ts' "
shows  " (\<forall>i.( i>0\<and>i<length(memory ts)) \<longrightarrow> ( Msg.loc(memory ts' ! i) =  Msg.loc (memory ts ! i) ))"
  using assms
  by (metis bot_nat_0.extremum mem_l_step)





lemma loc_cas_succ_same_trans:
  assumes "thrdsvars"
  and "total_wfs (ts)"
 and  " ts' =   cas_succ_trans t ind c  v1 v2  c1 nv mnv
            ts" 
shows  " (\<forall>i.( i>0\<and>i<length(memory ts)) \<longrightarrow> ( Msg.loc(memory ts' ! i) =  Msg.loc (memory ts ! i) ))"
  using assms
  by (metis less_eq_nat.simps(1) mem_l_casucc)
 




lemma loc_cas_succ_same:
  assumes "thrdsvars"
  and "total_wfs (ts)"
 and  "step t ( CAS x  v1 v2 r) ts ts'" 
and "    regs ts' t r = 1 "
shows  " (\<forall>i.( i\<ge>0\<and>i<length(memory ts)) \<longrightarrow> ( Msg.loc(memory ts' ! i) =  Msg.loc (memory ts ! i) ))"
  using assms
  apply (simp add: step_def total_wfs_def)

  by (metis assms(4) bot_nat_0.extremum cas_fail_reg mem_l_casucc zero_neq_one)



lemma comploc_wr_same:
  assumes "thrdsvars"
  and "total_wfs (ts)"
 and  "step t ( Store x v) ts ts' "
shows  " (\<forall>i.(i\<ge>0\<and>i<length(memory ts)) \<longrightarrow> ( comploc(memory ts' ! i) c = comploc (memory ts ! i) c))"
  using assms
  using mem_l_step by presburger



lemma comploc_cas_succ_same_trans:
  assumes "thrdsvars"
  and "total_wfs (ts)"
 and  " ts' =   cas_succ_trans t ind c  v1 v2  c1 nv mnv
            ts" 
shows  " (\<forall>i  c.(i\<ge>0\<and>i<length(memory ts)) \<longrightarrow> ( comploc(memory ts' ! i) c = comploc (memory ts ! i) c))"
  using assms
  by (metis mem_l_casucc)




lemma comploc_cas_succ_same:
  assumes "thrdsvars"
  and "total_wfs (ts)"
  and  "step t ( CAS x  v1 v2 r) ts ts'" 
and "    regs ts' t r = 1 "
shows  " (\<forall>i  c.(i\<ge>0\<and>i<length(memory ts)) \<longrightarrow> ( comploc(memory ts' ! i) c = comploc (memory ts ! i) c))"
  using assms
  apply (simp add: step_def total_wfs_def)
  by (metis assms(4) bot_nat_0.extremum cas_fail_reg mem_l_casucc zero_neq_one)

lemma compval_wr_same:
  assumes "thrdsvars"
  and "total_wfs (ts)"
 and  "step t ( Store x v) ts ts' "
shows  " (\<forall>i c.(i\<ge>0\<and>i<length(memory ts)) \<longrightarrow> ( compval ts' (memory ts' ! i) c = compval ts (memory ts ! i) c))"
  using assms
  by (metis compval_def mem_l_step survived_val_preserved_store)



lemma compval_cas_succ_same_trans:
  assumes "thrdsvars"
  and "total_wfs (ts)"
 and  " ts' =   cas_succ_trans t ind c  v1 v2  c1 nv mnv
            ts" 
shows  " (\<forall>i c.(i\<ge>0\<and>i<length(memory ts)) \<longrightarrow> ( compval ts' (memory ts' ! i) c = compval ts (memory ts ! i) c))"
  using assms 
  apply (simp add:  cas_succ_trans_def)
  by (metis nth_append)



lemma compval_cas_succ_same:
  assumes "thrdsvars"
  and "total_wfs (ts)"
  and  "step t ( CAS x  v1 v2 r) ts ts'" 
and "    regs ts' t r = 1 "
shows  " (\<forall>i c.(i\<ge>0\<and>i<length(memory ts)) \<longrightarrow> ( compval ts' (memory ts' ! i) c = compval ts (memory ts ! i) c))"
  using assms 
  apply (simp add: step_def total_wfs_def)
  by (metis assms(3) cas_fail_reg le0 mem_l_casucc n_not_Suc_n survived_val_preserved_cas)


(* \<and> (\<forall>\<nu>. k < \<nu> \<and> \<nu> < j \<longrightarrow> Msg.loc ((memory ts)!\<nu>) \<noteq>  glb   ) *)

lemma wr_noteq_length_v2:
assumes "(\<forall> i . \<forall> j . i < j \<and> a \<noteq> c \<and>
          0 < i   \<and> j  <  length(memory ts) \<and>
          comploc ((memory ts)!i) c = c   \<and>  even ( compval ts ((memory ts)!i) c) \<and>  Msg.loc ((memory ts)!j) = a
 \<longrightarrow> ( \<exists>k. k > i \<and>  k < j  \<and>  Msg.loc((memory ts)!k)  = glb \<and> odd (  Msg.val((memory ts)!k)) \<and> (\<forall>\<nu>. k < \<nu> \<and> \<nu> < j \<longrightarrow> Msg.loc ((memory ts)!\<nu>) \<noteq>  glb   )  ) )"

 and "total_wfs (ts)"
 and "step t ( Store x v) ts ts'"
and "thrdsvars"

shows "(\<forall> i . \<forall> j . i < j \<and> a \<noteq> c  \<and>   i \<noteq> length(memory ts) 
         \<and> j \<noteq> length(memory ts) \<and>
          0 < i   \<and> j  <  length(memory ts') \<and>
          comploc ((memory ts')!i) c = c   \<and>  even ( compval ts' ((memory ts')!i) c) \<and>  Msg.loc ((memory ts')!j) = a
 \<longrightarrow> ( \<exists>k. k > i \<and>  k < j  \<and>  Msg.loc((memory ts')!k)  = glb \<and> odd (  Msg.val((memory ts')!k)) \<and> (\<forall>\<nu>. k < \<nu> \<and> \<nu> < j \<longrightarrow> Msg.loc ((memory ts')!\<nu>) \<noteq>  glb   ) ) )"

  using assms
  apply (subgoal_tac "(\<forall> i . \<forall> j . i < j 
 \<and>  0 \<le> i   \<and> j  <  length(memory ts)  \<longrightarrow>   ( compval ts' (memory ts' ! i) c = compval ts (memory ts ! i) c) \<and>
                                              ( comploc(memory ts' ! i) c = comploc (memory ts ! i) c) \<and>
                                               ( Msg.loc(memory ts' ! i) =  Msg.loc (memory ts ! i) )    )   ")
   prefer 2

   apply (smt (z3) compval_wr_same mem_l_step order_less_trans)

  apply (subgoal_tac "(\<forall> i . \<forall> j . i < j \<and> a \<noteq> c  \<and>
          0 < i   \<and> j  <  length(memory ts) \<and>
          comploc ((memory ts')!i) c = c   \<and>  even ( compval ts' ((memory ts')!i) c) \<and>  Msg.loc ((memory ts')!j) = a
 \<longrightarrow> ( \<exists>k. k > i \<and>  k < j  \<and>  Msg.loc((memory ts')!k)  = glb \<and> odd (  Msg.val((memory ts')!k))\<and> (\<forall>\<nu>. k < \<nu> \<and> \<nu> < j \<longrightarrow> Msg.loc ((memory ts')!\<nu>) \<noteq>  glb   )  ) )")
   prefer 2

   apply (smt (verit, del_insts) le_neq_implies_less less_or_eq_imp_le mem_l_step order_less_trans)

  apply (subgoal_tac " \<forall> i. (i\<ge>0\<and>i<length(memory ts')) \<and> i \<noteq> length(memory ts) \<longrightarrow>
i < length(memory ts) ")
   prefer 2
   apply (simp add: step_def)
   apply (simp add: store_trans_def)
   apply (meson not_less_less_Suc_eq)
  using bot_nat_0.extremum by presburger




lemma wr_noteq_length:
assumes "(\<forall> i . \<forall> j . i < j \<and> a \<noteq> c \<and>
          0 < i   \<and> j  <  length(memory ts) \<and>
          comploc ((memory ts)!i) c = c   \<and>  even ( compval ts ((memory ts)!i) c) \<and>  Msg.loc ((memory ts)!j) = a
 \<longrightarrow> ( \<exists>k. k > i \<and>  k < j  \<and>  Msg.loc((memory ts)!k)  = glb \<and> odd (  Msg.val((memory ts)!k))) )"

 and "total_wfs (ts)"
 and "step t ( Store x v) ts ts'"
and "thrdsvars"

shows "(\<forall> i . \<forall> j . i < j \<and> a \<noteq> c  \<and>   i \<noteq> length(memory ts) 
         \<and> j \<noteq> length(memory ts) \<and>
          0 < i   \<and> j  <  length(memory ts') \<and>
          comploc ((memory ts')!i) c = c   \<and>  even ( compval ts' ((memory ts')!i) c) \<and>  Msg.loc ((memory ts')!j) = a
 \<longrightarrow> ( \<exists>k. k > i \<and>  k < j  \<and>  Msg.loc((memory ts')!k)  = glb \<and> odd (  Msg.val((memory ts')!k))) )"

  using assms
  apply (subgoal_tac "(\<forall> i . \<forall> j . i < j 
 \<and>  0 \<le> i   \<and> j  <  length(memory ts)  \<longrightarrow>   ( compval ts' (memory ts' ! i) c = compval ts (memory ts ! i) c) \<and>
                                              ( comploc(memory ts' ! i) c = comploc (memory ts ! i) c) \<and>
                                               ( Msg.loc(memory ts' ! i) =  Msg.loc (memory ts ! i) )    )   ")
   prefer 2
   apply (smt (z3) compval_wr_same mem_l_step order_less_trans)

  apply (subgoal_tac "(\<forall> i . \<forall> j . i < j \<and> a \<noteq> c  \<and>
          0 < i   \<and> j  <  length(memory ts) \<and>
          comploc ((memory ts')!i) c = c   \<and>  even ( compval ts' ((memory ts')!i) c) \<and>  Msg.loc ((memory ts')!j) = a
 \<longrightarrow> ( \<exists>k. k > i \<and>  k < j  \<and>  Msg.loc((memory ts')!k)  = glb \<and> odd (  Msg.val((memory ts')!k))) )")
   prefer 2

   apply (smt (verit, del_insts) le_neq_implies_less less_or_eq_imp_le mem_l_step order_less_trans)

  apply (subgoal_tac " \<forall> i. (i\<ge>0\<and>i<length(memory ts')) \<and> i \<noteq> length(memory ts) \<longrightarrow>
i < length(memory ts) ")
   prefer 2
   apply (simp add: step_def)
   apply (simp add: store_trans_def)
   apply (meson not_less_less_Suc_eq)
  using bot_nat_0.extremum by presburger



lemma commit_up_glb_mem_inv:
  assumes "thrdsvars"
  and "total_wfs (ts)"
 and  "ts [glb := Suc (lastVal glb (ts))]\<^sub>t ts' "
and " n \<noteq> glb"
and " even ( Suc (lastVal glb (ts))  )"
and " mem_tml_prop    glb n  (ts) "
shows  " mem_tml_prop    glb  n  (ts')"
  using assms  apply (unfold  mem_tml_prop_def  total_wfs_def)
  apply (subgoal_tac "  \<forall>i j. i < j \<and>
          n \<noteq> glb \<and>
          0 < i \<and>
          j < length (memory ts') \<and>
           i \<noteq> length(memory ts) 
         \<and> j \<noteq> length(memory ts) \<and>
          comploc (memory ts' ! i) glb = glb \<and>
          even (compval ts' (memory ts' ! i) glb) \<and> Msg.loc (memory ts' ! j) = n \<longrightarrow>
          (\<exists>k>i. k < j \<and>
                 Msg.loc (memory ts' ! k) = glb \<and> odd (Msg.val (memory ts' ! k)))")

   prefer 2
  using   wr_noteq_length [where a = n and c = glb] 
  using assms(2) apply presburger
  apply clarify
  apply (case_tac " i = length (memory ts) ")
  apply (metis Nat.add_0_right One_nat_def add_Suc_right not_less_eq st_mem_length)
  apply (case_tac " j = length (memory ts) ")
   apply (meson st_loc)
  by presburger




lemma recover_up_glb_mem_inv:
  assumes "thrdsvars"
  and "total_wfs (ts)"
 and  "ts [glb := v]\<^sub>t ts' "
and " mem_tml_prop    glb n  (ts) "
shows  " mem_tml_prop    glb  n  (ts')"
  using assms  apply (unfold  mem_tml_prop_def  total_wfs_def)
  apply (subgoal_tac "  \<forall>i j. i < j \<and>
          n \<noteq> glb \<and>
          0 < i \<and>
          j < length (memory ts') \<and>
           i \<noteq> length(memory ts) 
         \<and> j \<noteq> length(memory ts) \<and>
          comploc (memory ts' ! i) glb = glb \<and>
          even (compval ts' (memory ts' ! i) glb) \<and> Msg.loc (memory ts' ! j) = n \<longrightarrow>
          (\<exists>k>i. k < j \<and>
                 Msg.loc (memory ts' ! k) = glb \<and> odd (Msg.val (memory ts' ! k)))")

   prefer 2
  using   wr_noteq_length [where a = n and c = glb] 
   apply (case_tac  " n \<noteq> glb" )
    apply (metis assms(2))

  apply (smt (z3) assms(1) assms(2) assms(3))
  apply clarify
  apply (case_tac " i = length (memory ts) ")
  apply (metis Nat.add_0_right One_nat_def add_Suc_right not_less_eq st_mem_length)
  apply (case_tac " j = length (memory ts) ")
   apply (meson st_loc)
  by presburger







lemma commit_up_glb_mem_inv3:
  assumes "thrdsvars"
  and "total_wfs (ts)"
 and  "ts [glb := (Suc v)]\<^sub>t ts' "
and "\<lceil>glb: v\<rceil> ts "
and " mem_tml_prop3   ts "
and " glb_monotone_inv  ts "
shows  " mem_tml_prop3   ts'"
  using assms 
  apply (unfold total_wfs_def glb_monotone_inv_def )
 apply (subgoal_tac "  glb_monotone_inv  ts'")
   prefer 2
  using  st_glb_monotone_preserved[where glb = glb and ts = ts ]
  apply (metis (no_types, opaque_lifting) glb_monotone_inv_def)
  apply (simp add: step_def)

  apply (subgoal_tac " \<forall> i. i < length (memory ts ) \<longrightarrow>(memory ts') ! i = (memory ts) ! i ")
   prefer 2
  using bot_nat_0.extremum mem_l apply presburger


  apply (subgoal_tac " (State.loc (memory( ts')!(length (memory ts))) ) = glb ")
   prefer 2
  using assms(3) st_loc apply presburger

  (*

 apply (subgoal_tac " \<forall> i.(0 <i \<and> i < length (memory ts) \<and> (State.loc (memory( ts')!i) ) = glb)  \<longrightarrow>(compval ts'  (memory( ts')!i) glb ) \<le> compval ts'  (memory( ts')!(length (memory ts)) ) glb ")
   prefer 2
   apply (smt (verit, best) Suc_lessD assms(3) glb_monotone_inv_def last_entry_bounded less_or_eq_imp_le less_trans_Suc mem_structured_preserved st_lastEntry_lc vbounded_preserved)
*)

 apply (subgoal_tac " \<forall> i.(0 <i \<and> i < (last_entry  ts  glb)  \<and> (State.loc (memory( ts)!i) ) = glb)  \<longrightarrow>(compval ts  (memory( ts)!i) glb ) \<le>  compval ts  (memory( ts)!(last_entry  ts  glb)  ) glb ")
   prefer 2

   apply (smt (z3) Suc_lessD assms(6) glb_monotone_inv_def i_noteqo_loc last_entry_bounded last_entry_loc less_or_eq_imp_le less_trans_Suc)

 apply (subgoal_tac " \<forall> i.(0 <i \<and> i < length (memory ts) \<and> (State.loc (memory( ts')!i) ) = glb)  \<longrightarrow>(compval ts'  (memory( ts')!i) glb ) < compval ts'  (memory( ts')!(length (memory ts)) ) glb ")
   prefer 2

 apply (subgoal_tac " \<forall> i.(0 <i \<and> i < length (memory ts) \<and> (State.loc (memory( ts')!i) ) = glb)  \<longrightarrow>(compval ts'  (memory( ts')!i) glb ) \<le> compval ts'  (memory( ts')!((last_entry  ts  glb)) ) glb ")
    prefer 2
    apply (subgoal_tac  " \<forall> i.(0 <i \<and> i < length (memory ts) \<and> (State.loc (memory( ts')!i) ) = glb) \<longrightarrow> i \<le> (last_entry  ts  glb) ")
     prefer 2
     apply (unfold last_entry_def)
     apply (subgoal_tac "\<forall> i.(0 <i \<and> i < length (memory ts) \<and> (State.loc (memory( ts')!i) ) = glb) \<longrightarrow> i \<in> last_entry_set ts glb ")
      prefer 2
  apply (simp add: last_entry_set_def)
      apply (metis (no_types, lifting))
     apply (subgoal_tac " \<forall> i. i \<in> last_entry_set ts glb  \<longrightarrow> i  \<le> Max (last_entry_set ts glb) ")
      prefer 2
  using  finite_last_entry_set 
      apply (metis Max.coboundedI)
     apply metis
  apply (smt (z3) Suc_leI assms(1) assms(2) assms(3) assms(6) bot_nat_0.extremum compval_wr_same glb_monotone_inv_def i_noteqo_loc last_entry_bounded last_entry_def last_entry_loc le_trans less_eq_Suc_le less_or_eq_imp_le loc_wr_same)

  apply (subgoal_tac "compval ts'  (memory ts' ! Max (last_entry_set ts glb)) glb \<noteq> compval ts'  (memory ts'!(length(memory ts)))  glb ")
  prefer 2 
  apply (smt (z3) Store_Rules.st_lv_lc assms(3) compval_def last_entry_bounded last_entry_def n_not_Suc_n st_lastEntry_lc survived_val_preserved_store)

   apply (subgoal_tac " (length (memory ts' )) = length(memory ts) +1 ")
    prefer 2
  using assms(3) st_mem_length apply presburger

  apply (smt (z3) Store_Rules.st_lv_lc Suc_le_lessD add_le_cancel_left assms(3) compval_def last_entry_bounded last_entry_def plus_1_eq_Suc st_lastEntry_lc survived_val_preserved_store)

  apply (  simp del: comploc_def compval_def)
  apply (unfold mem_tml_prop3_def)
  apply clarify
  apply (case_tac " j = length(memory ts)  ")

   apply (metis nat_neq_iff nth_append_length store_add)
 
  apply (case_tac " i = length(memory ts)  ")
   apply (metis length_append_singleton less_trans_Suc nat_less_le store_add)

(*
apply (subgoal_tac " (length (memory ts' )) = length(memory ts) +1 ")
    prefer 2
   apply (metis assms(3) st_mem_length)

  by (smt (z3) Nat.add_0_right One_nat_def add_Suc_right less_Suc_eq less_trans_Suc nat_neq_iff store_add store_wfs val_eq_compval)

*)
  apply (case_tac " i \<noteq> length(memory ts) \<and> j \<noteq> length(memory ts) ")

 apply (subgoal_tac " (length (memory ts' )) = length(memory ts) +1 ")
    prefer 2
    apply (metis assms(3) st_mem_length)
  apply (smt (z3) Nat.add_0_right One_nat_def Suc_less_eq add_Suc_right less_Suc_eq less_trans_Suc not_less_less_Suc_eq store_add store_wfs val_eq_compval)
  by blast





lemma commit_up_glb_mem_inv4:
  assumes "thrdsvars"
  and "total_wfs (ts)"
 and  "ts [glb := (Suc v)]\<^sub>t ts' "
and "\<lceil>glb: v\<rceil> ts "
and " mem_tml_prop4   ts "
and " glb_monotone_complete_inv  ts "
shows  " mem_tml_prop4   ts'"
  using assms 

  apply (unfold total_wfs_def  glb_monotone_complete_inv_def )

 apply (subgoal_tac "  glb_monotone_complete_inv  ts'")
   prefer 2
  using  st_glb_monotone_complete_preserved[where glb = glb and ts = ts and ts' = ts' ]
  apply (metis (no_types, lifting) glb_monotone_complete_inv_def)



  apply (simp add: step_def)

  apply (subgoal_tac " \<forall> i. i < length (memory ts ) \<longrightarrow>(memory ts') ! i = (memory ts) ! i ")
   prefer 2
  using bot_nat_0.extremum mem_l apply presburger



  apply (subgoal_tac "  comploc ((memory ts')! (length (memory ts))) glb  = glb ")
   prefer 2

  using assms(3) comploc_def st_loc apply presburger

 apply (subgoal_tac " \<forall> i.(0 \<le> i \<and> i < (last_entry  ts  glb)  \<and> (   comploc ((memory ts')! (i  )) glb  = glb           ) ) \<longrightarrow>(compval ts  (memory( ts)!i) glb ) \<le>  compval ts  (memory( ts)!(last_entry  ts  glb)  ) glb ")
   prefer 2
  apply (smt (z3) Nat.lessE Suc_lessD assms(6) glb_monotone_complete_inv_def last_entry_bounded last_entry_loc less_or_eq_imp_le less_trans_Suc zero_less_Suc)


 apply (subgoal_tac " \<forall> i.(0 \<le>  i \<and> i < length (memory ts) \<and> (comploc ((memory ts')! (i  )) glb  = glb  ))  \<longrightarrow>(compval ts'  (memory( ts')!i) glb ) < compval ts'  (memory( ts')!(length (memory ts)) ) glb ")
   prefer 2

 apply (subgoal_tac " \<forall> i.(0 \<le>i \<and> i < length (memory ts) \<and> (    comploc ((memory ts')! i  ) glb)  = glb   )  \<longrightarrow>(compval ts'  (memory( ts')!i) glb ) \<le> compval ts'  (memory( ts')!((last_entry  ts  glb)) ) glb ")
    prefer 2
    apply (subgoal_tac  " \<forall> i.(0 \<le>  i \<and> i < length (memory ts) \<and> ( comploc ((memory ts')! i  ) glb)  = glb ) \<longrightarrow> i \<le> (last_entry  ts  glb) ")
     prefer 2
     apply (unfold last_entry_def)
     apply (subgoal_tac "\<forall> i.(0  \<le>  i \<and> i < length (memory ts) \<and>   (comploc ((memory ts')! i  ) glb)  = glb     ) \<longrightarrow> i \<in> last_entry_set ts glb ")
      prefer 2
  apply (simp add: last_entry_set_def)
      apply (metis (no_types, lifting))
     apply (subgoal_tac " \<forall> i. i \<in> last_entry_set ts glb  \<longrightarrow> i  \<le> Max (last_entry_set ts glb) ")
      prefer 2
  using  finite_last_entry_set 
      apply (metis Max.coboundedI)
     apply metis

  apply (metis assms(1) assms(2) assms(3) compval_wr_same last_entry_bounded last_entry_def le0 le_eq_less_or_eq)
  apply (subgoal_tac "compval ts'  (memory ts' ! Max (last_entry_set ts glb)) glb \<noteq> compval ts'  (memory ts'!(length(memory ts)))  glb ")
  prefer 2 
  apply (smt (z3) Store_Rules.st_lv_lc assms(3) compval_def last_entry_bounded last_entry_def n_not_Suc_n st_lastEntry_lc survived_val_preserved_store)

   apply (subgoal_tac " (length (memory ts' )) = length(memory ts) +1 ")
    prefer 2
  using assms(3) st_mem_length apply presburger

  apply (smt (z3) Store_Rules.st_lv_lc Suc_le_lessD add_le_cancel_left assms(3) compval_def last_entry_bounded last_entry_def plus_1_eq_Suc st_lastEntry_lc survived_val_preserved_store)

  apply (  simp del: comploc_def compval_def)
  apply (unfold mem_tml_prop4_def)
  apply clarify
  apply (case_tac " j = length(memory ts)  ")

   apply (metis nat_neq_iff nth_append_length store_add)
 
  apply (case_tac " i = length(memory ts)  ")
   apply (metis length_append_singleton less_trans_Suc nat_less_le store_add)
  apply (case_tac " i \<noteq> length(memory ts) \<and> j \<noteq> length(memory ts) ")

 apply (subgoal_tac " (length (memory ts' )) = length(memory ts) +1 ")
    prefer 2
    apply (metis assms(3) st_mem_length)

  apply (smt (z3) add.right_neutral add_Suc_right add_less_cancel_left assms(1) assms(2) assms(3) bot_nat_0.extremum compval_wr_same less_trans_Suc nat_neq_iff plus_1_eq_Suc store_add)
  by force
(*CHECK IT *)





(*
lemma write_cas_fail_mem_inv:
  assumes "thrdsvars"
  and "total_wfs (ts)"
and " ts [CAS glb regs (\<tau> \<sigma>) t   DTML.loc Suc(regs (ts) t DTML.loc) c1]\<^sub>t ts'"
and " mem_tml_prop    glb a  (ts) "
and " regs ts' t c1 = 0 "

shows  " mem_tml_prop   glb  a  (ts')"
  using assms
  apply (unfold total_wfs_def)
  apply (subgoal_tac   " memory ts = memory ts' ")
  prefer 2
  using assms(5) cas_fail_mem_same apply blast
  apply (unfold  mem_tml_prop_def)
  apply (subgoal_tac "  survived_val ts' glb = survived_val ts glb")
  prefer 2
  using survived_val_preserved_cas apply presburger
  apply (subgoal_tac  " (\<forall>i c.( i>0\<and>i<length(memory ts')) \<longrightarrow>
       (   ( Msg.loc(memory ts' ! i) =  Msg.loc (memory ts ! i) ) \<and>
          ( compval ts' (memory ts' ! i) c = compval ts (memory ts ! i) c) ) \<and>
         ( comploc(memory ts' ! i) c = comploc (memory ts ! i) c))")
   prefer 2
   apply (metis compval_def survived_val_preserved_cas)
  by (metis compval_def)
*)

lemma write_cas_fail_mem_inv:
  assumes "thrdsvars"
  and "total_wfs (ts)"
and " ts [CAS glb v1  v2  c1]\<^sub>t ts'"
and " mem_tml_prop    glb a  (ts) "
and " regs ts' t c1 = 0 "

shows  " mem_tml_prop   glb  a  (ts')"
  using assms
  apply (unfold total_wfs_def)
  apply (subgoal_tac   " memory ts = memory ts' ")
  prefer 2
  using assms(5) cas_fail_mem_same apply blast
  apply (unfold  mem_tml_prop_def)
  apply (subgoal_tac "  survived_val ts' glb = survived_val ts glb")
  prefer 2
  using survived_val_preserved_cas apply presburger
  apply (subgoal_tac  " (\<forall>i c.( i>0\<and>i<length(memory ts')) \<longrightarrow>
       (   ( Msg.loc(memory ts' ! i) =  Msg.loc (memory ts ! i) ) \<and>
          ( compval ts' (memory ts' ! i) c = compval ts (memory ts ! i) c) ) \<and>
         ( comploc(memory ts' ! i) c = comploc (memory ts ! i) c))")
   prefer 2
   apply (metis compval_def survived_val_preserved_cas)
  by (metis compval_def)




lemma write_cas_fail_mem_inv_v3:
  assumes "thrdsvars"
  and "total_wfs (ts)"
and " ts [CAS glb regs (\<tau> \<sigma>) t   DTML.loc Suc(regs (ts) t DTML.loc) c1]\<^sub>t ts'"
and " mem_tml_prop3    (ts) "
and " regs ts' t c1 = 0 "

shows  " mem_tml_prop3    (ts')"
  using assms
  apply (unfold total_wfs_def)
  apply (subgoal_tac   " memory ts = memory ts' ")
  prefer 2
  using assms(5) cas_fail_mem_same apply blast
  apply (unfold  mem_tml_prop3_def)
  apply (subgoal_tac "  survived_val ts' glb = survived_val ts glb")
  prefer 2
  using survived_val_preserved_cas apply presburger
  apply (subgoal_tac  " (\<forall>i c.( i>0\<and>i<length(memory ts')) \<longrightarrow>
       (   ( Msg.loc(memory ts' ! i) =  Msg.loc (memory ts ! i) ) \<and>
          ( compval ts' (memory ts' ! i) c = compval ts (memory ts ! i) c) ) \<and>
         ( comploc(memory ts' ! i) c = comploc (memory ts ! i) c))")
   prefer 2
   apply (metis compval_def survived_val_preserved_cas)
  by (smt (verit, best) Suc_lessD less_trans_Suc)




lemma write_cas_fail_mem_inv_v4:
  assumes "thrdsvars"
  and "total_wfs (ts)"
and " ts [CAS glb regs (\<tau> \<sigma>) t   DTML.loc Suc(regs (ts) t DTML.loc) c1]\<^sub>t ts'"
and " mem_tml_prop4    (ts) "
and " regs ts' t c1 = 0 "

shows  " mem_tml_prop4    (ts')"
  using assms
  apply (unfold total_wfs_def)
  apply (subgoal_tac   " memory ts = memory ts' ")
  prefer 2
  using assms(5) cas_fail_mem_same apply blast
  apply (unfold  mem_tml_prop4_def)
  apply (subgoal_tac "  survived_val ts' glb = survived_val ts glb")
  prefer 2
  using survived_val_preserved_cas apply presburger
  by (metis compval_def)








lemma cas_noteq_length:
assumes "(\<forall> i . \<forall> j . i < j \<and> a \<noteq> c \<and>
          0 < i   \<and> j  <  length(memory ts) \<and>
          comploc ((memory ts)!i) c = c   \<and>  even ( compval ts ((memory ts)!i) c) \<and>  Msg.loc ((memory ts)!j) = a
 \<longrightarrow> ( \<exists>k. k > i \<and>  k < j  \<and>  Msg.loc((memory ts)!k)  = c \<and> odd (  Msg.val((memory ts)!k))) )"

 and "total_wfs (ts)"
 and " ts' =   cas_succ_trans t ind c  v1 v2  c1 nv mnv
            ts"
and "thrdsvars"

shows "(\<forall> i . \<forall> j . i < j \<and> a \<noteq> c  \<and>   i \<noteq> length(memory ts) 
         \<and> j \<noteq> length(memory ts) \<and>
          0 < i   \<and> j  <  length(memory ts') \<and>
          comploc ((memory ts')!i) c = c   \<and>  even ( compval ts' ((memory ts')!i) c) \<and>  Msg.loc ((memory ts')!j) = a
 \<longrightarrow> ( \<exists>k. k > i \<and>  k < j  \<and>  Msg.loc((memory ts')!k)  = c  \<and> odd (  Msg.val((memory ts')!k))) )"
  using assms
  apply ( unfold total_wfs_def)
 apply (subgoal_tac "(\<forall> i  . 0 \<le> i   \<and> i  <  length(memory ts)  \<longrightarrow>   ( compval ts' (memory ts' ! i) c = compval ts (memory ts ! i) c) \<and>
                                              ( comploc(memory ts' ! i) c = comploc (memory ts ! i) c)   )   ")
   prefer 2
   apply (metis assms(2) compval_cas_succ_same_trans mem_l_casucc)
  apply (subgoal_tac " (\<forall> i  . 0 < i   \<and> i  <  length(memory ts)  \<longrightarrow>   
                                               ( Msg.loc(memory ts' ! i) =  Msg.loc (memory ts ! i) )  ) ")
   prefer 2
  using bot_nat_0.extremum mem_l_casucc apply presburger
 apply (subgoal_tac "(\<forall> i . \<forall> j . i < j \<and> a \<noteq> c \<and>
          0 < i   \<and> j  <  length(memory ts) \<and>
          comploc ((memory ts')!i) c = c   \<and>  even ( compval ts' ((memory ts')!i) c) \<and>  Msg.loc ((memory ts')!j) = a
 \<longrightarrow> ( \<exists>k. k > i \<and>  k < j  \<and>  Msg.loc((memory ts')!k)  = c \<and> odd (  Msg.val((memory ts')!k))) )")
   prefer 2
                    
  apply (subgoal_tac   "(\<forall>i.(i\<ge>0\<and>i<length(memory ts)) \<longrightarrow> ( memory ts)!i =( memory ts')!i) ")
    prefer 2
  using mem_l_casucc apply presburger
  apply (smt (verit, best) Suc_lessD bot_nat_0.extremum less_trans_Suc)
   apply (subgoal_tac " \<forall> i. (i\<ge>0\<and>i<length(memory ts')) \<and> i \<noteq> length(memory ts) \<longrightarrow>
i < length(memory ts) ")
   prefer 2
   apply (simp add:  cas_succ_trans_def)
   apply (metis less_SucE)
  using bot_nat_0.extremum by presburger



lemma cas_succ_mem_inv:
  assumes "thrdsvars"
  and "total_wfs (ts)"
and " ts [CAS glb v1 v2  c1]\<^sub>t ts'"
and " mem_tml_prop    glb a  (ts) "
and " regs ts' t c1 \<noteq> 0 "
(*and "glb \<noteq> a"*)
shows  " mem_tml_prop   glb  a  (ts')"
  using assms
  apply (simp add : step_def total_wfs_def)
  apply clarify
  apply (subgoal_tac "   ts' =
           cas_succ_trans t ind glb
            v1
           v2  c1 nv mnv
            ts")
   prefer 2

  apply (metis assms(5) cas_fail_reg)

  apply (subgoal_tac "  \<forall>i j. i < j \<and>
          a \<noteq> glb \<and>
          0 < i \<and>
          j < length (memory ts') \<and>
           i \<noteq> length(memory ts) 
         \<and> j \<noteq> length(memory ts) \<and>
          comploc (memory ts' ! i) glb = glb \<and>
          even (compval ts' (memory ts' ! i) glb) \<and> Msg.loc (memory ts' ! j) = a \<longrightarrow>
          (\<exists>k>i. k < j \<and>
                 Msg.loc (memory ts' ! k) = glb \<and> odd (Msg.val (memory ts' ! k)))")
   prefer 2
apply (unfold  mem_tml_prop_def  )
   using  cas_noteq_length [where a = a and c = glb] 
   using assms(1) assms(2) apply presburger 
  apply clarify
   apply (case_tac " i = length (memory ts) ")

   apply (metis assms(3) assms(5) aux cas_fail_diff_lv cas_fail_reg diff_is_0_eq diff_less_mono gr0_conv_Suc lastVal_def last_entry_notoverwritten last_entry_succ_daddr_preserved lessI less_Suc_eq_le less_natE less_nat_zero_code less_or_eq_imp_le mem_structured_preserved not_add_less1 not_less_eq not_less_eq_eq notoverwritten_def numeral_1_eq_Suc_0 numerals(1) old.nat.inject pinf(6) plus_1_eq_Suc valOf_def vbounded_preserved zero_less_Suc)
   apply (case_tac " j = length (memory ts) ")
   apply (metis cas_suc_loc)

   by presburger




lemma write_cas_succ_mem_inv_v3:
  assumes "thrdsvars"
  and "total_wfs (ts)"
and " ts [CAS glb regs ts t   DTML.loc Suc(regs (ts) t DTML.loc) c1]\<^sub>t ts'"
and " mem_tml_prop3 (ts) "
and " regs ts' t c1 \<noteq> 0 "
and " glb_monotone_inv  ts "
shows  " mem_tml_prop3 (ts')"
  using assms
  apply (simp add: step_def)
  apply clarify
  apply (subgoal_tac " ts' =
           cas_succ_trans t ind glb
            (regs (ts) t DTML.loc)
            (Suc (regs ts t DTML.loc)) c1 nv mnv ts")
   prefer 2
   apply (metis assms(2) assms(5) cas_fail_reg total_wfs_def)

  apply (unfold total_wfs_def  glb_monotone_inv_def )

  apply (subgoal_tac "  \<lceil>glb :   (regs (ts) t DTML.loc) \<rceil> ts  ")
    prefer 2
  apply (metis assms(3) assms(5) cas_nlv_lc)

  apply (subgoal_tac "  glb_monotone_inv  ts'  ")
  prefer 2
  apply (subgoal_tac   "ts'  =
       cas_succ_trans t  (last_entry ts glb)  glb (regs (ts) t DTML.loc)
        (Suc( regs (ts) t DTML.loc)) c1 nv mnv ts")
    prefer 2
  apply (metis assms(5) cas_fail_reg)
  using glb_monotone_inv_def  cas_succ_glb_monotone_preserved [where ts = ts and glb = glb and ts' = ts'] 
   apply metis

 apply (subgoal_tac " \<forall> i. i < length (memory ts ) \<longrightarrow>(memory ts') ! i = (memory ts) ! i ")
   prefer 2
  using le0 mem_l_casucc apply presburger

 apply (subgoal_tac " (State.loc (memory( ts')!(length (memory ts))) ) = glb ")
   prefer 2
  using cas_suc_loc apply presburger

 apply (subgoal_tac " \<forall> i.(0 <i \<and> i < (last_entry  ts  glb)  \<and> (State.loc (memory( ts)!i) ) = glb)  \<longrightarrow>(compval ts  (memory( ts)!i) glb ) \<le>  compval ts  (memory( ts)!(last_entry  ts  glb)  ) glb ")
   prefer 2
   apply (smt (z3) Suc_lessD assms(6) glb_monotone_inv_def i_noteqo_loc last_entry_bounded last_entry_loc less_or_eq_imp_le less_trans_Suc)

 apply (subgoal_tac " \<forall> i.(0 <i \<and> i < length (memory ts) \<and> (State.loc (memory( ts')!i) ) = glb)  \<longrightarrow>(compval ts'  (memory( ts')!i) glb ) < compval ts'  (memory( ts')!(length (memory ts)) ) glb ")
   prefer 2

 apply (subgoal_tac " \<forall> i.(0 <i \<and> i < length (memory ts) \<and> (State.loc (memory( ts')!i) ) = glb)  \<longrightarrow>(compval ts'  (memory( ts')!i) glb ) \<le> compval ts'  (memory( ts')!((last_entry  ts  glb)) ) glb ")
    prefer 2
    apply (subgoal_tac  " \<forall> i.(0 <i \<and> i < length (memory ts) \<and> (State.loc (memory( ts')!i) ) = glb) \<longrightarrow> i \<le> (last_entry  ts  glb) ")
     prefer 2
     apply (unfold last_entry_def)
     apply (subgoal_tac "\<forall> i.(0 <i \<and> i < length (memory ts) \<and> (State.loc (memory( ts')!i) ) = glb) \<longrightarrow> i \<in> last_entry_set ts glb ")
      prefer 2
  apply (simp add: last_entry_set_def)
      apply (metis (no_types, lifting))
     apply (subgoal_tac " \<forall> i. i \<in> last_entry_set ts glb  \<longrightarrow> i  \<le> Max (last_entry_set ts glb) ")
      prefer 2
  using  finite_last_entry_set 
      apply (metis Max.coboundedI)
  apply metis
  apply (metis assms(1) assms(2) cas_succ_valOf_dt_ni compval_cas_succ_same_trans le_eq_less_or_eq valOf_def)
  apply (subgoal_tac "compval ts'  (memory ts' ! Max (last_entry_set ts glb)) glb \<noteq> compval ts'  (memory ts'!(length(memory ts)))  glb ")
  prefer 2 
  apply (metis assms(1) assms(2) aux cas_suc_compval compval_cas_succ_same_trans n_not_Suc_n)
  apply (metis assms(1) assms(2) aux cas_suc_compval compval_cas_succ_same_trans le_imp_less_Suc)
  apply (  simp del: comploc_def compval_def)
  apply (unfold mem_tml_prop3_def)
  apply clarify
  apply (case_tac " j = length(memory ts)  ")
  apply (metis cas_succ_add nat_less_le nth_append_length)
  apply (case_tac " i = length(memory ts)  ")
  apply (metis cas_succ_add length_append_singleton not_less_eq)
  apply (case_tac " i \<noteq> length(memory ts) \<and> j \<noteq> length(memory ts) ")

 apply (subgoal_tac " (length (memory ts' )) = length(memory ts) +1 ")
    prefer 2
    apply (metis Suc_eq_plus1 cas_succ_add length_append_singleton)
  apply (smt (z3) One_nat_def add.right_neutral add_Suc_right add_gr_0 add_less_cancel_left assms(1) assms(2) canonically_ordered_monoid_add_class.lessE compval_cas_succ_same_trans less_SucE less_imp_le_nat less_trans_Suc loc_cas_succ_same_trans plus_1_eq_Suc)
  by blast



lemma write_cas_succ_mem_inv_v4:
  assumes "thrdsvars"
  and "total_wfs (ts)"
and " ts [CAS glb regs ts t   DTML.loc Suc(regs (ts) t DTML.loc) c1]\<^sub>t ts'"
and " mem_tml_prop4 (ts) "
and " regs ts' t c1 \<noteq> 0 "
and " glb_monotone_complete_inv  ts "
shows  " mem_tml_prop4 (ts')"
  using assms
  apply (simp add: step_def)
  apply clarify
  apply (subgoal_tac " ts' =
           cas_succ_trans t ind glb
            (regs (ts) t DTML.loc)
            (Suc (regs ts t DTML.loc)) c1 nv mnv ts")
   prefer 2
   apply (metis assms(2) assms(5) cas_fail_reg total_wfs_def)

  apply (unfold total_wfs_def  glb_monotone_complete_inv_def )

  apply (subgoal_tac "  \<lceil>glb :   (regs (ts) t DTML.loc) \<rceil> ts  ")
    prefer 2
  apply (metis assms(3) assms(5) cas_nlv_lc)

  apply (subgoal_tac "   glb_monotone_complete_inv  ts'  ")
  prefer 2
  apply (subgoal_tac   "ts'  =
       cas_succ_trans t  (last_entry ts glb)  glb (regs (ts) t DTML.loc)
        (Suc( regs (ts) t DTML.loc)) c1 nv mnv ts")
    prefer 2
    apply (metis assms(5) cas_fail_reg)

  using  glb_monotone_complete_inv_def    cas_succ_glb_monotone_complete_preserved [where ts = ts and glb = glb and ts' = ts'] 
  apply (metis (no_types, lifting))


 apply (subgoal_tac " \<forall> i. i < length (memory ts ) \<longrightarrow>(memory ts') ! i = (memory ts) ! i ")
   prefer 2
  using le0 mem_l_casucc apply presburger

 apply (subgoal_tac " (State.loc (memory( ts')!(length (memory ts))) ) = glb ")
   prefer 2
  using cas_suc_loc apply presburger

 apply (subgoal_tac " \<forall> i.(0 \<le> i \<and> i < (last_entry  ts  glb)  \<and> ( comploc(memory ts ! i) glb  ) = glb)  \<longrightarrow>(compval ts  (memory( ts)!i) glb ) \<le>  compval ts  (memory( ts)!(last_entry  ts  glb)  ) glb ")
   prefer 2
  apply (smt (z3) Nat.lessE Suc_lessD last_entry_bounded last_entry_loc less_or_eq_imp_le less_trans_Suc zero_less_Suc)




 apply (subgoal_tac " \<forall> i.(0 \<le>  i \<and> i < length (memory ts) \<and> ( comploc(memory ts' ! i) glb  ) = glb )  \<longrightarrow>(compval ts'  (memory( ts')!i) glb ) < compval ts'  (memory( ts')!(length (memory ts)) ) glb ")
   prefer 2

 apply (subgoal_tac " \<forall> i.(0 \<le> i \<and> i < length (memory ts) \<and> ( comploc(memory ts' ! i) glb  ) = glb  )  \<longrightarrow>(compval ts'  (memory( ts')!i) glb ) \<le> compval ts'  (memory( ts')!((last_entry  ts  glb)) ) glb ")
    prefer 2
    apply (subgoal_tac  " \<forall> i.(0 \<le> i \<and> i < length (memory ts) \<and> ( comploc(memory ts' ! i) glb  ) = glb ) \<longrightarrow> i \<le> (last_entry  ts  glb) ")
     prefer 2
     apply (unfold last_entry_def)
     apply (subgoal_tac "\<forall> i.(0 \<le> i \<and> i < length (memory ts) \<and> (comploc(memory ts' ! i) glb  ) = glb    ) \<longrightarrow> i \<in> last_entry_set ts glb ")
      prefer 2
      apply (simp add: last_entry_set_def)

      apply (metis (no_types, lifting))
     apply (subgoal_tac " \<forall> i. i \<in> last_entry_set ts glb  \<longrightarrow> i  \<le> Max (last_entry_set ts glb) ")
      prefer 2
  using  finite_last_entry_set 
      apply (metis Max.coboundedI)
  apply metis
  apply (metis assms(1) assms(2) cas_succ_valOf_dt_ni compval_cas_succ_same_trans le_eq_less_or_eq valOf_def)
  apply (subgoal_tac "compval ts'  (memory ts' ! Max (last_entry_set ts glb)) glb \<noteq> compval ts'  (memory ts'!(length(memory ts)))  glb ")
  prefer 2 
  apply (metis assms(1) assms(2) aux cas_suc_compval compval_cas_succ_same_trans n_not_Suc_n)
  apply (metis assms(1) assms(2) aux cas_suc_compval compval_cas_succ_same_trans le_imp_less_Suc)
  apply (  simp del: comploc_def compval_def)
  apply (unfold mem_tml_prop4_def)
  apply clarify
  apply (case_tac " j = length(memory ts)  ")
  apply (metis cas_succ_add nat_less_le nth_append_length)
  apply (case_tac " i = length(memory ts)  ")
  apply (metis cas_succ_add length_append_singleton not_less_eq)
  apply (case_tac " i \<noteq> length(memory ts) \<and> j \<noteq> length(memory ts) ")
 apply (subgoal_tac " (length (memory ts' )) = length(memory ts) +1 ")
    prefer 2
    apply (metis Suc_eq_plus1 cas_succ_add length_append_singleton)
  apply (smt (z3) One_nat_def add.right_neutral add_Suc_right add_less_cancel_left assms(1) assms(2) bot_nat_0.extremum cas_succ_add compval_cas_succ_same_trans less_SucE less_trans_Suc plus_1_eq_Suc)
  by meson

















(*
  apply (subgoal_tac "compval ts'  (memory ts' ! Max (last_entry_set ts glb)) glb \<noteq> compval ts'  (memory ts'!(length(memory ts)))  glb ")
    prefer 2 

  apply (metis assms(1) assms(2) aux cas_suc_compval compval_cas_succ_same_trans n_not_Suc_n)
  apply (metis assms(1) assms(2) aux cas_suc_compval compval_cas_succ_same_trans le_imp_less_Suc)
  apply (  simp del: comploc_def compval_def)
  apply (unfold mem_tml_prop3_def)
  apply clarify
  apply (case_tac " j = length(memory ts)  ")
  apply (metis cas_succ_add nat_less_le nth_append_length)
  apply (case_tac " i = length(memory ts)  ")
  apply (metis cas_succ_add length_append_singleton not_less_eq)
  apply (case_tac " i \<noteq> length(memory ts) \<and> j \<noteq> length(memory ts) ")

 apply (subgoal_tac " (length (memory ts' )) = length(memory ts) +1 ")
    prefer 2
    apply (metis Suc_eq_plus1 cas_succ_add length_append_singleton)
  apply (smt (z3) One_nat_def add.right_neutral add_Suc_right add_gr_0 add_less_cancel_left assms(1) assms(2) canonically_ordered_monoid_add_class.lessE compval_cas_succ_same_trans less_SucE less_imp_le_nat less_trans_Suc loc_cas_succ_same_trans plus_1_eq_Suc)
  by blast

*)











lemma write_write_a_mem_inv:
 assumes "thrdsvars"
  and "total_wfs (ts)"
and " ts [a := v]\<^sub>t ts' "
and "glb \<noteq> a"
and " \<lceil>glb\<rceil>\<^sub>t ts'"
and "  odd( lastVal glb (ts'))"
and " mem_tml_prop    glb b  (ts) "
shows  " mem_tml_prop   glb  b  (ts')"
 using assms
  apply (simp add : step_def total_wfs_def )
 apply (subgoal_tac " \<forall> i.( 0 <  i \<and> i < length (memory ts') \<and>   Msg.loc (memory ts' ! i)    = glb) \<longrightarrow> i \<in> last_entry_set ts' glb   ")
   prefer 2
   apply (simp add: last_entry_set_def)
  apply (subgoal_tac " \<forall> i. i \<in> last_entry_set ts' glb  \<longrightarrow> i \<le>  last_entry ts' glb ")
  prefer 2
  using finite_last_entry_set 
   apply (metis Max.coboundedI last_entry_def)
 apply (subgoal_tac " \<forall> i.( 0 <  i \<and> i < length (memory ts') \<and>   comploc (memory ts' ! i) glb   = glb) \<longrightarrow> i \<le> last_entry ts' glb   ")
   prefer 2
   apply (simp add: last_entry_def)
  apply (metis length_append_singleton mem_structured_def store_add store_wfs)
  apply (subgoal_tac " \<forall> i. ( last_entry ts' glb  < i \<and> i \<le> length(memory ts)) \<longrightarrow>  Msg.loc (memory ts' ! i) \<noteq> glb ")
  prefer 2
  apply (simp add: last_entry_def)
   apply (metis last_entry_def le_imp_less_Suc length_append_singleton less_nat_zero_code nat_neq_iff not_less_eq store_add)
  apply (unfold mem_tml_prop_def)


 apply clarify
  apply (case_tac " i = length (memory ts) ")

  apply (metis assms(3) i_noteqo_loc last_entry_bounded st_lastEntry_lc st_loc store_wfs vbounded_preserved)

  apply (case_tac " j = length (memory ts) ")
   apply (subgoal_tac "    Msg.loc (memory ts' !  length(memory ts) ) = b ")
  prefer 2
    apply meson
 apply (rule_tac x=" last_entry ts' glb " in exI)
   apply (intro conjI)
      apply (subgoal_tac " i \<noteq> last_entry ts' glb ")
       prefer 2
       apply (metis lastVal_def)
  apply (metis Suc_lessD bot_nat_0.extremum le_neq_implies_less less_trans_Suc)
     apply (metis last_entry_bounded st_last_entry_daddr_preserved)
  apply(subgoal_tac " last_entry ts' glb \<noteq> 0 ")
     prefer 2
  apply (metis i_noteqo_loc less_imp_le_nat mem_l)
  apply (subgoal_tac "  comploc ( memory ts'!( last_entry ts' glb)) glb = glb")
     prefer 2
     apply (metis assms(3) last_entry_loc store_wfs vbounded_preserved)
    apply (simp add: comploc_def)
    apply (metis last_entry_bounded less_or_eq_imp_le mem_l mem_structured_def st_last_entry_daddr_preserved store_add)
  apply (subgoal_tac "  odd ( (compval ( (ts') )((memory ( ts'))!(last_entry ( ts') glb)) glb) )" )
  prefer 2
    apply (metis lastVal_def)
  apply (subgoal_tac " (last_entry ( ts') glb)  \<noteq> 0 ")
    prefer 2
  apply (metis i_noteqo_loc less_imp_le_nat mem_l)
   apply (simp(no_asm) add: mem_structured_def)
  apply (metis aux compval_def gr_implies_not_zero mem_structured_def nat_neq_iff singletonI store_add store_wfs)
  using   wr_noteq_length [where a = b and c = glb] 
  using assms(1) assms(2) assms(3) by blast


lemma write_write_a_mem_inv_v3:
  assumes "thrdsvars"
  and "total_wfs (ts)"
and " ts [a := v]\<^sub>t ts' "
and "glb \<noteq> a"
and " mem_tml_prop3 (ts) "
shows  " mem_tml_prop3 (ts')"
  using assms
  apply (unfold mem_tml_prop3_def  total_wfs_def)

  apply (subgoal_tac "  Msg.loc (memory ts'!(length(memory ts))) \<noteq> glb  ")
   prefer 2
  using st_loc apply presburger

  apply (subgoal_tac " length (memory ts') = length(memory ts) + 1 ")
  prefer 2
  using st_mem_length apply presburger

  apply (subgoal_tac " \<forall> i. i < length (memory ts ) \<longrightarrow>(memory ts') ! i = (memory ts) ! i ")
   prefer 2
  using less_eq_nat.simps(1) mem_l_step apply presburger
  by (smt (verit, best) Nat.add_0_right assms(2) assms(3) assms(4) compval_wr_same group_cancel.add2 le0 less_antisym less_or_eq_imp_le less_trans_Suc nat_add_left_cancel_less plus_1_eq_Suc st_loc)



lemma write_write_a_mem_inv_v4:
  assumes "thrdsvars"
  and "total_wfs (ts)"
and " ts [a := v]\<^sub>t ts' "
and "glb \<noteq> a"
and " mem_tml_prop4 (ts) "
shows  " mem_tml_prop4 (ts')"
  using assms
  apply (unfold mem_tml_prop4_def  total_wfs_def)
  apply (subgoal_tac "  comploc (memory ts' ! (length(memory ts))   ) glb    \<noteq> glb  ")
   prefer 2
  apply (metis Nat.lessE Zero_not_Suc bot_nat_0.not_eq_extremum i_noteqo_loc last_entry_bounded mem_structured_preserved st_lastEntry_lc st_loc vbounded_preserved)
  apply (subgoal_tac " length (memory ts') = length(memory ts) + 1 ")
  prefer 2
  using st_mem_length apply presburger

  apply (subgoal_tac " \<forall> i. i < length (memory ts ) \<longrightarrow>(memory ts') ! i = (memory ts) ! i ")
   prefer 2
  using less_eq_nat.simps(1) mem_l_step apply presburger
  by (smt (verit, best) Nat.add_0_right assms(2) assms(3) assms(4) compval_wr_same group_cancel.add2 le0 less_antisym less_or_eq_imp_le less_trans_Suc nat_add_left_cancel_less plus_1_eq_Suc st_loc)



end
