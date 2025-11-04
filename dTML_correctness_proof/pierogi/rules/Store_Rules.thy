theory Store_Rules
  imports "../State" "../Language"  "../Assertions"  "../Wellformedness"
begin

(* The lemmas that begin with the  comment "rule: __" are the proof rules regarding the store instruction.
   All the other lemmas are auxiliary and are used for proving the proof rules.
   Rules that end with "lc" concern mostly local correctness.
   Rules that end with "ni" concern  mostly  non-interference.
   Rules that end with "gen" concern non-interference and local correctness.
   Rules that end with "rel" concern relations between view sets. *) 


lemma st_mem_length:
 assumes  "step t ( Store  x v) ts ts'"
    shows " length(memory ts') = length(memory ts) + 1 "
  using assms
  by(simp add:  step_def )


lemma st_loc:
 assumes  "step t ( Store  x v) ts ts'"
 shows "loc ((memory (ts'))! (length(memory ts)) )   = x "
  using assms
  by (simp add: step_def)

lemma st_val:
 assumes  "step t ( Store  x v) ts ts'"
 shows "val ((memory (ts'))! (length(memory ts)) )   = v "
  using assms
  by (simp add: step_def)





lemma st_mem:
 assumes  "step t ( Store  x v) ts ts'"
 shows " memory ts'  = ((memory ts)@ [msg x v t]) "
using assms
  by (simp add: step_def store_trans_def)




lemma mem_l_step:
 assumes  "step t ( Store  x v) ts ts'"
    shows "(\<forall>i.(i\<ge>0\<and>i<length(memory ts)) \<longrightarrow> ( memory ts)!i =( memory ts')!i) "
  using assms
  apply (simp add:  step_def )
  by (simp add: nth_append)





lemma mem_last_l:
  assumes "memory ts' = memory (store_trans ts l v ti)" 
  shows "compval ts' ( memory ts' ! (length( memory ts') -1)) l = v"
  using assms
  apply (simp add:  store_trans_def )
  done

lemma mem_last_no:
  assumes  "mem_structured ts"
and  "memory ts' = memory (store_trans ts l v ti)" 
shows "\<forall>i.(  i < length(memory ts') \<and> i \<ge>0) \<longrightarrow> notoverwritten ts' i  ( (length( memory ts') -1)) l"
  using assms
  apply (simp add:  mem_structured_def  notoverwritten_def)
  done


lemma mem_last_coh:
assumes  "mem_structured ts"
and  " ts' = store_trans ts l v ti" 
shows " ( coh ts' ti l =  (length(memory ts') -1)  )"
  using assms
  apply (simp add:  store_trans_def  mem_structured_def  )
  done

lemma coh_less_than_lastentry:
  assumes  "mem_structured  ts"
and  " ts' = store_trans ts l v ti"
shows " \<forall>t. (( 0\<le> t \<and> t < length(memory ts')-1 \<and> 
         l = comploc  (memory ts'!t) l)  \<longrightarrow> coh ts' ti l > t)"
  using assms
  apply(simp add:  mem_structured_def  )
  using assms apply clarify
  apply (case_tac " t=0")
  using assms apply ( simp add:  mem_structured_def )
   apply (subgoal_tac"memory (store_trans ts l v ti) ! 0= Init_Msg " )
    prefer 2
  using assms 
    apply (metis le0 length_greater_0_conv mem_l)
   apply simp
  using assms  mem_last_coh 
   apply auto[1]
  using assms  mem_last_coh 
  by auto

lemma OTS_lastentry:
 assumes  "mem_structured ts"
and  " ts' = store_trans ts x v ti"
shows " OTS ts' ti x = { length(memory ts')-1} "
 using assms 
  apply(simp add:  mem_structured_def   OTS_def OTSF_def store_trans_def notoverwritten_def
  )
  using  mem_last_coh  coh_less_than_lastentry apply simp
  apply (case_tac " 0 \<notin> OTS ts' ti x" )
   prefer 2
  using  assms   apply (simp add: OTS_def OTSF_def notoverwritten_def )
  using assms   apply  (subgoal_tac" ( coh ts' ti x > 0 )" )
  prefer 2
  using assms 
   apply simp
  apply clarsimp
  using  mem_last_coh
  apply(auto simp add: split: Msg.split)
  done



(*rule: After executing a store, a thread can only observe the newly written value.*)
lemma st_ov_lc:
  assumes "mem_structured ts"
 and  "step t ( Store  x v) ts ts'"
shows "  [x]\<^sub>t ts' = {v}"
  using assms 
 apply (simp add: step_def)
  apply (subgoal_tac " OTS ts' t x = { length(memory ts')-1}")
   prefer 2
   apply (simp add: OTS_lastentry)
  apply (simp add: mapval_def)
  done



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


lemma coh_st_dt:
assumes "mem_structured ts"
and "vbounded ts"
and " ts' = store_trans ts x v t'"
and "t \<noteq> t'"
shows " coh ts t  x = coh ts' t x"
  using assms
  apply (simp add: store_trans_def)
  done 

lemma vrnew_st_dt:
assumes "mem_structured ts"
and "vbounded ts"
and " ts' = store_trans ts x v t'"
and "t \<noteq> t'"
shows " vrnew ts t   = vrnew ts' t "
  using assms
  apply (simp add: store_trans_def)
  done 

lemma mem_st_dt:
assumes "mem_structured ts"
and "vbounded ts"
and " ts' = store_trans ts x v t'"
shows " memory ts'   = memory ts  @ [msg x v t'] "
  using assms
  apply (simp add: store_trans_def)
  done

  
lemma st_ots_dt_lc:
  assumes "mem_structured ts"
and "vbounded ts"
 and  "step t' ( Store  x v) ts ts'"
and " t \<noteq> t'"
shows " OTS ts' t x  = OTS ts t x \<union>  { length(memory ts')-1} "
  using assms
  apply (simp add: step_def)
  apply (subgoal_tac "  coh ts t  x = coh ts' t x")
  prefer 2
  using coh_st_dt apply blast
  apply (subgoal_tac "  vrnew ts t  = vrnew  ts' t ")
   prefer 2
  using vrnew_st_dt apply blast
  apply (subgoal_tac "  memory ts'  =  memory ts  @ [msg x v t'] ")
   prefer 2
   apply auto[1] 
  apply (simp add: OTS_def)
  apply (simp add: OTSF_def)
  apply safe
                      apply (simp_all)
  using mem_l apply auto[1]
                    apply (simp add: mem_l)
                   apply (simp add: notoverwritten_def)
                   apply (metis antisym_conv3 le_less less_SucI less_nat_zero_code mem_l store_add)
                  apply (simp add: notoverwritten_def)
                  apply (metis antisym_conv3 le_less less_SucI less_nat_zero_code mem_l store_add)
                 apply (simp add: notoverwritten_def)
  using mem_l apply auto[1]
                apply (simp add: notoverwritten_def)
  using mem_l apply auto[1]
               apply (simp add: notoverwritten_def)
  apply (metis antisym_conv3 le_less less_SucI less_nat_zero_code mem_l store_add)
              apply (simp add: notoverwritten_def)
              apply (simp add: mem_l)
             apply (simp add: notoverwritten_def)
  apply (metis antisym_conv3 le_less less_SucI less_nat_zero_code mem_l store_add)
            apply (simp add: nat_less_le vbounded_def)
           apply (simp add: notoverwritten_def)
          apply (simp add: nth_append)
         apply (simp add: notoverwritten_def)
         apply (simp add: nth_append)
        prefer 3
        apply (simp add: nth_append)
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
  by (simp add: nth_append)


(*rule: After executing a store on address x, the set of observable values (OV) for address x (for all threads) is augmented with
the newly written value.*)
lemma  st_ov_dt_lc:
  assumes "mem_structured ts"
  and "vbounded ts"
  and "t \<noteq> t'"
  and  "step t' ( Store  x v) ts ts'"
shows "  [x]\<^sub>t ts'  =  [x]\<^sub>t ts  \<union> {v}"
  using assms
  apply (simp add: step_def)
   apply (subgoal_tac  " OTS ts' t x  = OTS ts t x \<union>  { length(memory ts')-1} ")
  prefer 2
  using assms(4) st_ots_dt_lc apply auto[1]
  apply (subgoal_tac " mapval ts x  (OTS ts t x) (memory ts @ [msg x v t']) = mapval ts x (OTS ts t x) (memory ts )")
 prefer 2
    apply (subgoal_tac "\<forall> i. i \<in> (OTS ts t x) \<longrightarrow> i < length (memory ts)")
    prefer 2
    apply (simp add: OTS_def)
   apply (unfold mapval_def )
  using mem_l apply auto[1]
   apply (subgoal_tac " survived_val ts x = survived_val ts' x")
   prefer 2
   apply (simp add: store_trans_def)
  by (simp add: compval_def)




lemma st_ots_ni:
  assumes "mem_structured ts"
  and "vbounded ts"
 and  "step t' ( Store  x v) ts ts'"
and "x \<noteq> y" 
shows "   (OTS ts' t y = OTS ts t y)"
 using assms 
  apply (simp add: step_def)
   apply (simp add: OTS_def)
   apply (simp add: OTSF_def)
   apply (subgoal_tac "  coh ts'  t' y =  coh ts  t' y")
    prefer 2
  apply (simp add: store_trans_def)
   apply (simp add: store_trans_def)
   apply (simp add:  notoverwritten_def)
   apply safe
                   apply (metis Msg.sel(1) less_antisym nth_append_length)
                     apply (metis dual_order.strict_trans nth_append)
                     apply (metis Msg.sel(1) less_antisym nth_append_length)
                     apply (metis Msg.sel(1) less_SucE nth_append nth_append_length)
  apply (metis antisym_conv3 le_less less_SucI less_nat_zero_code mem_l store_add)
                     apply (metis Msg.distinct(1) less_antisym nth_append_length)
                     apply (metis antisym_conv3 le_less less_SucI less_nat_zero_code mem_l store_add)
                     apply (metis Msg.distinct(1) less_antisym nth_append_length)
                     apply (metis Msg.distinct(1) less_SucE nth_append nth_append_length)
                     apply (metis dual_order.strict_trans nth_append)
                     apply (metis Msg.sel(1) less_antisym nth_append_length)
                     apply (metis antisym_conv3 le_less less_SucI less_nat_zero_code mem_l store_add)
                     apply (metis Msg.sel(1) less_antisym nth_append_length)
                     apply (metis Msg.sel(1) less_SucE nth_append nth_append_length)
                    apply (metis antisym_conv3 le_less less_SucI less_nat_zero_code mem_l store_add)
                   apply linarith
                  apply (metis nth_append)
  using less_Suc_eq apply blast
                 apply (metis nth_append)
  apply (metis less_SucE mem_l nat_less_le order.asym store_add vbounded_def zero_le)
               apply linarith
              apply (metis mem_l nat_less_le not_less_less_Suc_eq order.asym store_add vbounded_def zero_le)
             apply linarith
            apply (metis nth_append)
           apply (metis nth_append)
  using less_Suc_eq apply blast
  apply (metis mem_l nat_less_le not_less_less_Suc_eq order.asym store_add vbounded_def zero_le)
        apply linarith
       apply (metis nth_append)
                      apply (metis mem_l nat_less_le not_less_less_Suc_eq order.asym store_add vbounded_def zero_le)
                      apply (metis Msg.sel(1) less_antisym nth_append_length)
                      apply (metis dual_order.strict_trans nth_append)
                      apply (metis Msg.sel(1) less_antisym nth_append_length)
                      apply (metis Msg.sel(1) less_SucE nth_append nth_append_length)
                      apply (metis antisym_conv3 le_less less_SucI less_nat_zero_code mem_l store_add)
                      apply (metis Msg.distinct(1) less_antisym nth_append_length)
                      apply (metis antisym_conv3 le_less less_SucI less_nat_zero_code mem_l store_add)
                      apply (metis Msg.distinct(1) less_antisym nth_append_length)
                      apply (metis Msg.distinct(1) less_SucE nth_append nth_append_length)
                      apply (metis dual_order.strict_trans nth_append)
                      apply (metis Msg.sel(1) less_antisym nth_append_length)
                      apply (metis antisym_conv3 le_less less_SucI less_nat_zero_code mem_l store_add)
                     apply (metis Msg.sel(1) less_antisym nth_append_length)
                    apply (metis Msg.sel(1) less_SucE nth_append nth_append_length)
                   apply (metis antisym_conv3 le_less less_SucI less_nat_zero_code mem_l store_add)
                  apply linarith
                 apply (metis nth_append)
  using less_SucI apply blast
               apply (metis nth_append)
              apply (metis Msg.sel(1) less_SucE nth_append nth_append_length)
  using less_Suc_eq apply blast
            apply (metis mem_l nat_less_le not_less_less_Suc_eq order.asym store_add vbounded_def zero_le)
  using less_Suc_eq apply blast
          apply (metis nth_append)
         apply (metis nth_append)
        apply linarith
       apply (metis dual_order.strict_trans2 mem_l store_add vbounded_def zero_le)
      apply linarith
     apply (metis nth_append)
    apply (metis dual_order.strict_trans2 mem_l store_add vbounded_def zero_le)
  done

(*rule: After executing a store, the observable values (OV) of addresses  different from the newly written address
remain the same*)
lemma st_ov_ni:
  assumes "mem_structured ts"
  and "vbounded ts"
 and  "step t' ( Store  x v) ts ts'"
and "x \<noteq> y" 
shows "   [y]\<^sub>t ts=  [y]\<^sub>t ts'"
 using assms 
  apply (simp add: step_def)
  apply (subgoal_tac "  \<forall>i .  compval ts (( memory ts)!i) y  =  compval ts' (( memory ts)!i) y ")
  prefer 2
  using assms(3) survived_val_preserved_store apply auto[1]

  apply (subgoal_tac "OTS ts' t y = OTS ts t y")
  prefer 2
  using assms(3) st_ots_ni apply auto[1]
  apply (subgoal_tac " mapval ts' y (OTS ts t y) (memory ts @ [msg x v t']) = mapval ts  y (OTS ts t y) (memory ts )")
    prefer 2
    apply (subgoal_tac "\<forall> i. i \<in> (OTS ts t y) \<longrightarrow> i < length (memory ts)")
     prefer 2
  apply (simp add: OTS_def)
    apply (unfold mapval_def )
   apply (metis (no_types, lifting) butlast_snoc image_cong nth_butlast)
  by blast


lemma ld_cobts_lc_intro : 
  assumes "mem_structured ts"
  and "t \<noteq> t'"
  and "step t ( Store x v) ts ts'"
 and "vbounded ts"
  and " x \<noteq> y" 
 and " \<forall>k. ( k \<in> OTS ts t'  x  \<longrightarrow> compval ts  (memory ts! k) x \<noteq> v )"
 and  "  OTS ts t y =  S "
and " \<forall>ti l. comploc ( (memory ts)!(coh ts ti l)) l = l"

shows "   COBTS x y v t' ts' \<subseteq>  S "
  using assms
  apply (simp add: step_def )
  apply clarify
  apply (subgoal_tac "  { j   | j. j \<in> OTS ts' t'  x \<and> v = compval ts' ((memory ts')!j) x} =  { length(memory ts')-1}  ")
  prefer 2
   apply (subgoal_tac "  OTS ts' t' x  = OTS ts t' x \<union>  { length(memory ts')-1} ")
    prefer 2
  using assms(3) st_ots_dt_lc apply auto[1]
   apply (subgoal_tac "  compval ts' (memory ts' ! ( length(memory ts')-1) ) x = v ")
    prefer 2
  using mem_last_l apply blast
   apply safe 
    apply (simp )
    apply (subgoal_tac " j \<in> OTS ts t' x \<longrightarrow> compval ts (memory ts!j) x \<noteq> v  ")
     prefer 2
  using assms(6) apply blast
   apply (subgoal_tac " j \<in> OTS ts t' x \<longrightarrow> compval ts' (memory ts'!j) x \<noteq> v  ")
     prefer 2
     apply (subgoal_tac " \<forall> j.  j \<in> OTS ts t' x \<longrightarrow> j < length (memory ts)")
      prefer 2
      apply (simp add: OTS_def)
     apply (metis assms(3) bot_nat_0.extremum compval_def mem_l survived_val_preserved_store)
    apply force
   apply simp
   apply (subgoal_tac "  cond_ts ts'  t' x v = { compvrnew ts' t'  ( length(memory ts')-1)  x }")
   prefer 2
   apply (unfold cond_ts_def)

   apply (smt Collect_cong mem_Collect_eq singleton_conv2)
  apply (subgoal_tac "   COBTS x y v t' ts' = OTSF ts' t'  y ( compvrnew ts' t'  ( length(memory ts')-1)  x ) ")
   prefer 2
   apply (simp add: COBTS_def cond_ts_def)
  apply (subgoal_tac " \<forall> j. j \<in>   OTSF ts' t'  y ( compvrnew ts' t'  ( length(memory ts')-1)  x ) \<longrightarrow> j \<in>  OTS ts t y")
   prefer 2
   apply (subgoal_tac " OTS ts t y = OTS ts' t y ")
    prefer 2
  using  st_ots_ni 
  using assms(3) apply blast
  apply (subgoal_tac " \<forall> j. j \<in>   OTSF ts' t'  y ( compvrnew ts' t'  ( length(memory ts')-1)  x ) \<longrightarrow> j \<in>  OTS ts' t y")
  prefer 2
  apply (simp add: OTS_def )
   apply ( unfold OTSF_def )
   apply (case_tac "  coh ts'  t' y >  coh ts' t y")
    apply (subgoal_tac " compvrnew ts'  t' ( length(memory ts) ) x  \<ge> vrnew ts' t ")
     prefer 2
     apply (simp add: compvrnew_def)
     apply (subgoal_tac " length (memory ts)  \<noteq> coh ts t' x ")
      prefer 2
      apply (subgoal_tac "coh ts t' x < length (memory ts)")
       prefer 2
       apply (simp add: vbounded_def)
      apply linarith
     apply simp
     apply (subgoal_tac " vrnew (store_trans ts x v t) t = vrnew ts t")
      prefer 2
      apply (simp add: store_trans_def)
     apply simp
  apply (subgoal_tac "   vrnew ts t
          < (length (memory ts))")
      prefer 2
      apply (simp add: vbounded_def)
      apply linarith
     apply (smt le_eq_less_or_eq le_trans mem_Collect_eq test)
 (***************)
    apply (subgoal_tac "  \<forall> j. ( coh ts'  t'  y \<le> j \<and>  coh ts'  t y > j \<and>   comploc (memory ts' ! j) y =y)  \<longrightarrow>
  \<not> ( notoverwritten ts'(compvrnew ts' t'  (length (memory ts)) x) j y )  ") 
     prefer 2
     apply (simp add: notoverwritten_def compvrnew_def)
     apply safe 
        apply (simp_all)
      apply (rule_tac x=" coh ts'  t y" in exI)
  apply (rule conjI)
       apply (subgoal_tac " vbounded ts' ")
        prefer 2
  using assms(3) vbounded_preserved apply auto[1]
       apply (subgoal_tac " length (memory ts') =  Suc (length (memory ts))")
        prefer 2
        apply simp
       apply (simp add: vbounded_def)
      apply simp
      apply (rule conjI)
       apply (subgoal_tac "   coh ts'  t y =  coh ts  t y")
        prefer 2
        apply (simp add: store_trans_def)
       apply simp
       apply (subgoal_tac "  coh ts t y < length (memory ts)")
        prefer 2
        apply (simp add: vbounded_def)
       apply simp
   apply (subgoal_tac " \<forall>ti l. comploc ( (memory ts')!(coh ts' ti l)) l = l ")
       prefer 2
  using coh_loc_rel_preserved 
  using assms(3) assms(8) apply presburger
      apply simp
  apply (subgoal_tac " (memory ts @ [msg x v t]) ! coh (store_trans ts x v t) t y  \<noteq>
              Init_Msg")
  apply (simp add: mem_structured_def)
       apply meson
(************************************************)
      apply (subgoal_tac " mem_structured ts' ")
       prefer 2
  using store_wfs apply auto[1]
   apply ( simp add: mem_structured_def)
      apply (subgoal_tac "  (memory ts @ [msg x v t]) = memory ts'")
       prefer 2
  using store_add apply presburger
   apply (subgoal_tac " coh (store_trans ts x v t) t y  > 0")
       prefer 2
       apply linarith
      apply (subgoal_tac " coh (store_trans ts x v t) t y<  Suc (length (memory ts))")
       prefer 2
  apply (subgoal_tac " vbounded ts' ")
        prefer 2
  using assms(3) vbounded_preserved 
        apply presburger
       apply(unfold vbounded_def)
       apply (metis length_append_singleton)
      apply blast
(***************************second safe******************)
   apply (rule_tac x=" coh ts'  t y" in exI)
     apply (rule conjI)  (*5*)
   apply (subgoal_tac " vbounded ts' ")
        prefer 2
  using assms(3) vbounded_preserved 
  using assms(4) apply presburger
   apply (subgoal_tac " length (memory ts') =  Suc (length (memory ts))")
        prefer 2
        apply simp
       apply (simp add: vbounded_def)
     apply simp
     apply (rule conjI) (*5*)
       apply (subgoal_tac "    coh ts' t (loc ((memory ts @ [msg x v t]) ! j)) < length( memory ts')")
        prefer 2
       apply (simp add: store_trans_def)
       apply (simp add: less_SucI)
      apply (subgoal_tac "    coh ts' t (loc ((memory ts @ [msg x v t]) ! j)) \<le> length( memory ts)")
  prefer 2
       apply simp
  apply auto[1]
 apply (subgoal_tac " \<forall>ti l. comploc ( (memory ts')!(coh ts' ti l)) l = l ")
       prefer 2
  using coh_loc_rel_preserved 
  using assms(3) assms(8) 
      apply (meson assms(4))
  apply simp
  apply (subgoal_tac " mem_structured ts' ")
       prefer 2
  using store_wfs apply auto[1]
  apply (simp add: mem_structured_def)
 apply (subgoal_tac "  coh (store_trans ts x v t) t
             (loc ((memory ts @ [msg x v t]) ! j)) > 0")
      prefer 2
      apply linarith
  apply (subgoal_tac "  coh (store_trans ts x v t) t
             (loc ((memory ts @ [msg x v t]) ! j)) < Suc (length (memory ts))")
      prefer 2
 apply (subgoal_tac " vbounded ts' ")
        prefer 2
  using assms(3) vbounded_preserved 
  using assms(4) apply presburger
  apply (subgoal_tac " length (memory ts') =  Suc (length (memory ts))")
        prefer 2
       apply simp
      apply (simp add: vbounded_def)
  apply meson
  apply auto[1]
   apply auto[1]
  apply(rule conjI)
   apply (metis (no_types, lifting) less_or_eq_imp_le linorder_neqE_nat)
  apply (subgoal_tac " compvrnew ts'  t' ( length(memory ts) ) x  \<ge> vrnew ts' t ")
     prefer 2
     apply (simp add: compvrnew_def)
     apply (subgoal_tac " length (memory ts)  \<noteq> coh ts t' x ")
      prefer 2
      apply (subgoal_tac "coh ts t' x < length (memory ts)")
       prefer 2
       apply (simp add: vbounded_def)
      apply linarith
     apply simp
     apply (subgoal_tac " vrnew (store_trans ts x v t) t = vrnew ts t")
      prefer 2
      apply (simp add: store_trans_def)
     apply simp
  apply (subgoal_tac "   vrnew ts t
          < (length (memory ts))")
      prefer 2
      apply (simp add: vbounded_def)
   apply linarith
  by (metis (no_types, lifting) le_neq_implies_less test)

lemma opv_opts_rel:
assumes "  v \<notin> [x]\<^sub>t' ts "
shows " \<forall>k. ( k \<in> OTS ts t'  x  \<longrightarrow> compval ts (memory ts! k) x \<noteq> v )"
  using assms
  apply( simp add: mapval_def)
  using inf.strict_coboundedI2 by auto



(*rule: Introduction rule for conditional observation*)
lemma ld_cobv_lc_intro : 
  assumes "mem_structured ts"
  and "t \<noteq> t'"
  and "step t ( Store x v) ts ts'"
 and "vbounded ts"
  and " x \<noteq> y"
 and "  v \<notin> [x]\<^sub>t' ts "
 and  "  [y]\<^sub>t ts  =  S "
and " \<forall>ti l. comploc ( (memory ts)!(coh ts ti l)) l = l"
shows "  \<langle>x  v\<rangle>[y]\<^sub>t' ts'  \<subseteq>  S "
 using assms
  apply (simp add: step_def )
  apply (subgoal_tac "  \<forall>k. ( k \<in> OTS ts t'  x  \<longrightarrow> compval ts (memory ts! k) x \<noteq> v )")
   prefer 2
  using opv_opts_rel
   apply blast
 apply (subgoal_tac "  COBTS x y v t' ts' \<subseteq>   OTS ts t y ")
   prefer 2
  using assms(3) ld_cobts_lc_intro apply auto[1]
  apply (subgoal_tac " mapval ts y ( OTS ts t y)  (memory ts')  =mapval ts y ( OTS ts t y)  (memory ts)") 
  prefer 2
   apply (subgoal_tac "\<forall> i. i \<in> (OTS ts t y) \<longrightarrow> i < length (memory ts)")
  prefer 2
    apply (simp add: OTS_def)
   apply (unfold mapval_def)
  using mem_l apply auto[1]
  by (smt (verit, ccfv_SIG) assms(3) assms(7) image_subsetI opv_opts_rel st_mem st_ots_ni st_ov_ni subsetD)





lemma [simp]:
 assumes "mem_structured ts"
and "i = 0"
shows "(memory ts ) ! i =  Init_Msg"
  using assms
  apply (simp add: mem_structured_def vbounded_def )
  done 


lemma vp_commit_st:
assumes  "mem_structured ts"
and  " ts' = store_trans ts l v ti'" 
shows " ( vpcommit ts' ti' l =  vpcommit ts ti' l  )" 
 using assms
  apply (simp add:  store_trans_def  )
  done

lemma vp_commit_gen:
assumes  "mem_structured ts"                                  
and  " ts' = store_trans ts l v ti'" 
shows " ( \<forall> ti. ( vpcommit ts' ti l =  vpcommit ts ti l)  )"
 using assms
 apply (simp add: store_trans_def)
  done



lemma OATS_st:
  assumes "mem_structured ts"
and "vbounded ts"
and " i \<in> ( OATS ts ti l)"
and  " ts' = store_trans ts l v t" 
shows " i \<in>  (OATS ts' ti  l)"
 using assms
  apply (simp add: OATS_def )
 apply ( case_tac " i = 0")
   apply (subgoal_tac "(memory ts @ [msg l v t]) ! 0 = Init_Msg")
   prefer 2
   apply (metis mem_structured_def nth_append)
  apply (subgoal_tac " vpasync ts' ti l  = vpasync ts ti l")
   prefer 2
  apply (simp add: store_trans_def)
 apply(subgoal_tac "  vpasync ts ti l  <(length (memory ts)) ")
   prefer 2
   apply(simp add: vbounded_def)
  apply (smt (z3) less_or_eq_imp_le mem_l notoverwritten_def order.strict_trans1)
  apply (subgoal_tac " (memory ts @ [msg l v t]) ! i \<noteq> Init_Msg")
  prefer 2
  apply (metis bot_nat_0.not_eq_extremum less_or_eq_imp_le mem_l mem_structured_def store_add)
 apply (subgoal_tac " vpasync ts' ti l  = vpasync ts ti l")
   prefer 2
   apply (simp add: store_trans_def)
 apply(subgoal_tac "  vpasync ts ti l  <(length (memory ts)) ")
   prefer 2
  apply(simp add: vbounded_def)
  apply simp
  apply (simp add: notoverwritten_def)

  by (smt (z3) dual_order.strict_trans1 less_or_eq_imp_le mem_l not_less store_add)


lemma OPTS_st:
  assumes "mem_structured ts"
and "vbounded ts"
and " i \<in> ( OPTS ts l)"
and  " ts' = store_trans ts l v ti" 
shows " i \<in>  (OPTS ts' l)"
 using assms
  apply (simp add: OPTS_def   )
  apply ( case_tac " i = 0")
   apply (subgoal_tac "(memory ts @ [msg l v ti]) ! 0 = Init_Msg")
   prefer 2
   apply (unfold  mem_structured_def)
   apply simp
   apply (simp add: nth_append)
  apply simp
  apply (simp add: notoverwritten_def)
  apply (subgoal_tac"  maxvp (store_trans ts l v ti) l = maxvp ts l")
   prefer 2
   apply (simp add: store_trans_def)
   apply(subgoal_tac " maxvp ts l < Suc (length (memory ts)) ")
   prefer 2
   apply(simp add: vbounded_def)
  apply (simp add: less_Suc_eq)
   apply(subgoal_tac " maxvp ts l <(length (memory ts)) ")
   prefer 2
   apply(simp add: vbounded_def)
  apply (simp add: nth_append)
   apply (subgoal_tac " (memory ts @ [msg l v ti]) ! i \<noteq> Init_Msg")
  prefer 2
  using mem_l apply auto[1]
   apply simp
   apply (simp add: nth_append)
  apply (simp add: notoverwritten_def)
  apply (subgoal_tac"  maxvp (store_trans ts l v ti) l = maxvp ts l")
   prefer 2
   apply (simp add: store_trans_def)
   apply(subgoal_tac " maxvp ts l < Suc (length (memory ts)) ")
   prefer 2
   apply(simp add: vbounded_def)
  apply (simp add: less_Suc_eq)
   apply(subgoal_tac " maxvp ts l <(length (memory ts)) ")
   prefer 2
   apply(simp add: vbounded_def)
  by (metis le_less_trans nth_append)


lemma [simp]: "mem_structured ts \<Longrightarrow> \<forall>i. 0 < i \<and> i < length(memory ts)  \<longrightarrow>memory ts ! i \<noteq> Init_Msg"
  apply (unfold mem_structured_def)
  by simp

lemma [simp]:  "mem_structured ts \<Longrightarrow> memory ts ! 0 = Init_Msg"
  using mem_structured_def by auto


lemma st_oats_gen:
  assumes "mem_structured ts"
  and "vbounded ts"
  and  "step t ( Store  x v) ts ts'"
shows "  OATS ts' ti x  =  OATS ts ti x \<union> {length (memory ts)}"
  using assms
  apply (simp add: step_def)
  apply (subgoal_tac " \<forall>i. i \<in> OATS ts ti x \<longrightarrow> i \<in> OATS  ts' ti x")
   prefer 2
  using assms OATS_st apply blast
apply (subgoal_tac "length (memory ts) \<in> OATS ts' ti x ")
   prefer 2
  using assms  apply (simp add:  OATS_def )
   apply (unfold notoverwritten_def)
   apply (subgoal_tac "vpasync ts' ti x = vpasync ts ti x")
    prefer 2
    apply (simp add: store_trans_def)
   apply simp
 apply (subgoal_tac" \<nexists>i. i \<in> OATS ts' ti  x \<and> (i \<notin> (OATS ts ti x \<union> {length (memory ts)})) ")
   prefer 2
   apply (simp  add: OATS_def ) 
   apply clarify
   apply (case_tac " i = 0")
  apply (subgoal_tac " length (memory (store_trans ts x v t)) = length(memory ts) +1 ")
     prefer 2
     apply (simp add: store_trans_def)
  apply (subgoal_tac "  memory ts \<noteq> []")
     prefer 2
  using mem_structured_def apply blast
   apply (subgoal_tac "vpasync (store_trans ts x v t) ti x = vpasync ts ti x")
   prefer 2
     apply (simp add: store_trans_def)
 apply simp
    apply (subgoal_tac " (memory ts @ [msg x v t]) ! 0 = Init_Msg ")
     prefer 2
     apply (subgoal_tac " \<forall> i < length(memory ts) . (memory ts @ [msg x v t]) ! i = (memory ts ) ! i")
      prefer 2
      apply (simp add: nth_append)
    apply (subgoal_tac " memory ts ! 0 = Init_Msg")
     prefer 2
  using mem_structured_def apply blast
 apply (subgoal_tac " 0 < length(memory ts)")
      prefer 2
      apply blast
     apply presburger
  apply simp
    apply (simp (no_asm) add:notoverwritten_def)
    apply (metis le0 less_Suc_eq mem_l store_add)
  apply simp
   apply (subgoal_tac " 0 < i \<and> i < length(memory ts)  \<longrightarrow>memory ts ! i \<noteq> Init_Msg")
  prefer 2
    apply simp
 apply (subgoal_tac" vpasync (store_trans ts x v t) ti x = vpasync ts ti x")
   prefer 2
     apply (simp add: store_trans_def)
   apply simp
   apply(intro conjI)
    apply (meson leI le_less_Suc_eq mem_structured_def)
 apply (subgoal_tac " \<forall> i < length(memory ts) . (memory ts @ [msg x v t]) ! i = (memory ts ) ! i")
      prefer 2
    apply (simp add: nth_append)
   apply simp
 apply(safe)
         apply (metis less_antisym)
        apply linarith
       apply (metis less_antisym)
      apply (metis less_SucE)
  using less_antisym apply blast
    apply (simp(no_asm) add: notoverwritten_def)
    apply safe
  apply (metis length_append_singleton less_Suc_eq_le nat_less_le notoverwritten_def store_add)
   apply auto[1]
  by blast


lemma st_opts_gen:
  assumes "mem_structured ts"
  and "vbounded ts"
  and  "step ti ( Store  x v) ts ts'"
shows "  OPTS ts' x  =  OPTS ts x \<union> {length (memory ts)}"
using assms 
  apply (simp add: step_def)
  apply (subgoal_tac "\<forall> i. i \<in> OPTS ts x \<longrightarrow>  i \<in> OPTS  ts' x")
  prefer 2
  using assms OPTS_st 
  apply blast
  apply (subgoal_tac "length (memory ts) \<in> OPTS ts' x ")
   prefer 2
  using assms  apply (simp add:  OPTS_def )
   apply (unfold notoverwritten_def)
  using  vp_commit_gen 
  using less_le_trans order.asym apply fastforce
  apply (subgoal_tac" \<nexists>i. i \<in> OPTS ts' x \<and> (i \<notin> (OPTS ts x \<union> {length (memory ts)})) ")
   prefer 2
   apply (simp  add: OPTS_def ) 
   apply clarify
   apply (case_tac " i = 0")
    apply (subgoal_tac " length (memory (store_trans ts x v ti)) = length(memory ts) +1 ")
     prefer 2
     apply (simp add: store_trans_def)
    apply (subgoal_tac "  memory ts \<noteq> []")
     prefer 2
  using mem_structured_def apply blast
    apply simp
  apply (subgoal_tac"  maxvp (store_trans ts x v ti) x = maxvp ts x")
   prefer 2
     apply (simp add: store_trans_def)
    apply simp
    apply (subgoal_tac " (memory ts @ [msg x v ti]) ! 0 = Init_Msg ")
     prefer 2
     apply (subgoal_tac " \<forall> i < length(memory ts) . (memory ts @ [msg x v ti]) ! i = (memory ts ) ! i")
      prefer 2
      apply (simp add: nth_append)
    apply (subgoal_tac " memory ts ! 0 = Init_Msg")
     prefer 2
  using mem_structured_def apply blast
     apply (subgoal_tac " 0 < length(memory ts)")
      prefer 2
      apply blast
     apply presburger
  apply simp
    apply (simp (no_asm) add:notoverwritten_def)
    apply (metis le0 less_Suc_eq mem_l store_add)
  apply simp
   apply (subgoal_tac " 0 < i \<and> i < length(memory ts)  \<longrightarrow>memory ts ! i \<noteq> Init_Msg")
  prefer 2
    apply simp
 apply (subgoal_tac"  maxvp (store_trans ts x v ti) x = maxvp ts x")
   prefer 2
     apply (simp add: store_trans_def)
   apply simp
   apply(intro conjI)
    apply (meson leI le_less_Suc_eq mem_structured_def)
 apply (subgoal_tac " \<forall> i < length(memory ts) . (memory ts @ [msg x v ti]) ! i = (memory ts ) ! i")
      prefer 2
    apply (simp add: nth_append)
   apply simp
   apply(safe)
         apply (metis less_antisym)
        apply linarith
       apply (metis less_antisym)
      apply (metis less_SucE)
  using less_antisym apply blast

    apply (smt length_append_singleton lessI less_trans notoverwritten_def store_add)
   apply blast
  by simp

(*rule: After executing a store, the sets of asynchronous observable values (OAV) for x (for all threads) are augmented with
the newly written value.*)
lemma st_oav_gen:
  assumes "mem_structured ts"
  and "vbounded ts"
  and  "step ti ( Store  x v) ts ts'"
shows "   [x]\<^sup>A\<^sub>t  ts'  =   [x]\<^sup>A\<^sub>t ts  \<union> {v}"
using assms 
  apply (simp add: step_def )
 apply (subgoal_tac"  OATS ts' t  x  =  OATS ts t x \<union> {length (memory ts)}")
  prefer 2
  using assms(3) st_oats_gen apply blast
  apply (subgoal_tac " mapval ts x  ( OATS ts t x)  (memory ts') = mapval ts x  ( OATS ts t  x)  (memory ts)")
   prefer 2
 apply (subgoal_tac "  length (memory ts') > length (memory ts)") 
  prefer  2
    apply (simp add:  store_trans_def)
   apply (subgoal_tac "\<forall> i. i \<in>  ( OATS ts t x) \<longrightarrow> i < length (memory ts)")
   prefer 2
  apply (simp add:  OATS_def)
   apply (subgoal_tac "\<forall> i. i \<in>  (  OATS ts t x) \<longrightarrow> i < length (memory ts')")
    prefer 2
  using less_trans apply blast
   apply (unfold mapval_def)
   apply (metis (mono_tags, lifting) bot.extremum_strict bot_nat_def image_cong mem_l not_le_imp_less)
  apply (subgoal_tac " survived_val ts x = survived_val ts' x")
   prefer 2
   apply (simp add: store_trans_def)
  by (simp add: compval_def)
 

(*rule: After executing a store in address x, the set of observable persistent values (OPV) for x is  augmented with
the newly written value.*)
lemma st_opv_gen:
  assumes "mem_structured ts"
  and "vbounded ts"
  and  "step ti ( Store  x v) ts ts'"
shows "   [x]\<^sub>P ts'  =  [x]\<^sub>P ts  \<union> {v}"
using assms 
  apply (simp add: step_def )
 apply (subgoal_tac"  OPTS ts'  x  =  OPTS ts x \<union> {length (memory ts)}")
  prefer 2
  using assms(3) st_opts_gen apply blast
  apply (subgoal_tac " mapval ts x  ( OPTS ts x)  (memory ts') = mapval ts x  ( OPTS ts x)  (memory ts)")
   prefer 2
   apply (subgoal_tac "  length (memory ts') > length (memory ts)") 
  prefer  2
    apply (simp add:  store_trans_def)
   apply (subgoal_tac "\<forall> i. i \<in>  ( OPTS ts x) \<longrightarrow> i < length (memory ts)")
  prefer 2
    apply (simp add:  OPTS_def)
   apply (subgoal_tac "\<forall> i. i \<in>  ( OPTS ts x) \<longrightarrow> i < length (memory ts')")
    prefer 2
  using less_trans apply blast
   apply (unfold mapval_def)
   apply (metis (mono_tags, lifting) bot.extremum_strict bot_nat_def image_cong mem_l not_le_imp_less)
  apply (subgoal_tac " survived_val ts x = survived_val ts' x")
   prefer 2
   apply (simp add: store_trans_def)
  by (simp add: compval_def)


lemma st_opts_daddr_ni: 
  assumes "mem_structured ts"
  and "vbounded ts"
 and "x \<noteq> y"
  and  "step ti ( Store  x v) ts ts'"
shows " OPTS ts'  y  =  OPTS ts y "
using assms 
  apply (simp add: step_def)
  apply (simp add: OPTS_def)

  apply (subgoal_tac " maxvp ts' y = maxvp ts y")
  prefer 2
  apply (simp add: store_trans_def)
  apply clarify
  apply safe
  using less_SucE apply fastforce
                      apply (metis Msg.sel(1) less_SucE nth_append nth_append_length)
  using less_antisym apply fastforce
                      apply (metis Msg.sel(1) less_SucE nth_append nth_append_length)
                      apply (simp add: notoverwritten_def)
  apply (metis less_SucI less_Suc_eq_0_disj less_Suc_eq_le mem_l store_add)
  using less_SucE apply fastforce
                      apply (unfold  notoverwritten_def)
  apply (metis length_append_singleton less_SucI less_Suc_eq_0_disj less_nat_zero_code mem_l nat_less_le store_add)
  apply (metis Msg.distinct(1) less_antisym nth_append_length)
  apply (metis Msg.distinct(1) less_SucE nth_append nth_append_length)
                      apply (metis nth_append order.strict_trans)
                     apply (metis Msg.sel(1) less_antisym nth_append_length)
  apply (metis length_append_singleton less_SucI less_Suc_eq_0_disj less_nat_zero_code mem_l nat_less_le store_add)
  apply (metis Msg.sel(1) less_antisym nth_append_length)
  apply (metis Msg.sel(1) less_SucE nth_append nth_append_length)
                 apply (metis length_append_singleton less_SucI less_Suc_eq_0_disj less_Suc_eq_le mem_l store_add)
  using less_Suc_eq apply blast
               apply (simp add: mem_l)
  using less_Suc_eq apply blast
             apply (metis nth_append)
            apply simp
            apply (metis Msg.sel(1) less_SucE nth_append nth_append_length)
  using less_Suc_eq apply blast
          apply (subgoal_tac " xa = 0")
           prefer 2
  using mem_structured_def neq0_conv apply blast
          apply (simp (no_asm))
          apply (metis Msg.sel(1) less_antisym nth_append nth_append_length)
  using less_Suc_eq apply blast
  apply (metis nth_append)
       apply (metis nth_append)
      apply linarith

 apply (subgoal_tac " xa = 0")
           prefer 2
      apply (metis mem_structured_def neq0_conv nth_append)
     apply (simp (no_asm))
  apply (metis Msg.sel(1) less_antisym nth_append nth_append_length)
  using less_Suc_eq apply blast
   apply (metis nth_append)
  apply (simp (no_asm))
  by (metis Msg.sel(1) less_SucE nth_append nth_append_length)


lemma st_oats_daddr_ni: 
  assumes "mem_structured ts"
  and "vbounded ts"
 and "x \<noteq> y"
  and  "step ti ( Store  x v) ts ts'"
shows " OATS ts' t  y  =  OATS ts t  y "
using assms 
  apply (simp add: step_def)
  apply (simp add: OATS_def)
  apply (subgoal_tac " vpasync ts' t  y = vpasync ts t  y")
  prefer 2
  apply (simp add: store_trans_def)
  apply clarify
  apply safe
  using less_antisym apply fastforce
  apply (metis Msg.sel(1) less_SucE nth_append nth_append_length)
  using less_antisym apply fastforce
  apply (metis Msg.sel(1) less_SucE nth_append nth_append_length)
                      apply (simp add: notoverwritten_def)
  apply (metis less_SucI less_Suc_eq_0_disj less_Suc_eq_le mem_l store_add)
  using less_SucE apply fastforce
                      apply (simp(no_asm) add: notoverwritten_def)
                      apply (metis (no_types, lifting) Nat.lessE length_append_singleton less_SucI less_Suc_eq_0_disj mem_l nat_less_le notoverwritten_def store_add)
  using less_SucE apply fastforce
  apply (metis length_append_singleton mem_structured_def neq0_conv store_add store_wfs)
                      apply (metis Msg.distinct(1) less_SucE nth_append nth_append_length)
                     apply (metis Msg.sel(1) less_antisym nth_append_length)
                    apply (simp(no_asm) add: notoverwritten_def)
                    apply (smt Nat.lessE length_append_singleton less_SucI less_Suc_eq_0_disj mem_l nat_less_le notoverwritten_def store_add)
                   apply (metis Msg.sel(1) less_antisym nth_append_length)
                  apply (metis Msg.sel(1) less_SucE nth_append nth_append_length)
                 apply (simp(no_asm) add: notoverwritten_def)
  apply (metis length_append_singleton less_SucI notoverwritten_def nth_append store_add)
  using less_Suc_eq apply blast
               apply (metis nth_append)
  using less_Suc_eq apply blast
  apply (metis nth_append)
            apply (simp(no_asm) add: notoverwritten_def)
  apply (metis Msg.sel(1) less_SucE notoverwritten_def nth_append nth_append_length)
  using less_Suc_eq apply blast
          apply (simp(no_asm) add: notoverwritten_def)
          apply (metis Msg.sel(1) less_SucE notoverwritten_def nth_append nth_append_length)
  using less_Suc_eq apply blast
        apply (metis nth_append)
       apply (metis nth_append)
  using less_Suc_eq apply blast
     apply (simp(no_asm) add: notoverwritten_def)
  apply (metis Msg.sel(1) less_SucE notoverwritten_def nth_append nth_append_length)
  using less_Suc_eq apply blast
   apply (metis nth_append)
     apply (simp(no_asm) add: notoverwritten_def)
  by (metis Msg.sel(1) less_SucE notoverwritten_def nth_append nth_append_length)


(*rule: After executing a store, the observable persistent values (OPV) of addresses  different from the newly written address
remain the same*)
lemma st_opv_daddr_ni: 
  assumes "mem_structured ts"
  and "vbounded ts"
  and  "x \<noteq> y"
  and  "step ti ( Store  x v) ts ts'"
shows "   [y]\<^sub>P ts=  [y]\<^sub>P ts'"
 using assms 
  apply (simp add: step_def)
  apply (subgoal_tac " OPTS ts  y = OPTS ts'  y")
  prefer 2
  using assms(4) st_opts_daddr_ni apply blast
 apply (subgoal_tac "mapval ts y  ( OPTS ts y)  (memory ts')  = mapval  ts y ( OPTS ts y)  (memory ts)")
   prefer 2
   apply (subgoal_tac "  length (memory ts') > length (memory ts)") 
  prefer  2
    apply (simp add:  store_trans_def)
   apply (subgoal_tac "\<forall> i. i \<in>  ( OPTS ts y) \<longrightarrow> i < length (memory ts)")
  prefer 2
    apply (simp add:  OPTS_def)
   apply (subgoal_tac "\<forall> i. i \<in>  ( OPTS ts y) \<longrightarrow> i < length (memory ts')")
    prefer 2
     apply (simp add: OPTS_def)
  using Msg.sel(1) apply auto[1]
   apply (unfold  mapval_def)
   apply (metis (no_types, lifting) image_cong le0 mem_l)
  apply simp
  using assms(4) survived_val_preserved_store by force


(*rule: After executing a store, the observable asynchronous values (OAV)  of addresses  different from the newly written address
remain the same*)
lemma st_oav_daddr_ni: 
  assumes "mem_structured ts"
  and "vbounded ts"
  and  "x \<noteq> y"
  and  "step ti ( Store  x v) ts ts'"
shows "   [y]\<^sup>A\<^sub>t ts =  [y]\<^sup>A\<^sub>t ts'"
using assms 
  apply (simp add: step_def)
  apply (subgoal_tac " OATS ts t  y = OATS ts' t  y")
  prefer 2
  using assms(4) st_oats_daddr_ni apply auto[1]
 apply (subgoal_tac "mapval ts y  ( OATS ts t y)  (memory ts')  = mapval ts y ( OATS ts t  y)  (memory ts)")
   prefer 2
   apply (subgoal_tac "  length (memory ts') > length (memory ts)") 
  prefer  2
    apply (simp add:  store_trans_def)
   apply (subgoal_tac "\<forall> i. i \<in>  ( OATS ts t y) \<longrightarrow> i < length (memory ts)")
  prefer 2
    apply (simp add:  OATS_def)
  apply fastforce
   apply (subgoal_tac "\<forall> i. i \<in>  ( OATS ts t y) \<longrightarrow> i < length (memory ts')")
    prefer 2
  using less_trans apply blast
   apply (unfold  mapval_def)
   apply (metis (no_types, lifting) image_cong le0 mem_l)
  apply simp
  using assms(4) survived_val_preserved_store by force


lemma COBS_not_empty:
assumes "mem_structured ts"
and "vbounded ts"
and  "\<forall>ti l. comploc ( (memory ts)!(coh ts ti l)) l = l"
and " cond_ts ts ti x v \<noteq> {}" 
and " \<forall>  nview ti l. OTSF ts ti l nview \<noteq> {}"
shows " ( COBTS x y v ti ts \<noteq> {})"
 using assms apply (simp add:  vbounded_def  step_def )
  apply (simp add: COBTS_def)
  by (metis all_not_in_conv)


lemma COBV_not_empty: 
assumes "mem_structured s"
and "vbounded s"
and  "\<forall>ti l. comploc ( (memory s)!(coh s ti l)) l = l"
and    "v \<in> [x]\<^sub>t s" 
and " \<forall>  nview ti l. OTSF s ti l nview \<noteq> {}"
shows "\<langle>x  v\<rangle>[y]\<^sub>t s  \<noteq> {}"
  using assms
  apply (subgoal_tac " OTS s t x \<noteq> {} ")
   prefer 2
   apply (simp add: OTS_def)  
  apply (subgoal_tac " cond_ts s t x v \<noteq> {}")
  prefer 2
   apply (unfold  cond_ts_def )
  apply (subgoal_tac "  { ta  |ta.
     ta \<in> OTS s t x \<and>
     v = compval s  (memory s ! ta) x} \<noteq>
    {}") 
    prefer 2 
  apply (smt assms(4) disjoint_iff_not_equal image_iff inf_bot_right mapval_def mem_Collect_eq)
  apply (subgoal_tac "  COBTS x y v t s \<noteq> {}")
    prefer 2
    apply (simp add: COBS_not_empty cond_ts_def setcompr_eq_image)
   apply blast
  apply (unfold  mapval_def)
  using COBS_not_empty cond_ts_def by blast
 
(*rule: Introduction rule for conditional observation when OV is singleton *)  
corollary ld_cobv_lc_intro_s:
  assumes "mem_structured ts"
  and "t \<noteq> t'"
  and "step t ( Store x v) ts ts'"
 and "vbounded ts"
  and " x \<noteq> y"
 and "  v \<notin> [x]\<^sub>t' ts "
 and "  v \<in> [x]\<^sub>t' ts' "
 and  "  [y]\<^sub>t ts  =  {w} "
and " \<forall>ti l. comploc ( (memory ts)!(coh ts ti l)) l = l"
and  " \<forall>  nview ti l . OTSF ts ti l nview \<noteq> {}"
shows "  \<langle>x  v\<rangle>[y]\<^sub>t' ts'  =  {w} "
  using assms
  apply (subgoal_tac " \<langle>x  v\<rangle>[y]\<^sub>t' ts' \<subseteq>  [y]\<^sub>t ts")
   prefer 2
  using ld_cobv_lc_intro apply blast
 
  apply (subgoal_tac " \<langle>x  v\<rangle>[y]\<^sub>t' ts' \<noteq>  {}")
   prefer 2
  using COBV_not_empty OTSF_notempty_preserved coh_loc_rel_preserved mem_structured_preserved vbounded_preserved apply presburger
  by (simp add: subset_singleton_iff)



(*rule: After executing a store, the last store of all addresses that are different from the newly written address
remain the same*)
lemma st_ots_lm_ni:
  assumes "mem_structured ts"
  and "vbounded ts"
  and  "step t ( Store  x v) ts ts'"
  and "x \<noteq> y"
  and "  \<lceil>y\<rceil>\<^sub>t'  ts "
shows "  \<lceil>y\<rceil>\<^sub>t'  ts'  "
  using assms
 apply (simp add:  last_entry_def )
  apply (subgoal_tac "  OTS ts' t' y = OTS ts t' y")
   prefer 2
   apply (meson st_ots_ni)
  apply (simp add: OTS_def)
  apply (simp add: OTSF_def )
  apply (simp add: step_def)
  apply (unfold last_entry_set_def)
  by (smt (z3) Collect_cong Msg.distinct(1) Msg.sel(1) assms(4) comploc_def length_append_singleton less_Suc_eq mem_l nth_append_length store_add)

(*rule: After a thread t executes a store on address x, the observable timestamp of x for t is the last store.*)
lemma st_ots_lm_lc:
  assumes "mem_structured ts"
 and  "step t ( Store  x v) ts ts'"
and " vbounded ts' "
shows " \<lceil>x\<rceil>\<^sub>t ts' "
  using assms
  apply (simp add: step_def)
  apply (subgoal_tac "  OTS ts' t x = { length(memory ts')-1}" )
   prefer 2
  using OTS_lastentry apply auto[1] 
  apply (subgoal_tac " last_entry ts' x = length(memory ts')-1") 
  prefer 2

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
  using Max_eqI apply auto[1]
  by simp 

(*rule: After a thread t executes  a store on address x  the expression \<lceil>FLUSH y\<rceil> holds for t. *)
lemma st_ord_lc:
assumes  "mem_structured ts"
and "vbounded ts"
 and  "step t ( Store  x v) ts ts'"
shows "\<lceil>FLUSH y\<rceil>\<^sub>t ts' "
  using assms
  apply (simp add: step_def)
  apply (subgoal_tac " maxcoh ts' t  = length (memory ts) ")
  prefer 2
  apply (simp add: store_trans_def)
  apply (subgoal_tac " last_entry ts'  y \<le>  length (memory ts) ")
   prefer 2
   apply (subgoal_tac " last_entry ts'  y \<in>  last_entry_set ts' y ")
    prefer 2
  using assms(3) last_entry_in_last_entry_set store_wfs vbounded_preserved apply blast
   apply (subgoal_tac "   last_entry ts' y < length (memory ts' ) ")
    prefer 2
  using assms(3) last_entry_bounded store_wfs vbounded_preserved apply blast
   apply (simp add: store_trans_def)
  by fastforce 

(*rule: After a thread t executes  a store on address x  the expression \<lceil>MFENCE y\<rceil> holds for t. *)
lemma st_m_ord_lc:
assumes  "mem_structured ts"
and "vbounded ts"
 and  "step t ( Store  x v) ts ts'"
shows " \<lceil>MFENCE y\<rceil>\<^sub>t ts' "
  using assms
  apply (simp add: step_def)
  apply (subgoal_tac " maxcoh ts' t  = length (memory ts) ")
  prefer 2
  apply (simp add: store_trans_def)
  apply (subgoal_tac " last_entry ts'  y \<le>  length (memory ts) ")
   prefer 2
   apply (subgoal_tac " last_entry ts'  y \<in>  last_entry_set ts' y ")
    prefer 2
  using assms(3) last_entry_in_last_entry_set store_wfs vbounded_preserved apply blast
   apply (subgoal_tac "   last_entry ts' y < length (memory ts' ) ")
    prefer 2
  using assms(3) last_entry_bounded store_wfs vbounded_preserved apply blast
   apply (simp add: store_trans_def)
  by fastforce 



(*rule: If a thread t executes a store on address x,and \<lceil>FLUSH y\<rceil> holds for 
t before executing the store, and x different to y, \<lceil>FLUSH y\<rceil> still holds for t.*)
lemma st_ord_ni:
 assumes "mem_structured ts"
  and "vbounded ts"
  and  "step t' ( Store  x v ) ts ts'"
  and  "\<lceil>FLUSH y \<rceil>\<^sub>t ts "
  and "x \<noteq> y"
shows  "\<lceil>FLUSH y \<rceil>\<^sub>t ts' "
  using assms
  apply (case_tac " t = t'")
  apply (simp add: st_ord_lc)
  apply (simp add: step_def)
   apply (subgoal_tac " last_entry_set ts' y = last_entry_set ts y ")
   prefer 2
   apply (simp add: last_entry_set_def)
  apply (simp add: store_trans_def)
  apply (metis (no_types, lifting) Msg.distinct(1) Msg.sel(1) bot_nat_0.extremum le_imp_less_Suc less_or_eq_imp_le linorder_neqE_nat mem_l not_less_eq nth_append_length store_add)
  apply(simp add: last_entry_def)
  by(simp add: store_trans_def)  


(*rule: If a thread t executes  a store on address x, and \<lceil>MFENCE y\<rceil> holds for 
t before executing the store, and x different to y, \<lceil>MFENCE y\<rceil> still holds for t.*)
lemma st_m_ord_ni:
 assumes "mem_structured ts"
  and "vbounded ts"
  and  "step t' ( Store  x v ) ts ts'"
  and  "\<lceil>MFENCE y\<rceil>\<^sub>t ts "
  and "x \<noteq> y"
shows  "\<lceil>MFENCE y\<rceil>\<^sub>t ts' "
  using assms
  apply (case_tac " t = t'")
  apply (simp add: st_m_ord_lc)
  apply (simp add: step_def)
   apply (subgoal_tac " last_entry_set ts' y = last_entry_set ts y ")
   prefer 2
   apply (simp add: last_entry_set_def)
  apply (simp add: store_trans_def)
  apply (metis (no_types, lifting) Msg.distinct(1) Msg.sel(1) bot_nat_0.extremum le_imp_less_Suc less_or_eq_imp_le linorder_neqE_nat mem_l not_less_eq nth_append_length store_add)
  apply(simp add: last_entry_def)
  by(simp add: store_trans_def) 

(*rule: The number of writes on x with value v is incremented by 1, after a thread t' executes a store on x with value v. *)
lemma st_oc_lc:
 assumes "mem_structured ts"
  and "vbounded ts"
  and  "step t' ( Store  x v ) ts ts'"
shows " \<lparr>x,v\<rparr>  ts' = \<lparr>x,v\<rparr>   ts +1"
using assms
  apply (simp add: step_def)
 apply (subgoal_tac " oc_set ts'  x v = oc_set ts  x v \<union> {(length (memory ts))}")
  prefer 2
apply (subgoal_tac " \<forall> i. i \<in> oc_set ts' x v   \<longrightarrow> 0 \<le> i \<and> i \<le> (length (memory ts))")
  prefer 2
  apply (subgoal_tac " length (memory ts')  = length (memory ts)+ 1")
   prefer 2
   apply (simp add: store_trans_def)
   apply (simp add: oc_set_def)
 apply (subgoal_tac " \<forall> i. 0 \<le> i \<and> i <  length (memory ts) \<longrightarrow> ( i \<in> oc_set ts' x v \<longrightarrow>  i \<in> oc_set ts x v)")
  prefer 2
  apply( simp(no_asm) add: oc_set_def)
  apply (metis assms(3) le0 mem_l survived_val_preserved_store)
apply (subgoal_tac " length (memory ts)\<in> oc_set ts'  x v ")
  prefer 2
   apply (subgoal_tac "  compval ts' (memory ts' ! (length (memory ts))) x = v \<and> comploc (memory ts' ! (length (memory ts))) x = x \<and> 0 \<le> (length (memory ts)) \<and> (length (memory ts)) < length (memory ts') ")
  prefer 2
   apply (simp add: store_trans_def)

  apply (smt (verit, del_insts) mem_Collect_eq oc_set_def)
apply (subgoal_tac " \<nexists> k.  k \<in> oc_set ts' x v \<and> k \<noteq> length (memory ts) \<and> k \<notin> oc_set ts x v ")
  prefer 2
  apply (meson le_imp_less_or_eq)

  apply (subgoal_tac " \<forall> i. i \<in> oc_set ts x v   \<longrightarrow>  i \<in> oc_set ts' x v")
  prefer 2
  apply (simp(no_asm) add: store_trans_def oc_set_def)
  apply (metis assms(3) less_add_one mem_st_dt nth_append order.strict_trans st_mem_length survived_val_preserved_store)
  apply safe
  apply blast
  apply presburger
  by  (simp add:   oc_set_def)





(*rule: The number of writes on x with value v remains the same after a thread t' executes a store on x with value different from v. *)
lemma st_noc_lc:
 assumes "mem_structured ts"
  and "vbounded ts"
  and  "step t' ( Store  x v ) ts ts'"
and "v \<noteq> v'"
shows " \<lparr>y,v'\<rparr>  ts' =  \<lparr>y,v'\<rparr>  ts"
 using assms
  apply (simp add: step_def)
  apply (subgoal_tac " \<forall> j. 0 \<le> j \<and> j < length (memory ts) \<longrightarrow> ( (memory ts' ! j) = (memory ts ! j))")
  prefer 2
    apply (simp add: store_trans_def)
  apply (metis bot.extremum bot_nat_def mem_l store_add)

  apply (simp add: store_trans_def)
  apply (simp add:  oc_set_def)
  by (metis (no_types, lifting)  Msg.discI Msg.sel(2) less_Suc_eq nth_append_length)
 (* by (smt (verit, best) Collect_cong Msg.distinct(1) Msg.sel(2) less_Suc_eq nth_append_length)*)


(*rule: The value of the last write  on x remains the same after a thread t' executes a store on an address different from x.*)
lemma st_lv_ni:
  assumes "mem_structured ts"
 and "vbounded ts"
and  "step t' ( Store  y v ) ts ts'"
and "x \<noteq> y"
shows " \<lceil>x:v\<rceil> ts' =\<lceil>x:v\<rceil> ts  "
  using assms
  apply (simp add: step_def)
  apply (subgoal_tac "  last_entry ts'  x = last_entry ts  x")
   prefer 2 
  apply (simp add: last_entry_def)
   apply (simp add: last_entry_set_def)
   apply (subgoal_tac"( \<forall>i.(i\<ge>0\<and>i<length(memory ts)) \<longrightarrow> ( memory ts)!i =( memory ts')!i)")
    prefer 2
  using mem_l apply blast   
   apply simp   
   apply (metis (no_types, lifting) Collect_cong Msg.discI Msg.sel(1) less_Suc_eq not_less_less_Suc_eq nth_append_length)
  by (smt (z3) assms(3) bot.extremum_uniqueI bot_nat_def last_entry_bounded le_cases3 mem_l store_add survived_val_preserved_store)



(*rule: The value of the last write  on x becomes v after a thread t' executes a store on x with value v.*)
lemma st_lv_lc:
  assumes "mem_structured ts"
 and "vbounded ts"
and  "step t' ( Store  x v ) ts ts'"
shows " \<lceil>x:v\<rceil> ts' "
  using assms
  apply (simp add: step_def)
  apply (subgoal_tac " last_entry ts' x = length(memory ts')-1") 
   prefer 2
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
  using Max_eqI apply auto[1]
  by (simp add: store_trans_def)


lemma st_last_entry_init_message_ni:
  assumes "mem_structured ts"
 and "vbounded ts"
and "memory ts ! last_entry ts lx \<noteq> Init_Msg "
and  "step t' ( Store  x v ) ts ts'"
and " lx \<noteq> x"
shows "memory ts' ! last_entry ts' lx \<noteq> Init_Msg "
  using assms
  apply (simp add: step_def)
  apply (subgoal_tac " last_entry ts lx = last_entry ts' lx ")
   prefer 2 
  apply (simp add: last_entry_def)
   apply (simp add: last_entry_set_def)
   apply (subgoal_tac"( \<forall>i.(i\<ge>0\<and>i<length(memory ts)) \<longrightarrow> ( memory ts)!i =( memory ts')!i)")
    prefer 2
  using mem_l apply blast   
   apply simp   
  apply (metis (no_types, lifting) Msg.discI Msg.sel(1) less_Suc_eq nth_append_length)
  by (metis bot_nat_0.extremum last_entry_bounded mem_l store_add)


lemma st_last_entry_val_ni:
  assumes "mem_structured ts"
 and "vbounded ts"
and "val (memory ts ! last_entry ts lx) = y"
and  "step t' ( Store  x v ) ts ts'"
and " lx \<noteq> x"
shows "val (memory ts' ! last_entry ts' lx) = y"
  using assms
  apply (simp add: step_def)
  apply (subgoal_tac " last_entry ts lx = last_entry ts' lx ")
   prefer 2 
  apply (simp add: last_entry_def)
   apply (simp add: last_entry_set_def)
   apply (subgoal_tac"( \<forall>i.(i\<ge>0\<and>i<length(memory ts)) \<longrightarrow> ( memory ts)!i =( memory ts')!i)")
    prefer 2
  using mem_l apply blast   
   apply simp
   apply (metis (no_types, lifting)  Msg.discI Msg.sel(1) less_Suc_eq nth_append_length)
  by (metis bot_nat_0.extremum last_entry_bounded mem_l store_add)

(*rule: The number of writes on x with value v remains the same after a thread t' executes a store on x with value different from v. *)
lemma st_last_entry_daddr_preserved:
 assumes "mem_structured ts"
 and "vbounded ts"
and " x \<noteq> y"
and "  ts' =store_trans ts x v t"
shows "  last_entry ts'  y = last_entry ts  y"
  using assms 
  apply (subgoal_tac " (\<forall>i.(i\<ge>0\<and>i<length(memory ts)) \<longrightarrow> ( memory ts)!i =( memory ts')!i) ")
  prefer 2
  using mem_l apply blast
 apply (simp add: last_entry_def)
  apply (subgoal_tac " last_entry_set ts' y = last_entry_set ts y")
   prefer 2
   apply (simp add: last_entry_set_def)
   apply (subgoal_tac " length(memory ts) \<notin> last_entry_set ts' y")
    prefer 2
    apply (simp add: last_entry_set_def)
  apply (metis (no_types, lifting) Collect_cong Msg.distinct(1) Msg.sel(1) less_Suc_eq nth_append_length)
  by metis



lemma st_pm_inv_preserved:
  assumes "mem_structured ts"
  and "vbounded ts"
and " x \<in> A"
and "  step t ( Store  x v ) ts ts'" 
  and " ( \<forall> addr . (( addr \<noteq> y)  \<and> addr \<notin> A)  \<longrightarrow> [addr]\<^sub>P ts =  { lastVal  addr  ts  })"
(*and "\<forall> ti l.  OTS  ts ti  l \<noteq> {}"
and  "\<forall>ti l. comploc ( (memory ts)!(coh ts ti l)) l = l" *)
shows "  ( \<forall> addr . (( addr \<noteq>y)  \<and> addr \<notin> A )  \<longrightarrow> [addr]\<^sub>P ts' =  { lastVal  addr  ts'  })  "
  using assms
apply (subgoal_tac " \<forall> addr . (( addr \<noteq> y)  \<and> addr \<notin> A)  \<longrightarrow>  [addr]\<^sub>P ts' =  [addr]\<^sub>P ts  ")
   prefer 2
   apply (metis st_opv_daddr_ni)
apply (subgoal_tac"  \<forall> addr . (( addr \<noteq> y)  \<and> addr \<notin> A)  \<longrightarrow> lastVal  addr ts = lastVal  addr ts'")
    prefer 2
   apply (subgoal_tac"  \<forall> addr . (( addr \<noteq> y)  \<and> addr \<notin> A)  \<longrightarrow> last_entry ts'  addr = last_entry ts  addr")
    prefer 2
    apply (simp add: step_def)
  apply (metis st_last_entry_daddr_preserved)
   apply (simp add: lastVal_def)
  apply (metis gr_zeroI last_entry_bounded mem_structured_def mem_structured_preserved st_last_entry_init_message_ni st_last_entry_val_ni survived_val_preserved_store)
  by simp


lemma st_valOf_dt_ni:
assumes "vbounded ts" 
and "mem_structured ts"
and "step t ( Store  x v ) ts ts'" 
shows "\<forall> i.  i \<in> OTS ts ti glb \<longrightarrow>  ( valOf  i glb  ts  = valOf  i glb  ts' )"
  using assms
 apply (simp add: step_def)
  apply (subgoal_tac " (\<forall>i.(i\<ge>0\<and>i<length(memory ts)) \<longrightarrow> ( memory ts)!i =( memory ts')!i) ")
  prefer 2
  apply (metis mem_l) 
  by (simp add: valOf_def
 store_trans_def)

(*rule: The monotonicity property of glb holds after a write on an address different form glb.*)
lemma st_glb_monotonicity_preserved:
 assumes " ( \<forall> i j . ( j \<in> OTS ts ti  glb \<and>  i \<in> OTS ts ti glb \<and>  i \<le> j)  \<longrightarrow> valOf  i glb  ts  \<le> valOf j glb  ts)"
 and "vbounded ts"
and "mem_structured ts"
and "  step t ( Store  x v ) ts ts'" 
and "x \<noteq> glb"
shows  " ( \<forall> i j . ( j \<in> OTS ts' ti  glb \<and>  i \<in> OTS ts' ti glb \<and>  i \<le> j)  \<longrightarrow> valOf  i glb  ts'  \<le> valOf j glb  ts')"
  using assms
  apply (subgoal_tac "  OTS ts' ti  glb = OTS ts ti  glb ")
   prefer 2
  using st_ots_ni apply auto[1]
  apply (simp add: step_def)
  apply (subgoal_tac " (\<forall>i.(i\<ge>0\<and>i<length(memory ts)) \<longrightarrow> ( memory ts)!i =( memory ts')!i) ")
  prefer 2
  apply (metis mem_l) 
 apply (subgoal_tac " \<forall> i.  i \<in> OTS ts ti glb \<longrightarrow>  ( valOf  i glb  ts  = valOf  i glb  ts' )")
   prefer 2
   apply (simp add: valOf_def store_trans_def)
  by metis


(*rule:   After a store on x the timestamp of the last write of x becomes equal to the length of the memory in the pre-state.*)
lemma st_lastEntry_lc: 
  assumes "mem_structured ts"
  and "vbounded ts"
  and  "step ti ( Store  x v) ts ts'"
shows "  last_entry ts' x = length(memory ts) "
  using assms
 apply (simp add: step_def)
  apply (simp add: store_trans_def)
 apply(simp add: last_entry_def) 
   apply (subgoal_tac "  length(memory ts) \<in> last_entry_set ts' x  ")
    prefer 2
    apply (simp add: last_entry_set_def)
    apply (subgoal_tac " \<forall>i. i \<in>(last_entry_set ts' x) \<longrightarrow> i \<le>  length ( memory ts)")
  prefer 2
    apply (simp add: last_entry_set_def)
  by (meson Max_eqI finite_last_entry_set)

(*rule:   After a store on x of a value v the value of the last write on x becomes v.*)
lemma st_lastVal_lc:
  assumes "mem_structured ts"
  and "vbounded ts"
  and  "step ti ( Store  x v) ts ts'"
shows " lastVal x ts' = v "
  using assms
  apply (simp add: step_def)
  apply (simp add: store_trans_def)
  apply (simp add: lastVal_def)
  apply (subgoal_tac "  last_entry ts' x = length(memory ts)")
   prefer 2
  using assms(3) st_lastEntry_lc apply blast
  by force


(*rule: The monotonicty property of glb holds after a write on glb of the form: store glb v + 1, where v is the value of the last write on glb*)
lemma st_glb_monotonicity_preserved2:
assumes " \<lceil>glb:v\<rceil> ts " 
and "mem_structured ts"
and "vbounded ts"
and  "step t (Store  glb (v+1)) ts ts'"
and " \<forall> ti l. last_entry ts l \<in>   OTS ts ti l "
and " \<forall> ti l. lastVal  l ts  \<in>  [l]\<^sub>ti ts "
and " ( \<forall> i j ti . ( j \<in> OTS ts ti  glb \<and>  i \<in> OTS ts ti glb \<and>  i \<le> j)  \<longrightarrow> valOf  i glb  ts  \<le> valOf j glb  ts)"
shows "  ( \<forall> i j ti . ( j \<in> OTS ts' ti  glb \<and>  i \<in> OTS ts' ti glb \<and>  i \<le> j)  \<longrightarrow> valOf  i glb  ts'  \<le> valOf j glb  ts')"
  using assms
  apply (subgoal_tac "  valOf (last_entry  ts  glb)  glb  ts = v")
   prefer 2
   apply (simp add: valOf_def)
  apply (subgoal_tac "  \<forall> i j ti . ( j \<in> OTS ts ti glb  \<longrightarrow> ( j \<le> last_entry  ts  glb) )")
   prefer 2
 apply (simp add: OTS_def)
  apply (simp add: OTSF_def)
   apply (simp add: last_entry_def)
   apply (simp(no_asm) add: last_entry_set_def) 
  apply (subgoal_tac "   last_entry  ts' glb =  length (memory ts) ")
   prefer 2
   apply (simp add: step_def)
  using assms(4) st_lastEntry_lc apply presburger
  apply (subgoal_tac "  \<forall> i j ti . ( j \<in> OTS ts' ti glb  \<longrightarrow>  j <  length (memory ts') ) ")
   prefer 2
apply (simp add: OTS_def)
   apply (simp add: OTSF_def)
  apply (subgoal_tac " length (memory ts' ) = length(memory ts) + 1")
  prefer 2
   apply (simp add: step_def)
 apply (subgoal_tac "  \<forall> i j ti . ( j \<in> OTS ts' ti glb  \<longrightarrow>  j \<le>  length(memory ts) ) ")
   prefer 2
   apply (metis discrete leD leI)
 apply (subgoal_tac "  \<forall> i j ti . ( j \<in> OTS ts' ti glb  \<longrightarrow>  j \<le>  last_entry  ts'  glb ) ")
   prefer 2
   apply presburger
  apply (subgoal_tac " \<forall> i j ti .  ( j \<in> OTS ts ti  glb  \<longrightarrow>  valOf  j  glb  ts  \<le>  v )  ")
    prefer 2
   apply metis
  apply (subgoal_tac " \<forall> i j ti .  ( j \<in> OTS ts' ti  glb  \<longrightarrow>  (valOf  j  glb  ts'  \<le>  v+1) )  ")
   prefer 2
  apply (subgoal_tac "  valOf (last_entry  ts'  glb)  glb  ts' = v+1")
   prefer 2
    apply (metis st_lv_lc valOf_def)
 apply (subgoal_tac " \<forall> i t.  i \<in> OTS ts t glb \<longrightarrow>  ( valOf  i glb  ts  = valOf  i glb  ts' )")
   prefer 2
  apply (meson st_valOf_dt_ni)
   apply clarify
   apply (case_tac " t = ti")
    apply (metis Orderings.order_eq_iff opv_opts_rel singletonD st_ov_lc valOf_def)
  apply (subgoal_tac " OTS ts' ti glb  = OTS ts ti glb \<union>  { length(memory ts')-1}")
    prefer 2
  using st_ots_dt_lc apply presburger
   apply (case_tac " j \<in>  OTS ts ti glb ")
  apply (metis trans_le_add1)
   apply (metis UnE diff_add_inverse2 le_eq_less_or_eq singletonD)
  apply clarify
  apply (case_tac " t \<noteq> ti" )
  apply (subgoal_tac " OTS ts' ti glb  = OTS ts ti glb \<union>  { length(memory ts')-1}")
    prefer 2
  using st_ots_dt_lc apply presburger
  apply (smt (z3) Un_iff diff_add_inverse2 insert_absorb insert_iff insert_not_empty le_add_diff_inverse2 le_neq_implies_less not_add_less2 st_lv_lc st_valOf_dt_ni valOf_def)
  by (metis opv_opts_rel singletonD st_ov_lc valOf_def)









lemma st_glb_monotonicity_preserved_reg:
assumes "  (if memory ts ! last_entry ts  glb = Init_Msg then survived_val ts glb
     else Msg.val (memory ts ! last_entry ts glb)) =
    regs ts t l " 
and "mem_structured ts"
and "vbounded ts"
and  "step t (Store  glb ( Suc (regs ts t l)) ) ts ts'"
and " \<forall> ti l. last_entry ts l \<in>   OTS ts ti l "
and " \<forall> ti l. lastVal  l ts  \<in>  [l]\<^sub>ti ts "
and " ( \<forall> i j ti . ( j \<in> OTS ts ti  glb \<and>  i \<in> OTS ts ti glb \<and>  i \<le> j)  \<longrightarrow> valOf  i glb  ts  \<le> valOf j glb  ts)"
shows "  ( \<forall> i j ti . ( j \<in> OTS ts' ti  glb \<and>  i \<in> OTS ts' ti glb \<and>  i \<le> j)  \<longrightarrow> valOf  i glb  ts'  \<le> valOf j glb  ts')"
  using assms
  using st_glb_monotonicity_preserved2 
  by simp


lemma st_glb_monotone_preserved:
  assumes " \<lceil>glb:v\<rceil> ts " 
and"(  \<forall> i j  .0 < j \<and>  j < length(memory ts)  \<and> 0 <  i \<and>  i < length(memory ts)  \<and>  i \<le> j \<and>  (State.loc (memory( ts)!i) ) = glb  \<and>  (State.loc (memory( ts)!j) ) = glb  \<longrightarrow> ((compval ts  (memory( ts)!i) glb ) \<le> (compval ts  (memory( ts)!j) glb ) ))"
and "mem_structured ts"
and "vbounded ts"
and  "step t (Store  glb (Suc v)) ts ts'"
and " \<forall> ti l. last_entry ts l \<in>   OTS ts ti l "
and " \<forall> ti l. lastVal  l ts  \<in>  [l]\<^sub>ti ts "
shows   "(  \<forall> i j  . 0 < j \<and>  j < length(memory ts')  \<and> 0 <  i \<and>  i < length(memory ts')  \<and>  i \<le> j \<and>  (State.loc (memory( ts')!i) ) = glb  \<and>  (State.loc (memory( ts')!j) ) = glb  \<longrightarrow> ((compval ts'  (memory( ts')!i) glb ) \<le> (compval ts'  (memory( ts')!j) glb ) ))"

  using assms
  apply (subgoal_tac "  valOf (last_entry  ts  glb)  glb  ts = v")
   prefer 2
   apply (simp add: valOf_def)
apply (subgoal_tac "   last_entry  ts' glb =  length (memory ts) ")
   prefer 2
  using st_lastEntry_lc apply blast

  apply (subgoal_tac "  valOf (last_entry  ts'  glb)  glb  ts' = Suc v")
   prefer 2
   apply (simp add: step_def  )

  apply (metis assms(5) st_lv_lc valOf_def)


apply (subgoal_tac " (\<forall>i.(i>0\<and>i<length(memory ts)) \<longrightarrow> ( memory ts)!i =( memory ts')!i) ")
   prefer 2
   apply (simp add: step_def)
  apply (metis less_nat_zero_code linorder_le_less_linear mem_l mem_st_dt)
apply (subgoal_tac " \<forall> i .(i>0\<and>i<length(memory ts)) \<longrightarrow>  ( valOf  i glb  ts  = valOf  i glb  ts' )")
   prefer 2
  apply (metis compval_def survived_val_preserved_store valOf_def)

apply (subgoal_tac "  \<forall>  j . (  (0 < j \<and>  j < length(memory ts)  \<and> comploc ((memory ts)!j) glb = glb)   \<longrightarrow>  valOf  j  glb  ts  \<le>  v ) ")
   prefer 2  
apply (subgoal_tac " \<forall> j . (0 < j \<and>  j < length(memory ts)  \<and> comploc ((memory ts)!j) glb = glb)  \<longrightarrow>  j \<le> last_entry  ts  glb  ")
   prefer 2
    apply (subgoal_tac "\<forall> j .(0 < j \<and>  j < length(memory ts)  \<and> comploc ((memory ts)!j) glb = glb)  \<longrightarrow>  j \<in> last_entry_set ts glb")
  prefer 2
     apply (simp add: last_entry_set_def)
     apply metis
    apply (subgoal_tac "\<forall> i. i \<in>  last_entry_set ts glb \<longrightarrow> i \<le>  last_entry  ts  glb  ")
     prefer 2
  apply (simp add: last_entry_def)
  using  finite_last_entry_set    apply (metis Max_ge)
    apply metis
  apply (metis bot_nat_0.extremum_uniqueI last_entry_bounded last_entry_loc loc_eq_comploc valOf_def zero_less_iff_neq_zero)
  apply (subgoal_tac " (\<forall> i j  .( 0 < j \<and>  j < length(memory ts') \<and> 0 < i \<and>  i < length(memory ts') \<and>  i \<le> j \<and> comploc ((memory ts')!i) glb = glb \<and> comploc ((memory ts')!j) glb = glb  ) \<longrightarrow>
            ( valOf  i glb ts'  \<le> valOf j glb  ts')  )")
   prefer 2
  apply (intro allI impI)
   apply (case_tac"  j < length (memory ts) \<and>  i < length (memory ts) ")

  apply (metis loc_eq_comploc valOf_def)
   apply (subgoal_tac " length (memory ts') = length (memory ts) + 1 ")
  prefer 2
  using st_mem_length apply presburger
  apply (metis Suc_eq_plus1 le_Suc_eq le_less_Suc_eq not_less_less_Suc_eq)
  by (smt (verit) comploc_def order.strict_trans1 valOf_def)



(*rule: The monotonicty property of glb holds, considering also the initial message of the memory,  after a write on glb of the form: store glb v + 1, where v is the value of the last write on glb*)
lemma st_glb_monotone_complete_preserved:
  assumes " \<lceil>glb:v\<rceil> ts " 
and"(  \<forall> i j  .0 < j \<and>  j < length(memory ts)  \<and> 0 \<le>  i \<and>  i < length(memory ts)  \<and>  i \<le> j \<and>  comploc ((memory ts)!j) glb = glb  \<and>  comploc ((memory ts)!i) glb = glb   \<longrightarrow> ((compval ts  (memory( ts)!i) glb ) \<le> (compval ts  (memory( ts)!j) glb ) ))"
and "mem_structured ts"
and "vbounded ts"
and  "step t (Store  glb (Suc v)) ts ts'"
and " \<forall> ti l. last_entry ts l \<in>   OTS ts ti l "
and " \<forall> ti l. lastVal  l ts  \<in>  [l]\<^sub>ti ts "
shows   "(  \<forall> i j  . 0 < j \<and>  j < length(memory ts')  \<and> 0 \<le>  i \<and>  i < length(memory ts')  \<and>  i \<le> j \<and>   comploc ((memory ts')!j) glb = glb \<and>  comploc ((memory ts')!i) glb = glb   \<longrightarrow> ((compval ts'  (memory( ts')!i) glb ) \<le> (compval ts'  (memory( ts')!j) glb ) ))"

  using assms
  apply (subgoal_tac "  valOf (last_entry  ts  glb)  glb  ts = v")
   prefer 2
   apply (simp add: valOf_def)
apply (subgoal_tac "   last_entry  ts' glb =  length (memory ts) ")
   prefer 2
  using st_lastEntry_lc apply presburger
  apply (subgoal_tac "  valOf (last_entry  ts'  glb)  glb  ts' = Suc v")
   prefer 2
   apply (simp add: step_def  )
  apply (metis assms(5) st_lv_lc valOf_def)
apply (subgoal_tac " (\<forall>i.(i\<ge>0\<and>i<length(memory ts)) \<longrightarrow> ( memory ts)!i =( memory ts')!i) ")
   prefer 2
   apply (simp add: step_def)
  apply (metis less_nat_zero_code linorder_le_less_linear mem_l mem_st_dt)
apply (subgoal_tac " \<forall> i .(i\<ge>0\<and>i<length(memory ts)) \<longrightarrow>  ( valOf  i glb  ts  = valOf  i glb  ts' )")
   prefer 2
  apply (metis compval_def survived_val_preserved_store valOf_def)

apply (subgoal_tac "  \<forall>  j . (  (0 \<le> j \<and>  j < length(memory ts)  \<and> comploc ((memory ts)!j) glb = glb)   \<longrightarrow>  valOf  j  glb  ts  \<le>  v ) ")
   prefer 2  
apply (subgoal_tac " \<forall> j . (0 \<le> j \<and>  j < length(memory ts)  \<and> comploc ((memory ts)!j) glb = glb)  \<longrightarrow>  j \<le> last_entry  ts  glb  ")
   prefer 2
    apply (subgoal_tac "\<forall> j .(0 \<le> j \<and>  j < length(memory ts)  \<and> comploc ((memory ts)!j) glb = glb)  \<longrightarrow>  j \<in> last_entry_set ts glb")
  prefer 2
     apply (simp add: last_entry_set_def)
     apply metis
    apply (subgoal_tac "\<forall> i. i \<in>  last_entry_set ts glb \<longrightarrow> i \<le>  last_entry  ts  glb  ")
     prefer 2
  apply (simp add: last_entry_def)
  using  finite_last_entry_set    apply (metis Max_ge)
    apply metis
  using  last_entry_bounded last_entry_loc loc_eq_comploc valOf_def 
  apply (metis assms(4) le_antisym le_eq_less_or_eq zero_less_iff_neq_zero)
 (*  apply (metis bot_nat_0.extremum_uniqueI last_entry_bounded last_entry_loc loc_eq_comploc valOf_def zero_less_iff_neq_zero)*)

  apply (subgoal_tac " (\<forall> i j  .( 0 < j \<and>  j < length(memory ts') \<and> 0 \<le> i \<and>  i < length(memory ts') \<and>  i \<le> j \<and> comploc ((memory ts')!i) glb = glb \<and> comploc ((memory ts')!j) glb = glb  ) \<longrightarrow>
            ( valOf  i glb ts'  \<le> valOf j glb  ts')  )")
   prefer 2
  apply (intro allI impI)
   apply (case_tac"  j < length (memory ts) \<and>  i < length (memory ts) ")
  apply (metis bot_nat_0.extremum valOf_def)
   apply (subgoal_tac " length (memory ts') = length (memory ts) + 1 ")
  prefer 2
  using st_mem_length apply presburger
   apply (metis Suc_eq_plus1 le_Suc_eq le_less_Suc_eq not_less_less_Suc_eq)
  by (metis valOf_def)




(*rule: The monotonicty property of glb holds, when a write operation occurs on an address that is different from glb*)
lemma st_ni_glb_monotonicity_preserved:
  assumes"(  \<forall> i j  .0 < j \<and>  j < length(memory ts)  \<and> 0 <  i \<and>  i < length(memory ts)  \<and>  i \<le> j \<and>    (State.loc (memory( ts)!i) ) = glb    \<and>  (State.loc (memory( ts)!j) ) = glb  \<longrightarrow> ((compval ts  (memory( ts)!i) glb ) \<le> (compval ts  (memory( ts)!j) glb ) ))"
 and "vbounded ts"
and "mem_structured ts"
and "  step t ( Store  x v ) ts ts'" 
and "x \<noteq> glb"
shows   "(  \<forall> i j  . 0 < j \<and>  j < length(memory ts')  \<and> 0 <  i \<and>  i < length(memory ts')  \<and>  i \<le> j \<and>  (State.loc (memory( ts')!i) ) = glb  \<and>  (State.loc (memory( ts')!j) ) = glb  \<longrightarrow> ((compval ts'  (memory( ts')!i) glb ) \<le> (compval ts'  (memory( ts')!j) glb ) ))"
  using assms
  apply (simp add: step_def)
  apply (subgoal_tac " (\<forall>i.(i\<ge>0\<and>i<length(memory ts)) \<longrightarrow> ( memory ts)!i =( memory ts')!i) ")
  prefer 2
   apply (metis mem_l)

  apply (subgoal_tac "  (loc (memory(ts')!(length (memory ts)))  \<noteq> glb ) ")
   prefer 2
   apply (simp add: store_trans_def)
  by (smt (verit, del_insts) assms(4) le_eq_less_or_eq less_SucE mem_structured_def st_mem)




(*rule: The monotonicty property of glb holds, when a write operation occurs on an address that is different from glb, considering also the initial message*)
lemma st_ni_glb_complete_monotonicity_preserved:
  assumes"(  \<forall> i j  .0 < j \<and>  j < length(memory ts)  \<and> 0 \<le>  i \<and>  i < length(memory ts)  \<and>  i \<le> j \<and>   comploc ((memory ts)!j) glb = glb   \<and>   comploc ((memory ts)!i) glb = glb   \<longrightarrow> ((compval ts  (memory( ts)!i) glb ) \<le> (compval ts  (memory( ts)!j) glb ) ))"
 and "vbounded ts"
and "mem_structured ts"
and "  step t ( Store  x v ) ts ts'" 
and "x \<noteq> glb"
shows   "(  \<forall> i j  . 0 < j \<and>  j < length(memory ts')  \<and> 0  \<le> i \<and>  i < length(memory ts')  \<and>  i \<le> j \<and>  comploc ((memory ts')!j) glb = glb   \<and>   comploc ((memory ts')!i) glb = glb   \<longrightarrow> ((compval ts'  (memory( ts')!i) glb ) \<le> (compval ts'  (memory( ts')!j) glb ) ))"
  using assms

  apply (simp add: step_def)
apply (subgoal_tac "  (comploc (memory(ts')!(length (memory ts)))glb  \<noteq> glb ) ")
   prefer 2
   apply (metis assms(4) assms(5) last_entry_bounded length_greater_0_conv loc_eq_comploc mem_structured_def st_lastEntry_lc st_loc store_wfs vbounded_preserved)
  apply (subgoal_tac " mem_structured ts' ")
   prefer 2
  using store_wfs apply blast
  apply (subgoal_tac " \<forall> z. survived_val ts z = survived_val ts' z ")
   prefer 2
  using assms(4) survived_val_preserved_store apply blast
  apply (unfold mem_structured_def)
  by (smt (z3) comploc_def length_append_singleton length_greater_0_conv less_Suc_eq_0_disj less_Suc_eq_le mem_l nless_le store_add zero_less_Suc)




corollary  st_sset_lc:
  assumes "mem_structured ts"
  and "t \<noteq> t'"
  and "step t ( Store x v) ts ts'"
 and "vbounded ts"
shows" [x]\<^sub>t' ts' \<supseteq>  [x]\<^sub>t' ts  "
  using assms assms
  by (metis Un_upper1 st_ov_dt_lc)


lemma  st_wfs_preserved :
  assumes "total_wfs ts"
  and "step t ( Store x v) ts ts'"
shows" total_wfs ts'   "
  using assms   
  apply (simp add: total_wfs_def)
  apply (intro conjI)
  using vbounded_preserved apply blast
  using mem_structured_preserved apply blast
  using OTSF_notempty_preserved total_OTSF_def apply auto[1]
  by (metis assms(1) assms(2) coh_loc_rel_def coh_loc_rel_preserved comploc_def lastVal_def le_in_oats le_in_opts le_in_ots lev_in_oav lev_in_opv opv_opts_rel total_wfs_def valOf_def)



lemma  reg_coh_dt_ni :
  assumes  "step t ( Store x v) ts ts'"
and " total_wfs ts"
and "t \<noteq> t'"
shows"  coh (ts') t' a =  coh (ts) t'  a"
  using assms
  apply (simp add: step_def)
  by (simp add: store_trans_def)



lemma  st_coh_notin_ots_dt:
assumes "total_wfs ts"
  and "step t ( Store x v) ts ts'"
and "t \<noteq> t' "
shows "  coh (ts') t' a \<noteq> (length (memory ts') -1) "
  using assms
  apply (simp add:  step_def total_wfs_def )
  apply (simp add: store_trans_def)
  apply (simp add: vbounded_def)
  by (metis order_less_irrefl)


lemma st_le_lim_dt_ni:
assumes " step t ( Store x v) ts ts'"
and " total_wfs ts"
and " t \<noteq> t' "
shows " last_entry_lim (ts') b (coh (ts') t' glb) =  last_entry_lim (ts) b (coh (ts) t' glb)"
  using assms
  apply (unfold total_wfs_def)
  apply (simp add: step_def)
  apply (subgoal_tac "  length (memory ts ) =  length (memory ts' ) - 1 ")
    prefer 2
   apply (simp )
  apply (subgoal_tac " memory ts' = memory ts @ [msg x v t]")
  prefer 2
  using store_add apply blast
   apply (subgoal_tac " (coh (ts') t' glb) = (coh (ts) t' glb)")
  prefer 2
  using assms(1) assms(2) reg_coh_dt_ni apply presburger
   apply (subgoal_tac " \<forall>i. 0 \<le> i \<and> i < length (memory ts ) \<longrightarrow> (memory ts)!i = (memory ts')!i ")
  prefer 2
  apply (metis nth_append)
   apply (subgoal_tac " (coh (ts') t' glb) <  length (memory ts )")
    prefer 2
  apply (subgoal_tac " vbounded ts' ")
  prefer 2
  using assms(1) vbounded_preserved apply blast
  apply (unfold vbounded_def)
  apply metis
   apply (unfold   last_entry_lim_def)
  apply (simp(no_asm) add: last_entry_set_lim_def)
   apply (subgoal_tac " mem_structured ts' ")
    prefer 2
  using store_wfs apply presburger
   apply (unfold  mem_structured_def)
  by (smt (z3) Collect_cong Suc_diff_1 length_greater_0_conv less_Suc0 less_Suc_eq less_Suc_eq_le not_less_eq)



lemma st_coh_valof_dt_ni:
assumes " step t ( Store x v) ts ts'"
and " total_wfs ts"
and " t \<noteq> t' "
shows " valOf (coh ts' t' glb)  b ts' = valOf   (coh ts t' glb) b ts"
  using assms
  apply (unfold total_wfs_def)
  apply (subgoal_tac " (coh ts t' glb)  = (coh ts' t' glb)  ")
  prefer 2
  apply (simp add: assms(2) reg_coh_dt_ni)
 apply (subgoal_tac " \<forall>i. 0 \<le> i \<and> i < length (memory ts ) \<longrightarrow> (memory ts)!i = (memory ts')!i ")
  prefer 2
  using mem_l_step apply blast
 apply (unfold vbounded_def)
   apply (subgoal_tac " (coh (ts) t' glb) <  length (memory ts )")
   prefer 2
  apply blast
  apply (simp add: valOf_def)
  using survived_val_preserved_store by presburger



lemma st_le_coh_valof_dt_ni:
assumes " step t ( Store x v) ts ts'"
and " total_wfs ts"
and " t \<noteq> t' "
shows " valOf (last_entry_lim ts b (coh ts t' glb)) b ts = 
valOf (last_entry_lim ts'  b (coh ts' t' glb)) b ts'"
  using assms
  apply (unfold total_wfs_def)
  apply (subgoal_tac " last_entry_lim (ts') b (coh (ts') t' glb) =  last_entry_lim (ts) b (coh (ts) t' glb)")
   prefer 2
  using assms(2) st_le_lim_dt_ni apply blast

 apply (subgoal_tac " \<forall>i. 0 \<le> i \<and> i < length (memory ts ) \<longrightarrow> (memory ts)!i = (memory ts')!i ")
  prefer 2
  using mem_l_step apply blast

  apply (subgoal_tac " last_entry_lim (ts) b (coh (ts) t' glb) < length(memory ts) ")
  prefer 2
  using last_entry_lim_bounded apply blast


 apply (subgoal_tac " \<forall>i. 0 \<le> i \<and> i < length (memory ts ) \<longrightarrow> valOf i
     glb ts' = valOf i  glb ts ")
   prefer 2
  apply (unfold valOf_def)
  apply (metis compval_def survived_val_preserved_store)
  by (simp add: survived_val_preserved_store)


lemma st_vrnew_dt_ni:
assumes " step t ( Store x v) ts ts'"
and " total_wfs ts"
and " t \<noteq> t' "
shows " vrnew ts' t'  = vrnew ts t'"
  using assms
  by (simp add: step_def store_trans_def)




lemma st_lv__daddr_ni:
assumes " step t ( Store x v) ts ts'"
and " total_wfs ts"
and "x \<noteq> y"
shows  "lastVal y (ts') = lastVal y (ts) "
  using assms
  apply (simp add: total_wfs_def)
  apply (subgoal_tac " last_entry ts' y =last_entry ts y ")
   prefer 2
   apply (simp add: step_def)
  using st_last_entry_daddr_preserved apply presburger
  apply (unfold lastVal_def)
  by (metis st_valOf_dt_ni valOf_def)

lemma st_comploc_daddr_ni:
assumes " step t ( Store x v) ts ts'"
and " total_wfs ts"
and "x \<noteq> y"
shows "(\<forall> n . (0 \<le> n \<and> n < length(memory ts' ) \<and> comploc ((memory (ts'))!n) y = y ) \<longrightarrow>  comploc ((memory (ts))!n) y = y ) "
  using assms
 using assms
  apply (unfold total_wfs_def)
 apply (subgoal_tac  "(\<forall>i.(i\<ge>0\<and>i<length(memory (ts) )) \<longrightarrow> ( memory (ts'))!i =( memory (ts))!i) ") 
   prefer 2
  apply (metis mem_l_step)
  apply (subgoal_tac "  length(memory ts' ) =  length(memory ts ) +1" )
prefer 2
  using st_mem_length apply presburger
  apply (subgoal_tac " comploc ((memory (ts'))!length(memory (ts) )) y   \<noteq> y ")
  prefer 2
  apply (metis i_noteqo_loc last_entry_bounded less_add_one less_nat_zero_code mem_structured_preserved not_gr_zero st_loc)
 apply (subgoal_tac  "(\<forall>i.(i\<ge>0\<and>i<length(memory (ts) )) \<longrightarrow> comploc  ((memory (ts')) !i)  y =comploc  ((memory (ts))!i)  y  ) ") 
   prefer 2
   apply presburger
  by (metis add_le_imp_le_right discrete le_neq_implies_less)


(* (compval (\<tau> cs') (memory (\<tau> cs') ! n) glb*)

lemma st_compval_daddr_ni:
assumes " step t ( Store x v) ts ts'"
and " total_wfs ts"
and "x \<noteq> y"
shows "(\<forall> n . (0 \<le> n \<and> n < length(memory ts' ) \<and> comploc ((memory (ts'))!n) y = y   ) \<longrightarrow> compval ( ts') (memory ( ts') ! n) y  =   compval ( ts) (memory ( ts) ! n) y   ) "
  using assms
  apply (unfold total_wfs_def)
 apply (subgoal_tac  "(\<forall>i.(i\<ge>0\<and>i<length(memory (ts) )) \<longrightarrow> ( memory (ts'))!i =( memory (ts))!i) ") 
   prefer 2
  apply (metis mem_l_step)
  apply (subgoal_tac "  length(memory ts' ) =  length(memory ts ) +1" )
prefer 2
  using st_mem_length apply presburger

 apply (subgoal_tac  "(\<forall>i.(i\<ge>0\<and>i<length(memory (ts) )) \<longrightarrow> compval ( ts) (memory ( ts) ! i) y =compval (ts') (memory ( ts') ! i) y  ) ") 
  prefer 2
   apply simp
  using survived_val_preserved_store apply presburger
  by (metis add_le_imp_le_right discrete i_noteqo_loc last_entry_bounded le_neq_implies_less less_nat_zero_code mem_structured_preserved st_loc)








lemma st_lelim_daddr_ni:
assumes " step t ( Store x v) ts ts'"
and " total_wfs ts"
and "x \<noteq> y"
shows "(\<forall> n l. (0 \<le> n \<and> n < length(memory ts )\<and>  comploc ((memory (ts'))!n) y= y) \<longrightarrow> valOf (last_entry_lim ts' l n) l (ts')  =    valOf (last_entry_lim ts l n) l ts  ) "
  using assms
  apply (unfold total_wfs_def)
 apply (subgoal_tac  "(\<forall>i.(i\<ge>0\<and>i<length(memory (ts) )) \<longrightarrow> ( memory (ts'))!i =( memory (ts))!i) ") 
   prefer 2
  apply (metis mem_l_step)
  apply (unfold  last_entry_lim_def)
  apply clarify
  apply (subgoal_tac " (last_entry_set_lim (ts') l n)  =  (last_entry_set_lim (ts) l n)")
   prefer 2
   apply (simp(no_asm)  add:   last_entry_set_lim_def)
  apply (metis (no_types, lifting) Collect_cong dual_order.strict_trans last_entry_bounded le_neq_implies_less less_nat_zero_code mem_structured_preserved nle_le st_lastEntry_lc vbounded_preserved)
  apply (simp(no_asm) add: valOf_def)
  by (metis bot_nat_0.extremum last_entry_lim_bounded last_entry_lim_def survived_val_preserved_store)



lemma st_lv_lim_eq_lv  :
   assumes "mem_structured ts"
  and "vbounded ts"
  and " step t ( Store x v) ts ts'"
shows "  (last_entry_lim (ts') l (length (memory ts)) )   =  last_entry (ts') l    "
  using assms 
    apply (simp add: step_def)
  apply (subgoal_tac " length (memory ts' ) = length (memory ts) + 1 ")
   prefer 2
   apply simp
 apply (subgoal_tac " \<forall>i. 0 \<le> i \<and> i < length (memory ts ) \<longrightarrow> (memory ts)!i = (memory ts')!i ")
  prefer 2
  using mem_l apply blast
  apply (case_tac " x = l ")
   apply (subgoal_tac "  (last_entry_lim (ts') l (length (memory ts)) )  =  (length (memory ts))  ")
  prefer 2
  apply (unfold last_entry_lim_def )
    apply (subgoal_tac " length (memory ts) \<in>  (last_entry_set_lim ts' l (length (memory ts)))")
     prefer 2
     apply (subgoal_tac " comploc (memory ts' !  (length (memory ts))) l = l ")
      prefer 2
  using assms(3) comploc_def st_loc apply presburger
  apply (simp(no_asm) add:  last_entry_set_lim_def )
  using last_entry_set_lim_not_empty  last_entry_lim_bounded finite_last_entry_set_lim
  apply (metis assms(3) less_add_one st_loc)
   apply (subgoal_tac " last_entry ts' l =  (length (memory ts)) ")
  prefer 2
   apply (subgoal_tac " length (memory ts) \<in>  (last_entry_set ts' l )")
     prefer 2
     apply (subgoal_tac " comploc (memory ts' !  (length (memory ts))) l = l ")
      prefer 2
  using assms(3) comploc_def st_loc apply presburger
      apply (metis assms(1) assms(2) assms(3) last_entry_in_last_entry_set mem_structured_preserved st_lastEntry_lc vbounded_preserved)
  using assms(3) st_lastEntry_lc apply blast
  using last_entry_set_lim_not_empty  last_entry_lim_bounded finite_last_entry_set_lim last_entry_set_lim_def
  apply (smt (verit, del_insts) Max_eqI mem_Collect_eq)
  using assms(3) st_lastEntry_lc apply presburger
  apply (subgoal_tac " last_entry ts' l = last_entry ts l ")
     prefer 2
  using st_last_entry_daddr_preserved apply blast
  apply (subgoal_tac " (last_entry_set_lim ts' l (length (memory ts)))  =
(last_entry_set_lim ts l (length (memory ts)))  ")
   prefer 2
  apply (subgoal_tac " comploc (memory ts' !  (length (memory ts))) l \<noteq>  l ")
    prefer 2
  apply (metis antisym_conv3 assms(3) i_noteqo_loc last_entry_lim_bounded less_add_one less_nat_zero_code st_loc store_wfs)
   apply (unfold last_entry_set_lim_def)
    apply (metis (no_types, lifting) Suc_eq_plus1 le_imp_less_Suc nat_less_le)
  apply (unfold last_entry_def last_entry_set_def)
  using Suc_eq_plus1 less_Suc_eq_le by presburger


lemma st_succ_lv_lim_eq_lv_val  :
   assumes "mem_structured ts"
  and "vbounded ts"
  and " step t ( Store x v) ts ts'"
shows " valOf   (last_entry_lim (ts') l (length (memory ts)) ) l  ts'    =  lastVal l ts'  "
  using assms
  by (simp add: lastVal_def st_lv_lim_eq_lv valOf_def)



lemma  st_valOf_nle_ni:
   assumes "mem_structured ts"
  and "vbounded ts"
   and " step t ( Store x v) ts ts'"
shows "(\<forall> n l. (0 \<le> n \<and> n < length(memory ts )) \<longrightarrow> valOf (n) l (ts')  =    valOf ( n) l ts  ) "
  using assms
  by (simp add: mem_l_step survived_val_preserved_store valOf_def)


lemma  st_succ_lelim_nle_ni:
   assumes "mem_structured ts"
  and "vbounded ts"
   and " step t ( Store x v) ts ts'"
shows "(\<forall> n l. (0 \<le> n \<and> n < length(memory ts )) \<longrightarrow> valOf (last_entry_lim ts' l n) l (ts')  =    valOf (last_entry_lim ts l n) l ts  ) "
  using assms 
  apply (subgoal_tac " length (memory ts' ) = length (memory ts) + 1 ")
   prefer 2
 apply (metis Nat.add_0_right One_nat_def add_Suc_right st_mem_length)
 apply (subgoal_tac " \<forall>i. 0 \<le> i \<and> i < length (memory ts ) \<longrightarrow> (memory ts)!i = (memory ts')!i ")
    prefer 2
  using mem_l_step apply blast
  apply clarify
  apply (subgoal_tac " last_entry_lim ts l n = last_entry_lim ts' l n ")
  apply (metis last_entry_lim_bounded le0 st_valOf_nle_ni)
   apply (unfold last_entry_lim_def)
   apply (unfold last_entry_set_lim_def)
  by (metis (no_types, lifting)  add.commute order.strict_trans1 trans_less_add2)

(*

lemma st_lastentry_eq_length:
  assumes  " ts [x := a]\<^sub>t  ts' "
and " total_wfs ts"
shows " last_entry  (ts') x  = length (memory ts' ) - 1 "
  using assms
  apply (unfold total_wfs_def)

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
     apply linarith
  apply (metis (no_types, opaque_lifting) One_nat_def Suc_eq_plus1 diff_Suc_1 le_eq_less_or_eq le_less_Suc_eq st_loc st_mem_length)
  apply (metis Nat.add_0_right One_nat_def add_Suc_right assms(1) diff_Suc_Suc minus_nat.diff_0 st_loc st_mem_length)
  by (simp add: st_lastEntry_lc st_mem_length)

*)















end
 

