theory Wellformedness 
  imports "Language" "Assertions"

begin


(*  Wellformedness for  the memory *)
definition "mem_structured ts  \<equiv> memory ts \<noteq> [] \<and> (memory ts !0)=Init_Msg \<and>
                                  (\<forall>i.(i>0\<and>i<length(memory ts))\<longrightarrow>(memory ts !i)\<noteq>Init_Msg)"


lemma loc_eq_comploc:
  assumes "mem_structured ts"
  shows " (\<forall>i. 0 < i \<and> i < length (memory ts) \<longrightarrow> ( comploc ((memory ts)!i) x) = loc  ((memory ts)!i)) "
  using assms
  by (simp add: mem_structured_def)



lemma val_eq_compval:
  assumes "mem_structured ts"
  shows " (\<forall>i. 0 < i \<and> i < length (memory ts) \<longrightarrow> ( compval   ts ((memory ts)!i) x) = val ((memory ts)!i)) "
  using assms
  by (simp add: mem_structured_def)



lemma comploc_ots:
  assumes " i \<in> (OTS  ts' t glb)"
  shows"  comploc  ((memory ts') !i) glb  = glb "
  using assms
  apply (unfold OTS_def)
  by (simp add: OTSF_def)




lemma st_wfs_m:
  assumes "start ts" 
  shows "mem_structured ts"
  using assms apply (simp add: mem_structured_def)
  apply(subgoal_tac "length(memory ts) = 1") prefer 2
   apply (simp add: start_size)
  apply(subgoal_tac " memory ts = [Init_Msg]") prefer 2
  using assms apply (simp add: start_def)
  by auto

lemma mem_l:
 assumes  "ts' = store_trans ts x v t"
    shows "(\<forall>i.(i\<ge>0\<and>i<length(memory ts)) \<longrightarrow> ( memory ts)!i =( memory ts')!i) "
  using assms  apply ( simp add:  mem_structured_def store_trans_def)
  by (simp add: nth_append)



lemma mem_l_casucc:
 assumes  "ts' = (cas_succ_trans ti ind x v1 v2 r nv1 nv2 ts)"
    shows "(\<forall>i.(i\<ge>0\<and>i<length(memory ts)) \<longrightarrow> ( memory ts)!i =( memory ts')!i) "
  using assms  apply ( simp add:  mem_structured_def store_trans_def)
  by (simp add: nth_append)

lemma store_wfs:
 assumes "mem_structured  ts"
 shows " mem_structured   ( store_trans ts x v t)"
  using assms  apply ( simp add:  mem_structured_def  store_trans_def )
 using assms   apply(subgoal_tac " (\<forall>i.(i\<ge>0\<and>i<length(memory ts)) \<longrightarrow> ( memory ts)!i =( memory ( store_trans ts x v t)!i))")
  prefer 2 
  using mem_l apply blast
    apply ( simp add: store_trans_def)
  apply (rule conjI)
   apply (metis length_greater_0_conv)
  by (metis Msg.distinct(1) less_antisym  nth_append_length)

lemma cas_succ_wfs:
 assumes "mem_structured  ts"
 shows " mem_structured   ( cas_succ_trans ti ind x v1 v2 r nv1 nv2  ts)"
  using assms  apply ( simp add:  mem_structured_def  ) 
  apply(subgoal_tac " (\<forall>i.(i\<ge>0\<and>i<length(memory ts)) \<longrightarrow> ( memory ts)!i =( memory ( cas_succ_trans ti ind x v1 v2 r nv1 nv2 ts)!i))")
   prefer 2
  using mem_l_casucc
   apply meson
   apply force
  apply (simp add: cas_succ_trans_def)
  by (metis Msg.distinct(1) length_0_conv less_SucE less_Suc_eq_0_disj nth_append_length)


lemma mem_structured_preserved:
  assumes "mem_structured ts"
      and "step t a ts ts'"
    shows " mem_structured  ts'"
 apply(rule step_cases)
  using assms apply (simp add: mem_structured_def )
       apply (subgoal_tac " memory ts = memory ts' ")
        prefer 2
        apply simp
       apply (simp add: mem_structured_def)
  using assms(1) mem_structured_def apply auto[1]
      apply (simp add: assms(1) store_wfs)
     apply (simp add: mem_structured_def)
  using assms(1) mem_structured_def apply auto[1]
  apply (simp add: mem_structured_def)
  using assms(1) mem_structured_def apply auto[1]
 apply (simp add: mem_structured_def)
  using assms(1) mem_structured_def apply auto[1]
 apply (simp add: mem_structured_def)
  using assms(1) mem_structured_def
    apply auto[1]
   apply (simp add: assms(1) cas_succ_wfs)
 apply (subgoal_tac " memory ts = memory ts' ")
        prefer 2
        apply simp
  apply (simp add: mem_structured_def)
  using assms(1) mem_structured_def by auto[1]






(*Wellformedness for views*)
definition 
"vbounded ts  \<equiv>
(\<forall> ti addr. 0 \<le> vrnew ts ti \<and> vrnew ts ti  <  length (memory ts)\<and>
            0 \<le> vpready ts ti \<and>vpready ts ti <  length (memory ts) \<and>
            0 \<le> coh ts ti addr \<and>  coh ts ti addr <  length (memory ts) \<and>
            0 \<le>  vpasync ts ti addr \<and>  vpasync ts ti addr <  length (memory ts) \<and>
            0 \<le>  vpcommit ts ti addr \<and>  vpcommit ts ti addr <  length (memory ts) \<and>
            0 \<le>  maxcoh ts ti \<and>  maxcoh ts ti < length (memory ts) \<and>
            0 \<le>  maxvp ts addr  \<and> maxvp ts addr  < length (memory ts) \<and> 
            coh ts ti addr \<le> maxcoh  ts ti \<and>
            vpcommit ts ti addr \<le> maxvp ts addr \<and>
            vrnew ts ti \<le>  maxcoh ts ti \<and> 
            vrnew ts ti \<le>  vpready ts ti
     ) " 


lemma  initial_vbounded:
 assumes "start ts" 
 shows "vbounded ts"
  apply (simp add: start_def vbounded_def)
  using assms start_def by auto

(*Some auxiliary functions*)
lemma store_add:
 " memory ( store_trans ts x v t) = memory ts @ [msg x v t]"
  apply ( simp add: store_trans_def )
  done

lemma maxvp_load:
  assumes "vbounded ts "
shows " \<forall> addr.  maxvp (load_trans t ind x ts r) addr  < length (memory (load_trans t ind x ts r))"
  using assms
  apply( simp add: load_trans_def)
  apply (case_tac " ind = coh ts t x ")
   apply (simp add:vbounded_def)
  apply (simp add:vbounded_def)
  done



lemma vbounded_preserved:
  assumes "vbounded ts"
      and "step t a ts ts'"
    shows " vbounded ts'"
 apply(rule step_cases)
  using assms apply (simp add: vbounded_def )
       apply (unfold vbounded_def)
(*LOAD*)
   apply (subgoal_tac "  \<forall>ti addr. coh (load_trans t ind x ts r) ti addr
          < length (memory (load_trans t ind x ts r))")
        prefer 2
  apply clarify
      apply (case_tac "ti = t")
         apply (case_tac "addr = x")
          apply(simp add: load_trans_def)
          apply (case_tac "ind \<noteq> coh ts t x")
           apply (simp add: OTSF_def OTS_def)
  using assms(1) dual_order.strict_implies_order vbounded_def apply blast
         apply (simp add: load_trans_def) 
  using assms(1) dual_order.strict_implies_order vbounded_def apply blast
        apply (simp add: load_trans_def) 
  using assms(1) dual_order.strict_implies_order vbounded_def apply blast
 apply (subgoal_tac" \<forall>ti .
          vrnew (load_trans t ind x ts r) ti
          < length
              (memory (load_trans t ind x ts r)) ")
       prefer 2
  apply clarify
        apply (case_tac "ti = t")
         apply(simp add: load_trans_def Let_def) 
         apply(case_tac "ind = coh ts t x")
  apply simp 
  using assms(1) vbounded_def apply blast
  apply simp
         apply (rule conjI)
  using assms(1) dual_order.strict_implies_order vbounded_def apply blast

  using OTSF_def OTS_def apply blast
       (*  apply (metis (full_types) fun_upd_same)*)
        apply(simp add: load_trans_def)
  using assms(1) vbounded_def apply blast


  apply (subgoal_tac " \<forall> ti addr.   coh (load_trans t ind x ts r) ti addr
          \<le> maxcoh (load_trans t ind x ts r) ti")
        prefer 2
        apply clarify
         apply (case_tac "ti = t")
         apply(simp add: load_trans_def Let_def) 
         apply(case_tac "ind = coh ts t x")
          apply simp
  using assms(1) max.coboundedI1 vbounded_def apply blast
  using assms(1) max.coboundedI1 vbounded_def apply blast
        apply(simp add: load_trans_def Let_def)
  using assms(1) vbounded_def apply blast
  apply (subgoal_tac " \<forall> addr.  maxvp (load_trans t ind x ts r) addr
          < length (memory (load_trans t ind x ts r)) ")
   prefer 2
  using maxvp_load[where t=t and  ts=ts ] and assms(1)
        apply simp
  apply (subgoal_tac " \<forall> ti addr. vpcommit (load_trans t ind x ts r) ti addr
          \<le> maxvp (load_trans t ind x ts r) addr")
        prefer 2
    apply clarify
         apply (case_tac "ti = t")
  using assms(1) apply (simp add: load_trans_def Let_def)
  apply(case_tac "ind = coh ts t x")
  using assms(1) apply (simp add: vbounded_def)
  using assms(1) apply (simp add: vbounded_def)
  using assms(1) apply (simp add: load_trans_def Let_def)
   apply(case_tac "ind = coh ts t x")
  using assms(1) apply (simp add: vbounded_def)
  using assms(1) apply (simp add: vbounded_def)
  apply (subgoal_tac "\<forall> ti addr.  maxcoh (load_trans t ind x ts r) ti
                < length (memory ts) ")
  prefer 2
   apply clarify
         apply (case_tac "ti = t")
  using assms(1) apply (simp add: load_trans_def Let_def)
  apply(case_tac "ind = coh ts t x")
          apply (rule conjI)
  using assms(1) apply (simp add: vbounded_def)
  using assms(1) apply (simp add: vbounded_def)
   apply (rule conjI)
  using assms(1) apply (simp add: vbounded_def)
  using assms(1) apply (simp add: vbounded_def )
         apply (simp add: OTS_def OTSF_def)
  using assms(1) apply (simp add: vbounded_def load_trans_def)
  apply simp


apply (subgoal_tac" \<forall>ti .
          vpready (load_trans t ind x ts r) ti
          < length
              (memory (load_trans t ind x ts r)) ")
       prefer 2
  apply clarify
        apply (case_tac "ti = t")
         apply(simp add: load_trans_def Let_def) 
         apply(case_tac "ind = coh ts t x")
  apply simp 
  using assms(1) vbounded_def apply blast
  apply simp
         apply (rule conjI)
  using assms(1) dual_order.strict_implies_order vbounded_def apply blast
       (*  apply (metis (full_types) fun_upd_same)*)
  apply (smt max_less_iff_conj)
        apply(simp add: load_trans_def)
  using assms(1) vbounded_def apply blast

  apply (subgoal_tac "\<forall> ti addr. vpasync (load_trans t ind x ts r) ti addr
                < length (memory ts)")
        prefer 2
        apply(simp add: load_trans_def Let_def)
  apply clarify
   apply (case_tac "ti = t")
         apply(simp add: load_trans_def Let_def) 
         apply(case_tac "ind = coh ts t x")
  apply (simp add: load_trans_def Let_def)
  using assms(1) vbounded_def apply blast
  using assms(1) vbounded_def apply blast
  using assms(1) vbounded_def apply blast
       apply simp

  apply (subgoal_tac "\<forall> ti addr. vpcommit (load_trans t ind x ts r) ti addr
                < length (memory ts)")
        prefer 2
        apply(simp add: load_trans_def Let_def)
  apply clarify
   apply (case_tac "ti = t")
         apply(simp add: load_trans_def Let_def) 
         apply(case_tac "ind = coh ts t x")
  apply (simp add: load_trans_def Let_def)
  using assms(1) vbounded_def apply blast
  using assms(1) vbounded_def apply blast
  using assms(1) vbounded_def apply blast
 apply simp

  apply (subgoal_tac "   \<forall>ti. vrnew (load_trans t ind x ts r) ti
            \<le> maxcoh (load_trans t ind x ts r) ti")
        prefer 2
 apply(case_tac "ind = coh ts t x")
         apply (simp add: load_trans_def Let_def)
  apply clarify
         apply (case_tac " ti = t")
          apply simp
          apply (subgoal_tac "vrnew ts t \<le> maxcoh ts t")
           prefer 2
  using assms(1) vbounded_def apply blast
  using max.coboundedI1 apply blast
    apply simp
  using assms(1) vbounded_def apply blast

        apply (simp add: load_trans_def Let_def)
 apply clarify
         apply (case_tac " ti = t")
          apply simp
          apply (subgoal_tac "vrnew ts t \<le> maxcoh ts t")
           prefer 2
  using assms(1) vbounded_def apply blast
  using max.coboundedI1 apply blast
    apply simp
  using assms(1) vbounded_def apply blast
       apply simp
  apply (subgoal_tac "\<forall>ti. vrnew (load_trans t ind x ts r) ti
            \<le> vpready (load_trans t ind x ts r) ti")
        prefer 2
        apply clarify
        apply (case_tac "ti = t")
         apply (simp add: load_trans_def)
 (*        apply (case_tac "ind = coh ts t x")
          apply simp *)
  apply (subgoal_tac " vrnew ts t \<le> vpready ts t")
          prefer 2
  using assms(1) apply (simp add: vbounded_def)
  using le_max_iff_disj apply blast
        apply (subgoal_tac " vrnew ts' ti = vrnew ts ti")
         prefer 2
         apply (simp add: load_trans_def)
 apply (subgoal_tac " vpready ts' ti = vpready ts ti")
         prefer 2
         apply (simp add: load_trans_def)
  apply simp
  using assms(1) vbounded_def apply blast
  apply simp

(*STORE*)
 apply (subgoal_tac " \<forall> ti addr.  coh (store_trans ts x v t) ti addr
              < length
                  (memory (store_trans ts x v t))")
  prefer 2
  apply clarify
       apply (case_tac "ti = t")
        apply(simp add: store_trans_def Let_def)
        apply clarify 
  using assms(1) less_SucI vbounded_def apply blast
 apply(simp add: store_trans_def Let_def)
  using assms(1) less_SucI vbounded_def apply blast
  apply ( subgoal_tac " \<forall> ti addr. vpcommit (store_trans ts x v t) ti addr
              < length (memory (store_trans ts x v t))")
  prefer 2
       apply(simp add: store_trans_def Let_def)
  using assms(1) less_SucI vbounded_def apply blast
  apply (subgoal_tac " \<forall> ti addr.  coh (store_trans ts x v t) ti addr
              \<le> maxcoh (store_trans ts x v t) ti ")
       prefer 2
    apply clarify
         apply (case_tac "ti = t")
        apply(simp add: store_trans_def Let_def)
  using assms(1) nat_less_le vbounded_def apply blast

       apply(simp add: store_trans_def Let_def)
  using assms(1) vbounded_def apply blast

  apply (subgoal_tac "\<forall> ti.  vrnew (store_trans ts x v t) ti
              \<le> maxcoh (store_trans ts x v t) ti")
  prefer 2
       apply(simp add: store_trans_def Let_def)
  apply clarify
       apply (case_tac "ti = t")
        apply simp
  using assms  apply (simp add: vbounded_def)
  using less_imp_le_nat apply blast
       apply simp
  using assms  apply (simp add: vbounded_def)
apply(simp add: store_trans_def Let_def)
  using assms(1) less_SucI vbounded_def apply blast

(*FLUSH*)

 apply (subgoal_tac " \<forall>ti addr. vpcommit (flush_trans t x ts) ti addr
            < length (memory (flush_trans t x ts))")
      prefer 2
      apply (simp add: flush_trans_def Let_def)
  apply clarify
      apply (case_tac "ti = t")
       apply simp
       apply clarify
       apply (case_tac "addr = x")
        apply simp
        apply (rule conjI)
  using assms(1) vbounded_def apply blast
  using assms(1) vbounded_def apply blast
       apply simp
  using assms(1) vbounded_def apply blast
      apply simp
  using assms(1) vbounded_def apply blast

 apply (subgoal_tac " \<forall>ti addr. vpasync (flush_trans t x ts) ti addr
            < length (memory (flush_trans t x ts))")
      prefer 2
      apply (simp add: flush_trans_def Let_def)
  apply clarify
      apply (case_tac "ti = t")
       apply simp
       apply clarify
       apply (case_tac "addr = x")
        apply simp
        apply (rule conjI)
  using assms(1) vbounded_def apply blast
  using assms(1) vbounded_def apply blast
       apply simp
  using assms(1) vbounded_def apply blast
      apply simp
  using assms(1) vbounded_def apply blast


  apply ( subgoal_tac "\<forall>addr.  maxvp (flush_trans t x ts) addr
            < length (memory (flush_trans t x ts))")
      prefer 2
      apply (simp add: flush_trans_def Let_def)
  apply clarify
      apply (case_tac" addr = x")
  apply simp
       apply (rule conjI)
  using assms(1) vbounded_def apply blast
  apply (rule conjI)
  using assms(1) vbounded_def apply blast
  using assms(1) vbounded_def apply blast
  apply simp
  using assms(1) vbounded_def apply blast
     apply simp
  apply (subgoal_tac "\<forall> ti addr.   vpcommit (flush_trans t x ts) ti addr
                  \<le> maxvp (flush_trans t x ts) addr")
    prefer 2
      apply (simp add: flush_trans_def Let_def)
  apply clarify
      apply (case_tac" ti = t")
       apply simp
  using assms(1) vbounded_def apply blast
      apply simp
  apply clarify
      apply (case_tac " ti = t")
  apply simp
      apply (rule conjI)
       apply (simp add: flush_trans_def)
       apply (subgoal_tac " vpcommit ts ti addr \<le> maxvp ts addr")
        prefer 2
  using assms(1) vbounded_def apply blast
  using max.coboundedI2 apply blast
  using assms(1) vbounded_def apply blast
     apply simp

  apply (subgoal_tac " \<forall> ti addr.  maxcoh (flush_trans t x ts) ti
                  < length (memory ts) ")
      prefer 2
      apply (simp add: flush_trans_def Let_def)
  using assms(1) vbounded_def apply blast
     apply simp
  apply (subgoal_tac " \<forall> ti addr.   coh (flush_trans t x ts) ti addr
                  < length (memory ts) ")
    prefer 2
      apply (simp add: flush_trans_def Let_def)
  using assms(1) vbounded_def apply blast
  apply simp
  apply (subgoal_tac" \<forall>ti addr. coh (flush_trans t x ts) ti addr
                  \<le> maxcoh (flush_trans t x ts) ti")
   prefer 2
      apply (simp add: flush_trans_def Let_def)
  using assms(1) vbounded_def apply blast
     apply simp
  apply (subgoal_tac "  \<forall>ti. vrnew (flush_trans t x ts) ti
              < length (memory ts) ")
  prefer 2
      apply (simp add: flush_trans_def Let_def)
  using assms(1) vbounded_def apply blast
  apply simp

 apply (subgoal_tac "  \<forall>ti. vpready (flush_trans t x ts) ti
              < length (memory ts) ")
  prefer 2
      apply (simp add: flush_trans_def Let_def)
  using assms(1) vbounded_def apply blast
     apply simp

apply (subgoal_tac "  \<forall>ti. vrnew (flush_trans t x ts) ti
              \<le> maxcoh (flush_trans t x ts) ti ")
      prefer 2
   apply (simp add: flush_trans_def Let_def)
  using assms(1) vbounded_def apply blast
     apply simp

  apply (subgoal_tac "   \<forall>ti. vrnew (flush_trans t x ts) ti
              \<le> vpready (flush_trans t x ts) ti")
      prefer 2
   apply (simp add: flush_trans_def Let_def)
  using assms(1) vbounded_def apply blast
     apply simp




(*FLUSHOPT*)
apply (subgoal_tac"\<forall> ti addr. vpasync (flush_opt_trans t x ts) ti addr
         < length (memory (flush_opt_trans t x ts))  ")
     prefer 2
 apply (simp add: flush_opt_trans_def Let_def)
     apply clarify
     apply (case_tac "ti = t")
  using assms(1) vbounded_def apply blast
     apply (simp add: flush_opt_trans_def Let_def)
  using assms(1) vbounded_def apply blast
    apply (simp add: flush_opt_trans_def Let_def)
  using assms(1) vbounded_def apply blast

(*MFENCE*)
 apply (subgoal_tac"\<forall>  ti addr. vpready (mfence_trans t ts) ti
       < length (memory (mfence_trans t ts))  ")
     prefer 2
    apply (simp add: mfence_trans_def Let_def )
  apply clarify
    apply (case_tac "ti = t")
  using assms(1) vbounded_def apply auto[1]
  using assms(1) vbounded_def apply blast 
 apply (subgoal_tac"\<forall>  ti addr. vrnew (mfence_trans t ts) ti
       < length (memory (mfence_trans t ts))  ")
     prefer 2
    apply (simp add: mfence_trans_def Let_def )
  apply clarify
    apply (case_tac "ti = t")
  using assms(1) vbounded_def apply auto[1]
  using assms(1) vbounded_def apply blast
   apply simp
  apply clarify
  apply (subgoal_tac" vrnew (mfence_trans t ts) ti
       \<le> vpready (mfence_trans t ts) ti")
    prefer 2
    apply (simp add: mfence_trans_def)
    apply (case_tac "ti = t")
     apply simp
     apply (subgoal_tac "  vrnew ts t \<le> vpready ts t")
      prefer 2
  using assms(1) vbounded_def apply blast
  using max.coboundedI1 apply blast
  apply (subgoal_tac "  vrnew ts ti \<le> vpready ts ti")
      prefer 2
  using assms(1) vbounded_def apply blast
    apply blast
apply (simp add: mfence_trans_def Let_def)
  using assms(1) vbounded_def apply blast
  

(*SFENCE*)
 apply (subgoal_tac"  \<forall> ti. vpready (sfence_trans t nv1 nv2  ts) ti
              < length  (memory (sfence_trans t nv1 nv2  ts)) ")
   prefer 2
  apply (simp add: vpcommit_nv_def  sfence_trans_def Let_def )
  apply clarify
   apply (case_tac "ti = t")
  using assms(1) vbounded_def apply auto[1]
  using assms(1) vbounded_def apply blast
apply (subgoal_tac"  \<forall> ti addr. vpcommit (sfence_trans t nv1 nv2 ts) ti addr
              < length  (memory (sfence_trans t nv1 nv2 ts))")
  prefer 2
   apply (simp add: vpcommit_nv_def maxvp_nv_def  sfence_trans_def Let_def )
 apply clarify
   apply (case_tac "ti = t")
  using assms(1) vbounded_def apply blast
  using assms(1) vbounded_def apply blast

  apply (subgoal_tac " \<forall> ti addr.  maxvp (sfence_trans t nv1 nv2 ts) addr
          < length (memory (sfence_trans t nv1 nv2 ts)) ")
   prefer 2
   apply (simp add: vpcommit_nv_def maxvp_nv_def  sfence_trans_def Let_def )
   apply clarify
   apply (rule conjI)
  using assms(1) vbounded_def apply blast
   apply (rule conjI)
  using assms(1) vbounded_def apply blast
  using assms(1) vbounded_def apply blast
  apply simp
  apply (subgoal_tac " \<forall> ti addr.  coh (sfence_trans t nv1 nv2 ts) ti addr
                \<le> maxcoh (sfence_trans t nv1 nv2 ts) ti")
   prefer 2
   apply (simp add: vpcommit_nv_def maxvp_nv_def  sfence_trans_def Let_def )
   apply clarify
  using assms(1) vbounded_def apply blast
  apply simp
   apply (subgoal_tac " \<forall> ti addr.  vpcommit (sfence_trans t nv1 nv2 ts) ti
                 addr
                \<le> maxvp (sfence_trans t nv1 nv2 ts) addr")
  prefer 2
   apply (simp add: vpcommit_nv_def maxvp_nv_def  sfence_trans_def Let_def )
   apply clarify
   apply (subgoal_tac " vpcommit ts ti addr \<le> maxvp ts addr")
  prefer 2
  using assms(1) vbounded_def apply blast
   apply simp
  apply simp
  apply (subgoal_tac " \<forall>addr ti.
                coh (sfence_trans t nv1 nv2 ts) ti addr
                < length (memory ts)")
 prefer 2
   apply (simp add: vpcommit_nv_def maxvp_nv_def  sfence_trans_def Let_def )
   apply clarify
  using assms(1) vbounded_def apply blast
  apply (subgoal_tac "\<forall>addr ti.
                vpasync (sfence_trans t nv1 nv2 ts) ti addr
                < length (memory ts)")
 prefer 2
   apply (simp add: vpcommit_nv_def maxvp_nv_def  sfence_trans_def Let_def )
   apply clarify
  using assms(1) vbounded_def apply blast
  apply (subgoal_tac "\<forall>addr ti. maxcoh (sfence_trans t nv1 nv2 ts) ti
                < length (memory ts)")
 prefer 2
   apply (simp add: vpcommit_nv_def maxvp_nv_def  sfence_trans_def Let_def )
   apply clarify
  using assms(1) vbounded_def apply blast
   apply (subgoal_tac "\<forall>addr ti. vrnew (sfence_trans t nv1 nv2 ts) ti
                < length (memory ts)")
 prefer 2
   apply (simp add: vpcommit_nv_def maxvp_nv_def  sfence_trans_def Let_def )
   apply clarify
  using assms(1) vbounded_def apply blast 
  apply simp

  apply (subgoal_tac " \<forall>ti.  vrnew (sfence_trans t nv1 nv2 ts) ti
            \<le> vpready (sfence_trans t nv1 nv2 ts) ti")
   prefer 2
   apply (simp add: sfence_trans_def vpcommit_nv_def maxvp_nv_def)
  apply clarify

  apply (case_tac "ti = t")
     apply simp
     apply (subgoal_tac "  vrnew ts t \<le> vpready ts t")
      prefer 2
  using assms(1) vbounded_def apply blast
  using max.coboundedI1 apply blast
  apply simp
  apply (subgoal_tac "  vrnew ts ti \<le> vpready ts ti")
      prefer 2
  using assms(1) vbounded_def apply blast
    apply blast
  apply simp
  apply (simp add: sfence_trans_def)
  using assms(1) vbounded_def apply  blast

(*cas_succ*)
 apply (subgoal_tac " \<forall> ti addr. vrnew ts ti \<le> vpready ts ti")
    prefer 2
 using assms(1) vbounded_def apply  blast
   apply  clarify
   apply (intro conjI; simp add:cas_succ_trans_def )
  apply (subgoal_tac" \<forall>t. maxcoh ts t <  (length (memory ts))")
                prefer 2
  using assms(1) vbounded_def apply  blast
  apply (subgoal_tac" \<forall>t. vrnew ts t <  (length (memory ts))")
                prefer 2
  using assms(1) vbounded_def apply  blast
  using less_Suc_eq apply blast
  apply (subgoal_tac" \<forall>t. vpready ts t <  (length (memory ts))")
                prefer 2
  using assms(1) vbounded_def apply  blast
 apply (subgoal_tac" \<forall>t. maxcoh ts t <  (length (memory ts))")
                prefer 2
  using assms(1) vbounded_def apply  blast
  using less_Suc_eq apply blast
           apply (subgoal_tac " \<forall> ti addr.  coh ts ti addr < length (memory ts) ")
            prefer 2
  using assms(1) vbounded_def apply  blast
  using less_Suc_eq apply blast
  apply (subgoal_tac " \<forall> ti addr.  vpasync ts ti addr < length (memory ts) ")
            prefer 2
  using assms(1) vbounded_def apply  blast
  using less_Suc_eq apply blast
  apply (subgoal_tac " \<forall> ti addr.  vpcommit ts ti addr < length (memory ts) ")
            prefer 2
  using assms(1) vbounded_def apply  blast




         apply (simp add: vpcommit_nv_def)
         apply (intro conjI impI)
           apply (subgoal_tac "  vpasync ts t addr < (length (memory ts))")
            prefer 2
  using assms(1) vbounded_def[where ts = ts ]
  apply presburger
  using less_Suc_eq apply blast
  using less_Suc_eq apply presburger
  using less_Suc_eq apply blast




 apply (subgoal_tac" \<forall>t. maxcoh ts t <  (length (memory ts))")
                prefer 2
  using assms(1) vbounded_def apply  blast
  using less_Suc_eq apply blast
apply (subgoal_tac" \<forall>t addr. maxvp ts addr <  (length (memory ts))")
                prefer 2
  using assms(1) vbounded_def  maxvp_nv_def  apply  blast

  apply (simp add: maxvp_nv_def) 
  using  maxvp_nv_def   apply (meson less_SucI)
  using  assms(1) vbounded_def[where ts = ts ]
  using less_Suc_eq apply presburger

  using  assms(1) vbounded_def[where ts = ts ]
  using less_Suc_eq apply presburger



      apply (subgoal_tac " \<forall>ti addr. coh ts ti addr \<le> maxcoh ts ti" )
       prefer 2
 using assms(1) vbounded_def apply  blast
     apply (subgoal_tac " \<forall> ti addr.  coh ts ti addr < length (memory ts) ")
            prefer 2
  using assms(1) vbounded_def apply  blast
  using less_imp_le_nat apply presburger
  using assms(1) vbounded_def[where ts = ts ]   maxvp_nv_def
   vpcommit_nv_def
  apply (smt (verit) le_max_iff_disj max.absorb_iff2 max.left_idem)




 (* using assms(1) vbounded_def apply  blast *)

    apply (subgoal_tac "\<forall> ti. vrnew ts ti \<le> maxcoh ts ti")
     prefer 2
  using assms(1) vbounded_def apply  blast
apply (subgoal_tac" \<forall>t addr. maxcoh ts t <  (length (memory ts))")
                prefer 2
  using assms(1) vbounded_def apply  blast
apply (subgoal_tac" \<forall>t addr. vrnew ts addr <  (length (memory ts))")
                prefer 2
  using assms(1) vbounded_def apply  blast
  using less_imp_le_nat apply presburger
 apply (subgoal_tac" \<forall>t addr. vrnew ts addr <  (length (memory ts))")
                prefer 2
  using assms(1) vbounded_def apply  blast
  using max.coboundedI2 apply blast

 (*cas fail*)
  apply (subgoal_tac "
(\<forall> ti addr. 0 \<le> vrnew ts ti \<and> vrnew ts ti  <  length (memory ts)\<and>
            0 \<le> vpready ts ti \<and>vpready ts ti <  length (memory ts) \<and>
            0 \<le> coh ts ti addr \<and>  coh ts ti addr <  length (memory ts) \<and>
            0 \<le>  vpasync ts ti addr \<and>  vpasync ts ti addr <  length (memory ts) \<and>
            0 \<le>  vpcommit ts ti addr \<and>  vpcommit ts ti addr <  length (memory ts) \<and>
            0 \<le>  maxcoh ts ti \<and>  maxcoh ts ti < length (memory ts) \<and>
            0 \<le>  maxvp ts addr  \<and> maxvp ts addr  < length (memory ts) \<and> 
            coh ts ti addr \<le> maxcoh  ts ti \<and>
            vpcommit ts ti addr \<le> maxvp ts addr \<and>
            vrnew ts ti \<le>  maxcoh ts ti \<and> 
            vrnew ts ti \<le>  vpready ts ti
     )")
  prefer 2
  using assms(1) vbounded_def apply  blast
 apply  clarify
  apply (intro conjI; simp add:cas_fail_trans_def )
  apply (subgoal_tac " ind < length (memory ts)")
             prefer 2
             apply (simp add: step_def)
             apply (simp add: OTS_def)
             apply (simp add: OTSF_def)
        apply presburger
 apply (subgoal_tac " ind < length (memory ts)")
             prefer 2
             apply (simp add: step_def)
             apply (simp add: OTS_def)
             apply (simp add: OTSF_def)
       apply presburger
 apply (subgoal_tac " ind < length (memory ts)")
             prefer 2
             apply (simp add: step_def)
             apply (simp add: OTS_def)
             apply (simp add: OTSF_def)
      apply presburger
 apply (subgoal_tac " ind < length (memory ts)")
             prefer 2
             apply (simp add: step_def)
             apply (simp add: OTS_def)
             apply (simp add: OTSF_def)
     apply presburger
  using max.coboundedI1 apply blast
  using max.coboundedI1 apply blast

  by (metis max.coboundedI1)




(*** A property for coherence ***)
definition  "coh_loc_rel  ts  \<equiv>
\<forall>ti l. comploc ( (memory ts)!(coh ts ti l)) l = l"


lemma coh_loc_rel_st:
   assumes "mem_structured ts"
  and "vbounded ts"
  and "start ts"
shows "coh_loc_rel  ts "
  using assms
  apply (simp add: coh_loc_rel_def start_def)
  done


lemma coh_loc_rel_preserved:
  assumes "mem_structured ts"
  and "vbounded ts"
 and  "\<forall>ti l. comploc ( (memory ts)!(coh ts ti l)) l = l"
  and "step t a ts ts'"
shows  "\<forall>ti l. comploc ( (memory ts')!(coh ts' ti l)) l = l"
  apply(rule step_cases)
  using assms apply (simp add: vbounded_def )
  using assms(3) apply (simp add: load_trans_def)
  apply clarify
       apply (case_tac " ind = coh ts t x")
        apply simp
        apply meson
       apply simp
  apply (smt OTSF_def OTS_def comploc_def mem_Collect_eq)
  using assms(3) apply (simp add: store_trans_def)
      apply clarify
      apply (case_tac "ti = t")
       apply simp
       apply (subgoal_tac"  \<forall>l. l \<noteq> x \<longrightarrow> (memory ts @ [msg x v t]) ! coh ts t l =  (memory ts ) ! coh ts t l")
  prefer 2
        apply (subgoal_tac "  \<forall>l. l \<noteq> x \<longrightarrow> coh ts t l < length(memory ts)")
         prefer 2
  using assms  apply (simp add: vbounded_def)
 apply (subgoal_tac "  \<forall>l. l \<noteq> x \<longrightarrow> coh ts t l < length((memory ts) @ [msg x v t])")
         prefer 2
  using assms  apply (simp add: vbounded_def)
  using less_SucI apply blast
        apply (simp add: nth_append)
       apply simp
       apply presburger
      apply simp

   apply (subgoal_tac"  \<forall>l. (memory ts @ [msg x v t]) ! coh ts ti l =  (memory ts ) ! coh ts ti l")
       prefer 2
   apply (subgoal_tac "  \<forall>l.  coh ts ti l < length(memory ts)")
        prefer 2
  using assms  apply (simp add: vbounded_def)
 apply (subgoal_tac "  \<forall>l. coh ts ti l < length((memory ts) @ [msg x v t])")
        prefer 2
  using assms  apply (simp add: vbounded_def)
  using less_SucI apply blast
       apply (simp add: nth_append)
  apply clarsimp
      apply (subgoal_tac "  loc ( (memory ts @ [msg x v t]) ! coh ts ti l) = loc ( (memory ts) ! coh ts ti l)")
       prefer 2
       apply auto[1]
      apply meson
     apply (simp add: flush_trans_def)
  apply (metis (no_types, lifting) assms(3) comploc_def ext_inject surjective update_convs(5) update_convs(6) update_convs(8))
    apply (simp add: flush_opt_trans_def)
    apply (metis assms(3) comploc_def)
   apply (simp add: mfence_trans_def)
   apply (metis assms(3) comploc_def)
  apply (simp add: sfence_trans_def)
    apply (metis assms(3) comploc_def)
(*cas added*)
  using assms(3) apply (simp add: cas_succ_trans_def)
      apply clarify
      apply (case_tac "ti = t")
       apply simp
       apply (subgoal_tac"  \<forall>l. l \<noteq> x \<longrightarrow> (memory ts @ [msg x v2 t]) ! coh ts t l =  (memory ts ) ! coh ts t l")
  prefer 2
        apply (subgoal_tac "  \<forall>l. l \<noteq> x \<longrightarrow> coh ts t l < length(memory ts)")
         prefer 2
  using assms  apply (simp add: vbounded_def)
 apply (subgoal_tac "  \<forall>l. l \<noteq> x \<longrightarrow> coh ts t l < length((memory ts) @ [msg x v2 t])")
         prefer 2
  using assms  apply (simp add: vbounded_def)
  using less_SucI apply blast
     apply (simp add: nth_append)
    apply presburger
   apply (subgoal_tac"  \<forall>l. (memory ts @ [msg x v2 t]) ! coh ts ti l =  (memory ts ) ! coh ts ti l")
       prefer 2
   apply (subgoal_tac "  \<forall>l.  coh ts ti l < length(memory ts)")
        prefer 2
  using assms  apply (simp add: vbounded_def)
 apply (subgoal_tac "  \<forall>l. coh ts ti l < length((memory ts) @ [msg x v2 t])")
        prefer 2
  using assms  apply (simp add: vbounded_def)
  using less_SucI apply blast
       apply (simp add: nth_append)
  apply clarsimp
      apply (subgoal_tac "  loc ( (memory ts @ [msg x v2 t]) ! coh ts ti l) = loc ( (memory ts) ! coh ts ti l)")
       prefer 2
       apply auto[1]
      apply meson
 using assms(3) apply (simp add: cas_fail_trans_def)
 apply clarify
       apply (case_tac " ind = coh ts t x")
        apply simp
        apply meson
  apply simp
  by (smt (z3) OTSF_def OTS_def comploc_def mem_Collect_eq)


(*  Wellformedness for sets *)
(*Sets in start not empty*)
lemma st_OTS:
  assumes "start ts" 
  shows "\<forall> l. \<forall> ti. OTS ts ti l = {0}"
   using assms apply (simp add: start_def OTS_def  OTSF_def  notoverwritten_def)
 apply(subgoal_tac "length(memory ts) = 1") prefer 2
   using  assms
   by auto
                              
lemma st_OTSF:
  assumes "start ts"
  shows "\<forall> l.\<forall> ti. OTSF ts ti l nview = {0}"
  using assms apply (simp add: start_def OTSF_def notoverwritten_def)
  by auto

lemma st_OPTS:
  assumes "start ts" 
  shows "\<forall> l. OPTS ts  l = {0}"
  using assms apply (simp add: start_def OPTS_def notoverwritten_def)
  using nth_Cons_0 singleton_conv2 by auto

lemma st_OATS:
 assumes "start ts" 
 shows "\<forall> l. \<forall> ti. OATS ts ti l = {0}"
  using assms apply (simp add: start_def OATS_def  notoverwritten_def)
  by auto

lemma st_OV:
  assumes "start ts" 
  shows "\<forall> l. \<forall> t. [l]\<^sub>t ts \<noteq> {}"
  using assms
  apply (subgoal_tac " \<forall> l. \<forall> ti. OTS ts ti l \<noteq> {}")
   prefer 2
   apply (simp add: st_OTS)
  apply (unfold mapval_def)
  by auto

lemma last_entry_set_start:
  assumes "start ts" 
  shows " last_entry_set ts l = {0}"
  using assms
   apply (simp add: last_entry_set_def)
   apply (subgoal_tac"  (memory ts = [Init_Msg])")
    prefer 2
    apply (simp add: start_def)
   apply simp
  by fastforce


lemma le_in_ots_st:    
  assumes "start ts"
  shows " (\<forall> l ti. last_entry ts l \<in>   OTS ts ti l )"
   using assms
   by (simp add: last_entry_def last_entry_set_start st_OTS)

lemma le_in_opts_st:    
  assumes "start ts"
  shows " (\<forall> l . last_entry ts l \<in>   OPTS ts l )"
  using assms
  by (simp add: last_entry_def last_entry_set_start st_OPTS)

lemma le_in_oats_st:    
  assumes "start ts"
  shows " (\<forall> l ti. last_entry ts l \<in>   OATS ts ti l )"
  using assms le_in_opts_st st_OATS st_OPTS by auto
 
lemma st_OV_le:
  assumes "start ts" 
  shows "\<forall>  t l. lastVal  l ts  \<in>  [l]\<^sub>t ts"
  using assms
  apply (simp add: lastVal_def)
  apply (unfold mapval_def)
  using le_in_ots_st by fastforce

lemma st_OPV_le:
  assumes "start ts" 
  shows "\<forall>   l. lastVal  l ts  \<in>  [l]\<^sub>P ts"
  using assms
  apply (simp add: lastVal_def)
  apply (unfold mapval_def)
  using le_in_opts_st by fastforce

lemma st_OAV_le:
  assumes "start ts" 
  shows "\<forall>   l. lastVal  l ts  \<in>   [l]\<^sup>A\<^sub>t ts "
  using assms
  apply (simp add: lastVal_def)
  apply (unfold mapval_def)
  using le_in_oats_st by fastforce


lemma st_OV_z:
  assumes "start ts" 
  shows "\<forall> l. \<forall> t. [l]\<^sub>t ts = {0}"
  using assms
  by (simp add: st_OTS start_def mapval_def)


lemma st_OPV:
 assumes "start ts" 
 shows "\<forall> l. [l]\<^sub>P ts \<noteq> {}"
  using assms
  using st_OPV_le by auto

lemma st_OPV_z:
  assumes "start ts" 
  shows "\<forall> l. [l]\<^sub>P ts = {0}"
  using assms
  by (simp add: st_OPTS start_def mapval_def)


lemma st_OAV:
  assumes "start ts" 
  shows "\<forall> l. \<forall> t. [l]\<^sup>A\<^sub>t ts  \<noteq> {}"
  using assms
  using st_OAV_le by auto


lemma st_OAV_z:
  assumes "start ts" 
  shows "\<forall> l. \<forall> t. [l]\<^sup>A\<^sub>t ts  = {0}"
  using assms
  by (simp add: st_OATS start_def mapval_def)

lemma st_oc: 
assumes "start ts" 
shows " (v \<noteq> 0) \<longrightarrow> \<lparr>x,v\<rparr>  ts = 0 "
  using assms
  apply (simp add: oc_set_def start_def )
  using mem_structured_def st_wfs_m start_size by auto
  
lemma st_lv:
  assumes "start ts"
  shows " \<lceil>x:0\<rceil> ts"
  using assms
  apply (simp add: last_entry_def)
 apply (subgoal_tac "  last_entry_set ts x = {0}")
   prefer 2
   apply (simp add: last_entry_set_start) 
 apply (subgoal_tac"  (memory ts = [Init_Msg])")
    prefer 2
   apply (simp add: start_def)
  by (simp add: start_def)


(******Some properties for last entry********)
lemma last_entry_notoverwritten:
assumes " mem_structured ts"
and " vbounded ts"
shows "  notoverwritten ts vi ( last_entry ts addr) addr "
  using assms
  apply (unfold last_entry_def)
 apply (subgoal_tac "  \<nexists> i. i \<in> last_entry_set ts addr \<and> i > Max (last_entry_set ts  addr)")
   prefer 2
   apply (subgoal_tac " last_entry_set ts addr \<noteq> {} ")
    prefer 2
    apply (subgoal_tac " 0 \<in> last_entry_set ts addr")
     prefer 2
     apply (unfold last_entry_set_def)
     apply clarify
     apply (rule_tac x=" 0" in exI)
  apply (simp add: vbounded_def)
  using mem_structured_def apply blast
    apply blast
   apply (subgoal_tac " finite (last_entry_set ts addr)") 
    prefer 2
  apply (simp add: last_entry_set_def)
   apply (metis Max_gr_iff last_entry_set_def less_irrefl_nat)
  apply (simp add: last_entry_set_def notoverwritten_def)
  by (smt Collect_cong)


lemma last_entry_loc:
assumes " mem_structured ts"
and " vbounded ts"
shows "  comploc ( memory ts!( last_entry ts addr)) addr = addr "
  using assms
(*  apply (unfold last_entry_def  )*)
    apply (subgoal_tac " \<forall> i . i \<in> last_entry_set ts addr  \<longrightarrow> comploc (( memory ts)!i) addr = addr ")
          prefer 2
   apply (simp  add: last_entry_set_def)
  apply (subgoal_tac " last_entry ts addr \<in> last_entry_set ts addr")
   prefer 2
   apply (simp  add: last_entry_def)
 apply (subgoal_tac " last_entry_set ts addr \<noteq> {} ")
    prefer 2
    apply (subgoal_tac " 0 \<in> last_entry_set ts addr")
     prefer 2
     apply (unfold last_entry_set_def)
     apply clarify
     apply (rule_tac x=" 0" in exI)
  apply (simp add: vbounded_def)
  using mem_structured_def apply blast
    apply blast
   apply (subgoal_tac "finite (last_entry_set ts addr)")
    prefer 2
    apply (simp add: last_entry_set_def)
   apply (metis Max_in last_entry_set_def)
  by blast


lemma last_entry_lim_loc:
assumes " mem_structured ts"
and " vbounded ts"
shows "  comploc ( memory ts!( last_entry_lim ts addr lim)) addr = addr "
  using assms
    apply (subgoal_tac " \<forall> i . i \<in> last_entry_set_lim ts addr lim  \<longrightarrow> comploc (( memory ts)!i) addr = addr ")
          prefer 2
   apply (simp  add: last_entry_set_lim_def)
  apply (subgoal_tac " last_entry_lim ts addr lim  \<in> last_entry_set_lim ts addr lim")
   prefer 2
   apply (simp  add: last_entry_lim_def)
 apply (subgoal_tac " last_entry_set_lim  ts addr lim \<noteq> {} ")
    prefer 2
    apply (subgoal_tac " 0 \<in> last_entry_set_lim ts addr lim")
     prefer 2
     apply (unfold last_entry_set_lim_def)
     apply clarify
     apply (rule_tac x=" 0" in exI)
  apply (simp add: vbounded_def)
  using mem_structured_def apply blast
    apply blast
   apply (subgoal_tac "finite (last_entry_set_lim ts addr lim)")
    prefer 2
    apply (simp add: last_entry_set_lim_def)
   apply (metis Max_in last_entry_set_lim_def)
  by blast


lemma finite_last_entry_set:
  shows "finite (last_entry_set ts addr)"
  by (simp add: last_entry_set_def)


lemma finite_last_entry_set_lim:
  shows "finite (last_entry_set_lim ts addr lim)"
  by (simp add: last_entry_set_lim_def)


lemma last_entry_in_last_entry_set :
  assumes "mem_structured ts"
and "vbounded ts"
shows " last_entry ts addr \<in>   last_entry_set  ts addr"
  using assms
 apply (simp add: vbounded_def )
(*  apply (unfold last_entry_set_def)*)
  apply (subgoal_tac "  last_entry_set  ts addr \<noteq> {}")
   prefer 2
   apply ( subgoal_tac "0 \<in> last_entry_set  ts addr" )
    apply blast
apply (subgoal_tac "finite(last_entry_set ts addr)" )
    prefer 2
  using finite_last_entry_set apply auto[1]
   prefer 2
   apply (simp add: finite_last_entry_set last_entry_def)

  apply (unfold last_entry_set_def)
  apply clarify
   apply (rule_tac x=" 0" in exI)
   apply (intro conjI )
  using gr_implies_not_zero apply blast
      apply simp
  using gr_implies_not_zero apply blast
  using assms(1) 
    apply auto[1]
  using mem_structured_def apply blast
  done


lemma last_entry_lim_in_last_entry_set_lim :
  assumes "mem_structured ts"
and "vbounded ts"
shows " last_entry_lim ts addr lim \<in>   last_entry_set_lim  ts addr lim"
 using assms
 apply (simp add: vbounded_def )
  apply (subgoal_tac "  last_entry_set_lim  ts addr lim \<noteq> {}")
   prefer 2
   apply ( subgoal_tac "0 \<in> last_entry_set_lim  ts addr lim" )
    apply blast
apply (subgoal_tac "finite(last_entry_set_lim ts addr lim)" )
    prefer 2
  using finite_last_entry_set_lim 
  apply blast
   prefer 2
   apply (simp add: finite_last_entry_set_lim  last_entry_lim_def)

  apply (unfold last_entry_set_lim_def)
  apply clarify
   apply (rule_tac x=" 0" in exI)
   apply (intro conjI )
  using gr_implies_not_zero apply blast
      apply simp
  using gr_implies_not_zero apply blast
  using assms(1) 
    apply auto[1]
  using mem_structured_def 
  by auto


lemma last_entry_set_not_empty :
assumes "mem_structured ts"
and "vbounded ts"
shows " last_entry_set ts addr \<noteq> {}"
  using assms
  using last_entry_in_last_entry_set by auto



lemma last_entry_set_lim_not_empty :
assumes "mem_structured ts"
and "vbounded ts"
shows " last_entry_set_lim ts addr lim \<noteq> {}"
  using assms
  using last_entry_lim_in_last_entry_set_lim  by auto


lemma last_entry_bounded:
assumes "mem_structured ts"
and "vbounded ts"
shows " last_entry ts addr < length (memory ts ) "
  using assms
  apply (subgoal_tac " \<forall>i. i \<in>(last_entry_set ts addr) \<longrightarrow> i <  length ( memory ts)")
  prefer 2
          apply (unfold last_entry_set_def)
          apply blast
 apply (subgoal_tac " last_entry ts addr \<in> last_entry_set ts addr")
   prefer 2
   apply (simp add: last_entry_in_last_entry_set)
  using last_entry_set_def by blast


lemma last_entry_lim_bounded:
assumes "mem_structured ts"
and "vbounded ts"
shows " last_entry_lim  ts addr lim < length (memory ts ) "
  using assms
  apply (subgoal_tac " \<forall>i. i \<in>(last_entry_set_lim  ts addr lim) \<longrightarrow> i <  length ( memory ts)")
  prefer 2
          apply (unfold last_entry_set_lim_def)
          apply blast
 apply (subgoal_tac " last_entry_lim  ts addr lim \<in> last_entry_set_lim  ts addr lim")
   prefer 2
  apply (simp add: last_entry_lim_in_last_entry_set_lim)
  by (simp add: last_entry_set_lim_def)



(****last entry always in sets *****)
lemma le_in_otsf:    
  assumes "mem_structured ts"
and "vbounded ts"
(*and " (\<forall> nview ti l. last_entry ts l \<in>   OTSF ts ti l nview)"*)
 and "step t a ts ts'"
and  "\<forall>ti l. comploc ( (memory ts)!(coh ts ti l)) l = l"
shows " (\<forall> nview ti l. last_entry ts' l \<in>   OTSF ts' ti l nview)"
 using assms apply (simp add:  vbounded_def  step_def)
  apply clarify
  apply ( subgoal_tac " \<forall> a. step t a ts ts'  \<longrightarrow> last_entry ts' l \<in>   OTSF ts' ti l nview")

 prefer 2
   apply clarify
   apply (subgoal_tac " last_entry ts' l \<in>   OTSF ts' ti l nview")
    prefer 2
    apply (unfold  OTSF_def)
    apply clarify
    apply (rule_tac x=" last_entry ts' l" in exI)
    apply (rule conjI)
  apply blast
    apply (subgoal_tac"vbounded ts' ")
     prefer 2
  using assms(2) vbounded_preserved apply auto[1]
    apply (subgoal_tac" mem_structured ts' ")
     prefer 2
  apply (meson mem_structured_preserved)
    apply (intro conjI impI)
        prefer 5
  using last_entry_notoverwritten apply blast
       apply blast
  using last_entry_bounded apply blast
     apply (metis last_entry_loc)
    apply (subgoal_tac"notoverwritten ts' nview (last_entry ts' l) l")
     prefer 2
  using last_entry_notoverwritten apply blast
    apply (simp add: notoverwritten_def)
apply (subgoal_tac " coh ts' ti l  < length(memory ts') ")
     prefer 2
          apply (subgoal_tac "vbounded ts'")
      prefer 2
  apply blast
          apply (unfold vbounded_def)
          apply meson
         apply (subgoal_tac " 0 \<le>  coh ts' ti l")
          prefer 2
     apply blast

 apply (subgoal_tac " \<forall> i. i \<in> last_entry_set ts'  l \<longrightarrow> i \<le> last_entry ts' l")
   prefer 2
   apply (simp add: last_entry_def )
   apply (metis Max.in_idem finite_last_entry_set max_def order_refl)
  apply (subgoal_tac " \<forall> i. 0\<le> i \<and> i < length (memory ts') \<and>  comploc ( memory ts'!i) l = l\<longrightarrow>  i \<in> last_entry_set ts'  l ")
   prefer 2
     apply (simp add: last_entry_set_def)
  apply (meson assms(2) assms(4) coh_loc_rel_preserved)
   apply blast
  by (meson assms(3))


lemma le_in_ots:    
  assumes "mem_structured ts"
and "vbounded ts"
and " (\<forall> ti l. last_entry ts l \<in>   OTS ts ti l )"
 and "step t a ts ts'"
and  "\<forall>ti l. comploc ( (memory ts)!(coh ts ti l)) l = l"
shows " (\<forall>  ti l. last_entry ts' l \<in>   OTS ts' ti l)"
  using assms
  apply (unfold OTS_def)
  by (simp add: le_in_otsf)



lemma lev_in_ov:    
  assumes "mem_structured ts"
and "vbounded ts"
and " (\<forall>  t l. lastVal  l ts  \<in>  [l]\<^sub>t ts )"
 and "step t a ts ts'"
and  "\<forall>ti l. comploc ( (memory ts)!(coh ts ti l)) l = l"
shows " (\<forall>  t l. lastVal  l ts'  \<in>  [l]\<^sub>t ts' )"
  using assms
  apply (simp add: lastVal_def)
  apply (subgoal_tac " \<forall>  ti l. last_entry ts' l \<in>   OTS ts' ti l")
   prefer 2
   apply (simp add: OTS_def le_in_otsf)
  apply (simp add: mapval_def valOf_def)
  by blast


(*lastVal  l \<sigma>*)


lemma  le_in_opts:
  assumes "mem_structured ts"
and "vbounded ts"
  and "step t a ts ts'"
shows "(\<forall>  l. last_entry ts' l \<in>   OPTS ts'  l )" 
  using assms
  apply clarify
 apply ( subgoal_tac " \<forall> a. step t a ts ts'  \<longrightarrow> last_entry ts' l \<in>  OPTS ts'  l")
   prefer 2
   apply clarify
   apply (subgoal_tac " last_entry ts' l \<in>  OPTS ts' l")
    prefer 2
    apply (unfold OPTS_def)
    apply clarify
    apply (rule_tac x=" last_entry ts' l" in exI)
    apply (rule conjI)
  apply blast
    apply (subgoal_tac"vbounded ts' ")
     prefer 2
     apply (metis assms(2)  vbounded_preserved)
    apply (subgoal_tac" mem_structured ts' ")
     prefer 2
  using assms(1) assms(3) mem_structured_preserved 
  apply blast
    apply (intro conjI impI)
     prefer 4
  apply (simp add: last_entry_notoverwritten)
  apply blast prefer 2
     apply (metis last_entry_loc)
  using last_entry_bounded apply blast
   apply blast
  by blast


lemma lev_in_opv:  
  assumes "mem_structured ts"
and "vbounded ts"
and "(\<forall>  l.  lastVal  l ts \<in>  [l]\<^sub>P ts )"
  and "step t a ts ts'"
shows "(\<forall>  l.  lastVal  l ts' \<in>  [l]\<^sub>P ts'  )" 
  using assms
  apply (simp add: lastVal_def)
  apply (subgoal_tac "\<forall>  l. last_entry ts' l \<in>   OPTS ts'  l ")
  prefer 2
  apply (simp add: OPTS_def le_in_opts)
  apply (metis comploc_def last_entry_bounded last_entry_loc last_entry_notoverwritten mem_structured_preserved vbounded_preserved)
  apply (simp add: mapval_def valOf_def)
  by blast 

(*and " (\<forall>  t l. lastVal  l ts  \<in>  [l]\<^sub>t ts )"*)


lemma  le_in_oats:
  assumes "mem_structured ts"
and "vbounded ts"
  and "step t a ts ts'"
shows "(\<forall>  l t. last_entry ts' l \<in>   OATS ts' t l )" 
  using assms
  apply clarify
  apply ( subgoal_tac " \<forall> a. step t a ts ts'  \<longrightarrow> last_entry ts' l \<in>  OATS ts' t l")
   prefer 2
   apply (subgoal_tac " last_entry ts' l \<in>  OATS ts' t l")
    prefer 2
    apply (unfold OATS_def)
    apply clarify
    apply (rule_tac x=" last_entry ts' l" in exI)
    apply (rule conjI)
  apply blast
    apply (subgoal_tac"vbounded ts' ")
     prefer 2
     apply (metis assms(2)  vbounded_preserved)
    apply (subgoal_tac" mem_structured ts' ")
     prefer 2
  using assms(1) assms(3) mem_structured_preserved 
  apply blast
    apply (intro conjI impI)
     prefer 4
  apply (simp add: last_entry_notoverwritten)
  apply blast prefer 2
     apply (metis last_entry_loc)
  using last_entry_bounded apply blast
   apply blast
  using last_entry_notoverwritten mem_structured_preserved vbounded_preserved by auto



lemma  lev_in_oav:
  assumes "mem_structured ts"
and "vbounded ts"
and "(\<forall> l t. lastVal  l ts \<in>  [l]\<^sup>A\<^sub>t  ts )"
  and "step t a ts ts'"
shows  "(\<forall>  l t. lastVal  l ts'  \<in> [l]\<^sup>A\<^sub>t  ts' )"
  using assms 
  apply (simp add: lastVal_def)
 apply (subgoal_tac "\<forall>  l t. last_entry ts' l \<in>   OATS ts' t  l ")
  prefer 2
   apply (simp add: OATS_def le_in_oats)
  apply (metis assms(4) comploc_def last_entry_bounded last_entry_loc last_entry_notoverwritten mem_structured_preserved vbounded_preserved)
  apply (simp add: mapval_def valOf_def)
  by blast




  
(**********************)

(*Sets are never empty*)
lemma OTSF_notempty_preserved:    
  assumes "mem_structured ts"
and "vbounded ts"
and " (\<forall> nview ti l. OTSF ts ti l nview \<noteq> {})"
 and "step t a ts ts'"
and  "\<forall>ti l. comploc ( (memory ts)!(coh ts ti l)) l = l"
shows " (\<forall> nview ti l. OTSF ts' ti l nview \<noteq> {})"
  using assms
  by (metis empty_iff le_in_otsf) 


lemma  OTS_notempty_preserved:
  assumes "mem_structured ts"
and "vbounded ts"
  and " (\<forall> ti addr. OTS   ts ti  addr \<noteq> {} )" 
  and "step t a ts ts'"
and  "\<forall>ti l. comploc ( (memory ts)!(coh ts ti l)) l = l"
shows " (\<forall> ti addr. OTS ts' ti  addr \<noteq> {} ) "
  using assms 
  by (metis OTS_def empty_iff le_in_otsf)


lemma  OV_notempty_preserved:
 assumes "mem_structured ts"
and "vbounded ts"
  and " (\<forall> ti addr.[addr]\<^sub>ti ts \<noteq> {} )" 
  and "step t a ts ts'"
and  "\<forall>ti l. comploc ( (memory ts)!(coh ts ti l)) l = l"
shows " (\<forall> ti addr.[addr]\<^sub>ti ts' \<noteq> {}) "
  using assms
  apply (simp add: mapval_def)
  by (metis OTS_def assms(5) disjoint_iff_not_equal le_in_otsf mem_Collect_eq)
 

lemma  OPTS_notempty_preserved:
  assumes "mem_structured ts"
and "vbounded ts"
  and " (\<forall>  addr. OPTS   ts   addr \<noteq> {} )" 
  and "step t a ts ts'"
and  "\<forall>ti l. comploc ( (memory ts)!(coh ts ti l)) l = l"
shows " (\<forall>  addr. OPTS ts'   addr \<noteq> {} ) "
  using assms 
  by (metis ex_in_conv le_in_opts) 


lemma  OPV_notempty_preserved:
  assumes "mem_structured ts"
and "vbounded ts"
  and " (\<forall>  addr. [addr]\<^sub>P  ts \<noteq> {} )" 
  and "step t a ts ts'"
and  "\<forall>ti l. comploc ( (memory ts)!(coh ts ti l)) l = l"
shows " (\<forall>  addr.  [addr]\<^sub>P  ts' \<noteq> {} ) "
  using assms
  apply (simp add: mapval_def)
  by (metis Int_Collect OPTS_notempty_preserved assms(5) equals0I)

lemma  OATS_notempty_preserved:
  assumes "mem_structured ts"
and "vbounded ts"
  and " (\<forall> ti addr. OATS   ts ti  addr \<noteq> {} )" 
  and "step t a ts ts'"
and  "\<forall>ti l. comploc ( (memory ts)!(coh ts ti l)) l = l"
shows " (\<forall> ti addr. OATS ts' ti  addr \<noteq> {} ) "
  using assms
  by (metis empty_iff le_in_oats)


lemma  OAV_notempty_preserved:
  assumes "mem_structured ts"
and "vbounded ts"
  and " (\<forall>  addr t. [addr]\<^sup>A\<^sub>t  ts \<noteq> {} )" 
  and "step t' a ts ts'"
and  "\<forall>ti l. comploc ( (memory ts)!(coh ts ti l)) l = l"
shows " (\<forall>  addr t. [addr]\<^sup>A\<^sub>t  ts' \<noteq> {} ) "
  using assms
  apply (simp add: mapval_def)
  by (metis disjoint_iff_not_equal le_in_oats mem_Collect_eq)


lemma  survived_val_cas_succ:
 assumes "ts' = cas_succ_trans t ind x v1 v2 r nv1 nv2 ts  "
 shows "  survived_val ts z = survived_val ts' z "
  using assms
  by (simp add: cas_succ_trans_def)

lemma  survived_val_cas_fail:
 assumes "ts' =  cas_fail_trans t ind x v1 v2 r ts  "
 shows "  survived_val ts z = survived_val ts' z "
  using assms
  by (simp add: cas_fail_trans_def)
 

lemma  survived_val_preserved_cas:
assumes " step t ( CAS x  v1 v2 r) ts ts' "
shows "  survived_val ts z = survived_val ts' z "
  using assms
  apply (simp add: step_def)
  apply clarify
  apply (case_tac "  ts' = cas_fail_trans t ind x v1 v2 r ts")
   apply (simp add: cas_fail_trans_def )
  by (simp add: cas_succ_trans_def )

lemma  survived_val_preserved_load :
assumes " step t  ( Load x r) ts ts' "
shows "  survived_val ts z = survived_val ts' z "
  using assms
  apply (simp add: step_def)
  apply (simp add: load_trans_def)
  by force

lemma  survived_val_preserved_store :
assumes " step t  ( Store x v) ts ts' "
shows "  survived_val ts z = survived_val ts' z "
  using assms
  apply (simp add: step_def)
  by (simp add: store_trans_def)

lemma  survived_val_preserved_flush:
assumes " step t  ( Flush x ) ts ts' "
shows "  survived_val ts z = survived_val ts' z "
  using assms
  apply (simp add: step_def)
  apply (simp add: flush_trans_def)
  by (metis (no_types, lifting) select_convs(9) surjective update_convs(5) update_convs(6) update_convs(8))

lemma  survived_val_preserved_flushopt:
assumes " step t  ( Flush_opt x ) ts ts' "
shows "  survived_val ts z = survived_val ts' z "
  using assms
  apply (simp add: step_def)
  by (simp add: flush_opt_trans_def)

lemma  survived_val_preserved_mfence:
assumes " step t  ( mfence ) ts ts' "
shows "  survived_val ts z = survived_val ts' z "
  using assms
  apply (simp add: step_def)
  by (simp add: mfence_trans_def)

lemma  survived_val_preserved_sfence:
assumes " step t  ( sfence ) ts ts' "
shows "  survived_val ts z = survived_val ts' z "
  using assms
  apply (simp add: step_def)
  apply (simp add: sfence_trans_def)
  by fastforce


lemma  survived_val_preserved_reg_write :
assumes "  ts' =  update_reg ti  r v   ts "
shows "  survived_val ts z = survived_val ts' z "
  using assms
  apply (simp add: step_def)
  by (simp add:  update_reg_def)


 

lemma  fl_crash [simp]:
  assumes "  step t  ( Flush x ) ts ts'  "
shows " \<forall>i z.  compval ts (( memory ts)!i) z  =  compval ts' (( memory ts)!i) z "
  using assms
  apply ( simp add: step_def)
  apply (simp add: flush_trans_def)
  using assms(1) survived_val_preserved_flush by presburger

lemma  flo_crash [simp]:
 assumes  "  step t  ( Flush_opt x ) ts ts'  "
shows " \<forall>i z.  compval ts (( memory ts)!i) z  =  compval ts' (( memory ts)!i) z "
  using assms
  apply ( simp add: step_def)
  by (simp add: flush_opt_trans_def)

lemma  ld_crash [simp]:
 assumes "  step t  ( Load x r) ts ts'  "
shows " \<forall>i z.  compval ts (( memory ts)!i) z  =  compval ts' (( memory ts)!i) z "
  using assms
  apply ( simp add: step_def)
  apply(simp add: load_trans_def)
  using assms survived_val_preserved_load by blast

lemma  sfence_crash [simp]:
 assumes "  step t  ( sfence) ts ts'  "
shows " \<forall>i z.  compval ts (( memory ts)!i) z  =  compval ts' (( memory ts)!i) z "
  using assms
  apply ( simp add: step_def)
  apply(simp add: sfence_trans_def)
  using assms survived_val_preserved_sfence by blast

lemma  mfence_crash [simp]:
 assumes "  step t  (mfence) ts ts'  "
shows " \<forall>i z.  compval ts (( memory ts)!i) z  =  compval ts' (( memory ts)!i) z "
  using assms
  apply ( simp add: step_def)
  by(simp add: mfence_trans_def)



lemma  cas_fail_crash [simp]:
 assumes "  ts' = cas_fail_trans  ti ind x  v1 v2 r ts  "
shows " \<forall>i z.  compval ts (( memory ts)!i) z  =  compval ts' (( memory ts)!i) z "
  using assms
  by(simp add: cas_fail_trans_def)


lemma  reg_write__crash [simp]:
 assumes " ts' =  update_reg ti  r v   ts "
shows " \<forall>i z.  compval ts (( memory ts)!i) z  =  compval ts' (( memory ts)!i) z "
  using assms
  by (simp add: update_reg_def)



(***A prperty for OTS and coherence ***)

(*coh_prop ts ti l *)


(*
lemma coh_ots_rel_st:
   assumes "mem_structured ts"
  and "vbounded ts"
  and "start ts"
shows "coh_prop  ts ti l "
  using assms
  apply (simp add: start_def coh_prop_def survived_val_def)
  by (simp add: assms(3) st_OTS)


lemma coh_prop__preserved:
  assumes "mem_structured ts"
  and "vbounded ts"
 and  "coh_prop  ts ti l"
  and "step t a ts ts'"
shows  "coh_prop  ts' ti l"
  apply(rule step_cases)
  using assms apply (simp add: step_def )
         apply (simp add:  coh_prop_def)
         apply (case_tac "t = ti")
          prefer 2
  apply (simp add: load_trans_def)*)

 
definition "total_OTSF s \<equiv>  \<forall>  nview ti l . OTSF s ti l nview \<noteq> {}"




definition " total_wfs ts  \<equiv>
       vbounded ts \<and>
       mem_structured ts \<and>
      total_OTSF ts \<and>
      ( \<forall> ti l. comploc ( (memory ts)!(coh ts ti l)) l = l \<and>
           last_entry ts l \<in>   OTS ts ti l \<and>
           last_entry ts l \<in>   OPTS ts l  \<and>
           last_entry ts l \<in>   OATS ts ti l  \<and>
           lastVal  l ts  \<in>  [l]\<^sub>ti ts   \<and>
           lastVal  l ts  \<in>  [l]\<^sub>P ts \<and>
            lastVal  l ts  \<in>   [l]\<^sup>A\<^sub>ti ts  ) " 

 

lemma i_noteqo_loc:
assumes "comploc ((memory ts)! i )  a = a"
(*and "total_wfs ts "*)
and " mem_structured ts "
and " i >0 "
and " i < length (memory ts) "
shows "Msg.loc ((memory ts)! i )   = a "
  using assms
(*  apply (simp add: total_wfs_def)*)
  by (simp add: mem_structured_def)

lemma gr_last_entry_lim:
assumes " i > last_entry_lim ts a b  "
and "total_wfs ts "
and "comploc ((memory ts)! i )  a = a"
and " i < length (memory ts)"
shows" b < i "
  using assms
  apply (simp add: total_wfs_def)
  apply (subgoal_tac " 0 \<le> i ")
  prefer 2
   apply blast
apply (subgoal_tac " \<forall>  i. i \<in> last_entry_set_lim  ts a b   \<longrightarrow> i \<le>   b")
    prefer 2
   apply (simp add:  last_entry_set_lim_def)
  apply (subgoal_tac " last_entry_lim  ts  a b  \<le> b  ")
   prefer 2
   apply (metis last_entry_lim_in_last_entry_set_lim)
  apply (subgoal_tac " \<forall>i. i \<in>  last_entry_set_lim  ts a b \<longrightarrow> i \<le> last_entry_lim ts a b ")
   prefer 2
   apply (simp add: last_entry_lim_def)
  apply (simp(no_asm) add:  last_entry_set_lim_def)
  apply (subgoal_tac " \<forall> i. comploc ((memory ts)! i )  a = a \<and> i \<le> b \<and> 0 \<le> i \<and> i < length (memory ts) \<longrightarrow> i \<in> last_entry_set_lim  ts a b ")
  prefer 2
  apply (simp add: last_entry_set_lim_def)
  apply (subgoal_tac " i \<notin> last_entry_set_lim  ts a b   ")
   prefer 2
  using leD apply blast
  by (metis assms(3) not_le_imp_less)
 








end







