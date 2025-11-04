theory Language 
imports  State
begin


 (*notoverwritten ts view selected_w l holds when there is no massage between the given views ( (selected_w, view] )such as its location is equal to l *)
definition notoverwritten :: "TState \<Rightarrow> V \<Rightarrow> V \<Rightarrow> Loc \<Rightarrow> bool"
 where 
  "notoverwritten ts view selected_w l \<equiv> \<forall>i.( ( i < length(memory ts)  \<and> i \<le> view  \<and> i > selected_w ) \<longrightarrow> loc  (memory ts!i) \<noteq>  l )"


(* Extracting the value and location from the message*)
(*definition "compval m \<equiv> if m = Init_Msg
                           then 0 else
                           val m "  *)


definition "compval ts m l  \<equiv> if m = Init_Msg
                           then (survived_val ts l)  else
                           val m "  

definition "comploc m l \<equiv> if m = Init_Msg
                           then l else
                           loc m  "



(*
definition "test  ind value ts  \<equiv> 
                          value=  compval ts  ((memory ts)!ind)  addr"*)


(*Semantics of store transition *)
definition store_trans :: "TState \<Rightarrow> Loc \<Rightarrow> Val \<Rightarrow> TId \<Rightarrow> TState"
  where " store_trans ts l v ti  \<equiv>
                            ts \<lparr>
                                     memory := ((memory ts)@ [msg l v ti] ),
                                     coh := (coh ts)(ti := (coh ts ti)(l :=  length (memory ts))),
                                     maxcoh := ( maxcoh ts)(ti := length (memory ts)  )
                              \<rparr>"  


(* Make the order of the arguments same with store_trans *)
(*definition store_trans :: "TState \<Rightarrow> Tid\<Rightarrow> Nat \<Rightarrow> Loc \<Rightarrow> \<Rightarrow> Regs \<Rightarrow>  TState" *)
(*Semantics of load transition *)
(*changed*)
definition load_trans ::  "TId \<Rightarrow> nat \<Rightarrow> Loc \<Rightarrow> TState \<Rightarrow> Reg \<Rightarrow> TState "
where
 " load_trans ti ind addr ts r  \<equiv> 
             let value=  compval ts  ((memory ts)!ind)  addr; 
                  nview =  if( ind \<noteq> (coh ts ti) addr )
                   then ind 
                else vrnew ts ti
                in
                  ts \<lparr> vrnew := (vrnew ts)(ti := max (vrnew ts ti) nview ), 
                      vpready := (vpready ts)(ti := max (vpready ts ti) nview ), 
                      maxcoh := ( maxcoh ts)(ti := max (maxcoh ts ti) ind ),
                      coh := (coh ts)(ti := (coh ts ti)(addr := ind)),
                      regs := (regs ts)(ti := (regs ts ti)(r := value))  \<rparr> "


(* A predicate for the sfence instruction *)
definition "vpcommit_nv ti ts nv \<equiv> \<forall> l. 
       nv l = max  (vpasync ts ti l ) (vpcommit ts ti l ) "

(* A predicate for the sfence instruction *)
definition "maxvp_nv ti ts nv \<equiv> \<forall> l. 
    nv l = max ( max  (vpasync ts ti l ) (vpcommit ts ti l ))  (maxvp ts l)  "



(*Semantics of succesful CAS transition *)
definition cas_succ_trans::  "TId \<Rightarrow> nat \<Rightarrow> Loc  \<Rightarrow>Val \<Rightarrow> Val\<Rightarrow> Reg\<Rightarrow> (nat \<Rightarrow>nat) \<Rightarrow>  (nat \<Rightarrow>nat) \<Rightarrow> TState \<Rightarrow> TState " 
  where 
 " cas_succ_trans ti ind addr  v1 v2 r vpc_nv mvp_nv  ts   \<equiv> 
  
                  ts \<lparr> 
                       vrnew := (vrnew ts)(ti :=  max ( max  (maxcoh ts ti ) (length (memory ts) ))  (vrnew ts ti)), 
                       vpready :=(vpready ts)(ti :=  max ( max  (maxcoh ts ti ) (length (memory ts) ))  (vpready ts ti)), 
                       maxcoh := ( maxcoh ts)(ti := length (memory ts)),
                       coh := (coh ts)(ti := (coh ts ti)(addr :=  length (memory ts))),
                       memory := ((memory ts)@ [msg addr v2  ti]),
                       regs := (regs ts)(ti := (regs ts ti)(r := 1)) ,
                        vpcommit := (vpcommit ts)(ti :=  vpc_nv), 
                        maxvp := mvp_nv

 \<rparr> "

(*Semantics of failed CAS transition *)
definition cas_fail_trans ::  "TId \<Rightarrow> nat \<Rightarrow> Loc \<Rightarrow>Val \<Rightarrow> Val\<Rightarrow> Reg  \<Rightarrow>  TState \<Rightarrow> TState " 
where
 " cas_fail_trans ti ind addr  v1 v2 r  ts   \<equiv> 
             let value= ( compval ts  ((memory ts)!ind)  addr ); 
                  nview =  if( ind \<noteq> (coh ts ti) addr )
                   then ind 
                else vrnew ts ti
                in
                  ts \<lparr> vrnew := (vrnew ts)(ti := max (vrnew ts ti) nview ), 
                      vpready := (vpready ts)(ti := max (vpready ts ti) nview ), 
                      maxcoh := ( maxcoh ts)(ti := max (maxcoh ts ti) ind ),
                      coh := (coh ts)(ti := (coh ts ti)(addr := ind)),
                      regs := (regs ts)(ti := (regs ts ti)(r := 0))   \<rparr> "


(*Semantics of mfence transition *)
definition   mfence_trans :: "TId \<Rightarrow> TState \<Rightarrow> TState "
  where
 " mfence_trans ti  ts  \<equiv>                 
             ts \<lparr> vrnew := (vrnew ts)(ti := max (vrnew ts ti)  (maxcoh ts ti)),
                 vpready := (vpready ts)(ti := max (vpready ts ti)  (maxcoh ts ti))  \<rparr> "


(*Semantics of flush transition *)
definition  flush_trans :: "TId \<Rightarrow> Loc \<Rightarrow> TState \<Rightarrow> TState"
 where
    "flush_trans ti addr ts  \<equiv>
                let  vpasync_nv  =   max (vpasync ts ti addr )  (maxcoh ts ti) ;
                     vpcommit_nv =  max (vpcommit ts ti addr )  (maxcoh ts ti)   in  
                       ts\<lparr> vpasync := (vpasync ts)(ti := (vpasync ts ti)(addr := vpasync_nv   )),
                           vpcommit := (vpcommit ts)(ti := (vpcommit ts ti)(addr := vpcommit_nv)),
                            maxvp  := (maxvp ts) (addr:=  max  vpcommit_nv  (maxvp ts addr) ) \<rparr>"


(*Semantics of  flushopt transition *)
definition flush_opt_trans :: "TId \<Rightarrow> Loc \<Rightarrow> TState \<Rightarrow> TState"
where
  "flush_opt_trans ti addr ts  \<equiv>
              let  c =(coh ts ti) addr in
                    ts\<lparr> vpasync := (vpasync ts)(ti := (vpasync ts ti) (addr := max (vpasync ts ti addr)(max (vpready ts ti) c )))\<rparr>"



(*sfence_trans :: "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> 'a TState_scheme \<Rightarrow> 'a TState_scheme"*)

(*Semantics of sfence transition *)
definition sfence_trans :: "TId \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> TState \<Rightarrow> TState"
  where
    "sfence_trans ti vpc_nv  mvp_nv  ts \<equiv>    
                let  vpready_nv = max (vpready ts ti)  (maxcoh ts ti)  in
           ts\<lparr> vpcommit := (vpcommit ts)(ti :=  vpc_nv), 
               vpready := (vpready ts)(ti := vpready_nv),
                maxvp := mvp_nv  \<rparr> " 




definition update_reg ::  "TId \<Rightarrow> Reg \<Rightarrow> Val \<Rightarrow>  TState \<Rightarrow> TState " 
  where 
 "  update_reg ti  r v   ts   \<equiv> 
                  ts \<lparr>  
                       regs := (regs ts)(ti := (regs ts ti)(r := v))  \<rparr> "


(* Basic lemmas about memory *)

lemma [simp]: "length (memory (  update_reg  ti  r v ts) ) = length(memory ts)"
  by (simp add:  update_reg_def) 


lemma [simp]: "length (memory (store_trans ts l addr ti) ) = length(memory ts) +1"
  by (simp add: store_trans_def) 


lemma length_s  [simp]: " length (memory (cas_succ_trans ti ind addr  v1 v2 r  vp mvp  ts)) =  length(memory ts) +1"
  by (simp add:  cas_succ_trans_def)


lemma [simp]: "memory (flush_trans ti addr ts) = memory ts"
  apply (simp add: flush_trans_def)
  by (metis (no_types, lifting) ext_inject surjective update_convs(5) update_convs(6) update_convs(8))

lemma [simp]: "memory (load_trans ti ind addr ts r) = memory ts"
  apply (simp add: load_trans_def)
  done

lemma [simp]: "memory (flush_opt_trans ti addr ts) = memory ts"
  by (simp add: flush_opt_trans_def)

lemma [simp]: "memory (mfence_trans ti ts) = memory ts"
  apply (simp add: mfence_trans_def)
  done

lemma [simp]: "memory (sfence_trans ti vp mvp ts) = memory ts"
  apply (simp add: sfence_trans_def)
  done
 
lemma [simp]: "memory (store_trans ts l addr ti) = (memory ts) @ [msg l addr ti] "
  by (simp add: store_trans_def)

lemma [simp]: "memory (cas_succ_trans ti ind addr  v1 v2  r  vp mvp  ts) = ( memory ts) @ [msg addr v2 ti] "
  by (simp add:  cas_succ_trans_def)

lemma [simp]: "memory (  cas_fail_trans ti ind addr  v1 v2 r ts ) = ( memory ts) "
  by (simp add:  cas_fail_trans_def)

(*lemma [simp]: "memory ( crash_trans ts) = [Init_Msg] "
  by (simp add:   crash_trans_def)*)

lemma coh_store_trans [simp]: "ti' \<noteq> ti \<Longrightarrow> coh (store_trans  ts l v ti') ti l =  coh ts ti l"
  by (simp add: store_trans_def)

(*************************)


(*Instructions *)
datatype instruction = 
     Load (lloc:Loc) (lreg:Reg) |
     Store (sloc: Loc)(sval:Val)|
     Flush (floc: Loc)          |
     Flush_opt (foloc: Loc)     |
     mfence                     |
     sfence                     |
     CAS (cloc:Loc) (cval1:Val) (cval2:Val)  (creg:Reg)
    


lemmas  comp_defs [simp] = compval_def comploc_def

(* Set of observable  timestamps given a view:  OTSF *)
definition  OTSF :: "TState \<Rightarrow> TId  \<Rightarrow> Loc \<Rightarrow> V \<Rightarrow> nat set"
where "OTSF ts ti l view  \<equiv> 

{t | t . 0\<le> t \<and> t < length(memory ts) \<and> 
         l= comploc ((memory ts)!t) l \<and> (coh ts ti l \<le> t) 
         \<and>( notoverwritten ts view t l)  } "


(* Set of observable  timestamps:  OTS *)
definition "OTS ts  ti  l  \<equiv> OTSF ts ti l (vrnew ts ti) "


(*

(* Set of all indexes in memory that point to messages with location addr *)
definition " last_entry_set ts addr \<equiv>  { i  | i. 0 \<le>i \<and> i < length(memory ts) \<and> comploc ((memory ts)!i) addr = addr}"



(* Set of all indexes in memory that point to messages with location addr *)
definition " last_entry_set_lim  ts addr lim  \<equiv>  { i  | i. 0 \<le>i \<and> i < length(memory ts) \<and> i \<le> lim  \<and> comploc ((memory ts)!i) addr = addr}"


(* Index in memory that point to last  message with location addr *)
definition " last_entry  ts addr  \<equiv> Max ( last_entry_set ts addr )"


(* Index in memory that point to last  message with location addr *)
definition " last_entry_lim  ts addr lim  \<equiv> Max ( last_entry_set_lim ts addr lim )"


*)



(* Set of all indexes in memory that point to messages with location addr *)
definition " last_entry_set ts addr \<equiv>  { i  | i. 0 \<le>i \<and> i < length(memory ts) \<and> comploc ((memory ts)!i) addr = addr}"




(* Index in memory that point to last  message with location addr *)
definition " last_entry  ts addr  \<equiv> Max ( last_entry_set ts addr )"




(*Assertion used in the CAS example: Returns true if the value of last  message with location x is v *)
abbreviation last_entry_val ::" Loc \<Rightarrow>Val\<Rightarrow>TState \<Rightarrow> bool" ("\<lceil>_:_\<rceil> _" [100,100,100])
  where
 "\<lceil>x:v\<rceil> \<sigma> \<equiv>  compval \<sigma> ( (memory \<sigma>)! ( last_entry  \<sigma>  x)) x= v  "


 (*Step definition*) 
definition step :: "TId \<Rightarrow> instruction \<Rightarrow> TState \<Rightarrow> TState\<Rightarrow> bool "
 where
    "step ti a ts ts'\<equiv>
     (case a of
         Load  x r  \<Rightarrow> 
          \<exists>ind. ind \<in> OTS ts  ti x  \<and>
           ts'  = load_trans  ti ind x ts r |

        CAS x  v1 v2 r \<Rightarrow>
         \<exists>ind  nv mnv . ( ind \<in> OTS ts ti x  \<and>  vpcommit_nv ti ts nv \<and> maxvp_nv ti ts mnv  \<and>
                  ( ( \<lceil>x:v1\<rceil> ts \<and> ( ind =last_entry  ts  x) \<and>ts' = cas_succ_trans  ti ind x  v1 v2 r nv mnv  ts )\<or>                     
                   ( ts' = cas_fail_trans  ti ind x  v1 v2 r ts) \<and> ( compval ts ( (memory ts)!  ind ) x \<noteq>  v1  \<or> ( ind \<noteq> last_entry  ts  x) ) ))
                  |
     
         Store  x v \<Rightarrow> 
           ts'  = store_trans ts x v ti | 
         Flush  x  \<Rightarrow> 
           ts'  = flush_trans  ti x ts |
         Flush_opt x \<Rightarrow>
           ts'  = flush_opt_trans  ti x ts|
          mfence  \<Rightarrow>
         ts' = mfence_trans ti ts  |
         sfence  \<Rightarrow>
          \<exists> nv mnv  . vpcommit_nv ti ts nv \<and> maxvp_nv ti ts mnv   \<and> ( ts'= sfence_trans ti nv mnv ts) 
                            
)" 


lemma step_cases:
       "step ti a ts ts'
          \<Longrightarrow> 
        \<lbrakk>\<And>  ind x r. ts' = load_trans  ti ind x ts r \<and> a = Load  x r \<and>  ind \<in> OTS ts ti x  \<Longrightarrow> P ts (load_trans  ti ind x ts r)\<rbrakk>
           \<Longrightarrow>
        \<lbrakk>\<And>  x v  .ts' = store_trans ts x v ti \<and> a = Store  x v  
  \<Longrightarrow> P ts (store_trans  ts x v ti)\<rbrakk>
          \<Longrightarrow>
        \<lbrakk>\<And>  x  .ts' = flush_trans ti x ts \<and> a = Flush  x 
  \<Longrightarrow> P ts (flush_trans ti x ts)\<rbrakk>
           \<Longrightarrow>
      \<lbrakk>\<And>  x  .ts' = flush_opt_trans ti x ts \<and> a = Flush_opt  x 
  \<Longrightarrow> P ts (flush_opt_trans ti x ts)\<rbrakk>
          \<Longrightarrow>
      \<lbrakk>ts' = mfence_trans ti  ts \<and> a = mfence
  \<Longrightarrow> P ts (mfence_trans ti ts)\<rbrakk>
            \<Longrightarrow>
 \<lbrakk>\<And>  nv1 nv2  .ts' = sfence_trans ti nv1 nv2 ts \<and> a = sfence \<and>
   vpcommit_nv ti ts nv1 \<and>   maxvp_nv  ti ts nv2
  \<Longrightarrow> P ts (sfence_trans ti nv1 nv2  ts)\<rbrakk>

 \<Longrightarrow>
      \<lbrakk>\<And>  x v1 v2 r ind nv1 nv2 . ts' = cas_succ_trans ti ind x v1 v2 r nv1 nv2 ts   \<and> a =  CAS x  v1 v2 r \<and>  ind \<in> OTS ts ti x \<and>  \<lceil>x:v1\<rceil> ts \<and> ind =  last_entry  ts  x \<and>
   vpcommit_nv ti ts nv1 \<and>   maxvp_nv  ti ts nv2
  \<Longrightarrow> P ts (cas_succ_trans ti ind x v1 v2 r nv1 nv2  ts)\<rbrakk>

 \<Longrightarrow>
      \<lbrakk>\<And>  x v1 v2 r ind . ts' = cas_fail_trans ti ind x v1 v2 r ts  \<and>  ind \<in> OTS ts ti x  \<and> a =  CAS x  v1 v2 r \<and> \<not>(  \<lceil>x:v1\<rceil> ts \<and> ind = last_entry  ts  x)
  \<Longrightarrow> P ts (cas_fail_trans ti ind x v1 v2 r ts)\<rbrakk>

  \<Longrightarrow> P ts ts'"
  apply (simp add: step_def)
  apply(case_tac a)
        apply(simp_all)
  by (auto +)

(*   \<Longrightarrow> 
       \<lbrakk> ts' = crash_trans ts \<and> a = crash  \<Longrightarrow> P ts (crash_trans ts )\<rbrakk>*)


(*read abbreviation *)
abbreviation LdX__abbr:: " TState  \<Rightarrow> Reg \<Rightarrow> Loc \<Rightarrow> TId\<Rightarrow> TState \<Rightarrow> bool" ("_ [_ \<leftarrow> _]\<^sub>_ _" [100,100,100,100,100])
  where "\<sigma> [r \<leftarrow> x]\<^sub>t \<sigma>' \<equiv> step t ( Load  x r ) \<sigma> \<sigma>'"

(*write abbreviation *)
abbreviation StX__abbr:: " TState \<Rightarrow> Loc \<Rightarrow> Val \<Rightarrow> TId \<Rightarrow> TState \<Rightarrow> bool" ("_ [_ := _]\<^sub>_ _" [100,100,100,100,100])
  where "\<sigma> [x := v]\<^sub>t \<sigma>' \<equiv> step t ( Store  x v) \<sigma> \<sigma>'"

(*flush abbreviation *)
abbreviation FlX__abbr:: " TState \<Rightarrow> Loc  \<Rightarrow> TId \<Rightarrow> TState \<Rightarrow> bool" ("_ [flush _]\<^sub>_ _" [100,100,100,100])
  where "\<sigma> [flush x]\<^sub>t \<sigma>' \<equiv> step t ( Flush  x) \<sigma> \<sigma>'"

(*flush_opt abbreviation *)
abbreviation FloX__abbr:: " TState \<Rightarrow> Loc  \<Rightarrow> TId \<Rightarrow> TState \<Rightarrow> bool" ("_ [flush\<^sub>o _]\<^sub>_ _" [100,100,100,100])
  where "\<sigma> [flush\<^sub>o x]\<^sub>t \<sigma>' \<equiv> step t (  Flush_opt  x) \<sigma> \<sigma>'"

(*sfence abbreviation *)
abbreviation Sfence__abbr:: " TState  \<Rightarrow> TId \<Rightarrow> TState \<Rightarrow> bool" ("_ [sfence ]\<^sub>_ _" [100,100,100])
  where "\<sigma> [sfence]\<^sub>t \<sigma>' \<equiv> step t (sfence) \<sigma> \<sigma>'"

(*mfence abbreviation *)
abbreviation Mfence__abbr:: " TState  \<Rightarrow> TId \<Rightarrow> TState \<Rightarrow> bool" ("_ [mfence ]\<^sub>_ _" [100,100,100])
  where "\<sigma> [mfence]\<^sub>t \<sigma>' \<equiv> step t (mfence) \<sigma> \<sigma>'"


(*cas abbreviation *)
abbreviation CASX__abbr:: " TState \<Rightarrow> Loc \<Rightarrow> Val \<Rightarrow>Val \<Rightarrow> Reg \<Rightarrow>  TId \<Rightarrow> TState \<Rightarrow> bool" ("_ [CAS _ _ _ _]\<^sub>_ _" [100,100,100,100,100,100,100])
  where "\<sigma>  [CAS x v1 v2 r]\<^sub>t \<sigma>' \<equiv> step t (  CAS x  v1 v2 r) \<sigma> \<sigma>'"

(*crash abbreviation *)
(*abbreviation Crash__abbr:: " TState \<Rightarrow> TState \<Rightarrow>  bool" ("_ [Crash] _" [100,100])
  where "\<sigma>  [Crash] \<sigma>' \<equiv> step  (crash) \<sigma> \<sigma>'"*)



lemma test:
  assumes "  notoverwritten ts v2 selected_w l"
  and " v2 > v1"
shows "   notoverwritten ts v1 selected_w l"
  using assms apply (simp add: notoverwritten_def)
  done


(*lemmas about registers*)
lemma reg_same_st:
 assumes "step t ( Store  x v) ts ts'"
shows "  regs ts   = regs ts'"
  using assms
  apply (simp add: step_def)
  by (simp add: store_trans_def)
  

lemma reg_same_fl:
  assumes "step t ( Flush  x ) ts ts'"
shows "  regs ts   = regs ts'"
  using assms
  apply (simp add: step_def)
  apply (simp add: flush_trans_def)
  by (metis (no_types, lifting) ext_inject surjective update_convs(5) update_convs(6) update_convs(8))


lemma reg_same_flo:
  assumes "step t ( Flush_opt  x ) ts ts'"
shows "  regs ts   = regs ts'"
 using assms
  apply (simp add: step_def)
  by (simp add: flush_opt_trans_def)


lemma reg_same_sfence:
  assumes "step t ( sfence ) ts ts'" 
shows "  regs ts   = regs ts'"
using assms
  apply (simp add: step_def)
  apply (simp add: sfence_trans_def)
  by auto


lemma reg_same_mfence:
  assumes "step t ( mfence ) ts ts'" 
shows "  regs ts   = regs ts'"
using assms
  apply (simp add: step_def)
  by (simp add: mfence_trans_def)

lemma reg_same_CAS_dt:
  assumes "step t (  CAS x  v1 v2 r ) ts ts'" 
and " t \<noteq> t'"
shows "  regs ts t'   = regs ts' t'"
using assms
  apply (simp add: step_def)
  apply clarify
  apply (case_tac " ts' = cas_succ_trans t ind x v1 v2 r nv mnv  ts")
  apply (simp add: cas_succ_trans_def)
  by (simp add: cas_fail_trans_def)


lemma reg_same_CAS_dr : 
  assumes "step t (  CAS x  v1 v2 r ) ts ts'" 
and " r \<noteq> z"
shows "  regs ts t z   = regs ts' t z "
using assms
  apply (simp add: step_def)
  apply clarify
  apply (case_tac " ts' = cas_succ_trans t ind x v1 v2  r nv mnv ts")
  apply (simp add: cas_succ_trans_def)
  by (simp add: cas_fail_trans_def)


lemma reg_same_ld_dt:
 assumes "step t ( Load  x r ) ts ts'"
and " r' \<noteq> r"
shows "  regs ts' t' r'    = regs ts t' r' "
  using assms
  apply (simp add: step_def)
  apply (simp add: load_trans_def)
  by fastforce


lemma reg_same_ld_dr:
assumes "step t ( Load  x r ) ts ts'"
and " t \<noteq> t'"
shows "  regs ts' t' r'    = regs ts t' r' "
  using assms
  apply (simp add: step_def)
  apply (simp add: load_trans_def)
  by fastforce

end

