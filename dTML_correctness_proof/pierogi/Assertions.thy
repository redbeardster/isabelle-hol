theory Assertions
imports  Language Main
begin




(* Set of all indexes in memory that point to messages with location addr *)
definition " last_entry_set_lim  ts addr lim  \<equiv>  { i  | i. 0 \<le>i \<and> i < length(memory ts) \<and> i \<le> lim  \<and> comploc ((memory ts)!i) addr = addr}"


(* Index in memory that point to last  message with location addr *)
definition " last_entry_lim  ts addr lim  \<equiv> Max ( last_entry_set_lim ts addr lim )"


definition "valOf  i l \<sigma>  \<equiv> (compval ( \<sigma>)((memory ( \<sigma>))!(i)) l)"

definition "lastVal  l \<sigma>  \<equiv> (compval ( \<sigma>)((memory ( \<sigma>))!(last_entry ( \<sigma>) l)) l)"



(* Set of observable persistent timestamps:  OPTS *)
definition "OPTS  ts  l  \<equiv> {t | t.  0\<le> t \<and> t < length(memory ts) \<and> l= comploc ((memory ts)!t) l
  \<and> ( notoverwritten ts (maxvp ts  l)  t l)} "


(* Set of observable asynchronous timestamps:  OATS *)
definition "OATS  ts ti  l  \<equiv> {t | t.  0\<le> t \<and> t < length(memory ts) \<and> l= comploc ((memory ts)!t) l
   \<and> ( notoverwritten ts (vpasync ts ti  l)  t l)} " 


(* Auxiliary definition for the set of conditional observation *)
definition " compvrnew ts ti ind l \<equiv> 
 let  nview =  if( ind \<noteq> (coh ts ti) l )
                   then ind 
                else vrnew ts ti
in  max nview (vrnew ts ti)"


(* Auxiliary definition for the set of conditional observation *)
definition " cond_ts ts ti l v \<equiv> {compvrnew ts ti t l   | t. t \<in> OTS ts ti l \<and> v = compval ts ((memory ts)!t) l }"


(* Set of conditionally observable timestamps: COBTS *)
definition " COBTS x y v ti ts \<equiv>  \<Union> { OTSF ts ti y nview | nview.   nview  \<in> cond_ts ts ti x v} "


(* Abbreviation for the set of observable persistent values: OPV *)
(*abbreviation OPab:: "Loc \<Rightarrow> TState \<Rightarrow> Val set " ("[_]\<^sub>P_"[100,100])
where
"[l]\<^sub>P \<sigma> \<equiv> mapval (OPTS  \<sigma>  l) (memory \<sigma>) "  *)


(*Auxiliary definition for sets of values.  Maps an index in the memory array to the value of the message that this index points to *)
definition mapval
  where "mapval ts addr  B li = (\<lambda>x. compval ts ((li)!x) addr ) ` B" 

(* Abbreviation for the set of observable asynchronous values: OAV *)
abbreviation OAab ::" Loc \<Rightarrow> TId \<Rightarrow> TState \<Rightarrow> Val set" ("[_]\<^sup>A\<^sub>_  _" [100,100,100])
where
"[l]\<^sup>A\<^sub>t \<sigma> \<equiv> mapval \<sigma> l (OATS  \<sigma> t  l) (memory \<sigma>)  "




abbreviation OPab:: "Loc \<Rightarrow> TState \<Rightarrow> Val set " ("[_]\<^sub>P_"[100,100])
where
"[l]\<^sub>P \<sigma> \<equiv> mapval \<sigma> l (OPTS  \<sigma>  l) (memory \<sigma>) " 

(*definition "select_survived_val \<sigma>  x = (SOME i. i \<in> [x]\<^sub>P \<sigma>)"*)


(* Abbreviation for the set of observable values: OV *)
abbreviation OVab ::" Loc \<Rightarrow> TId \<Rightarrow> TState \<Rightarrow> Val set" ("[_]\<^sub>_ _" [100,100,100])
  where
 "[l]\<^sub>t \<sigma> \<equiv> mapval \<sigma> l (OTS  \<sigma> t l) (memory \<sigma>)  "




(*Abbreviation for the  set of values of the conditional observation *)
abbreviation COBVab :: "Loc  \<Rightarrow> Val  \<Rightarrow> Loc  \<Rightarrow> TId \<Rightarrow> TState \<Rightarrow> Val set" ("\<langle>_  _\<rangle>[_]\<^sub>_ _ " [100, 100, 100, 100, 100])
  where "\<langle>x  v\<rangle>[y]\<^sub>t  \<sigma> \<equiv>  mapval \<sigma> y (COBTS x y v t \<sigma>) (memory \<sigma>) "
(*check*)

(*Abbreviation for set of observable timestamps containing only the last write at x *)
abbreviation OTS_local_max ::" Loc \<Rightarrow> TId \<Rightarrow> TState \<Rightarrow> bool" ("\<lceil>_\<rceil>\<^sub>_ _" [100,100,100])
  where
 "\<lceil>l\<rceil>\<^sub>t \<sigma> \<equiv>  (OTS  \<sigma> t l) = { last_entry  \<sigma>  l  }  "

(*new*)
abbreviation OPTS_local_max ::" Loc  \<Rightarrow> TState \<Rightarrow> bool" ("\<lceil>_\<rceil>\<^sub>P _" [100,100])
  where
 "\<lceil>l\<rceil>\<^sub>P \<sigma> \<equiv>  (OPTS  \<sigma>  l) = { last_entry  \<sigma>  l  }  "





(*Combining  OTS_local_max and  OVab in one abbreviation to save space  *)
abbreviation OV_local_max_comp ::" Loc \<Rightarrow>Val \<Rightarrow> TId \<Rightarrow> TState \<Rightarrow> bool" ("\<lceil>_,_\<rceil>\<^sub>_ _" [100, 100,100,100])
  where
 "\<lceil>x,v\<rceil>\<^sub>t \<sigma> \<equiv> [x]\<^sub>t \<sigma> ={v} \<and>  \<lceil>x\<rceil>\<^sub>t \<sigma> "


(* Expression that holds iff a flush on adress x is  guaranteed to flush the last  write to x to persistent memory.*)
abbreviation flush_order :: " Loc \<Rightarrow> TId \<Rightarrow>  TState \<Rightarrow> bool" ( "\<lceil>FLUSH _ \<rceil>\<^sub>_ _ "  [100,100,100])
 where
 "\<lceil>FLUSH l\<rceil>\<^sub>t \<sigma> \<equiv>   last_entry  \<sigma>  l \<le>   (max ( maxcoh \<sigma> t)  (maxvp \<sigma> l))   "


(*Expression that holds iff after performing an mfence, the view ofthread t will be the last write on adress l*)
abbreviation mfence_order :: " Loc \<Rightarrow> TId \<Rightarrow>  TState \<Rightarrow> bool" ( "\<lceil>MFENCE _ \<rceil>\<^sub>_ _ "  [100,100,100])
 where
 "\<lceil>MFENCE l\<rceil>\<^sub>t \<sigma> \<equiv>   last_entry  \<sigma>  l \<le>  (maxcoh \<sigma> t) " 


(*Auxiliary definition for count_oc *)
definition " oc_set ts  x v \<equiv>  {t | t.  0\<le> t \<and> t < length(memory ts) \<and> x= comploc ((memory ts)!t) x \<and> compval ts  ((memory ts)!t) x = v}"

(*Returns the number of memory messages with location x and value v *)
abbreviation count_oc :: " Loc \<Rightarrow> Val \<Rightarrow> TState \<Rightarrow> nat " ( "\<lparr>_,_\<rparr>  _" [100,100,100])
  where
" \<lparr>x,v\<rparr>  \<sigma>  \<equiv> card  (oc_set \<sigma>  x v) " 







(*see if i need*)
(*
(*new*)
definition "OTSr  ts  ti  l r x  \<equiv> {t | t. t \<in>   OTSF ts ti l (vrnew ts ti) \<and>
                                                 (notoverwritten  ts r t ( comploc ((memory ts)!t) x))  \<and>
                                                  t \<le> r } " 


abbreviation OVabr ::" Loc \<Rightarrow>Loc \<Rightarrow> TId \<Rightarrow> V \<Rightarrow> TState \<Rightarrow> Val set" ("[_|_]\<^sub>_   _ _" [100,100,100,100,100])
  where
 "[l|r]\<^sub>t x \<sigma>  \<equiv>  mapval \<sigma> l (OTSr  \<sigma>  t  l r x) (memory \<sigma>)  "

*)


(*auxiliary lemmas*)
lemma st_no:
  assumes "t = 0"
  and " start ts"
shows "\<forall>l ti.  notoverwritten ts (vrnew ts ti) t l"
  using assms  apply (simp add: start_def notoverwritten_def)
  by blast

lemma [simp]: "OTS (flush_trans ti l ts) ti l = OTS ts ti l"
  apply (simp add: flush_trans_def OTS_def OTSF_def notoverwritten_def  Let_def)
  done  



end