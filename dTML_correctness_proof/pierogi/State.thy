theory State
imports Main 
begin

(*declare [[ smt_timeout = 10000 ]]*)


type_synonym Val  = nat (* value *)
type_synonym Loc = nat (* location *)
type_synonym V = nat (* view *) 
type_synonym TId  = nat (* thread id*)
type_synonym Reg  = nat (*register*)


datatype Msg = msg (loc: Loc) (val: Val) (tid: TId)  | Init_Msg

consts syst :: TId

(*datatype exp = tid:TId | syst*)

(*The thread state is defined in "Cho, K., Lee, S. H., Raad, A., & Kang, J. (2021). Revamping Hardware Persistency Models." *)

(*thread state*)
record TState  = 
regs:: " TId \<Rightarrow> Reg \<Rightarrow> Val" (*  Contents of thread-local registers *)
coh ::"TId \<Rightarrow> Loc \<Rightarrow> V"     (* Upper bound of past reads and writes on a location (e.g. l) and lower bound of future reads and writes on l *)
vrnew ::"TId \<Rightarrow> V"          (* Upper bound of past updates, upper bound of external reads (from other threads) and lower bound of future reads *)
vpready:: "TId \<Rightarrow> V"        (* Upper bound of past external reads (from other threads)and lower bound of messages to be asynchronously flushed by future flushopt *)
vpcommit:: "TId \<Rightarrow> Loc \<Rightarrow> V" (*Upper bound of past  flush or flushopt  on a location (e.g. l) followed by fences/updates and lower bound of persisted messages on l to survive a crash*)
vpasync::"TId \<Rightarrow> Loc \<Rightarrow> V"  (* Upper bound of past flush/flushopt  on a location (e.g. l) and lower bound of messages on l to be persisted by future
fences/updates*)
maxcoh:: "TId \<Rightarrow> V"         (*Maximum coh view of a thread *)
maxvp:: "Loc \<Rightarrow> V"          (*Maximum vpcommit view for a location *)
survived_val:: "Loc \<Rightarrow> V"     
memory :: "Msg list"        (* Memory is represented as a list of messages *)


(* Start predicate. All views are 0 in the beginning *)
definition start :: "TState \<Rightarrow> bool"
  where
  "start s \<equiv>
      (\<forall> ti.\<forall>r. regs s ti r = 0)
    \<and> (\<forall> ti.\<forall>l.  coh s ti l = 0 \<and> vpcommit  s ti l = 0 \<and> vpasync  s ti l = 0  )
    \<and> (\<forall> ti. vrnew s ti = 0 \<and> vpready s ti = 0)
    \<and>  (\<forall> ti. maxcoh  s ti = 0)
    \<and>   (\<forall> l. maxvp s l = 0)
    \<and>  (\<forall> l. survived_val s l = 0)
    \<and> (memory s = [Init_Msg]) " 



(* The memory begins with just a single message *)
lemma start_size:
  assumes "start ts" 
  shows "size (memory ts) = 1"
  using assms by (simp add: start_def) 
end