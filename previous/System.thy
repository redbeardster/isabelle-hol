theory System
imports Main

begin
datatype ('proc, 'msg, 'val) event
  = Receive (msg_sender: 'proc) (recv_msg: 'msg)
  | Request 'val
  | Timeout

type_synonym ('proc, 'state, 'msg, 'val) step_func =
  \<open>'proc \<Rightarrow> 'state \<Rightarrow> ('proc, 'msg, 'val) event \<Rightarrow>
  ('state \<times> ('proc \<times> 'msg) set)\<close>

fun valid_event :: \<open>('proc, 'msg, 'val) event \<Rightarrow> 'proc \<Rightarrow>
                    ('proc \<times> 'proc \<times> 'msg) set \<Rightarrow> bool\<close>
where
  \<open>valid_event (Receive sender msg) recpt msgs =
    ((sender, recpt, msg) \<in> msgs)\<close> |
  \<open>valid_event (Request _) _ _ = True\<close> |
  \<open>valid_event Timeout _ _ = True\<close>


  inductive execute ::
  \<open>('proc, 'state, 'msg, 'val) step_func \<Rightarrow> ('proc \<Rightarrow> 'state) \<Rightarrow>
   'proc set \<Rightarrow> ('proc \<times> ('proc, 'msg, 'val) event) list \<Rightarrow>
   ('proc \<times> 'proc \<times> 'msg) set \<Rightarrow> ('proc \<Rightarrow> 'state) \<Rightarrow> bool\<close>
where
  \<open>execute step init procs [] {} init\<close> |
  \<open>\<lbrakk>execute step init procs events msgs states;
    proc \<in> procs;
    valid_event event proc msgs;
    step proc (states proc) event = (new_state, sent);
    events' = events @ [(proc, event)];
    msgs' = msgs \<union> {m. \<exists>(recpt, msg) \<in> sent.
                       m = (proc, recpt, msg)};
    states' = states (proc := new_state)
   \<rbrakk> \<Longrightarrow> execute step init procs events' msgs' states'\<close>


   theorem prove_invariant:
  assumes \<open>execute step init procs events msgs states\<close>
  shows \<open>some_invariant states\<close>
using assms proof (induction events arbitrary: msgs states
                   rule: List.rev_induct)
  case Nil
  then show \<open>some_invariant states\<close> sorry
next
  case (snoc event events)
  then show ?case sorry
qed

end