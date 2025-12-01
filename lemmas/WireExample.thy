theory WireExample
  imports Main
begin


datatype wire_state = Working | Broken
datatype message = Some message | None 


record system_state =
  wire :: wire_state
  alice_message :: "message" 
  bob_received :: "message"  

definition initial_state :: "system_state" where
  "initial_state = \<lparr> wire = Working, alice_message = None, bob_received = None \<rparr>"

definition alice_send :: "message \<Rightarrow> system_state \<Rightarrow> system_state" where
  "alice_send msg s = s \<lparr> alice_message := Some msg \<rparr>" 


value "alice_send None \<lparr> wire = Working, alice_message = None, bob_received = None\<rparr>"

 definition bob_receive :: "system_state \<Rightarrow> system_state" where
  "bob_receive s = (case alice_message s of
       message.None \<Rightarrow>  s \<lparr> bob_received := message.None\<rparr>
    | Some msg \<Rightarrow>  (case wire s of 
         Working \<Rightarrow> s \<lparr> bob_received := Some msg \<rparr>
         | Broken \<Rightarrow> s \<lparr> bob_received := message.None \<rparr>))"

 definition system_step :: "message  \<Rightarrow> system_state \<Rightarrow> system_state" where
  "system_step message s = bob_receive (alice_send message s)"


 lemma lemma3:  
  assumes "alice_message s = Some msg" "wire s = Working" 
  shows "bob_received (system_step msg s) = Some msg"
  by (simp add: alice_send_def assms(2) bob_receive_def system_step_def)
    
lemma lemma4:  
  assumes "alice_message s = Some msg"  "wire s = Broken"
  shows "bob_received (system_step msg s) = None"
   by (simp add: alice_send_def assms(2) bob_receive_def system_step_def)
 

 lemma lemma2: 
    assumes "alice_message s = message.None" and  "wire s = Working"
    shows "bob_received (system_step None s) = None"
   
 
  
(* 
datatype message = Some message  | Nothing
value "message"

record state =
  alice_sent :: message
  bob_received :: message

definition initial_state :: state where
  "initial_state \<equiv> \<lparr> alice_sent = Nothing, bob_received = Nothing \<rparr>"

definition send_message :: "message \<Rightarrow> state \<Rightarrow> state" where
  "send_message m s \<equiv> \<lparr> alice_sent = m, bob_received = m \<rparr>"

lemma bob_receives_nothing_if_alice_sends_nothing:
  "bob_received (send_message Nothing s) = Nothing"
  using [[simp_trace]]
  by (simp add: send_message_def)

 *)

function check :: "string \<Rightarrow> bool"
  where 
    "check (''good'') = True"
| "s \<noteq> ''good'' \<Longrightarrow> check s = False"
by auto
termination by (relation "{}") simp



end