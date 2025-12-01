theory BeautifulArrows
imports Main
begin

datatype SystemMode = NORMAL | ADMIN | LOCKED


definition enter_admin_mode :: "SystemMode \<Rightarrow> SystemMode" where
  "enter_admin_mode current_state = 
   (if current_state = NORMAL then ADMIN else current_state)"

notation enter_admin_mode ("_ \<hookrightarrow>\<lparr>admin\<rparr>" [1000] 1000)

definition exit_to_normal :: "SystemMode \<Rightarrow> SystemMode" where  
  "exit_to_normal _ = NORMAL"

notation exit_to_normal ("_ \<hookleftarrow>\<lparr>normal\<rparr>" [1000] 1000)

lemma beautiful_proof:
  "NORMAL \<hookrightarrow>\<lparr>admin\<rparr> \<hookleftarrow>\<lparr>normal\<rparr> = NORMAL"
  by (simp add: enter_admin_mode_def exit_to_normal_def)

end