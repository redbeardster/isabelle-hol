theory SimpleEntryExit
imports Main
begin


datatype SystemMode = NORMAL | ADMIN | LOCKED

definition enter_admin_mode :: "SystemMode \<Rightarrow> SystemMode" where
  "enter_admin_mode current_state = 
   (if current_state = NORMAL then 
      ADMIN
    else 
      current_state)"

definition exit_to_normal :: "SystemMode \<Rightarrow> SystemMode" where
  "exit_to_normal _ = NORMAL"

lemma test_admin_cycle:
  "exit_to_normal (enter_admin_mode NORMAL) = NORMAL"
  by (simp add: enter_admin_mode_def exit_to_normal_def)

lemma test_already_admin:
  "enter_admin_mode ADMIN = ADMIN"  
  by (simp add: enter_admin_mode_def)

end