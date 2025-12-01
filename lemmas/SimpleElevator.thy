theory SimpleElevator
  imports "HOL-TLA.TLA"
begin

(* Только 2 этажа для простоты *)
datatype floor = Floor1 | Floor2

consts
  AtFloor1 :: temporal
  AtFloor2 :: temporal  
  CallFrom1 :: temporal
  CallFrom2 :: temporal

axiomatization where
  initial_state: "\<turnstile> AtFloor1" and
  exclusivity: "\<turnstile> (AtFloor1 \<longrightarrow> \<not>AtFloor2) \<and> (AtFloor2 \<longrightarrow> \<not>AtFloor1)" and
  
  (* Действия *)
  move_to_2: "\<turnstile> AtFloor1 \<longrightarrow> \<diamond>AtFloor2" and
  move_to_1: "\<turnstile> AtFloor2 \<longrightarrow> \<diamond>AtFloor1" and
    
  (* Обслуживание вызовов *)
  serve_call_1: "\<turnstile> CallFrom1 \<and> AtFloor1 \<longrightarrow> \<diamond>\<not>CallFrom1" and
  serve_call_2: "\<turnstile> CallFrom2 \<and> AtFloor2 \<longrightarrow> \<diamond>\<not>CallFrom2" and
    
  (* Вызовы eventually обслуживаются *)
  liveness: "\<turnstile> CallFrom1 \<leadsto> \<not>CallFrom1 \<and> CallFrom2 \<leadsto> \<not>CallFrom2"

(* Основная теорема: каждый вызов будет обслужен *)
(* theorem all_requests_served:
  "\<turnstile> (CallFrom1 \<longrightarrow> \<diamond>\<not>CallFrom1) \<and> (CallFrom2 \<longrightarrow> \<diamond>\<not>CallFrom2)"
  using liveness  serve_call_1 serve_call_2 BoxRec Init.Init_simps InitDmd  inteq_reflection leadsto_def temp_simps unl_lift int_simps
  proof -
  have "\<forall>p. p = (AtFloor1 \<longrightarrow> AtFloor1) \<or> \<not> (\<turnstile> p)"
    by auto
  then show ?thesis
    by (smt (z3) exclusivity initial_state int_simps(10,12,13,2,20,32,4) inteq_reflection move_to_2 temp_simps(2))
qed 
 *)

(* Лифт eventually посещает все этажи *)
theorem visits_all_floors:
  "\<turnstile> \<diamond>AtFloor1 \<and> \<diamond>AtFloor2"
  using move_to_1 move_to_2 initial_state liveness  serve_call_1 serve_call_2 BoxRec Init.Init_simps(1,2) InitDmd  inteq_reflection temp_simps  int_simps(9,10,20)
  by metis

(* Вызов не остается вечно необслуженным *)
theorem no_starved_requests:
  "\<turnstile> \<box>(CallFrom1 \<longrightarrow> \<diamond>\<not>CallFrom1) \<and> \<box>(CallFrom2 \<longrightarrow> \<diamond>\<not>CallFrom2)"
  using liveness move_to_1 move_to_2 initial_state liveness  serve_call_1 serve_call_2 BoxRec Init.Init_simps(1,2) InitDmd  inteq_reflection temp_simps  int_simps(9,10,20)
  unfolding leadsto_def
  by (metis exclusivity int_simps(14) more_temp_simps3(7))

(* Безопасность: лифт всегда на каком-то этаже *)
theorem always_on_floor:
  "\<turnstile> \<box>(AtFloor1 \<or> AtFloor2)"
  using exclusivity
  by (simp add: initial_state necT tempD tempI)

lemma call_from_1_served_from_2:
  assumes "\<turnstile> CallFrom1 \<and> AtFloor2"
  shows "\<turnstile> \<diamond>(AtFloor1 \<and> \<not>CallFrom1)"
  unfolding leadsto_def
  using assms move_to_1 move_to_2 serve_call_1 liveness always_on_floor exclusivity no_starved_requests visits_all_floors  initial_state serve_call_1 serve_call_2 BoxRec Init.Init_simps(1,2) InitDmd  inteq_reflection temp_simps
  by fastforce
  


end