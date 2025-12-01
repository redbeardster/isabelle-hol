theory FSMReachable
  imports Main
begin

(* ===== Определение конечного автомата ===== *)
datatype State = INIT | WORKING | DONE | ERROR

(* Отношение переходов *)
definition trans :: "State \<Rightarrow> State \<Rightarrow> bool" where
  "trans s s' \<equiv> 
    (s = INIT \<and> s' = WORKING) \<or>
    (s = WORKING \<and> s' = DONE) \<or> 
    (s = WORKING \<and> s' = ERROR) \<or>
    (s = DONE \<and> s' = DONE) \<or>      
    (s = ERROR \<and> s' = ERROR)"     

(* Транзитивное замыкание *)
definition reachable :: "State \<Rightarrow> State \<Rightarrow> bool" where
  "reachable s s' \<equiv> (trans\<^sup>*\<^sup>*) s s'"

(* ===== Базовые свойства достижимости ===== *)

(* INIT достигает WORKING за 1 шаг *)
lemma INIT_to_WORKING: "trans INIT WORKING"
  unfolding trans_def by simp

lemma reachable_INIT_WORKING: "reachable INIT WORKING"
  unfolding reachable_def
  using INIT_to_WORKING by (rule r_into_rtranclp)

(* WORKING достигает DONE за 1 шаг *)
lemma WORKING_to_DONE: "trans WORKING DONE" 
  unfolding trans_def by simp

lemma reachable_WORKING_DONE: "reachable WORKING DONE"
  unfolding reachable_def
  using WORKING_to_DONE by (rule r_into_rtranclp)

(* INIT достигает DONE за 2 шага *)
lemma INIT_to_DONE_2_steps: "reachable INIT DONE"
proof -
  have "trans INIT WORKING" by (rule INIT_to_WORKING)
  moreover have "trans WORKING DONE" by (rule WORKING_to_DONE)
  ultimately show "reachable INIT DONE"
    unfolding reachable_def
  by simp
qed

(* ===== Анализ минимального числа шагов ===== *)
(* Достижимость за ТОЧНО n шагов *)
lemma INIT_to_DONE_exact_2_steps: "(trans ^^ 2) INIT DONE"
proof -
  have "trans INIT WORKING" by (rule INIT_to_WORKING)
  moreover have "trans WORKING DONE" by (rule WORKING_to_DONE)
  ultimately show ?thesis  by (metis Suc_1 relpowp_1 relpowp_Suc_I)
qed

(* НЕВОЗМОЖНО достичь DONE из INIT за 1 шаг *)
lemma not_INIT_to_DONE_1_step: "\<not> (trans ^^ 1) INIT DONE"
  unfolding trans_def relpowp.simps
  by auto

(* НЕВОЗМОЖНО достичь DONE из INIT за 0 шагов *)
lemma not_INIT_to_DONE_0_steps: "\<not> (trans ^^ 0) INIT DONE"
  by simp

(* Минимальное число шагов: 2 *)
lemma min_steps_INIT_to_DONE: 
  "\<exists>n. (trans ^^ n) INIT DONE \<and> 
       (\<forall>m < n. \<not> (trans ^^ m) INIT DONE)"
  using INIT_to_DONE_exact_2_steps less_2_cases by blast

(* ===== Анализ ВОЗМОЖНОЙ недостижимости ===== *)
datatype State2 = INIT2 | WORKING2 | DONE2 | ERROR2 | BROKEN

definition trans2 :: "State2 \<Rightarrow> State2 \<Rightarrow> bool" where
  "trans2 s s' \<equiv> 
    (s = INIT2 \<and> s' = WORKING2) \<or>
    (s = WORKING2 \<and> s' = ERROR2) \<or>  
    (s = ERROR2 \<and> s' = ERROR2)"

definition reachable2 :: "State2 \<Rightarrow> State2 \<Rightarrow> bool" where
  "reachable2 s s' \<equiv> (trans2\<^sup>*\<^sup>*) s s'"

(* DONE2 НЕдостижимо из INIT2 *)
lemma DONE2_unreachable_from_INIT2: "\<not> reachable2 INIT2 DONE2"
  by (metis State2.distinct(15,3) State2.simps(10) reachable2_def rtranclp.cases trans2_def)

(* ===== Автоматический анализ достижимости ===== *)

(* Множество достижимых состояний из INIT *)
definition reachable_set_from_INIT :: "State set" where
  "reachable_set_from_INIT = {s. reachable INIT s}"

lemma reachable_set_INIT: "reachable_set_from_INIT = {INIT, WORKING, DONE, ERROR}"
  unfolding reachable_set_from_INIT_def
proof (intro equalityI subsetI)
  fix s assume "s \<in> {s. reachable INIT s}"
  then obtain n where "(trans ^^ n) INIT s"
    unfolding reachable_def using rtranclp_imp_relpowp by fastforce  
  then show "s \<in> {INIT, WORKING, DONE, ERROR}"
  using State.exhaust by blast
next
  fix s assume "s \<in> {INIT, WORKING, DONE, ERROR}"
  then show "s \<in> {s. reachable INIT s}"
  by (metis FSMReachable.trans_def State.exhaust mem_Collect_eq reachable_def rtranclp.simps)
qed

(* ===== Анализ временны́х свойств ===== *)
(* DONE достижимо из INIT за КАК МИНИМУМ 2 шага *)
theorem DONE_reachable_in_at_least_2_steps:
  "reachable INIT DONE \<and> 
   (\<exists>n \<ge> 2. (trans ^^ n) INIT DONE) \<and>
   (\<forall>n < 2. \<not> (trans ^^ n) INIT DONE)"
proof -
  have reachable: "reachable INIT DONE"
    by (rule INIT_to_DONE_2_steps)  
  have exists_2_steps: "\<exists>n \<ge> 2. (trans ^^ n) INIT DONE"
    using INIT_to_DONE_exact_2_steps by auto   
  have not_fewer: "\<forall>n < 2. \<not> (trans ^^ n) INIT DONE"
    using not_INIT_to_DONE_0_steps not_INIT_to_DONE_1_step  using less_2_cases by fastforce    
  show ?thesis using reachable exists_2_steps not_fewer by blast
qed

(* DONE МОЖЕТ БЫТЬ недостижимо в другой конфигурации *)
theorem DONE_may_be_unreachable:
  "\<exists>trans_system. (let reach = (trans_system\<^sup>*\<^sup>*) in 
                   \<not> reach INIT DONE)"
proof -
  have "\<exists>p. \<not> p (sk DONE INIT p::State) DONE \<and> DONE \<noteq> INIT"
    by auto
  then show ?thesis
    by (meson rtranclp.cases)
qed

(* ===== Визуализация через теоремы ===== *)
(* Граф достижимости *)
lemma reachability_graph:
  "reachable INIT INIT"    
  "reachable INIT WORKING"   
  "reachable INIT DONE"    
  "reachable INIT ERROR"  
  apply (simp add: reachable_def)
  using reachable_INIT_WORKING apply blast
  apply (simp add: INIT_to_DONE_2_steps)
  using reachable_set_INIT reachable_set_from_INIT_def by auto

(* "Мертвые" состояния - те, из которых нельзя выйти *)
definition deadlock_state :: "State \<Rightarrow> bool" where
  "deadlock_state s \<equiv> \<forall>s'. trans s s' \<longrightarrow> s' = s"

lemma deadlock_states: "deadlock_state DONE" "deadlock_state ERROR"
  unfolding deadlock_state_def trans_def by auto

end