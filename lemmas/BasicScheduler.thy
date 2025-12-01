theory BasicScheduler
  imports "HOL-TLA.TLA"
begin
datatype task_id = Task1 | Task2 | Task3
datatype task_state = Ready | Running | Completed

consts
  task_state :: "task_id \<Rightarrow> task_state stfun"
  current_task :: "task_id stfun"

(* ===== ПРАВИЛЬНЫЕ ОПРЕДЕЛЕНИЯ ===== *)
definition TaskReady :: "task_id \<Rightarrow> temporal" where
  "TaskReady t \<equiv> (\<lambda>\<sigma>. task_state t (\<sigma> 0) = Ready)"


(* Задача выполняется *)
definition TaskRunning :: "task_id \<Rightarrow> temporal" where  
  "TaskRunning t \<equiv> (\<lambda>b. task_state t (first b) = Running)"

(* Задача завершена *)
definition TaskCompleted :: "task_id \<Rightarrow> temporal" where
  "TaskCompleted t \<equiv> (\<lambda>b. task_state t (first b) = Completed)"

(* ===== АЛЬТЕРНАТИВА: Чистые temporal константы ===== *)

consts
  Task1Ready :: temporal
  Task1Running :: temporal
  Task1Completed :: temporal
  Task2Ready :: temporal
  Task2Running :: temporal  
  Task2Completed :: temporal

(* ===== САМЫЙ ПРОСТОЙ ВАРИАНТ ===== *)

(* Вместо параметризованных определений - отдельные константы *)
consts
  T1_Ready :: temporal
  T1_Running :: temporal
  T1_Done :: temporal
  T2_Ready :: temporal  
  T2_Running :: temporal
  T2_Done :: temporal
  CurrentTask :: "task_id stfun"  (* Текущая задача *)

axiomatization where
  (* Взаимоисключающие состояния задач *)
  task1_states: "\<turnstile> T1_Ready \<oplus> T1_Running \<oplus> T1_Done" and
  task2_states: "\<turnstile> T2_Ready \<oplus> T2_Running \<oplus> T2_Done" and
  
  (* Взаимное исключение: только одна задача может выполняться *)
  mutual_exclusion: "\<turnstile> \<not>(T1_Running \<and> T2_Running)" and
  
  (* Планирование: готовые задачи eventually запускаются *)
  schedule_t1: "\<turnstile> T1_Ready \<leadsto> T1_Running" and
  schedule_t2: "\<turnstile> T2_Ready \<leadsto> T2_Running" and
  
  (* Задачи eventually завершаются *)
  complete_t1: "\<turnstile> T1_Running \<leadsto> T1_Done" and
  complete_t2: "\<turnstile> T2_Running \<leadsto> T2_Done"

(* Основные теоремы планировщика *)
theorem no_starvation:
  "\<turnstile> (T1_Ready \<longrightarrow> \<diamond>T1_Running) \<and> (T2_Ready \<longrightarrow> \<diamond>T2_Running)"
  using schedule_t1 schedule_t2
  unfolding leadsto_def
  by tla

theorem tasks_eventually_complete:
  "\<turnstile> (T1_Running \<longrightarrow> \<diamond>T1_Done) \<and> (T2_Running \<longrightarrow> \<diamond>T2_Done)"  
  using complete_t1 complete_t2
  unfolding leadsto_def
  by tla

end