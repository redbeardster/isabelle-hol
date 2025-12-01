theory ScalableScheduler
  imports "HOL-TLA.TLA" "HOL-Library.Cardinality"
begin

(* Определяем все необходимые типы *)
datatype task_state = Ready | Running | Completed
datatype task = Task1 | Task2 | Task3 | Task4 | Task5

(* Константы *)
consts 
  task_status :: "task \<Rightarrow> task_state stfun"
  current_task :: "task stfun"

(* Множество всех задач *)
definition all_tasks_set :: "task set" where
  "all_tasks_set = {Task1, Task2, Task3, Task4, Task5}"

(* Количественные предикаты *)
 definition is_task_ready :: "task \<Rightarrow> (state \<Rightarrow> bool)" where
  "is_task_ready t \<equiv> (\<lambda>s. task_status t s = Ready)"

definition task_in_set :: "task \<Rightarrow> (state \<Rightarrow> bool)" where
  "task_in_set t \<equiv> (\<lambda>s. t \<in> all_tasks_set)"


(* definition AnyTaskReady :: temporal where
  "AnyTaskReady \<equiv> (\<lambda>b. \<exists>t \<in> all_tasks_set. is_task_ready t (b 0))"
 *)





(* definition CountReadyTasks :: "nat \<Rightarrow> temporal" where
  "CountReadyTasks n \<equiv> #(card {t \<in> all_tasks_set. task_status t = Ready} = n)"

definition AllTasksCompleted :: temporal where
  "AllTasksCompleted \<equiv> \<forall>\<forall> t \<in> all_tasks_set. #(task_status t = Completed)"

(* Индивидуальные состояния задач *)
definition TaskReady :: "task \<Rightarrow> temporal" where
  "TaskReady t \<equiv> case t of
    Task1 \<Rightarrow> #(task_status Task1 = Ready)
  | Task2 \<Rightarrow> #(task_status Task2 = Ready)
  | Task3 \<Rightarrow> #(task_status Task3 = Ready)
  | Task4 \<Rightarrow> #(task_status Task4 = Ready)  
  | Task5 \<Rightarrow> #(task_status Task5 = Ready)"

definition TaskRunning :: "task \<Rightarrow> temporal" where
  "TaskRunning t \<equiv> case t of
    Task1 \<Rightarrow> #(task_status Task1 = Running)
  | Task2 \<Rightarrow> #(task_status Task2 = Running)
  | Task3 \<Rightarrow> #(task_status Task3 = Running)
  | Task4 \<Rightarrow> #(task_status Task4 = Running)  
  | Task5 \<Rightarrow> #(task_status Task5 = Running)"

(* Аксиомы планировщика *)
axiomatization where
  (* Взаимное исключение *)
  mutual_exclusion: "\<turnstile> \<forall>t1 t2. t1 \<noteq> t2 \<longrightarrow> \<not>(TaskRunning t1 \<and> TaskRunning t2)" and
  
  (* Планирование *)
  scheduling: "\<turnstile> \<forall>t. TaskReady t \<leadsto> TaskRunning t" and
  
  (* Завершение задач *)
  completion: "\<turnstile> \<forall>t. TaskRunning t \<leadsto> #(task_status t = Completed)" *)




end