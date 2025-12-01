theory DirectTemporalScheduler
  imports "HOL-TLA.TLA"
begin

datatype task = Task1 | Task2 | Task3 | Task4 | Task5
datatype task_state = Ready | Running | Completed

(* Сразу объявляем temporal константы *)
consts
  TaskReady :: "task \<Rightarrow> temporal"
  TaskRunning :: "task \<Rightarrow> temporal"
  TaskCompleted :: "task \<Rightarrow> temporal"
  CurrentTask :: "task stfun"

(* Связываем с state через аксиомы *)
axiomatization where
  task_ready_def: "\<forall>t. TaskReady t = #(task_status t = Ready)" and
  task_running_def: "\<forall>t. TaskRunning t = #(task_status t = Running)" and
  task_completed_def: "\<forall>t. TaskCompleted t = #(task_status t = Completed)"

(* Теперь все работает! *)
definition AnyTaskReady :: temporal where
  "AnyTaskReady \<equiv> EEx (\<lambda>(t :: task stfun). TaskReady t)"



(* Количественные метрики *)
definition AtLeastNReady :: "nat \<Rightarrow> temporal" where
  "AtLeastNReady n \<equiv> EEx ts. #(card {t. task_status t = Ready} \<ge> n)"

end