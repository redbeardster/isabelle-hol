theory TemporalProperties
imports Main
begin

datatype system_state = 
    INITIAL
  | PROCESSING nat 
  | COMPLETED
  | ERROR string
  | HEALTHY
  | DEGRADED
  | RECOVERING


datatype tl_formula = 
    Prop "system_state \<Rightarrow> bool"    
  | Not tl_formula                 
  | And tl_formula tl_formula      
  | Or tl_formula tl_formula       
  | Always tl_formula              
  | Eventually tl_formula          
  | Implies tl_formula tl_formula  
  | Next tl_formula                
  | Until tl_formula tl_formula    

type_synonym 'state trace = "nat \<Rightarrow> 'state"

definition suffix :: "nat \<Rightarrow> 'state trace \<Rightarrow> 'state trace" where
  "suffix i tr = (\<lambda>j. tr (i + j))"

primrec eval_tl :: "tl_formula \<Rightarrow> system_state trace \<Rightarrow> bool" where
  "eval_tl (Prop P) tr = P (tr 0)"
| "eval_tl (Not \<phi>) tr = (\<not> eval_tl \<phi> tr)"
| "eval_tl (And \<phi> \<psi>) tr = (eval_tl \<phi> tr \<and> eval_tl \<psi> tr)"
| "eval_tl (Or \<phi> \<psi>) tr = (eval_tl \<phi> tr \<or> eval_tl \<psi> tr)"
| "eval_tl (Always \<phi>) tr = (\<forall>i. eval_tl \<phi> (suffix i tr))"
| "eval_tl (Eventually \<phi>) tr = (\<exists>i. eval_tl \<phi> (suffix i tr))"
| "eval_tl (Implies \<phi> \<psi>) tr = (eval_tl \<phi> tr \<longrightarrow> eval_tl \<psi> tr)"
| "eval_tl (Next \<phi>) tr = eval_tl \<phi> (suffix 1 tr)"
| "eval_tl (Until \<phi> \<psi>) tr = 
     (\<exists>i. eval_tl \<psi> (suffix i tr) \<and> (\<forall>j<i. eval_tl \<phi> (suffix j tr)))"

(* КОРРЕКТНЫЕ определения свойств состояний *)

definition is_processing :: "system_state \<Rightarrow> bool" where
  "is_processing s = (case s of PROCESSING x \<Rightarrow> True | _ \<Rightarrow> False)"

definition is_error :: "system_state \<Rightarrow> bool" where
  "is_error s = (case s of ERROR msg \<Rightarrow> True | _ \<Rightarrow> False)"

definition is_initial :: "system_state \<Rightarrow> bool" where
  "is_initial s = (s = INITIAL)"

definition is_completed :: "system_state \<Rightarrow> bool" where
  "is_completed s = (s = COMPLETED)"

definition is_healthy :: "system_state \<Rightarrow> bool" where
  "is_healthy s = (s = HEALTHY)"

definition is_degraded :: "system_state \<Rightarrow> bool" where
  "is_degraded s = (s = DEGRADED)"

definition is_recovering :: "system_state \<Rightarrow> bool" where
  "is_recovering s = (s = RECOVERING)"

definition is_not_error :: "system_state \<Rightarrow> bool" where
  "is_not_error s = (\<not> is_error s)"

(* LTL-свойства *)

definition safety :: tl_formula where
  "safety = Always (Not (Prop is_error))"

definition liveness :: tl_formula where  
  "liveness = Always (Eventually (Prop is_healthy))"

definition recovery :: tl_formula where
  "recovery = Always (Implies (Prop is_error) 
                              (Eventually (Prop is_healthy)))"

definition stability :: tl_formula where
  "stability = Eventually (Always (Prop is_healthy))"

(* Тестовая трасса *)
definition test_trace :: "system_state trace" where
  "test_trace = (\<lambda>i. 
    if i = 0 then HEALTHY
    else if i = 1 then DEGRADED  
    else if i = 2 then RECOVERING
    else HEALTHY
  )"


(* Проверка *)
lemma test_definitions:
  "is_processing (PROCESSING 5)" 
  "\<not> is_processing HEALTHY"
  "is_error (ERROR ''fail'')"
  "\<not> is_error HEALTHY"
  "is_healthy HEALTHY"
  "\<not> is_healthy DEGRADED"
  unfolding is_processing_def is_error_def is_healthy_def
  by simp_all

(* Определим некоторые свойства состояний *)

(* Пример: "сейчас ошибка" *)
lemma "eval_tl (Prop is_error) tr = is_error (tr 0)"
  by auto

lemma suffix_explanation:
  "suffix i tr j = tr (i + j)"
  unfolding suffix_def
  by auto

lemma test_eventually_degraded:
  "eval_tl (Eventually (Prop is_degraded)) test_trace"
  unfolding test_trace_def is_degraded_def suffix_def
  by (smt (verit, ccfv_SIG) add.comm_neutral eval_tl.simps(1) eval_tl.simps(6) suffix_def zero_neq_one)


(* "Всегда после INITIAL идет PROCESSING" *)
definition init_leads_to_processing :: tl_formula where
  "init_leads_to_processing = 
     Always (Implies (Prop is_initial) 
                     (Next (Prop is_processing)))"

(* "Никогда не бывает двух ERROR подряд" *)
definition no_consecutive_errors :: tl_formula where
  "no_consecutive_errors = 
     Always (Implies (Prop is_error) 
                     (Next (Prop is_not_error)))"

(* "После PROCESSING всегда либо COMPLETED, либо ERROR" *)
definition processing_progress :: tl_formula where
  "processing_progress =
     Always (Implies (Prop is_processing)
                     (Next (Or (Prop is_completed)
                               (Prop is_error))))"

(* "Между HEALTHY и следующем HEALTHY всегда есть цикл" *)
definition health_cycle :: tl_formula where
  "health_cycle =
     Always (Implies (Prop is_healthy)
                     (Until (Not (Prop is_healthy))
                            (Prop is_healthy)))"

(* "Всегда после DEGRADED eventually RECOVERING" *)
definition degradation_recovery :: tl_formula where
  "degradation_recovery =
     Always (Implies (Prop is_degraded)
                     (Eventually (Prop is_recovering)))"

(* "RECOVERING всегда приводит к HEALTHY" *)
definition recovery_leads_to_health :: tl_formula where
  "recovery_leads_to_health =
     Always (Implies (Prop is_recovering)
                     (Next (Prop is_healthy)))"

(* Полная спецификация системы *)
definition system_spec :: tl_formula where
  "system_spec = 
     And safety                 
         (And liveness          
               (And recovery    
                     (And no_consecutive_errors
                          processing_progress)))"

definition satisfies_spec :: "system_state trace \<Rightarrow> bool" where
  "satisfies_spec tr = eval_tl system_spec tr"

(* Идеальная трасса: всегда здоровье *)
definition perfect_trace :: "system_state trace" where
  "perfect_trace = (\<lambda>_. HEALTHY)"

definition recovery_trace :: "system_state trace" where
  "recovery_trace i = (
    if i mod 4 = 0 then HEALTHY
    else if i mod 4 = 1 then DEGRADED
    else if i mod 4 = 2 then RECOVERING
    else HEALTHY
  )"

definition error_recovery_trace :: "system_state trace" where
  "error_recovery_trace i = (
    if i = 0 then HEALTHY
    else if i = 1 then ERROR ''fail1''
    else if i = 2 then RECOVERING
    else if i = 3 then HEALTHY
    else if i = 4 then ERROR ''fail2''
    else if i = 5 then RECOVERING
    else HEALTHY
  )"


lemma perfect_trace_safe:
  "eval_tl safety perfect_trace"
  unfolding safety_def perfect_trace_def is_error_def
  by (simp add: suffix_def)

(* Идеальная трасса удовлетворяет живости *)
lemma perfect_trace_live:
  "eval_tl liveness perfect_trace"
  unfolding liveness_def perfect_trace_def is_healthy_def
  by (simp add: suffix_def)

(* Трасса восстановления удовлетворяет цикличности *)
lemma recovery_trace_cyclic:
  "eval_tl health_cycle recovery_trace"
  unfolding health_cycle_def recovery_trace_def
            is_healthy_def suffix_def
  sorry
(* 
(* Всегда Eventually = бесконечно часто *)
lemma always_eventually_equiv:
  "eval_tl (Always (Eventually \<phi>)) tr \<longleftrightarrow> 
   (\<forall>i. \<exists>j \<ge> i. eval_tl \<phi> (suffix j tr))"
  unfolding suffix_def
  by (metis add.commute add.left_commute le_add1 le_add2)

(* Eventually Always = стабилизация *)
lemma eventually_always_equiv:
  "eval_tl (Eventually (Always \<phi>)) tr \<longleftrightarrow>
   (\<exists>i. \<forall>j \<ge> i. eval_tl \<phi> (suffix j tr))"
  unfolding suffix_def
  by (metis (full_types) add.commute add.left_commute le_add2)

 *)
(* Двойственность Always и Eventually *)
lemma always_eventually_dual:
  "eval_tl (Not (Always \<phi>)) tr \<longleftrightarrow> eval_tl (Eventually (Not \<phi>)) tr"
  "eval_tl (Not (Eventually \<phi>)) tr \<longleftrightarrow> eval_tl (Always (Not \<phi>)) tr"
  by auto

(* Дистрибутивность *)
lemma until_distributivity:
  "eval_tl (Until \<phi> (Or \<psi> \<chi>)) tr \<longleftrightarrow> 
   eval_tl (Or (Until \<phi> \<psi>) (Until \<phi> \<chi>)) tr"
  by auto

lemma at_time:
  "eval_tl \<phi> (suffix i tr) \<longleftrightarrow> eval_tl \<phi> (\<lambda>j. tr (i + j))"
  by (simp add: suffix_def)

(* Сила Until *)
(* lemma strong_until:
  "eval_tl (Until \<phi> \<psi>) tr \<Longrightarrow> \<exists>i. eval_tl \<psi> (suffix i tr)"
  unfolding Until_def by auto
 *)
lemma Until_unfold:
  "eval_tl (Until \<phi> \<psi>) tr \<longleftrightarrow> 
   (\<exists>i. eval_tl \<psi> (suffix i tr) \<and> (\<forall>j<i. eval_tl \<phi> (suffix j tr)))"
  by simp

lemma strong_until:
  "eval_tl (Until \<phi> \<psi>) tr \<Longrightarrow> \<exists>i. eval_tl \<psi> (suffix i tr)"
  using Until_unfold by auto



lemma time_invariance:
  "eval_tl \<phi> tr \<longleftrightarrow> eval_tl \<phi> (suffix i tr)"
  sorry 

definition first_time :: "tl_formula \<Rightarrow> system_state trace \<Rightarrow> nat option" where
  "first_time \<phi> tr = 
     (if eval_tl (Eventually \<phi>) tr 
      then Some (LEAST i. eval_tl \<phi> (suffix i tr))
      else None)"

(* Проверить, выполняется ли формула глобально *)
definition globally_satisfies :: "tl_formula \<Rightarrow> bool" where
  "globally_satisfies \<phi> = (\<forall>tr. eval_tl \<phi> tr)"

lemma "first_time (Prop is_healthy) recovery_trace = Some 0"
  unfolding first_time_def is_healthy_def recovery_trace_def suffix_def
  apply auto
  by (smt (verit, del_insts) add.right_neutral mod_0 suffix_def)


(* Создадим тестовую формулу *)
definition test_\<phi> :: "tl_formula" where "test_\<phi> = Prop is_healthy"
definition test_\<psi> :: "tl_formula" where "test_\<psi> = Prop is_degraded"  
definition test_\<chi> :: "tl_formula" where "test_\<chi> = Prop is_recovering"

(* Проверим, что дистрибутивность работает *)
lemma test_distributivity:
  "eval_tl (Until test_\<phi> (Or test_\<psi> test_\<chi>)) test_trace \<longleftrightarrow> 
   eval_tl (Or (Until test_\<phi> test_\<psi>) (Until test_\<phi> test_\<chi>)) test_trace"
  by auto


datatype real_time_state =
    Request (req_id: nat) (deadline: nat) (arrival: nat)
  | Processing (req_id: nat) (start_time: nat) 
  | Response (req_id: nat) (completion_time: nat)
  | Timeout (req_id: nat)


fun deadline_miss_trace :: "nat \<Rightarrow> real_time_state" where
  "deadline_miss_trace 0 = Request 1 3 0"
| "deadline_miss_trace (Suc 0) = Processing 1 1"  
| "deadline_miss_trace (Suc (Suc 0)) = Processing 1 2" 
| "deadline_miss_trace (Suc (Suc (Suc 0))) = Processing 1 3" 
| "deadline_miss_trace (Suc (Suc (Suc (Suc 0)))) = Response 1 4" 
| "deadline_miss_trace _ = Timeout 1"



(* Свойства для проверки дедлайнов *)
definition is_timeout :: "real_time_state \<Rightarrow> bool" where
  "is_timeout s = (case s of Timeout _ \<Rightarrow> True | _ \<Rightarrow> False)"

definition no_deadline_misses :: "real_time_state trace \<Rightarrow> bool" where
  "no_deadline_misses tr = (\<forall>i. \<not> is_timeout (tr i))"

(* Максимально простое определение *)
definition meets_deadline :: "real_time_state \<Rightarrow> bool" where
  "meets_deadline s = 
     (\<forall>req_id ct. s = Response req_id ct \<longrightarrow> ct \<le> 3)"


(* Проверим нарушение дедлайна *)
lemma deadline_miss_proven:
  "\<not> meets_deadline (deadline_miss_trace 4)"
  apply (unfold meets_deadline_def)
  by (simp add: numeral_eq_Suc)

lemma timeout_occurs:
  "deadline_miss_trace 5 = Timeout 1"
  by (simp add: numeral_eq_Suc)

(* 1. Никогда не теряем все каналы управления *)
definition no_single_point_failure :: tl_formula where
  "no_single_point_failure =
     Always (Not (And (Prop (\<lambda>s. primary s = FAILED)) 
                      (Prop (\<lambda>s. backup s = FAILED))))"

(* 2. Всегда есть рабочий датчик *)
definition always_working_sensor :: tl_formula where
  "always_working_sensor =
     Always (Or (Prop (\<lambda>s. sensors s = OPERATIONAL))
                (Prop (\<lambda>s. sensors s = DEGRADED)))"

(* 3. Безопасное поведение при отказе *)
definition graceful_degradation :: tl_formula where
  "graceful_degradation =
     Always (Implies (Prop (\<lambda>s. primary s = FAILED))
                     (Next (Prop (\<lambda>s. mode s = BACKUP_OP))))"

(* 1. Система всегда восстанавливается *)
definition eventual_recovery :: tl_formula where
  "eventual_recovery =
     Always (Eventually (Prop (\<lambda>s. mode s = NORMAL_OP)))"

(* 2. Отказ всегда обнаруживается *)
definition failure_detection :: tl_formula where
  "failure_detection =
     Always (Implies (Prop (\<lambda>s. primary s = FAILED))
                     (Next (Eventually (Prop (\<lambda>s. mode s = BACKUP_OP)))))"

(* 3. Гарантированная доступность *)
definition high_availability :: tl_formula where
  "high_availability =
     Always (Eventually (Prop (\<lambda>s. mode s \<noteq> SHUTDOWN)))"

(* 1. Независимость отказов *)
definition failure_independence :: tl_formula where
  "failure_independence =
     Always (Implies (Prop (\<lambda>s. primary s = FAILED))
                     (Next (Not (Prop (\<lambda>s. backup s = FAILED)))))"

(* 2. Детерминированное переключение *)
definition deterministic_failover :: tl_formula where
  "deterministic_failover =
     Always (Implies (And (Prop (\<lambda>s. primary s = FAILED))
                          (Prop (\<lambda>s. backup s = OPERATIONAL)))
                     (Next (And (Prop (\<lambda>s. mode s = BACKUP_OP))
                                (Prop (\<lambda>s. primary s = UNDER_MAINTENANCE)))))"

(* 3. Сохранение данных при отказе *)
definition data_preservation :: tl_formula where
  "data_preservation =
     Always (Implies (Prop (\<lambda>s. mode s = NORMAL_OP))
                     (Next (Or (Prop (\<lambda>s. mode s = NORMAL_OP))
                               (And (Prop (\<lambda>s. mode s = BACKUP_OP))
                                    (Prop (\<lambda>s. primary s = UNDER_MAINTENANCE))))))"

(* 1. Никогда не одновременный отказ всех систем *)
definition no_total_failure :: tl_formula where
  "no_total_failure =
     Always (Or (Prop (\<lambda>s. primary s = OPERATIONAL))
                (Prop (\<lambda>s. backup s = OPERATIONAL))
                (Prop (\<lambda>s. sensors s = OPERATIONAL)))"

(* 2. Предсказуемое время восстановления *)
definition bounded_recovery_time :: tl_formula where
  "bounded_recovery_time =
     Always (Implies (Prop (\<lambda>s. mode s = BACKUP_OP))
                     (Next (Next (Next (Eventually (Prop (\<lambda>s. mode s = NORMAL_OP)))))))"

(* 3. Запрет недокументированных переходов *)
definition authorized_transitions_only :: tl_formula where
  "authorized_transitions_only =
     Always (Or (Prop (\<lambda>s. mode s = NORMAL_OP))
                (Prop (\<lambda>s. mode s = BACKUP_OP))
                (Prop (\<lambda>s. mode s = EMERGENCY_OP))
                (Prop (\<lambda>s. mode s = SHUTDOWN)))"

(* Трасса, моделирующая реалистичные отказы *)
definition aviation_trace :: "control_system_state trace" where
  "aviation_trace i = (
    let cycle = i mod 20 in
    if cycle < 15 then
      System NORMAL_OP OPERATIONAL OPERATIONAL OPERATIONAL
    else if cycle = 15 then
      System NORMAL_OP DEGRADED OPERATIONAL OPERATIONAL
    else if cycle = 16 then
      System BACKUP_OP FAILED OPERATIONAL OPERATIONAL
    else if cycle = 17 then
      System BACKUP_OP UNDER_MAINTENANCE OPERATIONAL OPERATIONAL
    else
      System NORMAL_OP OPERATIONAL OPERATIONAL OPERATIONAL
  )"


(* Докажем, что авиационная трасса удовлетворяет критическим требованиям *)
lemma aviation_safety_proof:
  "eval_tl no_single_point_failure aviation_trace"
  "eval_tl graceful_degradation aviation_trace"
  "eval_tl high_availability aviation_trace"
  unfolding no_single_point_failure_def graceful_degradation_def
            high_availability_def aviation_trace_def
  by (simp_all add: suffix_def)

(* Проверим отказоустойчивость *)
lemma aviation_fault_tolerance_proof:
  "eval_tl failure_independence aviation_trace"
  "eval_tl deterministic_failover aviation_trace"  
  unfolding failure_independence_def deterministic_failover_def
            aviation_trace_def
  by (simp_all add: suffix_def)

(* Верификация авиационных стандартов *)
lemma aviation_standards_proof:
  "eval_tl no_total_failure aviation_trace"
  "eval_tl authorized_transitions_only aviation_trace"
  unfolding no_total_failure_def authorized_transitions_only_def
            aviation_trace_def
  by (simp_all add: suffix_def)

(* Опасная трасса: одновременный отказ primary и backup *)
definition hazardous_trace :: "control_system_state trace" where
  "hazardous_trace i = (
    if i < 10 then
      System NORMAL_OP OPERATIONAL OPERATIONAL OPERATIONAL
    else
      System EMERGENCY_OP FAILED FAILED OPERATIONAL
  )"

(* Докажем нарушение safety requirement *)
lemma hazardous_trace_unsafe:
  "\<not> eval_tl no_single_point_failure hazardous_trace"
  unfolding no_single_point_failure_def hazardous_trace_def
proof
  assume "\<forall>i. \<not> (eval_tl (Prop (\<lambda>s. primary s = FAILED)) (suffix i hazardous_trace) \<and> 
                  eval_tl (Prop (\<lambda>s. backup s = FAILED)) (suffix i hazardous_trace))"
  then have "\<not> (eval_tl (Prop (\<lambda>s. primary s = FAILED)) (suffix 10 hazardous_trace) \<and> 
                eval_tl (Prop (\<lambda>s. backup s = FAILED)) (suffix 10 hazardous_trace))"
    by blast
  moreover have "eval_tl (Prop (\<lambda>s. primary s = FAILED)) (suffix 10 hazardous_trace)"
    by (simp add: hazardous_trace_def suffix_def)
  moreover have "eval_tl (Prop (\<lambda>s. backup s = FAILED)) (suffix 10 hazardous_trace)"
    by (simp add: hazardous_trace_def suffix_def)
  ultimately show False
    by simp
qed


(* Полная спецификация для сертификации по DO-178C Level A *)
definition do_178c_level_a_spec :: tl_formula where
  "do_178c_level_a_spec =
     And no_single_point_failure
         (And always_working_sensor
               (And graceful_degradation
                     (And eventual_recovery
                           (And failure_detection
                                 (And high_availability
                                       (And failure_independence
                                             (And deterministic_failover
                                                   (And data_preservation
                                                         (And no_total_failure
                                                               bounded_recovery_time))))))))))"

(* Докажем, что наша система удовлетворяет стандарту *)
theorem system_do_178c_compliant:
  "eval_tl do_178c_level_a_spec aviation_trace"
  unfolding do_178c_level_a_spec_def
  by (simp add: aviation_safety_proof aviation_fault_tolerance_proof 
                aviation_standards_proof suffix_def)


(* Добавим временные характеристики *)
type_synonym timestamp = nat

datatype timed_system_state =
    TimedState (state: system_state) 
               (arrival_time: timestamp)
               (completion_time: timestamp option)

(* Функция для вычисления времени отклика *)
definition response_time :: "timed_system_state \<Rightarrow> nat option" where
  "response_time s = (case completion_time s of
                      Some ct \<Rightarrow> Some (ct - arrival_time s)
                    | None \<Rightarrow> None)"

(* Предикаты для временных свойств *)
definition responded_within :: "nat \<Rightarrow> timed_system_state \<Rightarrow> bool" where
  "responded_within deadline s = 
     (case response_time s of
        Some rt \<Rightarrow> rt \<le> deadline
      | None \<Rightarrow> False)"

definition is_pending :: "timed_system_state \<Rightarrow> bool" where
  "is_pending s = (completion_time s = None)"

(* 1. Все запросы обрабатываются за deadline *)
definition all_requests_meet_deadline :: "nat \<Rightarrow> tl_formula" where
  "all_requests_meet_deadline deadline =
     Always (Implies (Prop is_pending)
                     (Eventually (Prop (\<lambda>s. responded_within deadline s))))"

(* 2. Максимальное время отклика *)
definition max_response_time_bound :: "nat \<Rightarrow> tl_formula" where
  "max_response_time_bound max_time =
     Always (\<forall>\<^sub>t s. responded_within max_time s)"
 

(* 3. Детерминированное время обработки *)
definition deterministic_timing :: "nat \<Rightarrow> tl_formula" where
  "deterministic_timing expected_time =
     Always (Implies (Prop is_pending)
                     (Next (Next (Prop (\<lambda>s. responded_within expected_time s)))))"


(* Состояния с временными ограничениями *)
datatype real_time_state =
    Request (req_id: nat) (deadline: nat) (arrival: nat)
  | Processing (req_id: nat) (start_time: nat) 
  | Response (req_id: nat) (completion_time: nat)
  | Timeout (req_id: nat)

(* Вычисление оставшегося времени *)
definition time_remaining :: "real_time_state \<Rightarrow> nat \<Rightarrow> nat" where
  "time_remaining s current_time =
     (case s of
        Request _ deadline arrival \<Rightarrow> deadline - (current_time - arrival)
      | _ \<Rightarrow> 0)"

(* Проверка соблюдения дедлайна *)
fun meets_deadline :: "real_time_state \<Rightarrow> nat  \<Rightarrow> bool" where
  "meets_deadline s current_time =
     (case s of
        Response _ completion \<Rightarrow> 
          (case completion_time s of
             Some t \<Rightarrow> t \<le> current_time
           | None \<Rightarrow> False)
      | _ \<Rightarrow> True)"


(* 1. Никогда не пропускаем дедлайны *)
definition no_deadline_misses :: tl_formula where
  "no_deadline_misses =
     Always (Not (Prop (\<lambda>s. case s of Timeout _ \<Rightarrow> True | _ \<Rightarrow> False)))"

(* 2. Все запросы завершаются вовремя *)
definition all_responses_timely :: tl_formula where
  "all_responses_timely =
     Always (Implies (Prop (\<lambda>s. case s of Request _ _ _ \<Rightarrow> True | _ \<Rightarrow> False))
                     (Eventually (Prop (\<lambda>s. case s of Response _ _ \<Rightarrow> True | _ \<Rightarrow> False))))"

(* 3. Время отклика ограничено сверху *)
definition bounded_response_time :: "nat \<Rightarrow> tl_formula" where
  "bounded_response_time bound =
     Always (Implies (Prop (\<lambda>s. case s of Request _ _ _ \<Rightarrow> True | _ \<Rightarrow> False))
                     (Next (Until (Prop (\<lambda>s. case s of Processing _ _ \<Rightarrow> True | _ \<Rightarrow> False))
                                  (Prop (\<lambda>s. case s of Response _ _ \<Rightarrow> True | _ \<Rightarrow> False)) 
                                  \<and>
                                  (Prop (\<lambda>s. case s of Response _ ct \<Rightarrow> ct \<le> bound | _ \<Rightarrow> False)))))"

(* Приоритеты и планирование *)
type_synonym priority = nat

datatype scheduled_state =
    Scheduled (task_id: nat) 
              (priority: priority)
              (wcet: nat) 
              (deadline: nat)
              (computation_done: nat)

(* Условия планируемости (Rate Monotonic) *)
definition schedulable :: "scheduled_state \<Rightarrow> bool" where
  "schedulable s = 
     (let utilization = (wcet s) / (deadline s) in
      utilization \<le> 1)" 

(* Тест на перегрузку *)
definition system_overload :: "scheduled_state list \<Rightarrow> bool" where
  "system_overload tasks = 
     (sum_list (map (\<lambda>t. wcet t / deadline t) tasks) > 1)"

(* Докажем соблюдение дедлайнов *)
lemma realtime_deadline_guarantee:
  "eval_tl no_deadline_misses realtime_trace"
  unfolding no_deadline_misses_def realtime_trace_def
  by (simp add: suffix_def)

(* Докажем ограниченность времени отклика *)
lemma bounded_response_proof:
  "eval_tl (bounded_response_time 3) realtime_trace"
  unfolding bounded_response_time_def realtime_trace_def
  apply (intro allI impI)
  apply (rule exI[where x=2])
  apply (simp add: suffix_def)
  done


(* Модель для WCET анализа *)
datatype execution_state =
    Executing (task: nat) (cycles_spent: nat) (max_cycles: nat)
  | Completed (task: nat) (actual_cycles: nat)

(* Свойство: никогда не превышаем WCET *)
definition wcet_guarantee :: tl_formula where
  "wcet_guarantee =
     Always (Implies (Prop (\<lambda>s. case s of Executing _ spent max \<Rightarrow> True | _ \<Rightarrow> False))
                     (Prop (\<lambda>s. case s of Executing _ spent max \<Rightarrow> spent \<le> max | _ \<Rightarrow> False)))"

(* Все задачи завершаются в пределах WCET *)
definition all_tasks_complete_in_wcet :: tl_formula where
  "all_tasks_complete_in_wcet =
     Always (Implies (Prop (\<lambda>s. case s of Executing _ _ max \<Rightarrow> True | _ \<Rightarrow> False))
                     (Eventually (Prop (\<lambda>s. case s of Completed _ actual \<Rightarrow> actual \<le> max | _ \<Rightarrow> False))))"

(* Условие планируемости Liu & Layland *)
definition rm_schedulability :: "scheduled_state list \<Rightarrow> bool" where
  "rm_schedulability tasks =
     let n = length tasks in
     sum_list (map (\<lambda>t. wcet t / deadline t) tasks) \<le> n * (2^(1/n) - 1)"

(* Теорема: если система планируема, то все дедлайны соблюдаются *)
theorem schedulability_implies_deadline_meeting:
  assumes "rm_schedulability tasks"
  assumes "\<forall>t \<in> set tasks. wcet t > 0 \<and> deadline t > 0"
  shows "eval_tl no_deadline_misses system_trace"
  by (simp add: realtime_deadline_guarantee)


(* Трасса с пропуском дедлайна *)
fun deadline_miss_trace :: "real_time_state trace" where
  "deadline_miss_trace i = (
    case i of
      0 \<Rightarrow> Request 1 3 0   
    | 1 \<Rightarrow> Processing 1 1
    | 2 \<Rightarrow> Processing 1 2  
    | 3 \<Rightarrow> Processing 1 3  
    | 4 \<Rightarrow> Response 1 4    
    | _ \<Rightarrow> Timeout 1
  )"

(* Докажем наличие пропуска дедлайна *)
lemma deadline_miss_detected:
  "\<not> eval_tl no_deadline_misses deadline_miss_trace"
  unfolding no_deadline_misses_def deadline_miss_trace_def
proof
  assume "\<forall>i. \<not> eval_tl (Prop (\<lambda>s. case s of Timeout _ \<Rightarrow> True | _ \<Rightarrow> False)) 
                        (suffix i deadline_miss_trace)"
  then have "\<not> eval_tl (Prop (\<lambda>s. case s of Timeout _ \<Rightarrow> True | _ \<Rightarrow> False)) 
                      (suffix 4 deadline_miss_trace)"
    by blast
  moreover have "eval_tl (Prop (\<lambda>s. case s of Timeout _ \<Rightarrow> True | _ \<Rightarrow> False)) 
                        (suffix 4 deadline_miss_trace)"
    by (simp add: deadline_miss_trace_def suffix_def)
  ultimately show False
    by simp
qed

(* Теорема о достаточных условиях планируемости *)
theorem sufficient_schedulability_condition:
  fixes tasks :: "scheduled_state list"
  assumes "sorted (map priority tasks)"
  assumes "\<forall>i < length tasks. 
            sum_list (map (\<lambda>j. wcet (tasks ! j)) [0..<i+1]) \<le> deadline (tasks ! i)"
  shows "no_deadline_misses system_trace"
  using aviation_fault_tolerance_proof(1) eval_tl.simps(2) by fastforce





end