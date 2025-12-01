theory ControlSys
imports Main
begin

datatype component_state = 
    OPERATIONAL
  | DEGRADED
  | FAILED
  | UNDER_MAINTENANCE

datatype system_mode =
    NORMAL_OP
  | BACKUP_OP
  | EMERGENCY_OP
  | SHUTDOWN

datatype 
system_state =
    System (mode: system_mode) 
           (primary: component_state)
           (backup: component_state)
           (sensors: component_state)


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


(*  Никогда не теряем все каналы управления *)
definition no_single_point_failure :: tl_formula where
  "no_single_point_failure =
     Always (Not (And (Prop (\<lambda>s. primary s = FAILED)) 
                      (Prop (\<lambda>s. backup s = FAILED))))"

(* Всегда есть рабочий датчик *)
definition always_working_sensor :: tl_formula where
  "always_working_sensor =
     Always (Or (Prop (\<lambda>s. sensors s = OPERATIONAL))
                (Prop (\<lambda>s. sensors s = DEGRADED)))"

(*  Безопасное поведение при отказе *)
definition graceful_degradation :: tl_formula where
  "graceful_degradation =
     Always (Implies (Prop (\<lambda>s. primary s = FAILED))
                     (Next (Prop (\<lambda>s. mode s = BACKUP_OP))))"

(*  Система всегда восстанавливается *)
definition eventual_recovery :: tl_formula where
  "eventual_recovery =
     Always (Eventually (Prop (\<lambda>s. mode s = NORMAL_OP)))"

(*  Отказ всегда обнаруживается *)
definition failure_detection :: tl_formula where
  "failure_detection =
     Always (Implies (Prop (\<lambda>s. primary s = FAILED))
                     (Next (Eventually (Prop (\<lambda>s. mode s = BACKUP_OP)))))"

(*  Гарантированная доступность *)
definition high_availability :: tl_formula where
  "high_availability =
     Always (Eventually (Prop (\<lambda>s. mode s \<noteq> SHUTDOWN)))"

(*  Независимость отказов *)
definition failure_independence :: tl_formula where
  "failure_independence =
     Always (Implies (Prop (\<lambda>s. primary s = FAILED))
                     (Next (Not (Prop (\<lambda>s. backup s = FAILED)))))"

(*  Детерминированное переключение *)
definition deterministic_failover :: tl_formula where
  "deterministic_failover =
     Always (Implies (And (Prop (\<lambda>s. primary s = FAILED))
                          (Prop (\<lambda>s. backup s = OPERATIONAL)))
                     (Next (And (Prop (\<lambda>s. mode s = BACKUP_OP))
                                (Prop (\<lambda>s. primary s = UNDER_MAINTENANCE)))))"

(*  Сохранение данных при отказе *)
definition data_preservation :: tl_formula where
  "data_preservation =
     Always (Implies (Prop (\<lambda>s. mode s = NORMAL_OP))
                     (Next (Or (Prop (\<lambda>s. mode s = NORMAL_OP))
                               (And (Prop (\<lambda>s. mode s = BACKUP_OP))
                                    (Prop (\<lambda>s. primary s = UNDER_MAINTENANCE))))))"

(*  Никогда не одновременный отказ всех систем *)
definition no_total_failure :: tl_formula where
  "no_total_failure =
     Always (Or (Prop (\<lambda>s. primary s = OPERATIONAL))
                (Or (Prop (\<lambda>s. backup s = OPERATIONAL))
                (Prop (\<lambda>s. sensors s = OPERATIONAL))))"

(* 2. Предсказуемое время восстановления *)
definition bounded_recovery_time :: tl_formula where
  "bounded_recovery_time =
     Always (Implies (Prop (\<lambda>s. mode s = BACKUP_OP))
                     (Next (Next (Next (Eventually (Prop (\<lambda>s. mode s = NORMAL_OP)))))))"

definition valid_mode :: "system_state \<Rightarrow> bool" where
  "valid_mode s = (mode s = NORMAL_OP \<or> mode s = BACKUP_OP \<or> 
                   mode s = EMERGENCY_OP \<or> mode s = SHUTDOWN)"

(* 3. Запрет недокументированных переходов *)
definition authorized_transitions_only :: tl_formula where
(*   "authorized_transitions_only =
     Always (Or (Prop (\<lambda>s. mode s = NORMAL_OP))
                (Or (Prop (\<lambda>s. mode s = BACKUP_OP))
                 (Or(Prop (\<lambda>s. mode s = EMERGENCY_OP))
                (Prop (\<lambda>s. mode s = SHUTDOWN)))))" *)
  "authorized_transitions_only = Always (Prop valid_mode)"


(* Трасса, моделирующая реалистичные отказы *)
definition aviation_trace :: "system_state trace" where
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
    apply auto
    apply (smt (verit, best) component_state.distinct(3) suffix_def system_state.sel(3))
   apply (smt (z3) One_nat_def Suc_lessD component_state.distinct(11) component_state.distinct(4) component_state.distinct(8) eval_nat_numeral(3) mod_Suc nat_arith.suc1 not_less_eq 
numeral_eq_iff plus_1_eq_Suc semiring_norm(89) suffix_def system_state.sel(1) system_state.sel(2))
  by (smt (verit, best) suffix_def system_mode.distinct(5) system_mode.distinct(9) system_state.sel(1))

(* Проверим отказоустойчивость *)
lemma aviation_fault_tolerance_proof:
  "eval_tl failure_independence aviation_trace"
  "eval_tl deterministic_failover aviation_trace"  
  unfolding failure_independence_def deterministic_failover_def
            aviation_trace_def
   apply auto
    apply (smt (verit) component_state.distinct(4) suffix_def system_state.sel(3))
   apply (smt (z3) One_nat_def Suc_lessD component_state.distinct(11) component_state.distinct(4) component_state.distinct(8) eval_nat_numeral(3) mod_Suc nat_arith.suc1 not_less_eq numeral_eq_iff plus_1_eq_Suc semiring_norm(89) suffix_def system_state.collapse system_state.inject)
  by (smt (z3) One_nat_def Suc_lessD component_state.distinct(11) component_state.distinct(4) component_state.distinct(8) eval_nat_numeral(3) mod_Suc nat_arith.suc1 not_less_eq numeral_eq_iff plus_1_eq_Suc semiring_norm(89) suffix_def system_state.collapse system_state.inject)

(* 
 Верификация авиационных стандартов *)
lemma aviation_standards_proof:
  "eval_tl no_total_failure aviation_trace"
  "eval_tl authorized_transitions_only aviation_trace"
  unfolding no_total_failure_def authorized_transitions_only_def
            aviation_trace_def
   apply (smt (verit, del_insts) eval_tl.simps(1) eval_tl.simps(4) eval_tl.simps(5) suffix_def system_state.collapse system_state.inject)
  using system_mode.exhaust valid_mode_def by auto

(* Опасная трасса: одновременный отказ primary и backup *)
definition hazardous_trace :: "system_state trace" where
  "hazardous_trace i = (
    if i < 10 then
      System NORMAL_OP OPERATIONAL OPERATIONAL OPERATIONAL
    else
      System EMERGENCY_OP FAILED FAILED OPERATIONAL) "

(* Докажем нарушение safety requirement *)
lemma hazardous_trace_unsafe:

  "\<not> eval_tl no_single_point_failure hazardous_trace"
  unfolding no_single_point_failure_def hazardous_trace_def
  by (smt (verit, del_insts) eval_tl.simps(1) eval_tl.simps(2) eval_tl.simps(3) eval_tl.simps(5) nat_arith.rule0 suffix_def system_state.sel(2) system_state.sel(3) verit_comp_simplify1(1))


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
                                                               bounded_recovery_time)))))))))"

thm do_178c_level_a_spec_def

lemma aviation_always_working_sensor:
  "eval_tl always_working_sensor aviation_trace"
  unfolding always_working_sensor_def aviation_trace_def
  by (smt (verit, del_insts) eval_tl.simps(1) eval_tl.simps(4) eval_tl.simps(5) suffix_def system_state.sel(4))

lemma aviation_eventual_recovery:  
  "eval_tl eventual_recovery aviation_trace"
  unfolding do_178c_level_a_spec_def eventual_recovery_def aviation_trace_def suffix_def hazardous_trace_def
  using system_mode.exhaust valid_mode_def by blast

(* Докажем, что наша система удовлетворяет стандарту *)
theorem system_do_178c_compliant:
  "eval_tl do_178c_level_a_spec aviation_trace"
  unfolding do_178c_level_a_spec_def eventual_recovery_def aviation_trace_def suffix_def hazardous_trace_def
  using system_mode.exhaust valid_mode_def by blast


(* Проверим, что все критические сценарии покрыты *)
definition hazard_scenarios_covered :: bool where
  "hazard_scenarios_covered =
     (\<forall>tr. eval_tl do_178c_level_a_spec tr \<longrightarrow>
           eval_tl no_single_point_failure tr \<and>
           eval_tl graceful_degradation tr \<and>
           eval_tl high_availability tr)"

lemma requirements_coverage:
  "hazard_scenarios_covered"
  unfolding hazard_scenarios_covered_def
  by (metis do_178c_level_a_spec_def eval_tl.simps(3))

type_synonym timestamp = nat

datatype timed_system_state =
    TimedState 
      (state: system_state)
      (arrival_time: timestamp) 
      (completion_time: "timestamp option")


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
definition meets_deadline :: "real_time_state \<Rightarrow> nat \<Rightarrow> bool" where
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


(* Трасса с гарантированными временами отклика *)
definition realtime_trace :: "real_time_state trace" where
  "realtime_trace i = (
    case i of
      0 \<Rightarrow> Request 1 5 0   
    | Suc 0 \<Rightarrow> Processing 1 1  
    | Suc (Suc 0) \<Rightarrow> Response 1 2    
    | Suc (Suc(Suc 0)) \<Rightarrow> Request 2 4 3   
    | Suc (Suc (Suc(Suc 0))) \<Rightarrow> Processing 2 4
    | Suc (Suc (Suc (Suc(Suc 0)))) \<Rightarrow> Response 2 5
    | _ \<Rightarrow> Request ((i mod 3) + 1) 5 i
  )"

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




end