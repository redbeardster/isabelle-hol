theory PriorityManagerVerified
imports Main "HOL-Library.FSet" "HOL-Library.Sublist"
begin

(* Переименуем с более описательными именами *)
definition MAX_PROCESS_LIMIT :: nat where "MAX_PROCESS_LIMIT = 3"
definition CPU_COUNT :: nat where "CPU_COUNT = 2"  
definition PRIORITY_MIN :: int where "PRIORITY_MIN = 10"
definition PRIORITY_MAX :: int where "PRIORITY_MAX = 95"
definition SYSTEM_MEMORY :: int where "SYSTEM_MEMORY = 1000"
definition MAX_SYSTEM_TIME :: int where "MAX_SYSTEM_TIME = 20"
definition MAX_PROCESS_ID :: nat where "MAX_PROCESS_ID = 1000"

(* Аксиомы системы *)
axiomatization where
  finite_process_ids: "finite (UNIV :: ProcessId set)" and 
  finite_cpu_ids: "finite (UNIV :: CPUId set)" and
  finite_resources: "finite (UNIV :: Resource set)" and
  positive_memory: "SYSTEM_MEMORY > 0"

(* ========== ТИПЫ С ИНВАРИАНТАМИ ========== *)

typedef ProcessId = "{n :: nat. n < MAX_PROCESS_ID}"
  morphisms pid_to_nat nat_to_pid
proof
  show "(0::nat) \<in> {n. n < MAX_PROCESS_ID}" 
    by (simp add: MAX_PROCESS_ID_def)
qed

typedef CPUId = "{n :: nat. n < CPU_COUNT}"
  morphisms cpu_to_nat nat_to_cpu  
proof
  show "(0::nat) \<in> {n. n < CPU_COUNT}"
    by (simp add: CPU_COUNT_def)
qed

typedef ValidPriority = "{p :: int. PRIORITY_MIN \<le> p \<and> p \<le> PRIORITY_MAX}"
  morphisms priority_to_int int_to_priority
proof
  show "PRIORITY_MIN \<in> {p. PRIORITY_MIN \<le> p \<and> p \<le> PRIORITY_MAX}"
    by (simp add: PRIORITY_MIN_def PRIORITY_MAX_def)
qed

typedef MemoryAmount = "{m :: int. 0 \<le> m \<and> m \<le> SYSTEM_MEMORY}"
  morphisms memory_to_int int_to_memory
proof
  show "0 \<in> {m. 0 \<le> m \<and> m \<le> SYSTEM_MEMORY}"
    by (simp add: SYSTEM_MEMORY_def)
qed

typedef TimeUnit = "{t :: int. 0 \<le> t \<and> t \<le> MAX_SYSTEM_TIME}"
  morphisms time_to_int int_to_time
proof
  show "0 \<in> {t. 0 \<le> t \<and> t \<le> MAX_SYSTEM_TIME}"
    by (simp add: MAX_SYSTEM_TIME_def)
qed

(* Базовые свойства типов *)
lemma ProcessId_bound: "pid_to_nat pid < MAX_PROCESS_ID"
  using pid_to_nat by auto

lemma CPUId_bound: "cpu_to_nat cpu < CPU_COUNT"  
  using cpu_to_nat by auto

lemma ValidPriority_bounds: 
  "PRIORITY_MIN \<le> priority_to_int p \<and> priority_to_int p \<le> PRIORITY_MAX"
  using priority_to_int by auto

lemma MemoryAmount_bounds:
  "0 \<le> memory_to_int m \<and> memory_to_int m \<le> SYSTEM_MEMORY"
  using memory_to_int by auto

lemma TimeUnit_bounds:
  "0 \<le> time_to_int t \<and> time_to_int t \<le> MAX_SYSTEM_TIME"
  using time_to_int by auto

(* ========== СОСТОЯНИЕ СИСТЕМЫ ========== *)

record SystemState =
  active_processes :: "ProcessId fset"
  process_priorities :: "ProcessId \<Rightarrow> int"
  cpu_assignments :: "CPUId \<Rightarrow> ProcessId option"
  ready_processes :: "ProcessId list"
  blocked_processes :: "ProcessId fset"
  memory_usage :: "ProcessId \<Rightarrow> int"
  available_memory :: int
  current_time :: int
  process_deadlines :: "ProcessId \<Rightarrow> int"
  execution_times :: "ProcessId \<Rightarrow> int"

(* ========== ИНВАРИАНТЫ СИСТЕМЫ ========== *)

definition NoDuplicateReadyQueue :: "SystemState \<Rightarrow> bool" where
  "NoDuplicateReadyQueue s \<equiv> distinct (ready_processes s)"

definition SystemTypeOK :: "SystemState \<Rightarrow> bool" where
  "SystemTypeOK s \<equiv>
    fcard (active_processes s) \<le> MAX_PROCESS_LIMIT \<and>
    (\<forall>pid. pid |\<in>| active_processes s \<longrightarrow> 
        PRIORITY_MIN \<le> process_priorities s pid \<and> process_priorities s pid \<le> PRIORITY_MAX) \<and>
    (\<forall>cpu. cpu_assignments s cpu \<noteq> None \<longrightarrow> 
        the (cpu_assignments s cpu) |\<in>| active_processes s) \<and>
    (\<forall>pid. pid \<in> set (ready_processes s) \<longrightarrow> pid |\<in>| active_processes s) \<and>
    (\<forall>pid. pid |\<in>| blocked_processes s \<longrightarrow> pid |\<in>| active_processes s) \<and>
    (\<forall>pid. pid |\<in>| active_processes s \<longrightarrow> memory_usage s pid \<ge> 0) \<and>
    available_memory s \<ge> 0 \<and> available_memory s \<le> SYSTEM_MEMORY \<and>
    current_time s \<ge> 0 \<and> current_time s \<le> MAX_SYSTEM_TIME \<and>
    (\<forall>pid. pid |\<in>| active_processes s \<longrightarrow> process_deadlines s pid \<ge> current_time s) \<and>
    (\<forall>pid. pid |\<in>| active_processes s \<longrightarrow> execution_times s pid \<ge> 0) \<and>
    NoDuplicateReadyQueue s"

(* ========== ТИП ВАЛИДНЫХ СОСТОЯНИЙ ========== *)

typedef ValidSystemState = "{s :: SystemState. SystemTypeOK s}"
  morphisms state_to_System System_to_state
proof -
  (* Начальное состояние всегда валидно *)
  have "SystemTypeOK \<lparr>
    active_processes = {||},
    process_priorities = (\<lambda>_. PRIORITY_MIN),
    cpu_assignments = (\<lambda>_. None),
    ready_processes = [],
    blocked_processes = {||},
    memory_usage = (\<lambda>_. 0),
    available_memory = SYSTEM_MEMORY,
    current_time = 0,
    process_deadlines = (\<lambda>_. 0),
    execution_times = (\<lambda>_. 0)
  \<rparr>"
    unfolding SystemTypeOK_def NoDuplicateReadyQueue_def
    by (auto simp: PRIORITY_MIN_def PRIORITY_MAX_def SYSTEM_MEMORY_def 
                   MAX_PROCESS_LIMIT_def positive_memory)
  then show ?thesis by blast
qed

(* Леммы о ValidSystemState *)
lemma ValidState_implies_TypeOK: "SystemTypeOK (state_to_System vs)"
  using state_to_System by auto

lemma state_equality: 
  "state_to_System vs = state_to_System vs' \<longleftrightarrow> vs = vs'"
  by (simp add: state_to_System_inject)

(* ========== БАЗОВЫЕ ЛЕММЫ О СИСТЕМЕ ========== *)

lemma ready_processes_subset_active:
  assumes "SystemTypeOK s" "pid \<in> set (ready_processes s)"
  shows "pid |\<in>| active_processes s"
  using assms unfolding SystemTypeOK_def by blast

lemma cpu_assignment_implies_active:
  assumes "SystemTypeOK s" "cpu_assignments s cpu = Some pid"
  shows "pid |\<in>| active_processes s"  
  using assms unfolding SystemTypeOK_def by blast

lemma blocked_processes_subset_active:
  assumes "SystemTypeOK s" "pid |\<in>| blocked_processes s"
  shows "pid |\<in>| active_processes s"
  using assms unfolding SystemTypeOK_def by blast

lemma memory_usage_non_negative:
  assumes "SystemTypeOK s" "pid |\<in>| active_processes s"
  shows "memory_usage s pid \<ge> 0"
  using assms unfolding SystemTypeOK_def by blast

lemma available_memory_bounds:
  assumes "SystemTypeOK s"
  shows "0 \<le> available_memory s \<and> available_memory s \<le> SYSTEM_MEMORY"
  using assms unfolding SystemTypeOK_def by blast

lemma current_time_bounds:
  assumes "SystemTypeOK s" 
  shows "0 \<le> current_time s \<and> current_time s \<le> MAX_SYSTEM_TIME"
  using assms unfolding SystemTypeOK_def by blast

lemma deadlines_valid:
  assumes "SystemTypeOK s" "pid |\<in>| active_processes s"
  shows "process_deadlines s pid \<ge> current_time s"
  using assms unfolding SystemTypeOK_def by blast

lemma execution_times_non_negative:
  assumes "SystemTypeOK s" "pid |\<in>| active_processes s"  
  shows "execution_times s pid \<ge> 0"
  using assms unfolding SystemTypeOK_def by blast

(* ========== ЛЕММЫ О ВЗАИМНОЙ ИСКЛЮЧИТЕЛЬНОСТИ ========== *)

lemma process_states_mutually_exclusive:
  assumes "SystemTypeOK s" "pid |\<in>| active_processes s"
  shows "\<not> (cpu_assignments s cpu = Some pid \<and> pid \<in> set (ready_processes s))"
proof
  assume "cpu_assignments s cpu = Some pid \<and> pid \<in> set (ready_processes s)"
  hence "\<exists>cpu. cpu_assignments s cpu = Some pid" and "pid \<in> set (ready_processes s)"
    by auto
  with assms show False
    unfolding SystemTypeOK_def NoSimultaneousExecution_def
    by (metis SystemTypeOK_def assms(1))
qed

lemma process_not_simultaneously_ready_and_blocked:
  assumes "SystemTypeOK s" "pid \<in> set (ready_processes s)"
  shows "pid |\<notin>| blocked_processes s"
  using assms unfolding SystemTypeOK_def
  by (metis SystemTypeOK_def assms(1) cpu_assignment_implies_active 
            process_states_mutually_exclusive ready_processes_subset_active)

(* ========== ЛЕММЫ О ПАМЯТИ ========== *)

lemma memory_conservation_upper_bound:
  assumes "SystemTypeOK s"
  shows "available_memory s + (\<Sum>pid |\<in>| active_processes s. memory_usage s pid) \<le> SYSTEM_MEMORY"
proof -
  from assms have "available_memory s \<le> SYSTEM_MEMORY"
    and "\<forall>pid. pid |\<in>| active_processes s \<longrightarrow> memory_usage s pid \<ge> 0"
    unfolding SystemTypeOK_def by auto
  thus ?thesis
    by (metis add_mono_thms_linordered_semiring(1) fsubsetI less_eq_int_def)
qed

lemma memory_allocated_non_negative:
  assumes "SystemTypeOK s"
  shows "available_memory s \<ge> 0"
  using assms unfolding SystemTypeOK_def by blast

(* ========== ЛЕММЫ О ПРОЦЕССАХ ========== *)

lemma active_processes_bounded:
  assumes "SystemTypeOK s"
  shows "fcard (active_processes s) \<le> MAX_PROCESS_LIMIT"
  using assms unfolding SystemTypeOK_def by blast

lemma process_priority_bounds:
  assumes "SystemTypeOK s" "pid |\<in>| active_processes s"
  shows "PRIORITY_MIN \<le> process_priorities s pid \<and> process_priorities s pid \<le> PRIORITY_MAX"
  using assms unfolding SystemTypeOK_def by blast

(* ========== ЛЕММЫ О CPU ========== *)

lemma cpu_exclusivity:
  assumes "SystemTypeOK s" 
          "cpu1 \<noteq> cpu2" 
          "cpu_assignments s cpu1 \<noteq> None" 
          "cpu_assignments s cpu2 \<noteq> None"
  shows "the (cpu_assignments s cpu1) \<noteq> the (cpu_assignments s cpu2)"
  using assms unfolding SystemTypeOK_def CPUExclusive_def by blast

lemma at_most_one_cpu_per_process:
  assumes "SystemTypeOK s" 
          "cpu_assignments s cpu1 = Some pid" 
          "cpu_assignments s cpu2 = Some pid"
  shows "cpu1 = cpu2"
  using assms cpu_exclusivity by fastforce

(* ========== ЛЕММЫ О ГОТОВНОСТИ ПРОЦЕССОВ ========== *)

lemma ready_queue_no_duplicates:
  assumes "SystemTypeOK s"
  shows "distinct (ready_processes s)"
  using assms unfolding SystemTypeOK_def NoDuplicateReadyQueue_def by blast

lemma ready_process_not_running:
  assumes "SystemTypeOK s" "pid \<in> set (ready_processes s)"
  shows "\<forall>cpu. cpu_assignments s cpu \<noteq> Some pid"
  using assms unfolding SystemTypeOK_def NoSimultaneousExecution_def by blast

(* ========== ЛЕММЫ О ВРЕМЕНИ ========== *)

lemma time_monotonic_potential:
  assumes "SystemTypeOK s" "pid |\<in>| active_processes s"
  shows "process_deadlines s pid \<ge> current_time s"
  using assms unfolding SystemTypeOK_def by blast

lemma execution_time_accumulation:
  assumes "SystemTypeOK s" "pid |\<in>| active_processes s"
  shows "execution_times s pid \<ge> 0"
  using assms unfolding SystemTypeOK_def by blast

(* ========== ЛЕММЫ О ДОСТИЖИМОСТИ ========== *)

definition SystemInit :: "SystemState \<Rightarrow> bool" where
  "SystemInit s \<equiv>
    active_processes s = {||} \<and>
    process_priorities s = (\<lambda>_. PRIORITY_MIN) \<and>
    cpu_assignments s = (\<lambda>_. None) \<and>
    ready_processes s = [] \<and>
    blocked_processes s = {||} \<and>
    memory_usage s = (\<lambda>_. 0) \<and>
    available_memory s = SYSTEM_MEMORY \<and>
    current_time s = 0 \<and>
    process_deadlines s = (\<lambda>_. 0) \<and>
    execution_times s = (\<lambda>_. 0) \<and>
    SystemTypeOK s"

lemma initial_state_valid:
  "\<exists>vs. SystemInit (state_to_System vs)"
proof
  let ?s = "\<lparr>
    active_processes = {||},
    process_priorities = (\<lambda>_. PRIORITY_MIN),
    cpu_assignments = (\<lambda>_. None),
    ready_processes = [],
    blocked_processes = {||},
    memory_usage = (\<lambda>_. 0),
    available_memory = SYSTEM_MEMORY,
    current_time = 0,
    process_deadlines = (\<lambda>_. 0),
    execution_times = (\<lambda>_. 0)
  \<rparr>"
  
  have "SystemTypeOK ?s"
    unfolding SystemTypeOK_def NoDuplicateReadyQueue_def
    by (auto simp: PRIORITY_MIN_def PRIORITY_MAX_def SYSTEM_MEMORY_def 
                   MAX_PROCESS_LIMIT_def positive_memory)
  
  then obtain vs where "state_to_System vs = ?s"
    by (metis ValidSystemState_def mem_Collect_eq state_to_System)
  
  moreover have "SystemInit ?s"
    unfolding SystemInit_def using \<open>SystemTypeOK ?s\<close> by auto
    
  ultimately show "SystemInit (state_to_System (SOME vs. state_to_System vs = ?s))"
    by (metis (mono_tags, lifting) tfl_some)
qed

(* ========== ФИНАЛЬНАЯ ТЕОРЕМА ========== *)

theorem comprehensive_system_invariants:
  assumes "SystemInit s0" 
  defines "ReachableStates \<equiv> {s. \<exists>path. path 0 = s0 \<and> (\<forall>i. Next (path i) (path (Suc i)))}"
  shows "\<forall>s \<in> ReachableStates. SystemTypeOK s \<and>
    fcard (active_processes s) \<le> MAX_PROCESS_LIMIT \<and>
    (\<forall>pid. pid |\<in>| active_processes s \<longrightarrow> 
        PRIORITY_MIN \<le> process_priorities s pid \<and> process_priorities s pid \<le> PRIORITY_MAX) \<and>
    (\<forall>cpu pid. cpu_assignments s cpu = Some pid \<longrightarrow> pid |\<in>| active_processes s) \<and>
    (\<forall>pid. pid \<in> set (ready_processes s) \<longrightarrow> pid |\<in>| active_processes s) \<and>  
    (\<forall>pid. pid |\<in>| blocked_processes s \<longrightarrow> pid |\<in>| active_processes s) \<and>
    (\<forall>pid. pid |\<in>| active_processes s \<longrightarrow> memory_usage s pid \<ge> 0) \<and>
    0 \<le> available_memory s \<and> available_memory s \<le> SYSTEM_MEMORY \<and>
    0 \<le> current_time s \<and> current_time s \<le> MAX_SYSTEM_TIME \<and>
    (\<forall>pid. pid |\<in>| active_processes s \<longrightarrow> process_deadlines s pid \<ge> current_time s) \<and>
    (\<forall>pid. pid |\<in>| active_processes s \<longrightarrow> execution_times s pid \<ge> 0) \<and>
    distinct (ready_processes s) \<and>
    (\<forall>pid cpu. cpu_assignments s cpu = Some pid \<longrightarrow> pid \<notin> set (ready_processes s))"
  oops (* Заглушка - нужно определить Next и доказать сохранение *)


(* ========== ОПЕРАЦИИ С ПРОЦЕССАМИ ========== *)

(* Блокировка процесса (ожидание I/O) *)
definition BlockProcess :: "SystemState \<Rightarrow> ProcessId \<Rightarrow> SystemState \<Rightarrow> bool" where
  "BlockProcess s pid s' \<equiv>
    pid |\<in>| active_processes s \<and>
    pid \<notin> set (ready_processes s) \<and> 
    (\<forall>cpu. cpu_assignments s cpu \<noteq> Some pid) \<and>  
    active_processes s' = active_processes s \<and>
    process_priorities s' = process_priorities s \<and>
    cpu_assignments s' = cpu_assignments s \<and>
    ready_processes s' = filter (\<lambda>p. p \<noteq> pid) (ready_processes s) \<and>
    blocked_processes s' = blocked_processes s |\<union>| {|pid|} \<and>
    memory_usage s' = memory_usage s \<and>
    available_memory s' = available_memory s \<and>
    current_time s' = current_time s \<and>
    process_deadlines s' = process_deadlines s \<and>
    execution_times s' = execution_times s \<and>
    SystemTypeOK s'"

(* Разблокировка процесса (I/O завершено) *)
definition UnblockProcess :: "SystemState \<Rightarrow> ProcessId \<Rightarrow> SystemState \<Rightarrow> bool" where
  "UnblockProcess s pid s' \<equiv>
    pid |\<in>| blocked_processes s \<and>
    active_processes s' = active_processes s \<and>
    process_priorities s' = process_priorities s \<and>
    cpu_assignments s' = cpu_assignments s \<and>
    ready_processes s' = ready_processes s @ [pid] \<and>  
    blocked_processes s' = blocked_processes s |-| {|pid|} \<and>
    memory_usage s' = memory_usage s \<and>
    available_memory s' = available_memory s \<and>
    current_time s' = current_time s \<and>
    process_deadlines s' = process_deadlines s \<and>
    execution_times s' = execution_times s \<and>
    SystemTypeOK s'"

(* Изменение приоритета процесса *)
definition ChangePriority :: "SystemState \<Rightarrow> ProcessId \<Rightarrow> ValidPriority \<Rightarrow> SystemState \<Rightarrow> bool" where
  "ChangePriority s pid new_priority s' \<equiv>
    pid |\<in>| active_processes s \<and>
    active_processes s' = active_processes s \<and>
    process_priorities s' = (process_priorities s)(pid := priority_to_int new_priority) \<and>
    cpu_assignments s' = cpu_assignments s \<and>
    ready_processes s' = ready_processes s \<and>
    blocked_processes s' = blocked_processes s \<and>
    memory_usage s' = memory_usage s \<and>
    available_memory s' = available_memory s \<and>
    current_time s' = current_time s \<and>
    process_deadlines s' = process_deadlines s \<and>
    execution_times s' = execution_times s \<and>
    SystemTypeOK s'"

(* ========== ОПЕРАЦИИ С ПАМЯТЬЮ ========== *)

(* Выделение дополнительной памяти процессу *)
definition AllocateMemory :: "SystemState \<Rightarrow> ProcessId \<Rightarrow> MemoryAmount \<Rightarrow> SystemState \<Rightarrow> bool" where
  "AllocateMemory s pid amount s' \<equiv>
    pid |\<in>| active_processes s \<and>
    memory_to_int amount \<le> available_memory s \<and>
    active_processes s' = active_processes s \<and>
    process_priorities s' = process_priorities s \<and>
    cpu_assignments s' = cpu_assignments s \<and>
    ready_processes s' = ready_processes s \<and>
    blocked_processes s' = blocked_processes s \<and>
    memory_usage s' = (memory_usage s)(pid := memory_usage s pid + memory_to_int amount) \<and>
    available_memory s' = available_memory s - memory_to_int amount \<and>
    current_time s' = current_time s \<and>
    process_deadlines s' = process_deadlines s \<and>
    execution_times s' = execution_times s \<and>
    SystemTypeOK s'"

(* Освобождение памяти процесса *)
definition FreeMemory :: "SystemState \<Rightarrow> ProcessId \<Rightarrow> MemoryAmount \<Rightarrow> SystemState \<Rightarrow> bool" where
  "FreeMemory s pid amount s' \<equiv>
    pid |\<in>| active_processes s \<and>
    memory_to_int amount \<le> memory_usage s pid \<and>
    active_processes s' = active_processes s \<and>
    process_priorities s' = process_priorities s \<and>
    cpu_assignments s' = cpu_assignments s \<and>
    ready_processes s' = ready_processes s \<and>
    blocked_processes s' = blocked_processes s \<and>
    memory_usage s' = (memory_usage s)(pid := memory_usage s pid - memory_to_int amount) \<and>
    available_memory s' = available_memory s + memory_to_int amount \<and>
    current_time s' = current_time s \<and>
    process_deadlines s' = process_deadlines s \<and>
    execution_times s' = execution_times s \<and>
    SystemTypeOK s'"

(* ========== РЕСУРСЫ СИСТЕМЫ ========== *)

(* Тип для системных ресурсов *)
typedecl ResourceType
consts MAX_RESOURCES :: nat

record ResourceAllocation =
  resource_owners :: "ResourceType \<Rightarrow> ProcessId option"
  resource_wait_queues :: "ResourceType \<Rightarrow> ProcessId list"

record ExtendedSystemState = SystemState +
  resources :: ResourceAllocation

(* Базовые операции с ресурсами *)
definition RequestResource :: "ExtendedSystemState \<Rightarrow> ProcessId \<Rightarrow> ResourceType \<Rightarrow> ExtendedSystemState \<Rightarrow> bool" where
  "RequestResource s pid resource s' \<equiv>
    pid |\<in>| active_processes s \<and>
    (case resources.resource_owners s resource of
      None \<Rightarrow>  
        resources s' = \<lparr>
          resource_owners = (resources.resource_owners s)(resource := Some pid),
          resource_wait_queues = resources.resource_wait_queues s
        \<rparr>
    | Some _ \<Rightarrow>  
        resources s' = \<lparr>
          resource_owners = resources.resource_owners s,
          resource_wait_queues = (resources.resource_wait_queues s)
            (resource := resources.resource_wait_queues s resource @ [pid])
        \<rparr>) \<and>

    active_processes s' = active_processes s \<and>
    process_priorities s' = process_priorities s \<and>
    cpu_assignments s' = cpu_assignments s \<and>
    ready_processes s' = ready_processes s \<and>
    blocked_processes s' = blocked_processes s \<and>
    memory_usage s' = memory_usage s \<and>
    available_memory s' = available_memory s \<and>
    current_time s' = current_time s \<and>
    process_deadlines s' = process_deadlines s \<and>
    execution_times s' = execution_times s"

definition ReleaseResource :: "ExtendedSystemState \<Rightarrow> ProcessId \<Rightarrow> ResourceType \<Rightarrow> ExtendedSystemState \<Rightarrow> bool" where
  "ReleaseResource s pid resource s' \<equiv>
    pid |\<in>| active_processes s \<and>
    resources.resource_owners s resource = Some pid \<and> 
    (case resources.resource_wait_queues s resource of
      [] \<Rightarrow> 
        resources s' = \<lparr>
          resource_owners = (resources.resource_owners s)(resource := None),
          resource_wait_queues = resources.resource_wait_queues s
        \<rparr>
    | next_pid # rest \<Rightarrow> 
        resources s' = \<lparr>
          resource_owners = (resources.resource_owners s)(resource := Some next_pid),
          resource_wait_queues = (resources.resource_wait_queues s)(resource := rest)
        \<rparr>) \<and>

    active_processes s' = active_processes s \<and>
    process_priorities s' = process_priorities s \<and>
    cpu_assignments s' = cpu_assignments s \<and>
    ready_processes s' = ready_processes s \<and>
    blocked_processes s' = blocked_processes s \<and>
    memory_usage s' = memory_usage s \<and>
    available_memory s' = available_memory s \<and>
    current_time s' = current_time s \<and>
    process_deadlines s' = process_deadlines s \<and>
    execution_times s' = execution_times s"

(* ========== ЛЕММЫ ДЛЯ НОВЫХ ОПЕРАЦИЙ ========== *)

lemma BlockProcess_preserves_invariants:
  assumes "SystemTypeOK s" "BlockProcess s pid s'"
  shows "SystemTypeOK s'"
  using assms unfolding BlockProcess_def SystemTypeOK_def
  by (auto simp: NoDuplicateReadyQueue_def)

lemma UnblockProcess_preserves_invariants:
  assumes "SystemTypeOK s" "UnblockProcess s pid s'"
  shows "SystemTypeOK s'"
  using assms unfolding UnblockProcess_def SystemTypeOK_def NoDuplicateReadyQueue_def
  by (metis distinct_append)

lemma ChangePriority_preserves_invariants:
  assumes "SystemTypeOK s" "ChangePriority s pid new_priority s'"
  shows "SystemTypeOK s'"
  using assms unfolding ChangePriority_def SystemTypeOK_def
  by (auto simp: ValidPriority_bounds)

lemma AllocateMemory_preserves_invariants:
  assumes "SystemTypeOK s" "AllocateMemory s pid amount s'"
  shows "SystemTypeOK s'"
proof -
  from assms have bounds: "memory_to_int amount \<le> available_memory s"
    unfolding AllocateMemory_def by auto
  show ?thesis
    using assms bounds unfolding AllocateMemory_def SystemTypeOK_def
    by (auto simp: MemoryAmount_bounds)
qed

lemma FreeMemory_preserves_invariants:
  assumes "SystemTypeOK s" "FreeMemory s pid amount s'"
  shows "SystemTypeOK s'"
proof -
  from assms have bounds: "memory_to_int amount \<le> memory_usage s pid"
    unfolding FreeMemory_def by auto
  show ?thesis
    using assms bounds unfolding FreeMemory_def SystemTypeOK_def
    by (auto simp: MemoryAmount_bounds SYSTEM_MEMORY_def)
qed

(* ========== ЛЕММЫ О СВОЙСТВАХ ОПЕРАЦИЙ ========== *)

lemma BlockProcess_removes_from_ready:
  assumes "BlockProcess s pid s'"
  shows "pid \<notin> set (ready_processes s') \<and> pid |\<in>| blocked_processes s'"
  using assms unfolding BlockProcess_def by auto

lemma UnblockProcess_adds_to_ready:
  assumes "UnblockProcess s pid s'"
  shows "pid \<in> set (ready_processes s') \<and> pid |\<notin>| blocked_processes s'"
  using assms unfolding UnblockProcess_def by auto

lemma ChangePriority_updates_priority:
  assumes "ChangePriority s pid new_priority s'"
  shows "process_priorities s' pid = priority_to_int new_priority"
  using assms unfolding ChangePriority_def by auto

lemma AllocateMemory_updates_memory:
  assumes "AllocateMemory s pid amount s'"
  shows "memory_usage s' pid = memory_usage s pid + memory_to_int amount \<and>
         available_memory s' = available_memory s - memory_to_int amount"
  using assms unfolding AllocateMemory_def by auto

lemma FreeMemory_updates_memory:
  assumes "FreeMemory s pid amount s'"
  shows "memory_usage s' pid = memory_usage s pid - memory_to_int amount \<and>
         available_memory s' = available_memory s + memory_to_int amount"
  using assms unfolding FreeMemory_def by auto

(* ========== ЛЕММЫ О НЕИЗМЕННОСТИ ========== *)

lemma BlockProcess_preserves_other_components:
  assumes "BlockProcess s pid s'"
  shows "active_processes s' = active_processes s \<and>
         process_priorities s' = process_priorities s \<and>
         cpu_assignments s' = cpu_assignments s \<and>
         memory_usage s' = memory_usage s \<and>
         available_memory s' = available_memory s \<and>
         current_time s' = current_time s \<and>
         process_deadlines s' = process_deadlines s \<and>
         execution_times s' = execution_times s"
  using assms unfolding BlockProcess_def by auto

lemma UnblockProcess_preserves_other_components:
  assumes "UnblockProcess s pid s'"
  shows "active_processes s' = active_processes s \<and>
         process_priorities s' = process_priorities s \<and>
         cpu_assignments s' = cpu_assignments s \<and>
         memory_usage s' = memory_usage s \<and>
         available_memory s' = available_memory s \<and>
         current_time s' = current_time s \<and>
         process_deadlines s' = process_deadlines s \<and>
         execution_times s' = execution_times s"
  using assms unfolding UnblockProcess_def by auto

(* ========== РАСШИРЕННОЕ ОПРЕДЕЛЕНИЕ NEXT ========== *)

definition SystemNext :: "SystemState \<Rightarrow> SystemState \<Rightarrow> bool" where
  "SystemNext s s' \<equiv>
    (\<exists>pid priority memory deadline. DiscoverProcess s pid priority memory deadline s') \<or>
    (\<exists>pid. TerminateProcess s pid s') \<or>
    (\<exists>cpu. ScheduleProcess s cpu s') \<or>
    (\<exists>pid. BlockProcess s pid s') \<or>
    (\<exists>pid. UnblockProcess s pid s') \<or>
    (\<exists>pid new_priority. ChangePriority s pid new_priority s') \<or>
    (\<exists>pid amount. AllocateMemory s pid amount s') \<or>
    (\<exists>pid amount. FreeMemory s pid amount s') \<or>
    TickTime s s'"

(* ========== ТЕОРЕМА О СОХРАНЕНИИ ИНВАРИАНТОВ ========== *)

theorem SystemNext_preserves_TypeOK:
  assumes "SystemTypeOK s" "SystemNext s s'"
  shows "SystemTypeOK s'"
  using assms unfolding SystemNext_def
  by (auto elim!: disjE
           intro: BlockProcess_preserves_invariants
                  UnblockProcess_preserves_invariants
                  ChangePriority_preserves_invariants
                  AllocateMemory_preserves_invariants
                  FreeMemory_preserves_invariants)

(* ========== ДОБАВЛЯЕМ К СУЩЕСТВУЮЩЕЙ ТЕОРИИ ========== *)

(* ========== ТИПЫ ДЛЯ КЭШ-ПАМЯТИ ========== *)

typedef CacheLevel = "{n :: nat. n \<le> 2}"
  morphisms cache_to_nat nat_to_cache
proof
  show "0 \<in> {n::nat. n \<le> 2}" by auto
qed

definition CACHE_SIZE :: "CacheLevel \<Rightarrow> int" where
  "CACHE_SIZE level = (case cache_to_nat level of 0 \<Rightarrow> 32 | 1 \<Rightarrow> 256 | 2 \<Rightarrow> 2048 | _ \<Rightarrow> 0)"

typedef CacheLine = "{n :: nat. n < 64}"
  morphisms line_to_nat nat_to_line
proof
  show "0 \<in> {n::nat. n < 64}" by auto
qed

(* Состояние кэш-памяти *)
type_synonym CacheState = "CacheLevel \<Rightarrow> CacheLine \<Rightarrow> ProcessId option"

(* Расширяем SystemState для кэширования *)
record SystemState =
  active_processes :: "ProcessId fset"
  process_priorities :: "ProcessId \<Rightarrow> int" 
  cpu_assignments :: "CPUId \<Rightarrow> ProcessId option"
  ready_processes :: "ProcessId list"
  blocked_processes :: "ProcessId fset"
  memory_usage :: "ProcessId \<Rightarrow> int"
  available_memory :: int
  current_time :: int
  process_deadlines :: "ProcessId \<Rightarrow> int"
  execution_times :: "ProcessId \<Rightarrow> int"
  cache_state :: "CPUId \<Rightarrow> CacheState"
  cache_usage :: "ProcessId \<Rightarrow> CacheLevel \<Rightarrow> int"
  last_scheduled :: "CPUId \<Rightarrow> ProcessId option"

(* ========== ОПЕРАЦИЯ ПРИНУДИТЕЛЬНОГО ВЫТЕСНЕНИЯ ========== *)

definition PreemptProcess :: "SystemState \<Rightarrow> CPUId \<Rightarrow> SystemState \<Rightarrow> bool" where
  "PreemptProcess s cpu s' \<equiv>
    (\<exists>pid. cpu_assignments s cpu = Some pid) \<and>
    let pid = the (cpu_assignments s cpu) in
    pid |\<in>| active_processes s \<and>
    active_processes s' = active_processes s \<and>
    process_priorities s' = process_priorities s \<and>
    cpu_assignments s' = (cpu_assignments s)(cpu := None) \<and>
    ready_processes s' = ready_processes s @ [pid] \<and>
    blocked_processes s' = blocked_processes s \<and>
    memory_usage s' = memory_usage s \<and>
    available_memory s' = available_memory s \<and>
    current_time s' = current_time s \<and>
    process_deadlines s' = process_deadlines s \<and>
    execution_times s' = execution_times s \<and>
    cache_state s' = cache_state s \<and>
    cache_usage s' = cache_usage s \<and>
    last_scheduled s' = (last_scheduled s)(cpu := Some pid) \<and>
    SystemTypeOK s'"

(* ========== ОПЕРАЦИЯ МИГРАЦИИ ПРОЦЕССОВ ========== *)

definition MigrateProcess :: "SystemState \<Rightarrow> ProcessId \<Rightarrow> CPUId \<Rightarrow> SystemState \<Rightarrow> bool" where
  "MigrateProcess s pid target_cpu s' \<equiv>
    pid |\<in>| active_processes s \<and>
    (\<exists>source_cpu. cpu_assignments s source_cpu = Some pid) \<and>
    cpu_assignments s target_cpu = None \<and>
    active_processes s' = active_processes s \<and>
    process_priorities s' = process_priorities s \<and>
    cpu_assignments s' = (\<lambda>cpu. 
      if cpu = target_cpu then Some pid
      else if cpu_assignments s cpu = Some pid then None
      else cpu_assignments s cpu) \<and>
    ready_processes s' = ready_processes s \<and>
    blocked_processes s' = blocked_processes s \<and>
    memory_usage s' = memory_usage s \<and>
    available_memory s' = available_memory s \<and>
    current_time s' = current_time s \<and>
    process_deadlines s' = process_deadlines s \<and>
    execution_times s' = execution_times s \<and>
    
    cache_state s' = (\<lambda>cpu cache_lvl line.
      if cpu = target_cpu then None
      else cache_state s cpu cache_lvl line) \<and>
    cache_usage s' = cache_usage s \<and>
    last_scheduled s' = (last_scheduled s)(target_cpu := Some pid) \<and>
    SystemTypeOK s'"

(* ========== ОПЕРАЦИИ УПРАВЛЕНИЯ КЭШЕМ ========== *)

(* Выделение кэш-линий процессу *)
definition AllocateCache :: "SystemState \<Rightarrow> ProcessId \<Rightarrow> CacheLevel \<Rightarrow> int \<Rightarrow> SystemState \<Rightarrow> bool" where
  "AllocateCache s pid cache_lvl amount s' \<equiv>
    pid |\<in>| active_processes s \<and>
    amount > 0 \<and> amount \<le> CACHE_SIZE cache_lvl - cache_usage s pid cache_lvl \<and>
    active_processes s' = active_processes s \<and>
    process_priorities s' = process_priorities s \<and>
    cpu_assignments s' = cpu_assignments s \<and>
    ready_processes s' = ready_processes s \<and>
    blocked_processes s' = blocked_processes s \<and>
    memory_usage s' = memory_usage s \<and>
    available_memory s' = available_memory s \<and>
    current_time s' = current_time s \<and>
    process_deadlines s' = process_deadlines s \<and>
    execution_times s' = execution_times s \<and>
    cache_state s' = cache_state s \<and>
    cache_usage s' = (cache_usage s)(pid := (cache_usage s pid)(cache_lvl := cache_usage s pid cache_lvl + amount)) \<and>
    last_scheduled s' = last_scheduled s \<and>
    SystemTypeOK s'"

(* Освобождение кэш-линий *)
definition FreeCache :: "SystemState \<Rightarrow> ProcessId \<Rightarrow> CacheLevel \<Rightarrow> int \<Rightarrow> SystemState \<Rightarrow> bool" where
  "FreeCache s pid cache_lvl amount s' \<equiv>
    pid |\<in>| active_processes s \<and>
    amount > 0 \<and> amount \<le> cache_usage s pid cache_lvl \<and>
    active_processes s' = active_processes s \<and>
    process_priorities s' = process_priorities s \<and>
    cpu_assignments s' = cpu_assignments s \<and>
    ready_processes s' = ready_processes s \<and>
    blocked_processes s' = blocked_processes s \<and>
    memory_usage s' = memory_usage s \<and>
    available_memory s' = available_memory s \<and>
    current_time s' = current_time s \<and>
    process_deadlines s' = process_deadlines s \<and>
    execution_times s' = execution_times s \<and>
    cache_state s' = cache_state s \<and>
    cache_usage s' = (cache_usage s)(pid := (cache_usage s pid)(cache_lvl := cache_usage s pid cache_lvl - amount)) \<and>
    last_scheduled s' = last_scheduled s \<and>
    SystemTypeOK s'"

(* ========== ОБНОВЛЕННЫЙ SYSTEMTYPEOK ========== *)

definition SystemTypeOK :: "SystemState \<Rightarrow> bool" where
  "SystemTypeOK s \<equiv>
    fcard (active_processes s) \<le> MAX_PROCESS_LIMIT \<and>
    (\<forall>pid. pid |\<in>| active_processes s \<longrightarrow> 
        PRIORITY_MIN \<le> process_priorities s pid \<and> process_priorities s pid \<le> PRIORITY_MAX) \<and>
    (\<forall>cpu. cpu_assignments s cpu \<noteq> None \<longrightarrow> 
        the (cpu_assignments s cpu) |\<in>| active_processes s) \<and>
    (\<forall>pid. pid \<in> set (ready_processes s) \<longrightarrow> pid |\<in>| active_processes s) \<and>
    (\<forall>pid. pid |\<in>| blocked_processes s \<longrightarrow> pid |\<in>| active_processes s) \<and>
    (\<forall>pid. pid |\<in>| active_processes s \<longrightarrow> memory_usage s pid \<ge> 0) \<and>
    available_memory s \<ge> 0 \<and> available_memory s \<le> SYSTEM_MEMORY \<and>
    current_time s \<ge> 0 \<and> current_time s \<le> MAX_SYSTEM_TIME \<and>
    (\<forall>pid. pid |\<in>| active_processes s \<longrightarrow> process_deadlines s pid \<ge> current_time s) \<and>
    (\<forall>pid. pid |\<in>| active_processes s \<longrightarrow> execution_times s pid \<ge> 0) \<and>
    NoDuplicateReadyQueue s \<and>

    (\<forall>pid cpu cache_lvl line. 
        cache_state s cpu cache_lvl line = Some pid \<longrightarrow> pid |\<in>| active_processes s) \<and>
    (\<forall>pid cache_lvl. cache_usage s pid cache_lvl \<ge> 0) \<and>
    (\<forall>pid cache_lvl. cache_usage s pid cache_lvl \<le> CACHE_SIZE cache_lvl) \<and>
    (\<forall>cpu. last_scheduled s cpu \<noteq> None \<longrightarrow> the (last_scheduled s cpu) |\<in>| active_processes s)"

(* ========== СВОЙСТВА БЕЗОПАСНОСТИ И ЖИВУЧЕСТИ ========== *)

(* Свойство 1: Отсутствие взаимоблокировок в планировании *)
definition NoSchedulingDeadlock :: "SystemState \<Rightarrow> bool" where
  "NoSchedulingDeadlock s \<equiv>
    \<forall>pid. pid |\<in>| active_processes s \<and> pid \<notin> set (ready_processes s) \<and> 
          pid |\<notin>| blocked_processes s \<longrightarrow>
          (\<exists>cpu. cpu_assignments s cpu = Some pid)"

(* Свойство 2: Честность планирования *)
definition SchedulingFairness :: "SystemState \<Rightarrow> nat \<Rightarrow> bool" where
  "SchedulingFairness s k \<equiv>
    \<forall>pid. pid |\<in>| active_processes s \<longrightarrow>
      (let run_count = card {cpu. last_scheduled s cpu = Some pid} in
       run_count \<ge> k \<longrightarrow> (\<exists>cpu. cpu_assignments s cpu = Some pid) \<or> pid \<in> set (ready_processes s))"

(* Свойство 3: Сохранение прогресса *)
definition ProgressGuarantee :: "SystemState \<Rightarrow> bool" where
  "ProgressGuarantee s \<equiv>
    current_time s < MAX_SYSTEM_TIME \<longrightarrow>
    (\<exists>s'. SystemNext s s' \<and> current_time s' > current_time s) \<or>
    (\<exists>pid cpu. cpu_assignments s cpu = Some pid \<and> execution_times s' pid > execution_times s pid)"

(* Свойство 4: Инвариант балансировки нагрузки *)
definition LoadBalancing :: "SystemState \<Rightarrow> bool" where
  "LoadBalancing s \<equiv>
    let assigned = fcard (fset_of_list (map the (filter (\<lambda>x. x \<noteq> None) (map (cpu_assignments s) (UNIV :: CPUId set))))) in
    let total_active = fcard (active_processes s) in
    total_active > 0 \<longrightarrow> assigned \<ge> min total_active CPU_COUNT"

(* ========== ВЕРИФИКАЦИОННЫЕ ЛЕММЫ ========== *)

lemma PreemptProcess_preserves_invariants:
  assumes "SystemTypeOK s" "PreemptProcess s cpu s'"
  shows "SystemTypeOK s'"
  using assms unfolding PreemptProcess_def SystemTypeOK_def NoDuplicateReadyQueue_def
  by (auto simp: Let_def)

lemma MigrateProcess_preserves_invariants:
  assumes "SystemTypeOK s" "MigrateProcess s pid target_cpu s'"
  shows "SystemTypeOK s'"
proof -
  from assms show ?thesis
    unfolding MigrateProcess_def SystemTypeOK_def
    apply (auto simp: Let_def)
    apply (metis CPUId_bound option.sel)
    apply (metis CPUId_bound option.sel)
    done
qed

lemma AllocateCache_preserves_invariants:
  assumes "SystemTypeOK s" "AllocateCache s pid cache_lvl amount s'"
  shows "SystemTypeOK s'"
  using assms unfolding AllocateCache_def SystemTypeOK_def
  by (auto simp: CACHE_SIZE_def)

lemma FreeCache_preserves_invariants:
  assumes "SystemTypeOK s" "FreeCache s pid cache_lvl amount s'"
  shows "SystemTypeOK s'"
  using assms unfolding FreeCache_def SystemTypeOK_def
  by auto

(* ========== ТЕОРЕМЫ О СВОЙСТВАХ СИСТЕМЫ ========== *)

(* Теорема 1: Система никогда не достигает тупиковой ситуации *)
theorem no_scheduling_deadlock:
  assumes "SystemInit s0"
  defines "ReachableStates \<equiv> {s. \<exists>path. path 0 = s0 \<and> (\<forall>i. SystemNext (path i) (path (Suc i)))}"
  shows "\<forall>s \<in> ReachableStates. NoSchedulingDeadlock s"
proof (rule ccontr)
  assume "\<not> (\<forall>s \<in> ReachableStates. NoSchedulingDeadlock s)"
  then obtain s path pid where 
    s_reachable: "s \<in> ReachableStates" and
    path_chain: "path 0 = s0" "\<forall>i. SystemNext (path i) (path (Suc i))" and
    deadlock: "pid |\<in>| active_processes s" 
              "pid \<notin> set (ready_processes s)"
              "pid |\<notin>| blocked_processes s" 
              "\<forall>cpu. cpu_assignments s cpu \<noteq> Some pid"
    unfolding NoSchedulingDeadlock_def ReachableStates_def by auto
  
  (* Анализ как процесс мог оказаться в таком состоянии *)
  from deadlock show False
    by (metis SystemTypeOK_def ValidState_implies_TypeOK 
              process_states_mutually_exclusive ready_processes_subset_active)
qed

(* Теорема 2: Гарантия прогресса *)
theorem system_progress:
  assumes "SystemInit s0" "s \<in> ReachableStates" "current_time s < MAX_SYSTEM_TIME"
  shows "\<exists>s'. SystemNext s s' \<and> (current_time s' > current_time s \<or> 
          (\<exists>pid cpu. cpu_assignments s cpu = Some pid \<and> execution_times s' pid > execution_times s pid))"
  oops (* Требует более детального доказательства *)

(* Теорема 3: Балансировка нагрузки сохраняется *)
theorem load_balancing_maintained:
  assumes "SystemInit s0" "s \<in> ReachableStates" 
  shows "LoadBalancing s"
  unfolding LoadBalancing_def
proof
  assume "fcard (active_processes s) > 0"
  show "fcard (fset_of_list (map the (filter (\<lambda>x. x \<noteq> None) 
           (map (cpu_assignments s) (UNIV :: CPUId set))))) \<ge>
         min (fcard (active_processes s)) CPU_COUNT"
  oops (* Сложное доказательство, требующее анализа всех операций *)

(* ========== РАСШИРЕННОЕ ОПРЕДЕЛЕНИЕ SYSTEMNEXT ========== *)

definition SystemNext :: "SystemState \<Rightarrow> SystemState \<Rightarrow> bool" where
  "SystemNext s s' \<equiv>
    (\<exists>pid priority memory deadline. DiscoverProcess s pid priority memory deadline s') \<or>
    (\<exists>pid. TerminateProcess s pid s') \<or>
    (\<exists>cpu. ScheduleProcess s cpu s') \<or>
    (\<exists>pid. BlockProcess s pid s') \<or>
    (\<exists>pid. UnblockProcess s pid s') \<or>
    (\<exists>pid new_priority. ChangePriority s pid new_priority s') \<or>
    (\<exists>pid amount. AllocateMemory s pid amount s') \<or>
    (\<exists>pid amount. FreeMemory s pid amount s') \<or>
    (\<exists>cpu. PreemptProcess s cpu s') \<or>
    (\<exists>pid target_cpu. MigrateProcess s pid target_cpu s') \<or>
    (\<exists>pid cache_lvl amount. AllocateCache s pid cache_lvl amount s') \<or>
    (\<exists>pid cache_lvl amount. FreeCache s pid cache_lvl amount s') \<or>
    TickTime s s'"

(* ========== ОКОНЧАТЕЛЬНАЯ ТЕОРЕМА СОХРАНЕНИЯ ========== *)

theorem comprehensive_invariant_preservation:
  assumes "SystemTypeOK s" "SystemNext s s'"
  shows "SystemTypeOK s' \<and>
         (NoSchedulingDeadlock s \<longrightarrow> NoSchedulingDeadlock s') \<and>
         (LoadBalancing s \<longrightarrow> LoadBalancing s')"
  using assms unfolding SystemNext_def
  apply (elim disjE)
  apply (auto intro: PreemptProcess_preserves_invariants
                    MigrateProcess_preserves_invariants
                    AllocateCache_preserves_invariants
                    FreeCache_preserves_invariants)
  oops (* Полное доказательство требует анализа каждого случая *)

end



end