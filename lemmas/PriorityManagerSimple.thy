theory PriorityManagerSimple
imports Main "HOL-Library.FSet" "HOL-Library.Sublist"
begin

(* Базовые типы *)
typedecl ProcessId
typedecl CPUId  
typedecl Resource

(* Константы *)
definition MAX_PROCESSES :: nat where "MAX_PROCESSES = 3"
definition NUM_CPUS :: nat where "NUM_CPUS = 2"  
definition MIN_PRIORITY :: int where "MIN_PRIORITY = 10"
definition MAX_PRIORITY :: int where "MAX_PRIORITY = 95"
definition TOTAL_MEMORY :: int where "TOTAL_MEMORY = 1000"
definition MAX_TIME :: int where "MAX_TIME = 20"

(* NULL процесс *)
consts NULL :: ProcessId

(* Аксиомы конечности *)
axiomatization where
  ProcessIds_finite: "finite (UNIV :: ProcessId set)" and 
  CPUIds_finite: "finite (UNIV :: CPUId set)" and
  Resources_finite: "finite (UNIV :: Resource set)" and
  TOTAL_MEMORY_positive: "TOTAL_MEMORY > 0"

(* Упрощенное состояние системы *)
record State =
  processes :: "ProcessId fset"
  priorities :: "ProcessId \<Rightarrow> int"
  cpu_assignment :: "CPUId \<Rightarrow> ProcessId option"
  ready_queue :: "ProcessId list"
  blocked_processes :: "ProcessId fset"
  memory_usage :: "ProcessId \<Rightarrow> int"
  available_memory :: int
  current_time :: int
  deadlines :: "ProcessId \<Rightarrow> int"
  execution_time :: "ProcessId \<Rightarrow> int"

definition NoDuplicatesReadyQueue :: "State \<Rightarrow> bool" where
  "NoDuplicatesReadyQueue s \<equiv> distinct (ready_queue s)"

(* Типовые инварианты *)
definition TypeOK :: "State \<Rightarrow> bool" where
  "TypeOK s \<equiv>
    fcard (processes s) \<le> MAX_PROCESSES \<and>
    (\<forall>pid. pid |\<in>| processes s \<longrightarrow> 
        MIN_PRIORITY \<le> priorities s pid \<and> priorities s pid \<le> MAX_PRIORITY) \<and>
    (\<forall>cpu. cpu_assignment s cpu \<noteq> None \<longrightarrow> 
        the (cpu_assignment s cpu) |\<in>| processes s) \<and>
    (\<forall>pid. pid \<in> set (ready_queue s) \<longrightarrow> pid |\<in>| processes s) \<and>
    (\<forall>pid. pid |\<in>| blocked_processes s \<longrightarrow> pid |\<in>| processes s) \<and>
    (\<forall>pid. pid |\<in>| processes s \<longrightarrow> memory_usage s pid \<ge> 0) \<and>
    available_memory s \<ge> 0 \<and> available_memory s \<le> TOTAL_MEMORY \<and>
    current_time s \<ge> 0 \<and> current_time s \<le> MAX_TIME \<and>
    (\<forall>pid. pid |\<in>| processes s \<longrightarrow> deadlines s pid \<ge> current_time s) \<and>
    (\<forall>pid. pid |\<in>| processes s \<longrightarrow> execution_time s pid \<ge> 0) \<and>
    NoDuplicatesReadyQueue s"


(* Начальное состояние *)
definition Init :: "State \<Rightarrow> bool" where
  "Init s \<equiv>
    processes s = {||} \<and>
    priorities s = (\<lambda>_. MIN_PRIORITY) \<and>
    cpu_assignment s = (\<lambda>_. None) \<and>
    ready_queue s = [] \<and>
    blocked_processes s = {||} \<and>
    memory_usage s = (\<lambda>_. 0) \<and>
    available_memory s = TOTAL_MEMORY \<and>
    current_time s = 0 \<and>
    deadlines s = (\<lambda>_. 0) \<and>
    execution_time s = (\<lambda>_. 0) \<and>
    TypeOK s"

(* Действие: обнаружение нового процесса *)
definition DiscoverProcess :: "State \<Rightarrow> ProcessId \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> State \<Rightarrow> bool" where
  "DiscoverProcess s pid priority memory deadline s' \<equiv>
    \<not> pid |\<in>| processes s \<and>
    fcard (processes s) < MAX_PROCESSES \<and>
    MIN_PRIORITY \<le> priority \<and> priority \<le> MAX_PRIORITY \<and>
    memory \<le> available_memory s \<and>
    deadline > current_time s \<and>
    processes s' = processes s |\<union>| {|pid|} \<and>
    priorities s' = (priorities s)(pid := priority) \<and>
    cpu_assignment s' = cpu_assignment s \<and>
    ready_queue s' = ready_queue s @ [pid] \<and>
    blocked_processes s' = blocked_processes s \<and>
    memory_usage s' = (memory_usage s)(pid := memory) \<and>
    available_memory s' = available_memory s - memory \<and>
    current_time s' = current_time s \<and>
    deadlines s' = (deadlines s)(pid := deadline) \<and>
    execution_time s' = (execution_time s)(pid := 0) \<and>
    TypeOK s'"

(* Действие: завершение процесса *)
definition TerminateProcess :: "State \<Rightarrow> ProcessId \<Rightarrow> State \<Rightarrow> bool" where
  "TerminateProcess s pid s' \<equiv>
    pid |\<in>| processes s \<and>
    processes s' = processes s |-| {|pid|} \<and>
    priorities s' = (\<lambda>p. if p = pid then MIN_PRIORITY else priorities s p) \<and>
    cpu_assignment s' = (\<lambda>cpu. if cpu_assignment s cpu = Some pid then None else cpu_assignment s cpu) \<and>
    ready_queue s' = filter (\<lambda>p. p \<noteq> pid) (ready_queue s) \<and>
    blocked_processes s' = blocked_processes s |-| {|pid|} \<and>
    memory_usage s' = (\<lambda>p. if p = pid then 0 else memory_usage s p) \<and>
    available_memory s' = available_memory s + memory_usage s pid \<and>
    current_time s' = current_time s \<and>
    deadlines s' = (\<lambda>p. if p = pid then 0 else deadlines s p) \<and>
    execution_time s' = (\<lambda>p. if p = pid then 0 else execution_time s p) \<and>
    TypeOK s'"

(* Действие: назначение процесса на CPU - ИСПРАВЛЕННАЯ ВЕРСИЯ *)
definition ScheduleProcess :: "State \<Rightarrow> CPUId \<Rightarrow> State \<Rightarrow> bool" where
  "ScheduleProcess s cpu s' \<equiv>
    cpu_assignment s cpu = None \<and>
    ready_queue s \<noteq> [] \<and>
    (\<exists>pid. pid = hd (ready_queue s) \<and>
          (\<forall>other_cpu. other_cpu \<noteq> cpu \<longrightarrow> cpu_assignment s other_cpu \<noteq> Some pid) \<and>
          cpu_assignment s' = (cpu_assignment s)(cpu := Some pid) \<and>
          ready_queue s' = tl (ready_queue s)) \<and>
    processes s' = processes s \<and>
    priorities s' = priorities s \<and>
    blocked_processes s' = blocked_processes s \<and>
    memory_usage s' = memory_usage s \<and>
    available_memory s' = available_memory s \<and>
    current_time s' = current_time s \<and>
    deadlines s' = deadlines s \<and>
    execution_time s' = execution_time s \<and>
    TypeOK s'"

(* Действие: продвижение времени *)
definition TickTime :: "State \<Rightarrow> State \<Rightarrow> bool" where
  "TickTime s s' \<equiv>
    current_time s < MAX_TIME \<and>
    current_time s' = current_time s + 1 \<and>
    execution_time s' = (\<lambda>pid. 
      if pid |\<in>| processes s \<and> (\<exists>cpu. cpu_assignment s cpu = Some pid)
      then execution_time s pid + 1
      else execution_time s pid) \<and>
    processes s' = processes s \<and>
    priorities s' = priorities s \<and>
    cpu_assignment s' = cpu_assignment s \<and>
    ready_queue s' = ready_queue s \<and>
    blocked_processes s' = blocked_processes s \<and>
    memory_usage s' = memory_usage s \<and>
    available_memory s' = available_memory s \<and>
    deadlines s' = deadlines s \<and>
    TypeOK s'"

(* Следующее состояние *)
definition Next :: "State \<Rightarrow> State \<Rightarrow> bool" where
  "Next s s' \<equiv>
    (\<exists>pid priority memory deadline. DiscoverProcess s pid priority memory deadline s') \<or>
    (\<exists>pid. TerminateProcess s pid s') \<or>
    (\<exists>cpu. ScheduleProcess s cpu s') \<or>
    TickTime s s'"

(* Отношение достижимости *)
inductive Reachable :: "State \<Rightarrow> State \<Rightarrow> bool" where
  reachable_init: "Init s \<Longrightarrow> Reachable s s"
| reachable_step: "\<lbrakk> Reachable s0 s; Next s s' \<rbrakk> \<Longrightarrow> Reachable s0 s'"

(* Ключевые инварианты безопасности *)

definition PrioritiesInBounds :: "State \<Rightarrow> bool" where
  "PrioritiesInBounds s \<equiv>
    \<forall>pid. pid |\<in>| processes s \<longrightarrow> 
      MIN_PRIORITY \<le> priorities s pid \<and> priorities s pid \<le> MAX_PRIORITY"

definition MemoryBounded :: "State \<Rightarrow> bool" where
  "MemoryBounded s \<equiv>
    available_memory s \<ge> 0 \<and> available_memory s \<le> TOTAL_MEMORY \<and>
    (\<forall>pid. pid |\<in>| processes s \<longrightarrow> memory_usage s pid \<ge> 0) \<and>
    available_memory s \<le> TOTAL_MEMORY"

definition CPUExclusive :: "State \<Rightarrow> bool" where
  "CPUExclusive s \<equiv>
    \<forall>cpu1 cpu2. cpu1 \<noteq> cpu2 \<and> cpu_assignment s cpu1 \<noteq> None \<and> cpu_assignment s cpu2 \<noteq> None \<longrightarrow>
      the (cpu_assignment s cpu1) \<noteq> the (cpu_assignment s cpu2)"

definition NoSimultaneousExecution :: "State \<Rightarrow> bool" where
  "NoSimultaneousExecution s \<equiv>
    \<forall>pid. (\<exists>cpu. cpu_assignment s cpu = Some pid) \<longrightarrow> pid \<notin> set (ready_queue s)"

definition DeadlinesValid :: "State \<Rightarrow> bool" where
  "DeadlinesValid s \<equiv>
    \<forall>pid. pid |\<in>| processes s \<longrightarrow> deadlines s pid \<ge> current_time s"

definition ProcessCountBounded :: "State \<Rightarrow> bool" where
  "ProcessCountBounded s \<equiv> fcard (processes s) \<le> MAX_PROCESSES"

definition NoDuplicatesInReadyQueue :: "State \<Rightarrow> bool" where
  "NoDuplicatesInReadyQueue s \<equiv> distinct (ready_queue s)"



(* Леммы о начальном состоянии *)

lemma Init_implies_TypeOK:
  "Init s \<Longrightarrow> TypeOK s"
  by (simp add: Init_def)

lemma Init_implies_PrioritiesInBounds:
  "Init s \<Longrightarrow> PrioritiesInBounds s"
  by (auto simp: Init_def PrioritiesInBounds_def)

lemma Init_implies_MemoryBounded:
  "Init s \<Longrightarrow> MemoryBounded s"
  using Init_def MemoryBounded_def TOTAL_MEMORY_positive by auto

lemma Init_implies_CPUExclusive:
  "Init s \<Longrightarrow> CPUExclusive s"
  by (auto simp: Init_def CPUExclusive_def)

lemma Init_implies_NoSimultaneousExecution:
  "Init s \<Longrightarrow> NoSimultaneousExecution s"
  by (auto simp: Init_def NoSimultaneousExecution_def)

lemma Init_implies_DeadlinesValid:
  "Init s \<Longrightarrow> DeadlinesValid s"
  by (auto simp: Init_def DeadlinesValid_def)

lemma Init_implies_ProcessCountBounded:
  "Init s \<Longrightarrow> ProcessCountBounded s"
  using Init_def ProcessCountBounded_def by (simp add: fcard_fempty)

lemma Init_implies_NoDuplicatesReadyQueue:
  "Init s \<Longrightarrow> NoDuplicatesReadyQueue s"
  by (auto simp: Init_def NoDuplicatesReadyQueue_def)

(* Леммы о сохранении каждого инварианта *)

lemma TypeOK_preserved:
  assumes "TypeOK s" "Next s s'"
  shows "TypeOK s'"
  using assms
  by (auto simp: Next_def TypeOK_def
                DiscoverProcess_def TerminateProcess_def 
                ScheduleProcess_def TickTime_def)

lemma PrioritiesInBounds_preserved:
  assumes "PrioritiesInBounds s" "Next s s'"
  shows "PrioritiesInBounds s'"
  using assms
  using Next_def PrioritiesInBounds_def
                DiscoverProcess_def TerminateProcess_def 
                ScheduleProcess_def TickTime_def  by (smt (verit) TypeOK_def)

lemma MemoryBounded_preserved:
  assumes "MemoryBounded s" "Next s s'"
  shows "MemoryBounded s'"
  using assms
  using  Next_def MemoryBounded_def
                DiscoverProcess_def TerminateProcess_def 
                ScheduleProcess_def TickTime_def using TypeOK_def by auto

lemma head_not_in_tail_after_schedule:
  assumes "ScheduleProcess s cpu s'" 
  assumes "ready_queue s \<noteq> []"
  assumes "NoDuplicatesReadyQueue s"
  shows "hd (ready_queue s) \<notin> set (ready_queue s')"
  using assms
  using ScheduleProcess_def NoDuplicatesReadyQueue_def by (metis distinct.simps(2) list.exhaust_sel)


(* this lemma required us to correct Schedule definition!*)

lemma CPUExclusive_preserved:
  assumes "CPUExclusive s" "Next s s'"
  shows "CPUExclusive s'"
proof -
  from assms(2) have
    "(\<exists>pid priority memory deadline. DiscoverProcess s pid priority memory deadline s') \<or>
     (\<exists>pid. TerminateProcess s pid s') \<or>
     (\<exists>cpu. ScheduleProcess s cpu s') \<or>
     TickTime s s'"
    by (auto simp: Next_def)
  
  then show ?thesis
  proof (elim disjE)
    (* Case 1: DiscoverProcess *)
    assume "\<exists>pid priority memory deadline. DiscoverProcess s pid priority memory deadline s'"
    then obtain pid priority memory deadline where "DiscoverProcess s pid priority memory deadline s'"
      by blast
    then show "CPUExclusive s'"
      unfolding CPUExclusive_def DiscoverProcess_def
      using assms by (simp add: CPUExclusive_def)
  
  next
    (* Case 2: TerminateProcess *)
    assume "\<exists>pid. TerminateProcess s pid s'"
    then obtain pid where "TerminateProcess s pid s'"
      by blast
    then show "CPUExclusive s'"
      unfolding CPUExclusive_def TerminateProcess_def
      using assms by (auto simp: CPUExclusive_def split: if_splits)
  
  next
    (* Case 3: TickTime *)
    assume "TickTime s s'"
    then show "CPUExclusive s'"
      unfolding CPUExclusive_def TickTime_def
      using assms by (simp add: CPUExclusive_def)
  
  next
    (* Case 4: ScheduleProcess - COMPLETED *)
    assume "\<exists>cpu. ScheduleProcess s cpu s'"
    then obtain cpu where sched: "ScheduleProcess s cpu s'"
      by blast
    
    from sched obtain pid where
      cpu_none: "cpu_assignment s cpu = None"
      and queue_ne: "ready_queue s \<noteq> []"
      and pid_def: "pid = hd (ready_queue s)"
      and cpu_assignment': "cpu_assignment s' = (cpu_assignment s)(cpu := Some pid)"
      and ready_queue': "ready_queue s' = tl (ready_queue s)"
      and processes_eq: "processes s' = processes s"
      and TypeOK_s': "TypeOK s'"
      by (auto simp: ScheduleProcess_def)
    
    show "CPUExclusive s'"
      unfolding CPUExclusive_def
    proof (intro allI impI)
      fix cpu1 cpu2
      assume cond: "cpu1 \<noteq> cpu2 \<and> cpu_assignment s' cpu1 \<noteq> None \<and> cpu_assignment s' cpu2 \<noteq> None"
      
      from cond obtain p1 where assign1: "cpu_assignment s' cpu1 = Some p1"
        by auto
      from cond obtain p2 where assign2: "cpu_assignment s' cpu2 = Some p2"
        by auto
      from cond have cpu1_ne_cpu2: "cpu1 \<noteq> cpu2"
        by simp
      
      show "the (cpu_assignment s' cpu1) \<noteq> the (cpu_assignment s' cpu2)"
      proof (cases "cpu1 = cpu")
        case True
        then have p1_eq: "p1 = pid"
          using assign1 cpu_assignment' by auto
        
        show ?thesis
        proof (cases "cpu2 = cpu")
          case True
          with \<open>cpu1 = cpu\<close> cpu1_ne_cpu2 show ?thesis
            by auto
        next
          case False
          then have assign2_old: "cpu_assignment s cpu2 = Some p2"
            using assign2 cpu_assignment' by auto
          
          show ?thesis
          proof (cases "pid = p2")
            case True
            (* Contradiction case - already works *)
            have "the (cpu_assignment s' cpu1) = pid"
              using assign1 p1_eq by simp
            have "the (cpu_assignment s' cpu2) = pid"  
              using assign2 True by simp
            show ?thesis
              using \<open>the (cpu_assignment s' cpu1) = pid\<close> \<open>the (cpu_assignment s' cpu2) = pid\<close> using False ScheduleProcess_def assign2_old pid_def sched by force
          next
            case False
            (* Direct case: p1 = pid \<noteq> p2 *)
            show ?thesis
              unfolding \<open>p1 = pid\<close>
              using False assign1 assign2  using p1_eq by auto
          qed
        qed
        
      next
        case False
        then have assign1_old: "cpu_assignment s cpu1 = Some p1"
          using assign1 cpu_assignment' by auto
        
        show ?thesis
        proof (cases "cpu2 = cpu")
          case True
          then have p2_eq: "p2 = pid"
            using assign2 cpu_assignment' by auto
          
          show ?thesis
          proof (cases "p1 = pid")
            case True
            (* Contradiction case - symmetric *)
            have "the (cpu_assignment s' cpu1) = pid"
              using assign1 True by simp
            have "the (cpu_assignment s' cpu2) = pid"
              using assign2 p2_eq by simp
            show ?thesis
              using \<open>the (cpu_assignment s' cpu1) = pid\<close> \<open>the (cpu_assignment s' cpu2) = pid\<close>  using False ScheduleProcess_def assign1_old pid_def sched by auto
          next
            case False
            (* Direct case: p1 \<noteq> pid = p2 *)
            show ?thesis
              unfolding p2_eq
              using False assign1 assign2 by (simp add: p2_eq)
          qed
          
        next
          case False
          then have assign2_old: "cpu_assignment s cpu2 = Some p2"
            using assign2 cpu_assignment' by auto
          
          (* Both CPUs are unchanged from state s - use the original invariant *)
          show ?thesis
            using assms(1) cpu1_ne_cpu2 assign1_old assign2_old
            unfolding CPUExclusive_def           
          using assign1 assign2 by force
        qed
      qed
    qed
  qed
qed

(**)


(* ДИАГНОСТИЧЕСКАЯ ЛЕММА - проверим, что действительно не так *)
lemma debug_DiscoverProcess_NoSimultaneousExecution:
  assumes "NoSimultaneousExecution s" "TypeOK s"
  assumes "DiscoverProcess s pid priority memory deadline s'"
  assumes "cpu_assignment s' cpu = Some pid'" 
  assumes "pid' \<in> set (ready_queue s')"
  shows False
proof -
  from assms(3) have
    cpu_assignment_eq: "cpu_assignment s' = cpu_assignment s"
    and ready_queue_eq: "ready_queue s' = ready_queue s @ [pid]"
    and pid_not_in_processes: "pid |\<notin>| processes s"
    unfolding DiscoverProcess_def by auto

  from assms(4) cpu_assignment_eq have "cpu_assignment s cpu = Some pid'"
    by simp

  from assms(5) ready_queue_eq have "pid' \<in> set (ready_queue s) \<or> pid' = pid"
    by auto

  thus False
  proof
    assume "pid' \<in> set (ready_queue s)"
    with assms(1) \<open>cpu_assignment s cpu = Some pid'\<close> show False
      unfolding NoSimultaneousExecution_def by blast
  next
    assume "pid' = pid"
    with \<open>cpu_assignment s cpu = Some pid'\<close> have "cpu_assignment s cpu = Some pid"
      by simp
    
    (* АГА! Вот где проблема! *)
    (* По TypeOK: если процесс назначен на CPU, он должен быть в processes *)
    from assms(2) have "\<forall>cpu. cpu_assignment s cpu \<noteq> None \<longrightarrow> the (cpu_assignment s cpu) |\<in>| processes s"
      unfolding TypeOK_def by simp
    
    with \<open>cpu_assignment s cpu = Some pid\<close> have "pid |\<in>| processes s"
      by auto
    
    (* ПРОТИВОРЕЧИЕ: pid \<notin> processes s по DiscoverProcess, но pid \<in> processes s по TypeOK *)
    with pid_not_in_processes show False by simp
  qed
qed

(*-- *)
lemma ScheduleProcess_removes_head:
  assumes "ScheduleProcess s cpu s'"
  shows "ready_queue s' = tl (ready_queue s)"
  using assms by (auto simp: ScheduleProcess_def)

lemma ScheduleProcess_assigns_head:
  assumes "ScheduleProcess s cpu s'"
  shows "cpu_assignment s' cpu = Some (hd (ready_queue s))"
  using assms by (auto simp: ScheduleProcess_def)

lemma ScheduleProcess_preserves_other_CPUs:
  assumes "ScheduleProcess s cpu s'" "cpu' \<noteq> cpu"
  shows "cpu_assignment s' cpu' = cpu_assignment s cpu'"
  using assms by (auto simp: ScheduleProcess_def)


(* 3. Докажем сохранение NoSimultaneousExecution только для ScheduleProcess *)

lemma ScheduleProcess_preserves_NoSimultaneousExecution:
  assumes "NoSimultaneousExecution s" "TypeOK s" 
  assumes "ScheduleProcess s cpu s'"
  shows "NoSimultaneousExecution s'"
proof -
  from assms(3) obtain pid where
    queue_ne: "ready_queue s \<noteq> []"
    and pid_def: "pid = hd (ready_queue s)"
    and cpu_assignment': "cpu_assignment s' = (cpu_assignment s)(cpu := Some pid)"
    and ready_queue': "ready_queue s' = tl (ready_queue s)"
    by (auto simp: ScheduleProcess_def)
  
  (* Используем инвариант отсутствия дубликатов *)
  from assms(2) have "NoDuplicatesReadyQueue s"
    unfolding TypeOK_def by simp
  hence distinct_ready: "distinct (ready_queue s)"
    unfolding NoDuplicatesReadyQueue_def by simp
  
  show ?thesis
    unfolding NoSimultaneousExecution_def
  proof (intro allI impI)
    fix pid'
    assume "\<exists>cpu'. cpu_assignment s' cpu' = Some pid'"
    then obtain cpu' where assign': "cpu_assignment s' cpu' = Some pid'"
      by auto
    
    show "pid' \<notin> set (ready_queue s')"
    proof (cases "cpu' = cpu")
      case True
      with assign' cpu_assignment' have "pid' = pid" by simp
      show "pid' \<notin> set (ready_queue s')"
        unfolding ready_queue' `pid' = pid`
      proof
        assume "pid \<in> set (tl (ready_queue s))"
        (* Так как список без дубликатов, голова не может быть в хвосте *)
        with distinct_ready pid_def queue_ne show False
          by (metis distinct.simps(2) hd_Cons_tl list.set_sel(1))
      qed
      
    next
      case False
      with assign' cpu_assignment' have assign_old: "cpu_assignment s cpu' = Some pid'"
        by simp
      with assms(1) have "pid' \<notin> set (ready_queue s)"
        unfolding NoSimultaneousExecution_def by blast
      with ready_queue' show ?thesis
      by (metis list.set_sel(2) queue_ne)
    qed
  qed
qed

(*--*)
lemma NoSimultaneousExecution_preserved:
  assumes "NoSimultaneousExecution s" "TypeOK s" "Next s s'"
  shows "NoSimultaneousExecution s'"
proof -
  have cases: 
    "(\<exists>pid priority memory deadline. DiscoverProcess s pid priority memory deadline s') \<or>
     (\<exists>pid. TerminateProcess s pid s') \<or>
     (\<exists>cpu. ScheduleProcess s cpu s') \<or>
     TickTime s s'"
    using assms(3) by (auto simp: Next_def)

  consider 
    (discover) pid priority memory deadline where "DiscoverProcess s pid priority memory deadline s'"
  | (terminate) pid where "TerminateProcess s pid s'"  
  | (schedule) cpu where "ScheduleProcess s cpu s'"
  | (tick) "TickTime s s'"
    using cases by auto

  then show ?thesis
  proof cases
    case (discover pid priority memory deadline)
    show ?thesis
      unfolding NoSimultaneousExecution_def
    proof (intro allI impI)
      fix pid'
      assume "\<exists>cpu. cpu_assignment s' cpu = Some pid'"
      then obtain cpu where assign': "cpu_assignment s' cpu = Some pid'"
        by auto
      
      from discover have
        cpu_assignment_eq: "cpu_assignment s' = cpu_assignment s"
        and ready_queue_eq: "ready_queue s' = ready_queue s @ [pid]"
        and pid_not_in_processes: "pid |\<notin>| processes s"
        unfolding DiscoverProcess_def by auto

      from assign' cpu_assignment_eq have assign_s: "cpu_assignment s cpu = Some pid'"
        by simp

      from assms(1) assign_s have not_in_ready_s: "pid' \<notin> set (ready_queue s)"
        unfolding NoSimultaneousExecution_def by blast

      show "pid' \<notin> set (ready_queue s')"
        unfolding ready_queue_eq
      proof
        assume "pid' \<in> set (ready_queue s @ [pid])"
        hence "pid' \<in> set (ready_queue s) \<or> pid' = pid" by auto
        thus False
        proof
          assume "pid' \<in> set (ready_queue s)"
          with not_in_ready_s show False by simp
        next
          assume "pid' = pid"
          with assign_s have "cpu_assignment s cpu = Some pid" by simp
          from assms(2) have "\<forall>cpu. cpu_assignment s cpu \<noteq> None \<longrightarrow> the (cpu_assignment s cpu) |\<in>| processes s"
            unfolding TypeOK_def by simp
          with \<open>cpu_assignment s cpu = Some pid\<close> have "pid |\<in>| processes s"
            by auto
          with pid_not_in_processes show False by simp
        qed
      qed
    qed

  next
    case (terminate pid)
    show ?thesis
      unfolding NoSimultaneousExecution_def
    proof (intro allI impI)
      fix pid'
      assume "\<exists>cpu. cpu_assignment s' cpu = Some pid'"
      then obtain cpu where assign': "cpu_assignment s' cpu = Some pid'"
        by auto
      
      show "pid' \<notin> set (ready_queue s')"
        using terminate assign' assms(1)
        unfolding NoSimultaneousExecution_def TerminateProcess_def
        by (auto split: if_splits)
    qed

  next
    case (schedule cpu)
    then obtain pid where
      cpu_none: "cpu_assignment s cpu = None"
      and queue_ne: "ready_queue s \<noteq> []"
      and pid_def: "pid = hd (ready_queue s)"
      and not_on_other_cpus: "\<forall>other_cpu. other_cpu \<noteq> cpu \<longrightarrow> cpu_assignment s other_cpu \<noteq> Some pid"
      and cpu_assignment': "cpu_assignment s' = (cpu_assignment s)(cpu := Some pid)"
      and ready_queue': "ready_queue s' = tl (ready_queue s)"
      and processes_eq: "processes s' = processes s"
      and TypeOK_s': "TypeOK s'"
      by (auto simp: ScheduleProcess_def)
    
    show ?thesis
      unfolding NoSimultaneousExecution_def
    proof (intro allI impI)
      fix pid'
      assume "\<exists>cpu. cpu_assignment s' cpu = Some pid'"
      then obtain cpu' where assign': "cpu_assignment s' cpu' = Some pid'"
        by auto
      
      show "pid' \<notin> set (ready_queue s')"
      proof (cases "cpu' = cpu")
        case True
        with assign' cpu_assignment' have "pid' = pid" by simp
        show "pid' \<notin> set (ready_queue s')"
        proof
          assume "pid' \<in> set (ready_queue s')"
          hence "pid' \<in> set (tl (ready_queue s))"
            by (simp add: ready_queue')
          with \<open>pid' = pid\<close> have "pid \<in> set (tl (ready_queue s))"
            by simp
          with pid_def queue_ne show False
          using ScheduleProcess_def TypeOK_def assms(2) head_not_in_tail_after_schedule schedule by auto
        qed
      next
        case False
        with assign' cpu_assignment' have assign_old: "cpu_assignment s cpu' = Some pid'"
          by simp
        
        show "pid' \<notin> set (ready_queue s')"
        proof (cases "pid' = pid")
          case True
          with assign_old have "cpu_assignment s cpu' = Some pid" by simp
          with not_on_other_cpus False show ?thesis
            by auto
        next
          case False
          from assms(1) assign_old have "pid' \<notin> set (ready_queue s)"
            unfolding NoSimultaneousExecution_def by blast
          with ready_queue' show ?thesis
          by (metis list.set_sel(2) queue_ne)
        qed
      qed
    qed

  next
    case tick
    show ?thesis
      unfolding NoSimultaneousExecution_def TickTime_def
      using assms using NoSimultaneousExecution_def TickTime_def tick by auto
  qed
qed

(**)

lemma DeadlinesValid_preserved:
  assumes "DeadlinesValid s" "TypeOK s" "Next s s'"
  shows "DeadlinesValid s'"
proof -
  have cases: 
    "(\<exists>pid priority memory deadline. DiscoverProcess s pid priority memory deadline s') \<or>
     (\<exists>pid. TerminateProcess s pid s') \<or>
     (\<exists>cpu. ScheduleProcess s cpu s') \<or>
     TickTime s s'"
    using assms(3) by (auto simp: Next_def)

  consider 
    (discover) pid priority memory deadline where "DiscoverProcess s pid priority memory deadline s'"
  | (terminate) pid where "TerminateProcess s pid s'"  
  | (schedule) cpu where "ScheduleProcess s cpu s'"
  | (tick) "TickTime s s'"
    using cases by auto

  then show ?thesis
  proof cases
    case (discover pid priority memory deadline)
    show ?thesis
      unfolding DeadlinesValid_def DiscoverProcess_def
      using assms discover
      using DeadlinesValid_def using DiscoverProcess_def by auto

  next
    case (terminate pid)
    show ?thesis
      unfolding DeadlinesValid_def TerminateProcess_def
      using assms terminate
      using  DeadlinesValid_def  using TypeOK_def TypeOK_preserved by blast

  next
    case (schedule cpu)
    show ?thesis
      unfolding DeadlinesValid_def ScheduleProcess_def
      using assms DeadlinesValid_def using ScheduleProcess_def schedule by auto

  next
    case tick
    show ?thesis
      unfolding DeadlinesValid_def TickTime_def
      using assms tick
      using DeadlinesValid_def using TickTime_def TypeOK_def by blast
  qed
qed

(*--*)
lemma ProcessCountBounded_preserved:
  assumes "ProcessCountBounded s" "TypeOK s" "Next s s'"
  shows "ProcessCountBounded s'"
proof -
  have cases: 
    "(\<exists>pid priority memory deadline. DiscoverProcess s pid priority memory deadline s') \<or>
     (\<exists>pid. TerminateProcess s pid s') \<or>
     (\<exists>cpu. ScheduleProcess s cpu s') \<or>
     TickTime s s'"
    using assms(3) by (auto simp: Next_def)

  consider 
    (discover) pid priority memory deadline where "DiscoverProcess s pid priority memory deadline s'"
  | (terminate) pid where "TerminateProcess s pid s'"  
  | (schedule) cpu where "ScheduleProcess s cpu s'"
  | (tick) "TickTime s s'"
    using cases by auto

  then show ?thesis
  proof cases
    case (discover pid priority memory deadline)
    show ?thesis
      unfolding ProcessCountBounded_def DiscoverProcess_def
      using assms discover
      using ProcessCountBounded_def fcard_finsert_if using TypeOK_def TypeOK_preserved by blast

  next
    case (terminate pid)
    show ?thesis
      unfolding ProcessCountBounded_def TerminateProcess_def
      using assms terminate
      using  ProcessCountBounded_def  using TypeOK_def TypeOK_preserved by blast

  next
    case (schedule cpu)
    show ?thesis
      unfolding ProcessCountBounded_def ScheduleProcess_def
      using assms ProcessCountBounded_def  using TypeOK_def TypeOK_preserved by blast

  next
    case tick
    show ?thesis
      unfolding ProcessCountBounded_def TickTime_def
      using assms ProcessCountBounded_def  using TypeOK_def TypeOK_preserved by blast
  qed
qed

(**)
  (* Основная теорема безопасности *)
(**)
theorem safety_invariant:
  assumes "Init s0" "Reachable s0 s"
  shows 
    "TypeOK s \<and>
     PrioritiesInBounds s \<and>
     MemoryBounded s \<and>
     CPUExclusive s \<and>
     NoSimultaneousExecution s \<and>
     DeadlinesValid s \<and>
     ProcessCountBounded s"
  using assms(2,1)
proof (induction rule: Reachable.induct)
  case (reachable_init s)
  then show ?case 
    by (auto intro: Init_implies_TypeOK Init_implies_PrioritiesInBounds
                   Init_implies_MemoryBounded Init_implies_CPUExclusive
                   Init_implies_NoSimultaneousExecution Init_implies_DeadlinesValid
                   Init_implies_ProcessCountBounded)
next
  case (reachable_step s0 s s')
  then have inv_s:
    "TypeOK s" "PrioritiesInBounds s" "MemoryBounded s" "CPUExclusive s"
    "NoSimultaneousExecution s" "DeadlinesValid s" "ProcessCountBounded s"
    by auto

  have "TypeOK s'" by (rule TypeOK_preserved[OF inv_s(1) \<open>Next s s'\<close>])
  have "PrioritiesInBounds s'" by (rule PrioritiesInBounds_preserved[OF inv_s(2) \<open>Next s s'\<close>])
  have "MemoryBounded s'" by (rule MemoryBounded_preserved[OF inv_s(3) \<open>Next s s'\<close>])
  have "CPUExclusive s'" by (rule CPUExclusive_preserved[OF inv_s(4) \<open>Next s s'\<close>])
  have "NoSimultaneousExecution s'"   using NoSimultaneousExecution_preserved inv_s(1,5) reachable_step.hyps(2) by blast
  have "DeadlinesValid s'" using DeadlinesValid_preserved inv_s(1,6) reachable_step.hyps(2) by blast
  have "ProcessCountBounded s'"  using ProcessCountBounded_preserved inv_s(1,7) reachable_step.hyps(2) by blast

  show ?case
    using \<open>TypeOK s'\<close> \<open>PrioritiesInBounds s'\<close> \<open>MemoryBounded s'\<close>
          \<open>CPUExclusive s'\<close> \<open>NoSimultaneousExecution s'\<close> 
          \<open>DeadlinesValid s'\<close> \<open>ProcessCountBounded s'\<close>
    by blast
qed



end