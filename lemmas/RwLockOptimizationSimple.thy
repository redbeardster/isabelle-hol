theory RwLockOptimizationSimple
  imports Main "HOL-Library.FSet"
begin

(* Конкретные значения для констант *)
definition MIN_PRIORITY :: int where "MIN_PRIORITY = 0"
definition MAX_PRIORITY :: int where "MAX_PRIORITY = 100"
definition MAX_PROCESSES :: nat where "MAX_PROCESSES = 10"

(* Типы *)
typedecl ProcessId
typedecl OperationType
typedecl LockType

(* Конкретные значения для операций и блокировок *)
consts
  adjust_read :: LockType
  adjust_write :: LockType  
  cleanup_read :: LockType
  cleanup_write :: LockType
  check_lock :: LockType
  
  adjust_op :: OperationType
  cleanup_op :: OperationType
  discover_op :: OperationType
  check_op :: OperationType

axiomatization where
  distinct_lock_types: "distinct [adjust_read, adjust_write, cleanup_read, cleanup_write, check_lock]" and 
  distinct_op_types: "distinct [adjust_op, cleanup_op, discover_op, check_op]"

(* Множество всех ProcessId *)
consts Pids :: "ProcessId set"
axiomatization where Pids_nonempty: "Pids \<noteq> {}"

(* Состояние системы *)
record State =
  priorities :: "ProcessId \<Rightarrow> int"
  lock_holders :: "LockType fset"
  in_syscall :: "OperationType fset" 
  completed :: "OperationType fset"

(* Предикат корректности типов *)
definition TypeOK :: "State \<Rightarrow> bool" where
  "TypeOK s \<equiv> 
    (\<forall>pid \<in> Pids. let p = priorities s pid in MIN_PRIORITY \<le> p \<and> p \<le> MAX_PRIORITY) \<and>
    (\<forall>l. l |\<in>| lock_holders s \<longrightarrow> l \<in> {adjust_read, adjust_write, cleanup_read, cleanup_write, check_lock}) \<and>
    (\<forall>op. op |\<in>| in_syscall s \<longrightarrow> op \<in> {adjust_op, cleanup_op, discover_op}) \<and>
    (\<forall>op. op |\<in>| completed s \<longrightarrow> op \<in> {adjust_op, cleanup_op, discover_op, check_op})"

(* Начальное состояние *)
definition Init :: "State \<Rightarrow> bool" where
  "Init s \<equiv> 
    (\<forall>pid \<in> Pids. priorities s pid = 50) \<and>
    lock_holders s = {||} \<and>
    in_syscall s = {||} \<and>  
    completed s = {||} \<and>
    TypeOK s"

(* Оптимизированная операция adjust_priorities *)

definition AdjustPriorities_Read :: "State \<Rightarrow> State \<Rightarrow> bool" where
  "AdjustPriorities_Read s s' \<equiv>
    \<not> adjust_op |\<in>| completed s \<and>
    \<not> adjust_read |\<in>| lock_holders s \<and>
    \<not> adjust_write |\<in>| lock_holders s \<and>
    \<not> cleanup_write |\<in>| lock_holders s \<and>
    lock_holders s' = lock_holders s |\<union>| {|adjust_read|} \<and>
    priorities s' = priorities s \<and>
    in_syscall s' = in_syscall s \<and>
    completed s' = completed s \<and>
    TypeOK s'"

definition AdjustPriorities_Syscall :: "State \<Rightarrow> State \<Rightarrow> bool" where  
  "AdjustPriorities_Syscall s s' \<equiv>
    adjust_read |\<in>| lock_holders s \<and>
    lock_holders s' = lock_holders s |-| {|adjust_read|} \<and>
    in_syscall s' = in_syscall s |\<union>| {|adjust_op|} \<and>
    priorities s' = priorities s \<and>
    completed s' = completed s \<and>
    TypeOK s'"

definition AdjustPriorities_Write :: "State \<Rightarrow> State \<Rightarrow> bool" where
  "AdjustPriorities_Write s s' \<equiv>
    adjust_op |\<in>| in_syscall s \<and>
    lock_holders s = {||} \<and>
    in_syscall s' = in_syscall s |-| {|adjust_op|} \<and>
    lock_holders s' = {|adjust_write|} \<and>
    (\<exists>pid \<in> Pids. priorities s pid \<ge> MIN_PRIORITY + 5 \<and> 
          priorities s' = (priorities s)(pid := priorities s pid - 5)) \<and>
    completed s' = completed s \<and>
    TypeOK s'"

definition AdjustPriorities_Complete :: "State \<Rightarrow> State \<Rightarrow> bool" where
  "AdjustPriorities_Complete s s' \<equiv>
    adjust_write |\<in>| lock_holders s \<and>
    lock_holders s' = lock_holders s |-| {|adjust_write|} \<and>
    completed s' = completed s |\<union>| {|adjust_op|} \<and>
    priorities s' = priorities s \<and>
    in_syscall s' = in_syscall s \<and>
    TypeOK s'"

(* Оптимизированная операция cleanup_finished_processes *)

definition Cleanup_Read :: "State \<Rightarrow> State \<Rightarrow> bool" where
  "Cleanup_Read s s' \<equiv>
    \<not> cleanup_op |\<in>| completed s \<and>
    \<not> cleanup_read |\<in>| lock_holders s \<and>
    \<not> cleanup_write |\<in>| lock_holders s \<and>
    \<not> adjust_write |\<in>| lock_holders s \<and>
    lock_holders s' = lock_holders s |\<union>| {|cleanup_read|} \<and>
    priorities s' = priorities s \<and>
    in_syscall s' = in_syscall s \<and>
    completed s' = completed s \<and>
    TypeOK s'"

definition Cleanup_Syscall :: "State \<Rightarrow> State \<Rightarrow> bool" where
  "Cleanup_Syscall s s' \<equiv>
    cleanup_read |\<in>| lock_holders s \<and>
    lock_holders s' = lock_holders s |-| {|cleanup_read|} \<and>
    in_syscall s' = in_syscall s |\<union>| {|cleanup_op|} \<and>
    priorities s' = priorities s \<and>
    completed s' = completed s \<and>
    TypeOK s'"

definition Cleanup_Write :: "State \<Rightarrow> State \<Rightarrow> bool" where
  "Cleanup_Write s s' \<equiv>
    cleanup_op |\<in>| in_syscall s \<and>
    lock_holders s = {||} \<and>
    in_syscall s' = in_syscall s |-| {|cleanup_op|} \<and>
    lock_holders s' = {|cleanup_write|} \<and>
    priorities s' = priorities s \<and>
    completed s' = completed s \<and>
    TypeOK s'"

definition Cleanup_Complete :: "State \<Rightarrow> State \<Rightarrow> bool" where
  "Cleanup_Complete s s' \<equiv>
    cleanup_write |\<in>| lock_holders s \<and>
    lock_holders s' = lock_holders s |-| {|cleanup_write|} \<and>
    completed s' = completed s |\<union>| {|cleanup_op|} \<and>
    priorities s' = priorities s \<and>
    in_syscall s' = in_syscall s \<and>
    TypeOK s'"

(* Операция check (только чтение) *)

definition Check_Read :: "State \<Rightarrow> State \<Rightarrow> bool" where
  "Check_Read s s' \<equiv>
    \<not> check_op |\<in>| completed s \<and>
    \<not> adjust_write |\<in>| lock_holders s \<and>
    \<not> cleanup_write |\<in>| lock_holders s \<and>
    lock_holders s' = lock_holders s |\<union>| {|check_lock|} \<and>
    priorities s' = priorities s \<and>
    in_syscall s' = in_syscall s \<and>
    completed s' = completed s \<and>
    TypeOK s'"

definition Check_Complete :: "State \<Rightarrow> State \<Rightarrow> bool" where
  "Check_Complete s s' \<equiv>
    check_lock |\<in>| lock_holders s \<and>
    lock_holders s' = lock_holders s |-| {|check_lock|} \<and>
    completed s' = completed s |\<union>| {|check_op|} \<and>
    priorities s' = priorities s \<and>
    in_syscall s' = in_syscall s \<and>
    TypeOK s'"

(* Следующее состояние *)
definition Next :: "State \<Rightarrow> State \<Rightarrow> bool" where
  "Next s s' \<equiv>
    AdjustPriorities_Read s s' \<or>
    AdjustPriorities_Syscall s s' \<or>
    AdjustPriorities_Write s s' \<or>
    AdjustPriorities_Complete s s' \<or>
    Cleanup_Read s s' \<or>
    Cleanup_Syscall s s' \<or>
    Cleanup_Write s s' \<or>
    Cleanup_Complete s s' \<or>
    Check_Read s s' \<or>
    Check_Complete s s'"

(* Условие завершения *)
definition Termination :: "State \<Rightarrow> bool" where
  "Termination s \<equiv> 
    completed s = {|adjust_op, cleanup_op, check_op|}"

(* Ключевые инварианты *)

definition PriorityInBounds :: "State \<Rightarrow> bool" where
  "PriorityInBounds s \<equiv> 
    \<forall>pid \<in> Pids. let p = priorities s pid in MIN_PRIORITY \<le> p \<and> p \<le> MAX_PRIORITY"

definition NoSimultaneousWrites :: "State \<Rightarrow> bool" where
  "NoSimultaneousWrites s \<equiv>
    let write_locks = lock_holders s |\<inter>| {|adjust_write, cleanup_write|} in
    fcard write_locks \<le> 1"

definition NoSyscallsUnderWriteLock :: "State \<Rightarrow> bool" where
  "NoSyscallsUnderWriteLock s \<equiv>
    (adjust_op |\<in>| in_syscall s \<longrightarrow> \<not> adjust_write |\<in>| lock_holders s) \<and>
    (cleanup_op |\<in>| in_syscall s \<longrightarrow> \<not> cleanup_write |\<in>| lock_holders s)"

definition WriteIsExclusive :: "State \<Rightarrow> bool" where
  "WriteIsExclusive s \<equiv>
    (adjust_write |\<in>| lock_holders s \<or> cleanup_write |\<in>| lock_holders s) \<longrightarrow>
    fcard (lock_holders s) = 1"

definition MonotonicDecrease :: "State \<Rightarrow> bool" where
  "MonotonicDecrease s \<equiv>
    \<forall>pid \<in> Pids. priorities s pid \<ge> MIN_PRIORITY"

(* Отношение достижимости *)
inductive Reachable :: "State \<Rightarrow> State \<Rightarrow> bool" where
  reachable_init: "Init s \<Longrightarrow> Reachable s s"
| reachable_step: "\<lbrakk> Reachable s0 s; Next s s' \<rbrakk> \<Longrightarrow> Reachable s0 s'"

(* Леммы и утверждения *)

lemma Init_implies_TypeOK:
  "Init s \<Longrightarrow> TypeOK s"
  by (simp add: Init_def)

lemma Init_implies_PriorityInBounds:
  "Init s \<Longrightarrow> PriorityInBounds s"  
  by (auto simp add: Init_def PriorityInBounds_def MIN_PRIORITY_def MAX_PRIORITY_def)

lemma Init_implies_NoSimultaneousWrites:
  "Init s \<Longrightarrow> NoSimultaneousWrites s"
  using Init_def NoSimultaneousWrites_def by (simp add: order.order_iff_strict)

lemma Init_implies_NoSyscallsUnderWriteLock:
  "Init s \<Longrightarrow> NoSyscallsUnderWriteLock s"
  by (simp add: Init_def NoSyscallsUnderWriteLock_def)

lemma Init_implies_WriteIsExclusive:
  "Init s \<Longrightarrow> WriteIsExclusive s"
  by (simp add: Init_def WriteIsExclusive_def)

lemma Init_implies_MonotonicDecrease:
  "Init s \<Longrightarrow> MonotonicDecrease s"
  by (auto simp add: Init_def MonotonicDecrease_def MIN_PRIORITY_def)

(* Базовые леммы о сохранении TypeOK *)
lemma AdjustPriorities_Read_preserves_TypeOK:
  assumes "AdjustPriorities_Read s s'" "TypeOK s"
  shows "TypeOK s'"
  using assms by (auto simp add: AdjustPriorities_Read_def TypeOK_def)

lemma AdjustPriorities_Syscall_preserves_TypeOK:
  assumes "AdjustPriorities_Syscall s s'" "TypeOK s"  
  shows "TypeOK s'"
  using assms by (auto simp add: AdjustPriorities_Syscall_def TypeOK_def)

(* Леммы о порядке операций *)

lemma adjustment_sequence:
  assumes "AdjustPriorities_Read s s1" "AdjustPriorities_Syscall s1 s2" 
          "AdjustPriorities_Write s2 s3" "AdjustPriorities_Complete s3 s4"
  shows "completed s4 = completed s |\<union>| {|adjust_op|}"
  using assms
  by (auto simp: AdjustPriorities_Read_def AdjustPriorities_Syscall_def 
                 AdjustPriorities_Write_def AdjustPriorities_Complete_def)

lemma cleanup_sequence:
  assumes "Cleanup_Read s s1" "Cleanup_Syscall s1 s2"
          "Cleanup_Write s2 s3" "Cleanup_Complete s3 s4"
  shows "completed s4 = completed s |\<union>| {|cleanup_op|}"
  using assms
  by (auto simp: Cleanup_Read_def Cleanup_Syscall_def
                 Cleanup_Write_def Cleanup_Complete_def)



(* Теперь основная теорема *)
theorem termination_correct:
  assumes "Init s0" "Reachable s0 s" "Termination s"
  shows "completed s = {|adjust_op, cleanup_op, check_op|} \<and> lock_holders s = {||}"
proof -
  from assms have "Termination s" by simp
  hence "completed s = {|adjust_op, cleanup_op, check_op|}" 
    by (simp add: Termination_def)
  
  with assms show ?thesis 
    using no_locks_when_all_completed by blast
qed

(* Основной инвариант безопасности *)

theorem safety_invariant:
  assumes init: "Init s0"
  assumes reach: "Reachable s0 s"
  shows 
    "TypeOK s \<and>
     PriorityInBounds s \<and> 
     NoSimultaneousWrites s \<and> 
     NoSyscallsUnderWriteLock s \<and>
     WriteIsExclusive s \<and>
     MonotonicDecrease s"
  using reach
proof (induction rule: Reachable.induct)
  case (reachable_init s)
  then show ?case using init
    by (auto simp: Init_implies_TypeOK Init_implies_PriorityInBounds 
                  Init_implies_NoSimultaneousWrites Init_implies_NoSyscallsUnderWriteLock
                  Init_implies_WriteIsExclusive Init_implies_MonotonicDecrease)
next
  case (reachable_step s0 s s')
  note IH = this
  then have inv_s: 
    "TypeOK s" "PriorityInBounds s" "NoSimultaneousWrites s" 
    "NoSyscallsUnderWriteLock s" "WriteIsExclusive s" "MonotonicDecrease s"
    by auto

  show ?case
  proof -
    have "TypeOK s'" 
      using \<open>Next s s'\<close> inv_s(1)
      by (auto simp: Next_def AdjustPriorities_Read_def AdjustPriorities_Syscall_def
                    AdjustPriorities_Write_def AdjustPriorities_Complete_def
                    Cleanup_Read_def Cleanup_Syscall_def Cleanup_Write_def 
                    Cleanup_Complete_def Check_Read_def Check_Complete_def
                    TypeOK_def)
    
    have "PriorityInBounds s'"
    proof -
      have "\<forall>pid \<in> Pids. priorities s' pid \<ge> MIN_PRIORITY \<and> priorities s' pid \<le> MAX_PRIORITY"
      proof
        fix pid
        assume "pid \<in> Pids"
        show "priorities s' pid \<ge> MIN_PRIORITY \<and> priorities s' pid \<le> MAX_PRIORITY"
        proof (cases "AdjustPriorities_Write s s'")
          case True
          then obtain pid' where 
            pid': "pid' \<in> Pids" "priorities s pid' > MIN_PRIORITY"
            and priorities': "priorities s' = (priorities s)(pid' := priorities s pid' - 5)"
            by (auto simp: AdjustPriorities_Write_def)
          
          show ?thesis
          proof (cases "pid = pid'")
            case True
            then have "priorities s' pid = priorities s pid - 5"
              by (simp add: priorities')
            also have "\<dots> \<ge> MIN_PRIORITY"
              using pid'(2)  by (metis TypeOK_def \<open>TypeOK s'\<close> \<open>pid \<in> Pids\<close> calculation)
            also have "priorities s' pid \<le> MAX_PRIORITY"
              using inv_s \<open>pid \<in> Pids\<close> PriorityInBounds_def
              by (smt (verit) True priorities' fun_upd_apply)
            ultimately show ?thesis by simp
          next
            case False
            then have "priorities s' pid = priorities s pid"
              by (simp add: priorities')
            then show ?thesis
              using inv_s \<open>pid \<in> Pids\<close> PriorityInBounds_def by metis
          qed
        next
          case False
          with \<open>Next s s'\<close> have "priorities s' = priorities s"
            by (auto simp: Next_def AdjustPriorities_Read_def AdjustPriorities_Syscall_def
                          AdjustPriorities_Complete_def Cleanup_Read_def Cleanup_Syscall_def
                          Cleanup_Write_def Cleanup_Complete_def Check_Read_def Check_Complete_def)
          then show ?thesis
            using inv_s \<open>pid \<in> Pids\<close> PriorityInBounds_def by metis
        qed
      qed
      then show ?thesis by (simp add: PriorityInBounds_def)
    qed

   have "NoSimultaneousWrites s'"
    proof -
      have "fcard (lock_holders s' |\<inter>| {|adjust_write, cleanup_write|}) \<le> 1"
      proof (cases "AdjustPriorities_Write s s'")
        case True
        then have "lock_holders s' = {|adjust_write|}"
          by (auto simp: AdjustPriorities_Write_def)
        then show ?thesis  by (simp add: fcard_finsert_disjoint)
      next
        case False
        then show ?thesis
        proof (cases "Cleanup_Write s s'")
          case True
          then have "lock_holders s' = {|cleanup_write|}"
            by (auto simp: Cleanup_Write_def)
          then show ?thesis by (simp add: fcard_finsert_if)
        next
          case False
          then show ?thesis
          proof (cases "AdjustPriorities_Read s s'")
            case True
            then have "lock_holders s' = lock_holders s |\<union>| {|adjust_read|}"
              by (auto simp: AdjustPriorities_Read_def)
            then show ?thesis using inv_s
              using NoSimultaneousWrites_def AdjustPriorities_Read_def   by (metis (no_types, lifting) One_nat_def True fcard_fempty fcard_finsert_disjoint finsert_absorb finsert_iff finter_finsert_right_if1 finter_finsert_right_ifffempty funion_finsert_right
                inf_bot_right nle_le sup_bot.right_neutral)
          next
            case False
            then show ?thesis
            proof (cases "AdjustPriorities_Syscall s s'")
              case True
              then have "lock_holders s' = lock_holders s |-| {|adjust_read|}"
                by (auto simp: AdjustPriorities_Syscall_def)
              then show ?thesis using inv_s
                using NoSimultaneousWrites_def NoSimultaneousWrites_def AdjustPriorities_Read_def 
              by (smt (verit, del_insts) AdjustPriorities_Syscall_def True fcard_finsert_le finsert_fminus finter_finsert_left_if1 finter_finsert_left_ifffempty le_trans)
            next
              case False
              then show ?thesis
              proof (cases "AdjustPriorities_Complete s s'")
                case True
                then have "lock_holders s' = lock_holders s |-| {|adjust_write|}"
                  by (auto simp: AdjustPriorities_Complete_def)
                then show ?thesis using inv_s
                using NoSimultaneousWrites_def NoSimultaneousWrites_def AdjustPriorities_Read_def 
              by (metis (lifting) ext AdjustPriorities_Complete_def True WriteIsExclusive_def fcard_mono finter_lower1 fminus_fsubset inf.absorb_iff2 le_inf_iff)
              next
                case False
                then show ?thesis
                proof (cases "Cleanup_Read s s'")
                  case True
                  then have "lock_holders s' = lock_holders s |\<union>| {|cleanup_read|}"
                    by (auto simp: Cleanup_Read_def)
                  then show ?thesis using inv_s
                   using NoSimultaneousWrites_def NoSimultaneousWrites_def AdjustPriorities_Read_def  AdjustPriorities_Complete_def True WriteIsExclusive_def
                 by (simp add: Cleanup_Read_def fcard_finsert_if finter_finsert_right)
                next
                  case False
                  then show ?thesis
                  proof (cases "Cleanup_Syscall s s'")
                    case True
                    then have "lock_holders s' = lock_holders s |-| {|cleanup_read|}"
                      by (auto simp: Cleanup_Syscall_def)
                    then show ?thesis using inv_s NoSimultaneousWrites_def NoSimultaneousWrites_def AdjustPriorities_Read_def  AdjustPriorities_Complete_def True WriteIsExclusive_def
                    by (smt (verit, ccfv_SIG) Cleanup_Syscall_def dual_order.trans fcard_finsert_le finsert_fminus finter_finsert_left_if1 finter_finsert_left_ifffempty)
                  next
                    case False
                    then show ?thesis
                    proof (cases "Cleanup_Complete s s'")
                      case True
                      then have "lock_holders s' = lock_holders s |-| {|cleanup_write|}"
                        using  Cleanup_Complete_def  NoSimultaneousWrites_def NoSimultaneousWrites_def AdjustPriorities_Read_def  AdjustPriorities_Complete_def True WriteIsExclusive_def 
                      by blast
                      then show ?thesis using inv_s
                        using  Cleanup_Complete_def  NoSimultaneousWrites_def NoSimultaneousWrites_def AdjustPriorities_Read_def  AdjustPriorities_Complete_def True WriteIsExclusive_def 
                    by (simp add: fcard_finsert_if finter_finsert_right less_imp_le_nat)
                    next
                      case False
                      then show ?thesis
                      proof (cases "Check_Read s s'")
                        case True
                        then have "lock_holders s' = lock_holders s |\<union>| {|check_lock|}"
                          by (auto simp: Check_Read_def)
                        then show ?thesis using inv_s
                          using NoSimultaneousWrites_def Check_Read_def  AdjustPriorities_Read_def  AdjustPriorities_Complete_def  
                        by (metis (no_types, opaque_lifting) Check_Read_def One_nat_def True fcard_fempty fcard_finsert fcard_mono fempty_fminus finsert_absorb2 finsert_iff finter_finsert_right_if1
                            finter_finsert_right_ifffempty finter_lower2 funion_finsert_right sup_bot.right_neutral)
                      next
                        case False
                        then show ?thesis
                        proof (cases "Check_Complete s s'")
                          case True
                          then have "lock_holders s' = lock_holders s |-| {|check_lock|}"
                            by (auto simp: Check_Complete_def)
                          then show ?thesis using inv_s
                           NoSimultaneousWrites_def by (smt (verit, ccfv_SIG) fcard_mono finter_lower1 fminus_fsubset inf.orderE le_inf_iff)
                        next
                          case False
                          with \<open>Next s s'\<close> and
                            \<open>\<not> AdjustPriorities_Write s s'\<close> \<open>\<not> Cleanup_Write s s'\<close>
                            \<open>\<not> AdjustPriorities_Read s s'\<close> \<open>\<not> AdjustPriorities_Syscall s s'\<close>
                            \<open>\<not> AdjustPriorities_Complete s s'\<close> \<open>\<not> Cleanup_Read s s'\<close>
                            \<open>\<not> Cleanup_Syscall s s'\<close> \<open>\<not> Cleanup_Complete s s'\<close>
                            \<open>\<not> Check_Read s s'\<close>
                          show ?thesis
                            by (auto simp: Next_def)
                        qed
                      qed
                    qed
                  qed
                qed
              qed
            qed
          qed
        qed
      qed
      then show ?thesis by (simp add: NoSimultaneousWrites_def)
    qed

(*   *)

(*
  have "NoSyscallsUnderWriteLock s'"
    proof -
      have nsul: "(adjust_op |\<in>| in_syscall s' \<longrightarrow> \<not> adjust_write |\<in>| lock_holders s') \<and>
                  (cleanup_op |\<in>| in_syscall s' \<longrightarrow> \<not> cleanup_write |\<in>| lock_holders s')"
        using \<open>Next s s'\<close>
        unfolding Next_def
      proof (elim disjE)
        assume "AdjustPriorities_Read s s'"
        then show ?thesis 
          using AdjustPriorities_Read_def by blast
      next
        assume "AdjustPriorities_Syscall s s'"
        then show ?thesis 
          using AdjustPriorities_Syscall_def by blast
      next
        assume "AdjustPriorities_Write s s'"
        then show ?thesis 
          using AdjustPriorities_Write_def by blast
      next
        assume "AdjustPriorities_Complete s s'"
        then show ?thesis 
          using AdjustPriorities_Complete_def by blast
      next
        assume "Cleanup_Read s s'"
        then show ?thesis 
          using Cleanup_Read_def by blast
      next
        assume "Cleanup_Syscall s s'"
        then show ?thesis 
          using Cleanup_Syscall_def by blast
      next
        assume "Cleanup_Write s s'"
        then show ?thesis 
          using Cleanup_Write_def by blast
      next
        assume "Cleanup_Complete s s'"
        then show ?thesis 
          using Cleanup_Complete_def by blast
      next
        assume "Check_Read s s'"
        then show ?thesis 
          using Check_Read_def by blast
      next
        assume "Check_Complete s s'"
        then show ?thesis 
          using Check_Complete_def by blast
      qed
      then show ?thesis by (simp add: NoSyscallsUnderWriteLock_def)
    qed *)
(*  --  *)

(*     have "WriteIsExclusive s'"
    proof -
      from \<open>Next s s'\<close> 
      have "(adjust_write |\<in>| lock_holders s' \<or> cleanup_write |\<in>| lock_holders s') \<longrightarrow>
            fcard (lock_holders s') = 1"
        unfolding Next_def WriteIsExclusive_def
                AdjustPriorities_Read_def AdjustPriorities_Syscall_def
                AdjustPriorities_Write_def AdjustPriorities_Complete_def
                Cleanup_Read_def Cleanup_Syscall_def Cleanup_Write_def
                Cleanup_Complete_def Check_Read_def Check_Complete_def
        by blast
      then show ?thesis by (simp add: WriteIsExclusive_def)
    qed
 *)
(*   *)
(* 
   have "MonotonicDecrease s'"
    proof -
      have "\<forall>pid \<in> Pids. priorities s' pid \<ge> MIN_PRIORITY"
      proof
        fix pid
        assume "pid \<in> Pids"
        show "priorities s' pid \<ge> MIN_PRIORITY"
        proof (cases "AdjustPriorities_Write s s'")
          case True
          then obtain pid' where 
            pid': "pid' \<in> Pids" "priorities s pid' > MIN_PRIORITY"
            and priorities': "priorities s' = (priorities s)(pid' := priorities s pid' - 5)"
            by (auto simp: AdjustPriorities_Write_def)
          
          show ?thesis
          proof (cases "pid = pid'")
            case True
            then have "priorities s' pid = priorities s pid - 5"
              by (simp add: priorities')
            then show ?thesis 
              using pid'(2) by (metis PriorityInBounds_def \<open>PriorityInBounds s'\<close> \<open>pid \<in> Pids\<close>)
          next
            case False
            then have "priorities s' pid = priorities s pid"
              by (simp add: priorities')
            then show ?thesis
              using inv_s \<open>pid \<in> Pids\<close> MonotonicDecrease_def by auto
          qed
        next
          case False
          with \<open>Next s s'\<close> have "priorities s' = priorities s"
            by (auto simp: Next_def AdjustPriorities_Read_def AdjustPriorities_Syscall_def
                          AdjustPriorities_Complete_def Cleanup_Read_def Cleanup_Syscall_def
                          Cleanup_Write_def Cleanup_Complete_def Check_Read_def Check_Complete_def)
          then show ?thesis
            using inv_s \<open>pid \<in> Pids\<close> MonotonicDecrease_def by auto
        qed
      qed
      then show ?thesis by (simp add: MonotonicDecrease_def)
    qed

    show ?thesis
      using \<open>TypeOK s'\<close> \<open>PriorityInBounds s'\<close> \<open>NoSimultaneousWrites s'\<close>
            \<open>NoSyscallsUnderWriteLock s'\<close> \<open>WriteIsExclusive s'\<close> \<open>MonotonicDecrease s'\<close>
      sorry

  qed

qed
*)  
  
(* Ключевое свойство оптимизации - системные вызовы без write-блокировок *)

lemma syscalls_without_own_write_locks:
  assumes "AdjustPriorities_Syscall s s'" "TypeOK s"
  shows "adjust_op |\<in>| in_syscall s' \<and> \<not> adjust_write |\<in>| lock_holders s'"
  using assms
  using AdjustPriorities_Syscall_def sorry

(* lemma cleanup_syscalls_without_own_write_locks:  
  assumes "Cleanup_Syscall s s'" "TypeOK s"
  shows "cleanup_op |\<in>| in_syscall s' \<and> \<not> cleanup_write |\<in>| lock_holders s'"
  using assms
  using Next_def AdjustPriorities_Read_def AdjustPriorities_Syscall_def
                          AdjustPriorities_Complete_def Cleanup_Read_def Cleanup_Syscall_def
                          Cleanup_Write_def Cleanup_Complete_def Check_Read_def Check_Complete_def by metis
 *)

lemma cleanup_syscalls_without_own_write_locks:  
  assumes "Cleanup_Syscall s s'" "TypeOK s"
  shows "cleanup_op |\<in>| in_syscall s' \<and> \<not> cleanup_write |\<in>| lock_holders s'"
proof -
  from assms have 
    "cleanup_read |\<in>| lock_holders s" and
    "lock_holders s' = lock_holders s |-| {|cleanup_read|}" and
    "in_syscall s' = in_syscall s |\<union>| {|cleanup_op|}"
    by (auto simp: Cleanup_Syscall_def)
  then show ?thesis sorry
qed


(* Теорема о ключевом свойстве оптимизации *)
theorem no_syscalls_under_own_write_lock:
  assumes "Init s0" "Reachable s0 s"
  shows "NoSyscallsUnderWriteLock s"
  using assms
proof (induction rule: Reachable.induct)
  case (reachable_init s)
  then show ?case 
    using Init_implies_NoSyscallsUnderWriteLock sorry
next
  case (reachable_step s0 s s')
  then have "NoSyscallsUnderWriteLock s" by blast
  show ?case
  proof -
    have "(adjust_op |\<in>| in_syscall s' \<longrightarrow> \<not> adjust_write |\<in>| lock_holders s') \<and>
          (cleanup_op |\<in>| in_syscall s' \<longrightarrow> \<not> cleanup_write |\<in>| lock_holders s')"
      using \<open>Next s s'\<close> \<open>NoSyscallsUnderWriteLock s\<close>
      unfolding Next_def NoSyscallsUnderWriteLock_def
    proof (elim disjE)
      assume "AdjustPriorities_Read s s'"
      then show ?thesis unfolding AdjustPriorities_Read_def by simp
    next
      assume "AdjustPriorities_Syscall s s'"
      then show ?thesis unfolding AdjustPriorities_Syscall_def by simp
    next
      assume "AdjustPriorities_Write s s'"
      then show ?thesis unfolding AdjustPriorities_Write_def by simp
    next
      assume "AdjustPriorities_Complete s s'"
      then show ?thesis unfolding AdjustPriorities_Complete_def by simp
    next
      assume "Cleanup_Read s s'"
      then show ?thesis unfolding Cleanup_Read_def by simp
    next
      assume "Cleanup_Syscall s s'"
      then show ?thesis unfolding Cleanup_Syscall_def by simp
    next
      assume "Cleanup_Write s s'"
      then show ?thesis unfolding Cleanup_Write_def by simp
    next
      assume "Cleanup_Complete s s'"
      then show ?thesis unfolding Cleanup_Complete_def by simp
    next
      assume "Check_Read s s'"
      then show ?thesis unfolding Check_Read_def by simp
    next
      assume "Check_Complete s s'"
      then show ?thesis unfolding Check_Complete_def by simp
    qed
    then show ?thesis by (simp add: NoSyscallsUnderWriteLock_def)
  qed
qed


(* Свойства взаимного исключения *)
(* theorem mutual_exclusion:
  assumes "Init s0" "Reachable s0 s"
  shows "\<not> (adjust_write |\<in>| lock_holders s \<and> cleanup_write |\<in>| lock_holders s)"
  using assms safety_invariant
  by (auto simp: NoSimultaneousWrites_def)
 *)

(* theorem termination_correct:
  assumes "Init s0" "Reachable s0 s" "Termination s"
  shows "completed s = {|adjust_op, cleanup_op, check_op|} \<and> lock_holders s = {||}"
  sorry
 *)


(* Лемма: если все операции завершены, то нет активных блокировок *)
lemma no_locks_when_all_completed:
  assumes "Init s0" "Reachable s0 s"
  assumes "completed s = {|adjust_op, cleanup_op, check_op|}"
  shows "lock_holders s = {||}"
proof -
  from assms have "TypeOK s" by sledgehammer
  
  (* Проверяем, что ни одна операция не может держать блокировки при завершении *)
  show ?thesis
  proof (rule ccontr)
    assume "lock_holders s \<noteq> {||}"
    then obtain lock where "lock |\<in>| lock_holders s" by auto
    
    (* Анализируем возможные блокировки *)
    from \<open>TypeOK s\<close> have 
      "lock \<in> {adjust_read, adjust_write, cleanup_read, cleanup_write, check_lock}"
      by (auto simp: TypeOK_def)
    
    then consider 
        (adjust_read) "lock = adjust_read" 
      | (adjust_write) "lock = adjust_write"
      | (cleanup_read) "lock = cleanup_read" 
      | (cleanup_write) "lock = cleanup_write"
      | (check) "lock = check_lock" by auto
    
    then show False
    proof cases
      case adjust_read
      (* adjust_read означает, что adjust ещё не завершён *)
      with \<open>completed s = {|adjust_op, cleanup_op, check_op|}\<close> 
      show ?thesis by (auto simp: AdjustPriorities_Read_def)
    next
      case adjust_write
      (* adjust_write означает, что adjust ещё не завершён *)  
      with \<open>completed s = {|adjust_op, cleanup_op, check_op|}\<close>
      show ?thesis by (auto simp: AdjustPriorities_Write_def)
    next
      case cleanup_read
      (* cleanup_read означает, что cleanup ещё не завершён *)
      with \<open>completed s = {|adjust_op, cleanup_op, check_op|}\<close>
      show ?thesis by (auto simp: Cleanup_Read_def)
    next  
      case cleanup_write
      (* cleanup_write означает, что cleanup ещё не завершён *)
      with \<open>completed s = {|adjust_op, cleanup_op, check_op|}\<close>
      show ?thesis by (auto simp: Cleanup_Write_def)
    next
      case check
      (* check_lock означает, что check ещё не завершён *)
      with \<open>completed s = {|adjust_op, cleanup_op, check_op|}\<close>
      show ?thesis by (auto simp: Check_Read_def)
    qed
  qed
qed




end