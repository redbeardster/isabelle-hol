theory ConcurrencySpecification
imports Main  "HOL-Library.Multiset" 
begin

(* Определяем недостающие типы *)
type_synonym location = string
type_synonym val = nat  (* Изменили value на val *)
type_synonym channel = string
type_synonym message = string
type_synonym id = nat

(* Базовые процессы *)
datatype Action = 
    Read location 
  | Write location val  (* Используем val вместо value *)
  | Compute
  | Sync channel message

type_synonym Process = "Action list"

(* Функция чередования *)
fun interleave :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list set" where
  "interleave [] ys = {ys}"
| "interleave xs [] = {xs}"  
| "interleave (x#xs) (y#ys) = 
    {x # z | z. z \<in> interleave xs (y#ys)} \<union> 
    {y # z | z. z \<in> interleave (x#xs) ys}"

(* Параллельная композиция *)
definition parallel_composition :: "Process \<Rightarrow> Process \<Rightarrow> Process set" (infix "\<parallel>" 65) where
  "P \<parallel> Q = interleave P Q"

(* Состояния системы *)
type_synonym State = "(location \<Rightarrow> val) \<times> (channel \<Rightarrow> message list)"  (* Используем val *)

(* Прогресс процесса *)
definition can_progress :: "Process \<Rightarrow> State \<Rightarrow> bool" where
  "can_progress P s \<equiv> P \<noteq> []"

(* Свойства параллельных систем *)
definition deadlock_free :: "Process \<Rightarrow> bool" where
  "deadlock_free P \<equiv> \<forall>s. can_progress P s"

(* Для race condition нам нужно определить семантику выполнения *)
type_synonym Execution = "(State \<times> Action) list"

definition consistent_memory_view :: "Execution \<Rightarrow> location \<Rightarrow> bool" where
  "consistent_memory_view exec loc \<equiv> 
    \<forall>i j. i < j \<and> j < length exec \<longrightarrow> 
      (let (s_i, a_i) = exec!i; (s_j, a_j) = exec!j in
       case (a_i, a_j) of
         (Write loc1 v1, Read loc2) \<Rightarrow> loc1 = loc2 \<and> loc1 = loc \<longrightarrow> 
           (let (mem_i, _) = s_i; (mem_j, _) = s_j in
            mem_i loc1 = mem_j loc2)
       | _ \<Rightarrow> True)"



(* fun valid_execution :: "Process \<Rightarrow> Execution \<Rightarrow> bool" where
  "valid_execution [] [] = True"
| "valid_execution (a # P') ((s, a') # exec) = (a = a' \<and> valid_execution P' exec)"
| "valid_execution _ _ = False"
 *)


inductive valid_execution :: "Process \<Rightarrow> Execution \<Rightarrow> bool" where
  empty: "valid_execution [] []"
| step:  "valid_execution P exec \<Longrightarrow> valid_execution (a # P) ((s, a) # exec)"


definition race_condition_free :: "Process \<Rightarrow> bool" where
  "race_condition_free P \<equiv> 
    \<forall>exec. valid_execution P exec \<longrightarrow> 
      (\<forall>loc. consistent_memory_view exec loc)"


(* Пример: Producer-Consumer *)
definition buffer :: location where "buffer = ''buffer''"

definition producer :: "nat \<Rightarrow> Process" where  (* nat вместо val для простоты *)
  "producer n = [Write buffer n, Compute]"

definition consumer :: "Process" where  
  "consumer = [Read buffer, Compute]"

definition producer_consumer_system :: "Process set" where
  "producer_consumer_system = producer 1 \<parallel> consumer"

(* Базовые леммы о чередовании *)
lemma interleave_non_empty: "interleave xs ys \<noteq> {}"
  by (induction xs ys rule: interleave.induct) auto

lemma interleave_preserves_length: 
  "zs \<in> interleave xs ys \<Longrightarrow> length zs = length xs + length ys"
  by (induction xs ys arbitrary: zs rule: interleave.induct) auto

(* Верификация свойств *)
lemma producer_consumer_can_progress:
  "\<forall>s. \<exists>P \<in> producer_consumer_system. can_progress P s"
  unfolding producer_consumer_system_def parallel_composition_def
            producer_def consumer_def can_progress_def
  using interleave_non_empty by auto

(* Readers-Writers с исправленными типами *)
definition shared_data :: location where "shared_data = ''shared''"

(* Readers-Writers *)

definition reader :: "id \<Rightarrow> Process" where
  "reader rid = [Read shared_data, Compute]"

definition writer :: "id \<Rightarrow> val \<Rightarrow> Process" where
  "writer wid v = [Write shared_data v, Compute]"

definition readers_writers :: "Process set" where
  "readers_writers = 
    {reader 1, reader 2, writer 1 42, writer 2 43}"

(* Более простая спецификация с приоритетами *)
definition has_high_priority_action :: "Process \<Rightarrow> bool" where
  "has_high_priority_action P \<equiv> 
    \<exists>a\<in>set P. case a of Write _ _ \<Rightarrow> True | Sync _ _ \<Rightarrow> True | _ \<Rightarrow> False"

(* Приоритетная композиция возвращает множество процессов *)
definition prioritized_composition :: 
  "Process \<Rightarrow> Process \<Rightarrow> Process set" (infix "\<parallel>\<^sub>p" 65) where
  "P \<parallel>\<^sub>p Q = 
    (if has_high_priority_action P then
       interleave P Q
     else
       interleave Q P)"

(* Пример использования приоритетной композиции *)
definition prioritized_system :: "Process set" where
  "prioritized_system = writer 1 100 \<parallel>\<^sub>p reader 1"

(* Чередование сохраняет мультимножество действий *)
lemma interleave_preserves_mset:
  fixes xs ys zs :: "'a list"
  assumes "zs \<in> interleave xs ys"
  shows "mset zs = mset xs + mset ys"
  using assms
  by (induction xs ys arbitrary: zs rule: interleave.induct) auto

lemma interleave_same_length:
  "zs \<in> interleave xs ys \<Longrightarrow> length zs = length xs + length ys"
  by (induction xs ys arbitrary: zs rule: interleave.induct) auto

lemma producer_consumer_race_free:
  "\<forall> n. race_condition_free (producer n)"
  unfolding race_condition_free_def consistent_memory_view_def
(*   by (metis consistent_memory_view_def dual_order.refl linorder_not_less) *)  
  by (metis consistent_memory_view_def dual_order.refl linorder_not_less)


(* lemma reader_preserves_memory:
  assumes "valid_execution (reader rid) exec"
  shows "\<forall>i j. i \<le> j \<longrightarrow> fst (exec!i) shared_data = fst (exec!j) shared_data"
  using assms
  unfolding valid_execution_def reader_def
  by auto *)


(* lemma reader_preserves_memory:
  assumes "valid_execution (reader rid) exec"
  shows "\<forall>i j. i \<le> j \<longrightarrow> fst (fst (exec!i)) shared_data = fst (fst (exec!j)) shared_data"
  using assms
   unfolding valid_execution.induct reader_def
  by *)

(* lemma reader_preserves_memory:
  assumes "valid_execution (reader rid) exec"
  shows "\<forall>i j. i \<le> j \<longrightarrow> 
          (case fst (exec!i) of (mem_i, _) \<Rightarrow> mem_i shared_data) = 
          (case fst (exec!j) of (mem_j, _) \<Rightarrow> mem_j shared_data)"
  using assms
  unfolding valid_execution.induct reader_def
  by sledgehammer
 *)
lemma reader_preserves_memory:
  assumes "valid_execution (reader rid) exec"
  shows "\<forall>i j. i \<le> j \<and> j < length exec \<longrightarrow> 
          fst (fst (exec!i)) shared_data = fst (fst (exec!j)) shared_data"
proof -
  from assms show ?thesis
  proof (induction "reader rid" exec rule: valid_execution.induct)
    case empty
    then show ?case by simp
  next
    case (step P exec s a)
    hence reader_structure: "a = Read shared_data" "P = [Compute]"
      unfolding reader_def by auto
    
    show ?case
    proof (intro allI impI)
      fix i j
      assume "i \<le> j" "j < length ((s, a) # exec)"
      
      have memory_constant: "\<forall>k < length ((s, a) # exec). 
                            fst (fst (((s, a) # exec) ! k)) shared_data = 
                            fst (fst s) shared_data"
      proof
        fix k
        assume "k < length ((s, a) # exec)"
        show "fst (fst (((s, a) # exec) ! k)) shared_data = fst (fst s) shared_data"
        proof (cases k)
          case 0
          then show ?thesis by simp
        next
          case (Suc k')
          have "k' < length exec" using \<open>k < length ((s, a) # exec)\<close> Suc by simp
          with step.IH have "fst (fst (exec ! k')) shared_data = fst (fst (exec ! 0)) shared_data"
            by (metis le0)
          also have "fst (fst (exec ! 0)) shared_data = fst (fst s) shared_data"
          proof -
            from reader_structure have "P = [Compute]" by simp
            with step.hyps show ?thesis
              by (cases exec) (auto simp: reader_def)
          qed
          finally show ?thesis using Suc by simp
        qed
      qed
      
      then show "fst (fst (((s, a) # exec) ! i)) shared_data = 
                 fst (fst (((s, a) # exec) ! j)) shared_data"
        using memory_constant \<open>i \<le> j\<close> \<open>j < length ((s, a) # exec)\<close> by auto
    qed
  qed
qed

end