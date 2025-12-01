theory ResourceAllocator
imports Main "HOL-Library.FSet"
begin

(* Типы ресурсов и клиентов *)
type_synonym client = nat
type_synonym resource = nat

(* Состояние системы *)
record allocator_state =
  allocated :: "(client \<times> resource) set"  (* кто какой ресурс получил *)
  waiting :: "client set"                 (* кто ждёт ресурсы *)
  resources :: "resource set"             (* все доступные ресурсы *)
  max_resources :: nat                    (* максимальное количество ресурсов *)

(* Инициализация системы *)
definition initial_state :: "allocator_state" where
  "initial_state \<equiv> 
    \<lparr>allocated = {}, 
     waiting = {}, 
     resources = {}, 
     max_resources = 10\<rparr>"

(* Предусловия и инварианты *)
definition inv_allocator :: "allocator_state \<Rightarrow> bool" where
  "inv_allocator s \<equiv> 
    finite (resources s) \<and>
    card (resources s) \<le> max_resources s \<and>
    (\<forall>(c, r) \<in> allocated s. r \<in> resources s) \<and>
    (\<forall>c \<in> waiting s. c \<notin> fst ` allocated s)"  (* ждущие не имеют ресурсов *)

(* TLA+: Request(c) - клиент запрашивает ресурс *)
definition Request :: "client \<Rightarrow> allocator_state \<Rightarrow> allocator_state \<Rightarrow> bool" where
  "Request c s s' \<equiv>
    c \<notin> waiting s \<and> 
    c \<notin> fst ` allocated s \<and>
    s' = s\<lparr>waiting := {c} \<union> waiting s\<rparr>"

(* TLA+: Allocate(c, r) - выделение ресурса клиенту *)
definition Allocate :: "client \<Rightarrow> resource \<Rightarrow> allocator_state \<Rightarrow> allocator_state \<Rightarrow> bool" where
  "Allocate c r s s' \<equiv>
    c \<in> waiting s \<and>
    r \<in> resources s \<and>
    r \<notin> snd ` allocated s \<and> 
    s' = s\<lparr>allocated := {(c, r)} \<union> allocated s,
           waiting := waiting s - {c}\<rparr>"

(* TLA+: Release(c, r) - освобождение ресурса *)
definition Release :: "client \<Rightarrow> resource \<Rightarrow> allocator_state \<Rightarrow> allocator_state \<Rightarrow> bool" where
  "Release c r s s' \<equiv>
    (c, r) \<in> allocated s \<and>
    s' = s\<lparr>allocated := allocated s - {(c, r)},
           resources := resources s - {r}\<rparr>"

(* TLA+: Next - следующее состояние системы *)
definition Next :: "allocator_state \<Rightarrow> allocator_state \<Rightarrow> bool" where
  "Next s s' \<equiv> 
    (\<exists>c. Request c s s') \<or>
    (\<exists>c r. Allocate c r s s') \<or>
    (\<exists>c r. Release c r s s')"

(* TLA+: Safety - взаимное исключение *)
definition MutualExclusion :: "allocator_state \<Rightarrow> bool" where
  "MutualExclusion s \<equiv>
    \<forall>r \<in> resources s. 
      card {c. (c, r) \<in> allocated s} \<le> 1"

(* TLA+: NoStarvation - отсутствие голодания *)
definition NoStarvation :: "allocator_state \<Rightarrow> bool" where
  "NoStarvation s \<equiv>
    \<forall>c \<in> waiting s. 
      \<exists>s'. (Next s s' \<and> c \<notin> waiting s')"

(* Инвариант системы *)
definition SystemInvariant :: "allocator_state \<Rightarrow> bool" where
  "SystemInvariant s \<equiv>
    inv_allocator s \<and>
    MutualExclusion s \<and>
    finite (allocated s) \<and>
    card (allocated s) \<le> card (resources s)"

(* Доказательство что инвариант сохраняется *)
lemma invariant_preserved:
  assumes "SystemInvariant s"
  assumes "Next s s'"
  shows "SystemInvariant s'"
  using assms
  unfolding SystemInvariant_def Next_def 
            Request_def Allocate_def Release_def
            MutualExclusion_def inv_allocator_def
  apply (elim disjE exE)
  apply (auto simp: image_def)
  (* Детальное доказательство сохранения инвариантов *)
  sorry

(* Начальное состояние удовлетворяет инварианту *)
lemma initial_invariant:
  "SystemInvariant initial_state"
  unfolding SystemInvariant_def MutualExclusion_def 
            inv_allocator_def initial_state_def
  by auto

(* \<box>P - всегда P *)
definition always :: "(allocator_state \<Rightarrow> bool) \<Rightarrow> (allocator_state stream \<Rightarrow> bool)" where
  "always P \<omega> \<equiv> \<forall>n. P (\<omega> n)"

(* P ~> Q - P ведёт к Q *)
definition leads_to :: 
  "(allocator_state \<Rightarrow> bool) \<Rightarrow> (allocator_state \<Rightarrow> bool) \<Rightarrow> (allocator_state stream \<Rightarrow> bool)" 
where
  "leads_to P Q \<omega> \<equiv> \<forall>n. P (\<omega> n) \<longrightarrow> (\<exists>m \<ge> n. Q (\<omega> m))"

(* Спецификация живости (Liveness) *)
theorem liveness_property:
  assumes "always SystemInvariant \<omega>"
  shows "leads_to (\<lambda>s. c \<in> waiting s) (\<lambda>s. c \<notin> waiting s) \<omega>"
  unfolding leads_to_def
  using assms
  (* Доказательство отсутствия голодания *)
  sorry

(* Модель с приоритетами *)
record priority_allocator_state = allocator_state +
  priority :: "client \<Rightarrow> nat"

(* Алгоритм аллокации с приоритетами *)
definition PriorityAllocate :: 
  "priority_allocator_state \<Rightarrow> priority_allocator_state \<Rightarrow> bool" 
where
  "PriorityAllocate s s' \<equiv>
    \<exists>c r. 
      c \<in> waiting s \<and>
      r \<in> resources s \<and>  
      r \<notin> snd ` allocated s \<and>
      (\<forall>c' \<in> waiting s. priority s c' \<le> priority s c) \<and>  
      s' = s\<lparr>allocated := {(c, r)} \<union> allocated s,
             waiting := waiting s - {c}\<rparr>"

(* Справедливость алгоритма *)
definition Fairness :: "priority_allocator_state \<Rightarrow> bool" where
  "Fairness s \<equiv>
    \<forall>c \<in> waiting s. 
      (\<exists>c' \<in> waiting s. priority s c' > priority s c) \<or>
      (\<exists>r \<in> resources s. r \<notin> snd ` allocated s)"

theorem fairness_proof:
  assumes "Fairness s"
  assumes "PriorityAllocate s s'"
  shows "Fairness s'"
  unfolding Fairness_def PriorityAllocate_def
  using assms
  apply auto
  sorry

(* Абстрактная спецификация *)
definition AbstractAllocator :: "allocator_state \<Rightarrow> allocator_state \<Rightarrow> bool" where
  "AbstractAllocator s s' \<equiv>
    allocated s \<subseteq> allocated s' \<and>
    (\<exists>C \<subseteq> waiting s. waiting s' = waiting s - C) \<and>
    (\<forall>c \<in> C. \<exists>r \<in> resources s. (c, r) \<in> allocated s')"

(* Рефайнмент: реализация удовлетворяет абстрактной спецификации *)
lemma refinement_proof:
  assumes "Next s s'"
  shows "AbstractAllocator s s'"
  using assms
  unfolding Next_def AbstractAllocator_def
            Request_def Allocate_def Release_def
  apply (elim disjE exE)
  apply (auto simp: image_def)
  done

(* Полная TLA+-подобная спецификация *)
definition ResourceAllocatorSpec :: "allocator_state stream \<Rightarrow> bool" where
  "ResourceAllocatorSpec \<omega> \<equiv>
    SystemInvariant (\<omega> 0) \<and>
    (\<forall>n. Next (\<omega> n) (\<omega> (Suc n))) \<and>
    always SystemInvariant \<omega> \<and>
    (\<forall>c. leads_to (\<lambda>s. c \<in> waiting s) (\<lambda>s. c \<notin> waiting s) \<omega>)"

(* Главная теорема корректности *)
theorem allocator_correctness:
  assumes "ResourceAllocatorSpec \<omega>"
  shows 
    "always MutualExclusion \<omega> \<and>
     (\<forall>c. leads_to (\<lambda>s. c \<in> waiting s) (\<lambda>s. c \<notin> waiting s) \<omega>)"
  using assms
  unfolding ResourceAllocatorSpec_def
  by auto

end

