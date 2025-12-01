theory ResourceAllocatorTLA
imports Main "HOL-Library.FSet"
begin

section \<open>TLA+ Case Study: A Resource Allocator - Formal Verification in Isabelle/HOL\<close>

subsection \<open>Basic Types and State Definition\<close>

text \<open>Types for clients and resources\<close>
type_synonym client = nat
type_synonym resource = nat

text \<open>Main system state record\<close>
record allocator_state =
  allocated :: "(client \<times> resource) set"  \<comment> \<open>Client-Resource assignments\<close>
  waiting :: "client set"                 \<comment> \<open>Clients waiting for resources\<close>
  resources :: "resource set"             \<comment> \<open>Available resources\<close>
  max_resources :: nat                    \<comment> \<open>Maximum resource count\<close>

text \<open>Initial system state\<close>
definition initial_state :: "allocator_state" where
  "initial_state \<equiv> 
    \<lparr>allocated = {}, 
     waiting = {}, 
     resources = {}, 
     max_resources = 10\<rparr>"

subsection \<open>System Invariants and Safety Properties\<close>

definition inv_allocator :: "allocator_state \<Rightarrow> bool" where
  "inv_allocator s \<equiv> 
    finite (resources s) \<and>
    card (resources s) \<le> max_resources s \<and>
    (\<forall>(c, r) \<in> allocated s. r \<in> resources s) \<and>
    (\<forall>c \<in> waiting s. c \<notin> fst ` allocated s)"

definition MutualExclusion :: "allocator_state \<Rightarrow> bool" where
  "MutualExclusion s \<equiv>
    \<forall>r \<in> resources s. 
      card {c. (c, r) \<in> allocated s} \<le> 1"

definition SystemInvariant :: "allocator_state \<Rightarrow> bool" where
  "SystemInvariant s \<equiv>
    inv_allocator s \<and>
    MutualExclusion s \<and>
    finite (allocated s) \<and>
    card (allocated s) \<le> card (resources s)"

subsection \<open>TLA+ Actions\<close>

text \<open>Request(c) - client requests a resource\<close>
definition Request :: "client \<Rightarrow> allocator_state \<Rightarrow> allocator_state \<Rightarrow> bool" where
  "Request c s s' \<equiv>
    c \<notin> waiting s \<and> 
    c \<notin> fst ` allocated s \<and>
    s' = s\<lparr>waiting := {c} \<union> waiting s\<rparr>"

text \<open>Allocate(c, r) - allocate resource to client\<close>
definition Allocate :: "client \<Rightarrow> resource \<Rightarrow> allocator_state \<Rightarrow> allocator_state \<Rightarrow> bool" where
  "Allocate c r s s' \<equiv>
    c \<in> waiting s \<and>
    r \<in> resources s \<and>
    r \<notin> snd ` allocated s \<and>
    s' = s\<lparr>allocated := {(c, r)} \<union> allocated s,
           waiting := waiting s - {c}\<rparr>"

text \<open>Release(c, r) - client releases resource\<close>
definition Release :: "client \<Rightarrow> resource \<Rightarrow> allocator_state \<Rightarrow> allocator_state \<Rightarrow> bool" where
  "Release c r s s' \<equiv>
    (c, r) \<in> allocated s \<and>
    s' = s\<lparr>allocated := allocated s - {(c, r)}\<rparr>"

text \<open>Next state relation\<close>
definition Next :: "allocator_state \<Rightarrow> allocator_state \<Rightarrow> bool" where
  "Next s s' \<equiv> 
    (\<exists>c. Request c s s') \<or>
    (\<exists>c r. Allocate c r s s') \<or>
    (\<exists>c r. Release c r s s')"

subsection \<open>Hoare Logic Verification\<close>

definition hoare_triple :: 
  "(allocator_state \<Rightarrow> bool) \<Rightarrow> (allocator_state \<Rightarrow> allocator_state \<Rightarrow> bool) \<Rightarrow> (allocator_state \<Rightarrow> bool) \<Rightarrow> bool" 
  ("\<lbrace>_\<rbrace>/ _/ \<lbrace>_\<rbrace>" [0,0,0] 100) 
where
  "\<lbrace>P\<rbrace> S \<lbrace>Q\<rbrace> \<equiv> \<forall>\<sigma> \<sigma>'. P \<sigma> \<and> S \<sigma> \<sigma>' \<longrightarrow> Q \<sigma>'"

lemma Request_correct:
  "\<lbrace>\<lambda>s. c \<notin> waiting s \<and> c \<notin> fst ` allocated s\<rbrace>
   Request c
   \<lbrace>\<lambda>s'. c \<in> waiting s' \<and> waiting s' = {c} \<union> waiting s\<rbrace>"
  unfolding hoare_triple_def Request_def
  by auto

lemma Allocate_correct:
  "\<lbrace>\<lambda>s. c \<in> waiting s \<and> r \<in> resources s \<and> r \<notin> snd ` allocated s\<rbrace>
   Allocate c r
   \<lbrace>\<lambda>s'. (c, r) \<in> allocated s' \<and> c \<notin> waiting s'\<rbrace>"
  unfolding hoare_triple_def Allocate_def
  by auto

lemma Release_correct:
  "\<lbrace>\<lambda>s. (c, r) \<in> allocated s\<rbrace>
   Release c r
   \<lbrace>\<lambda>s'. (c, r) \<notin> allocated s'\<rbrace>"
  unfolding hoare_triple_def Release_def
  by auto

subsection \<open>Invariant Preservation Proofs\<close>

lemma Request_preserves_invariant:
  assumes "SystemInvariant s"
  assumes "Request c s s'"
  shows "SystemInvariant s'"
proof -
  from assms have "c \<notin> waiting s" and "c \<notin> fst ` allocated s"
    unfolding Request_def by auto
  with assms show ?thesis
    unfolding SystemInvariant_def Request_def inv_allocator_def MutualExclusion_def
    by (auto simp: image_def)
qed

lemma Allocate_preserves_invariant:
  assumes "SystemInvariant s"
  assumes "Allocate c r s s'"
  shows "SystemInvariant s'"
proof -
  from assms have 
    "c \<in> waiting s" and 
    "r \<in> resources s" and 
    "r \<notin> snd ` allocated s"
    unfolding Allocate_def by auto
  
  with assms show ?thesis
    unfolding SystemInvariant_def Allocate_def inv_allocator_def MutualExclusion_def
    apply (auto simp: image_def)
    apply (metis (no_types, lifting) fst_conv image_eqI insert_iff)
    apply (metis Suc_le_eq card.insert card_Diff_singleton_if finite_Diff)
    done
qed

lemma Release_preserves_invariant:
  assumes "SystemInvariant s"
  assumes "Release c r s s'"
  shows "SystemInvariant s'"
proof -
  from assms have "(c, r) \<in> allocated s"
    unfolding Release_def by auto
  
  with assms show ?thesis
    unfolding SystemInvariant_def Release_def inv_allocator_def MutualExclusion_def
    by (auto simp: image_def)
qed

theorem Next_preserves_invariant:
  assumes "SystemInvariant s"
  assumes "Next s s'"
  shows "SystemInvariant s'"
  using assms
  unfolding Next_def
  by (auto elim: disjE exE 
           intro: Request_preserves_invariant 
                  Allocate_preserves_invariant 
                  Release_preserves_invariant)

lemma initial_state_invariant:
  "SystemInvariant initial_state"
  unfolding SystemInvariant_def MutualExclusion_def 
            inv_allocator_def initial_state_def
  by auto

subsection \<open>Temporal Logic and Liveness\<close>

type_synonym behavior = "allocator_state stream"

definition always :: "(allocator_state \<Rightarrow> bool) \<Rightarrow> behavior \<Rightarrow> bool" where
  "always P \<omega> \<equiv> \<forall>n. P (\<omega> n)"

definition eventually :: "(allocator_state \<Rightarrow> bool) \<Rightarrow> behavior \<Rightarrow> bool" where
  "eventually P \<omega> \<equiv> \<exists>n. P (\<omega> n)"

definition leads_to :: 
  "(allocator_state \<Rightarrow> bool) \<Rightarrow> (allocator_state \<Rightarrow> bool) \<Rightarrow> behavior \<Rightarrow> bool" 
where
  "leads_to P Q \<omega> \<equiv> \<forall>n. P (\<omega> n) \<longrightarrow> (\<exists>m \<ge> n. Q (\<omega> m))"

definition NoStarvation :: "behavior \<Rightarrow> bool" where
  "NoStarvation \<omega> \<equiv> \<forall>c. leads_to (\<lambda>s. c \<in> waiting s) (\<lambda>s. c \<notin> waiting s) \<omega>"

subsection \<open>Priority-based Allocation\<close>

record priority_allocator_state = allocator_state +
  priority :: "client \<Rightarrow> nat"

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

definition MaxPriorityClient :: "priority_allocator_state \<Rightarrow> client set" where
  "MaxPriorityClient s \<equiv>
    {c \<in> waiting s. \<forall>c' \<in> waiting s. priority s c' \<le> priority s c}"

lemma PriorityAllocate_fairness:
  assumes "waiting s \<noteq> {}"
  assumes "resources s - snd ` allocated s \<noteq> {}"
  shows "\<exists>s'. PriorityAllocate s s'"
proof -
  from assms obtain c where "c \<in> MaxPriorityClient s"
    unfolding MaxPriorityClient_def
    by (metis all_not_in_conv empty_iff)
  
  moreover from assms obtain r where "r \<in> resources s" "r \<notin> snd ` allocated s"
    by auto
    
  ultimately show ?thesis
    unfolding PriorityAllocate_def MaxPriorityClient_def
    by blast
qed

subsection \<open>Refinement: Abstract vs Concrete Specification\<close>

definition AbstractAllocator :: "allocator_state \<Rightarrow> allocator_state \<Rightarrow> bool" where
  "AbstractAllocator s s' \<equiv>
    allocated s \<subseteq> allocated s' \<and>
    waiting s' \<subseteq> waiting s \<and>
    (\<forall>c \<in> waiting s - waiting s'. \<exists>r \<in> resources s. (c, r) \<in> allocated s')"

lemma Next_refines_Abstract:
  assumes "Next s s'"
  shows "AbstractAllocator s s'"
  using assms
  unfolding Next_def AbstractAllocator_def
            Request_def Allocate_def Release_def
  by (auto elim: disjE exE)

subsection \<open>Complete System Specification\<close>

definition ResourceAllocatorSpec :: "behavior \<Rightarrow> bool" where
  "ResourceAllocatorSpec \<omega> \<equiv>
    SystemInvariant (\<omega> 0) \<and>
    (\<forall>n. Next (\<omega> n) (\<omega> (Suc n))) \<and>
    always SystemInvariant \<omega>"

theorem system_safety:
  assumes "ResourceAllocatorSpec \<omega>"
  shows "always MutualExclusion \<omega>"
  using assms
  unfolding ResourceAllocatorSpec_def always_def
  by (metis Next_preserves_invariant SystemInvariant_def)

subsection \<open>Example Execution Trace\<close>

definition example_trace :: "nat \<Rightarrow> allocator_state" where
  "example_trace n \<equiv>
    case n of
      0 \<Rightarrow> initial_state\<lparr>resources := {1,2,3}, max_resources := 3\<rparr>
    | 1 \<Rightarrow> \<lparr>allocated = {}, waiting = {0}, resources = {1,2,3}, max_resources = 3\<rparr>
    | 2 \<Rightarrow> \<lparr>allocated = {(0,1)}, waiting = {}, resources = {1,2,3}, max_resources = 3\<rparr>
    | _ \<Rightarrow> initial_state\<lparr>resources := {1,2,3}, max_resources := 3\<rparr>"

lemma example_trace_valid:
  "ResourceAllocatorSpec example_trace"
  unfolding ResourceAllocatorSpec_def always_def
proof (intro conjI allI)
  show "SystemInvariant (example_trace 0)"
    unfolding example_trace_def SystemInvariant_def MutualExclusion_def 
              inv_allocator_def initial_state_def
    by auto
  
  fix n
  show "Next (example_trace n) (example_trace (Suc n))"
    unfolding Next_def example_trace_def
    by (cases n) (auto simp: Request_def Allocate_def Release_def)
  
  show "always SystemInvariant example_trace"
    unfolding always_def example_trace_def SystemInvariant_def 
              MutualExclusion_def inv_allocator_def
    by (cases_tac n) auto
qed

subsection \<open>Advanced: Deadlock Freedom\<close>

definition DeadlockFree :: "allocator_state \<Rightarrow> bool" where
  "DeadlockFree s \<equiv>
    waiting s = {} \<or> 
    (\<exists>c \<in> waiting s. \<exists>r \<in> resources s. r \<notin> snd ` allocated s)"

theorem system_deadlock_free:
  assumes "SystemInvariant s"
  assumes "waiting s \<noteq> {}"
  assumes "card (allocated s) < card (resources s)"
  shows "DeadlockFree s"
  using assms
  unfolding SystemInvariant_def DeadlockFree_def inv_allocator_def
  by (metis (no_types, lifting) card_le_sym_diff_ex finite_Diff imageI subsetI)

end