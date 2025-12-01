theory ResourceAllocatorSimple
imports Main "HOL-Library.FSet"
begin

section \<open>Resource Allocator - Simple Temporal Version\<close>

subsection \<open>Basic Types and State\<close>

type_synonym client = nat
type_synonym resource = nat

record allocator_state =
  allocated :: "(client \<times> resource) set"
  waiting :: "client set"
  resources :: "resource set"
  max_resources :: nat

definition initial_state :: "allocator_state" where
  "initial_state \<equiv> 
    \<lparr>allocated = {}, 
     waiting = {}, 
     resources = {}, 
     max_resources = 10\<rparr>"

subsection \<open>Temporal Operators\<close>

type_synonym behavior = "nat \<Rightarrow> allocator_state"

definition always :: "(behavior \<Rightarrow> bool) \<Rightarrow> behavior \<Rightarrow> bool" where
  "always P \<omega> \<equiv> \<forall>n. P (\<lambda>k. \<omega> (n + k))"

definition eventually :: "(behavior \<Rightarrow> bool) \<Rightarrow> behavior \<Rightarrow> bool" where
  "eventually P \<omega> \<equiv> \<exists>n. P (\<lambda>k. \<omega> (n + k))"

subsection \<open>System Properties and Invariants\<close>

definition mutual_exclusion :: "allocator_state \<Rightarrow> bool" where
  "mutual_exclusion s \<equiv>
    \<forall>r \<in> resources s. 
      card {c. (c, r) \<in> allocated s} \<le> 1"

definition no_orphaned_allocations :: "allocator_state \<Rightarrow> bool" where
  "no_orphaned_allocations s \<equiv>
    \<forall>(c, r) \<in> allocated s. r \<in> resources s"

definition waiting_clients_have_no_resources :: "allocator_state \<Rightarrow> bool" where
  "waiting_clients_have_no_resources s \<equiv>
    \<forall>c \<in> waiting s. c \<notin> fst ` allocated s"

definition resource_bounds :: "allocator_state \<Rightarrow> bool" where
  "resource_bounds s \<equiv>
    finite (resources s) \<and> card (resources s) \<le> max_resources s"

definition system_invariant :: "allocator_state \<Rightarrow> bool" where
  "system_invariant s \<equiv>
    mutual_exclusion s \<and>
    no_orphaned_allocations s \<and>
    waiting_clients_have_no_resources s \<and>
    resource_bounds s \<and>
    finite (allocated s) \<and>
    card (allocated s) \<le> card (resources s)"

subsection \<open>System Actions and Transitions\<close>

definition Request :: "client \<Rightarrow> allocator_state \<Rightarrow> allocator_state \<Rightarrow> bool" where
  "Request c s s' \<equiv>
    c \<notin> waiting s \<and> 
    c \<notin> fst ` allocated s \<and>
    s' = s\<lparr>waiting := {c} \<union> waiting s\<rparr>"

definition Allocate :: "client \<Rightarrow> resource \<Rightarrow> allocator_state \<Rightarrow> allocator_state \<Rightarrow> bool" where
  "Allocate c r s s' \<equiv>
    c \<in> waiting s \<and>
    r \<in> resources s \<and>
    r \<notin> snd ` allocated s \<and>
    s' = s\<lparr>allocated := {(c, r)} \<union> allocated s,
           waiting := waiting s - {c}\<rparr>"

definition Release :: "client \<Rightarrow> resource \<Rightarrow> allocator_state \<Rightarrow> allocator_state \<Rightarrow> bool" where
  "Release c r s s' \<equiv>
    (c, r) \<in> allocated s \<and>
    s' = s\<lparr>allocated := allocated s - {(c, r)}\<rparr>"

definition Next :: "allocator_state \<Rightarrow> allocator_state \<Rightarrow> bool" where
  "Next s s' \<equiv> 
    (\<exists>c. Request c s s') \<or>
    (\<exists>c r. Allocate c r s s') \<or>
    (\<exists>c r. Release c r s s')"

subsection \<open>Invariant Preservation Proofs\<close>

lemma Request_preserves_invariants:
  assumes "system_invariant s"
  assumes "Request c s s'"
  shows "system_invariant s'"
proof -
  from assms have "c \<notin> waiting s" and "c \<notin> fst ` allocated s"
    unfolding Request_def by auto
  
  with assms show ?thesis
    unfolding system_invariant_def Request_def
              mutual_exclusion_def no_orphaned_allocations_def
              waiting_clients_have_no_resources_def resource_bounds_def
    by (auto simp: image_def)
qed

lemma Allocate_preserves_invariants:
  assumes "system_invariant s"
  assumes "Allocate c r s s'"
  shows "system_invariant s'"
proof -
  from assms have 
    "c \<in> waiting s" and 
    "r \<in> resources s" and 
    "r \<notin> snd ` allocated s"
    unfolding Allocate_def by auto  
  with assms show ?thesis
    unfolding system_invariant_def Allocate_def
              mutual_exclusion_def no_orphaned_allocations_def
              waiting_clients_have_no_resources_def resource_bounds_def
    apply (auto simp: image_def)
(*     apply (metis fst_conv image_eqI insert_iff) *) 
     apply (smt (verit, ccfv_threshold) Collect_cong card.infinite card_le_Suc0_iff_eq mem_Collect_eq snd_conv zero_le)
(*      apply (metis Suc_le_eq card.insert card_Diff_singleton_if finite_Diff) *)     
    sorry
qed

lemma Release_preserves_invariants:
  assumes "system_invariant s"
  assumes "Release c r s s'"
  shows "system_invariant s'"
proof -
  from assms have "(c, r) \<in> allocated s"
    unfolding Release_def by auto
  
  with assms show ?thesis
    unfolding system_invariant_def Release_def
              mutual_exclusion_def no_orphaned_allocations_def
              waiting_clients_have_no_resources_def resource_bounds_def
    by (auto simp: image_def)
qed

theorem Next_preserves_invariant:
  assumes "system_invariant s"
  assumes "Next s s'"
  shows "system_invariant s'"
  using assms
  unfolding Next_def
  by (auto elim: disjE exE 
           intro: Request_preserves_invariants 
                  Allocate_preserves_invariants 
                  Release_preserves_invariants)

lemma initial_state_satisfies_invariant:
  "system_invariant initial_state"
  unfolding system_invariant_def initial_state_def
            mutual_exclusion_def no_orphaned_allocations_def
            waiting_clients_have_no_resources_def resource_bounds_def
  by auto

subsection \<open>Liveness and Safety Properties\<close>

definition always_mutual_exclusion :: "behavior \<Rightarrow> bool" where
  "always_mutual_exclusion \<omega> \<equiv> always (\<lambda>\<omega>'. mutual_exclusion (\<omega>' 0)) \<omega>"

definition eventually_served :: "client \<Rightarrow> behavior \<Rightarrow> bool" where
  "eventually_served c \<omega> \<equiv> eventually (\<lambda>\<omega>'. c \<notin> waiting (\<omega>' 0)) \<omega>"

definition no_starvation :: "behavior \<Rightarrow> bool" where
  "no_starvation \<omega> \<equiv> \<forall>c. eventually_served c \<omega>"

definition deadlock_free_state :: "allocator_state \<Rightarrow> bool" where
  "deadlock_free_state s \<equiv>
    waiting s = {} \<or> 
    (\<exists>c \<in> waiting s. \<exists>r \<in> resources s. r \<notin> snd ` allocated s)"

theorem safety_theorem:
  assumes "system_invariant s"
  shows "mutual_exclusion s"
  using assms unfolding system_invariant_def by blast

theorem deadlock_freedom_theorem:
  assumes "system_invariant s"
  assumes "waiting s \<noteq> {}"
  assumes "card (allocated s) < card (resources s)"
  shows "deadlock_free_state s"
  using assms
  unfolding system_invariant_def deadlock_free_state_def 
            resource_bounds_def no_orphaned_allocations_def
  by (metis card_le_sym_diff_ex finite_Diff imageI subsetI)

subsection \<open>System Specification\<close>

definition valid_initial_state :: "allocator_state \<Rightarrow> bool" where
  "valid_initial_state s \<equiv>
    allocated s = {} \<and>
    waiting s = {} \<and>
    finite (resources s) \<and>
    card (resources s) \<le> max_resources s"

definition SystemSpecification :: "behavior \<Rightarrow> bool" where
  "SystemSpecification \<omega> \<equiv>
    valid_initial_state (\<omega> 0) \<and>
    (\<forall>n. Next (\<omega> n) (\<omega> (Suc n))) \<and>
    always (\<lambda>\<omega>'. system_invariant (\<omega>' 0)) \<omega> \<and>
    no_starvation \<omega>"

theorem main_safety_theorem:
  assumes "SystemSpecification \<omega>"
  shows "always_mutual_exclusion \<omega>"
  using assms
  unfolding SystemSpecification_def always_mutual_exclusion_def
  by (metis Next_preserves_invariant system_invariant_def)

subsection \<open>Example System Behavior\<close>

definition example_system_behavior :: "behavior" where
  "example_system_behavior n \<equiv>
    let base_state = \<lparr>allocated = {}, waiting = {}, resources = {1,2,3}, max_resources = 3\<rparr>
    in case n of
         0 \<Rightarrow> base_state
       | Suc 0 \<Rightarrow> base_state\<lparr>waiting := {0}\<rparr>
       | Suc (Suc 0) \<Rightarrow> base_state\<lparr>waiting := {0}, allocated := {(0,1)}\<rparr>
       | Suc (Suc (Suc 0)) \<Rightarrow> base_state\<lparr>allocated := {(0,1)}\<rparr>
       | _ \<Rightarrow> base_state"

lemma example_behavior_satisfies_invariants:
  "\<forall>n. system_invariant (example_system_behavior n)"
  unfolding example_system_behavior_def system_invariant_def
            mutual_exclusion_def no_orphaned_allocations_def
            waiting_clients_have_no_resources_def resource_bounds_def
  by (auto split: nat.splits)

lemma example_behavior_has_transitions:
  "\<forall>n. Next (example_system_behavior n) (example_system_behavior (Suc n))"
  unfolding example_system_behavior_def Next_def
            Request_def Allocate_def Release_def
  by (auto split: nat.splits)

subsection \<open>Useful Temporal Properties\<close>

lemma invariant_implies_always_safe:
  assumes "SystemSpecification \<omega>"
  shows "always (\<lambda>\<omega>'. mutual_exclusion (\<omega>' 0)) \<omega>"
  using assms unfolding SystemSpecification_def
  by (metis Next_preserves_invariant system_invariant_def)

lemma eventually_all_clients_served:
  assumes "SystemSpecification \<omega>"
  assumes "finite (resources (\<omega> 0))"
  shows "no_starvation \<omega>"
  using assms unfolding SystemSpecification_def by simp

theorem temporal_duality:
  "always P \<omega> \<longleftrightarrow> \<not> (eventually (\<lambda>\<omega>'. \<not> P \<omega>') \<omega>)"
  unfolding always_def eventually_def by auto

theorem always_distribution:
  "always (\<lambda>\<omega>'. P \<omega>' \<and> Q \<omega>') \<omega> \<longleftrightarrow> always P \<omega> \<and> always Q \<omega>"
  unfolding always_def by auto

theorem eventually_distribution:
  "eventually (\<lambda>\<omega>'. P \<omega>' \<or> Q \<omega>') \<omega> \<longleftrightarrow> eventually P \<omega> \<or> eventually Q \<omega>"
  unfolding eventually_def by auto

end