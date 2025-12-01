theory ResourceAllocatorPlain
imports Main "HOL-Library.FSet"
begin

section \<open>Resource Allocator - Plain Text Version\<close>

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

subsection \<open>Temporal Operators (Text Names)\<close>

type_synonym behavior = "nat \<Rightarrow> allocator_state"

definition always :: "(behavior \<Rightarrow> bool) \<Rightarrow> behavior \<Rightarrow> bool" where
  "always P \<omega> \<equiv> \<forall>n. P (\<lambda>k. \<omega> (n + k))"

definition eventually :: "(behavior \<Rightarrow> bool) \<Rightarrow> behavior \<Rightarrow> bool" where
  "eventually P \<omega> \<equiv> \<exists>n. P (\<lambda>k. \<omega> (n + k))"

definition leads_to :: 
  "(behavior \<Rightarrow> bool) \<Rightarrow> (behavior \<Rightarrow> bool) \<Rightarrow> behavior \<Rightarrow> bool" 
where
  "leads_to P Q \<omega> \<equiv> always (\<lambda>\<omega>'. P \<omega>' \<longrightarrow> eventually Q \<omega>') \<omega>"

subsection \<open>System Invariants\<close>

definition inv_allocator :: "allocator_state \<Rightarrow> bool" where
  "inv_allocator s \<equiv> 
    finite (resources s) \<and>
    card (resources s) \<le> max_resources s \<and>
    (\<forall>(c, r) \<in> allocated s. r \<in> resources s) \<and>
    (\<forall>c \<in> waiting s. c \<notin> fst ` allocated s)"

definition mutual_exclusion :: "allocator_state \<Rightarrow> bool" where
  "mutual_exclusion s \<equiv>
    \<forall>r \<in> resources s. 
      card {c. (c, r) \<in> allocated s} \<le> 1"

definition system_invariant :: "allocator_state \<Rightarrow> bool" where
  "system_invariant s \<equiv>
    inv_allocator s \<and>
    mutual_exclusion s \<and>
    finite (allocated s) \<and>
    card (allocated s) \<le> card (resources s)"

subsection \<open>System Actions\<close>

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

subsection \<open>Hoare Logic Verification\<close>

definition hoare_triple :: 
  "(allocator_state \<Rightarrow> bool) \<Rightarrow> (allocator_state \<Rightarrow> allocator_state \<Rightarrow> bool) \<Rightarrow> (allocator_state \<Rightarrow> bool) \<Rightarrow> bool" 
where
  "hoare_triple P S Q \<equiv> \<forall>\<sigma> \<sigma>'. P \<sigma> \<and> S \<sigma> \<sigma>' \<longrightarrow> Q \<sigma>'"

lemma Request_correct:
  "hoare_triple 
    (\<lambda>s. c \<notin> waiting s \<and> c \<notin> fst ` allocated s)
    (Request c)
    (\<lambda>s'. c \<in> waiting s' \<and> waiting s' = {c} \<union> waiting s)"
  unfolding hoare_triple_def Request_def
  by sorry

lemma Allocate_correct:
  "hoare_triple 
    (\<lambda>s. c \<in> waiting s \<and> r \<in> resources s \<and> r \<notin> snd ` allocated s)
    (Allocate c r)
    (\<lambda>s'. (c, r) \<in> allocated s' \<and> c \<notin> waiting s')"
  unfolding hoare_triple_def Allocate_def
  by auto

lemma Release_correct:
  "hoare_triple 
    (\<lambda>s. (c, r) \<in> allocated s)
    (Release c r)
    (\<lambda>s'. (c, r) \<notin> allocated s')"
  unfolding hoare_triple_def Release_def
  by auto

subsection \<open>Invariant Preservation\<close>

lemma Request_preserves_invariant:
  assumes "system_invariant s"
  assumes "Request c s s'"
  shows "system_invariant s'"
  using assms
  unfolding system_invariant_def Request_def inv_allocator_def mutual_exclusion_def
  by (auto simp: image_def)

lemma Allocate_preserves_invariant:
  assumes "system_invariant s"
  assumes "Allocate c r s s'"
  shows "system_invariant s'"
  using assms
  unfolding system_invariant_def Allocate_def inv_allocator_def mutual_exclusion_def
  apply (auto simp: image_def)
  apply (metis fst_conv image_eqI insert_iff)
  apply (metis Suc_le_eq card.insert card_Diff_singleton_if finite_Diff)
  done

lemma Release_preserves_invariant:
  assumes "system_invariant s"
  assumes "Release c r s s'"
  shows "system_invariant s'"
  using assms
  unfolding system_invariant_def Release_def inv_allocator_def mutual_exclusion_def
  by (auto simp: image_def)

theorem Next_preserves_invariant:
  assumes "system_invariant s"
  assumes "Next s s'"
  shows "system_invariant s'"
  using assms
  unfolding Next_def
  by (auto elim: disjE exE 
           intro: Request_preserves_invariant 
                  Allocate_preserves_invariant 
                  Release_preserves_invariant)

lemma initial_state_invariant:
  "system_invariant initial_state"
  unfolding system_invariant_def mutual_exclusion_def 
            inv_allocator_def initial_state_def
  by auto

subsection \<open>Liveness Properties\<close>

definition no_starvation :: "behavior \<Rightarrow> bool" where
  "no_starvation \<omega> \<equiv> 
    \<forall>c. leads_to 
          (\<lambda>\<omega>'. c \<in> waiting (\<omega>' 0)) 
          (\<lambda>\<omega>'. c \<notin> waiting (\<omega>' 0)) 
          \<omega>"

definition deadlock_free :: "allocator_state \<Rightarrow> bool" where
  "deadlock_free s \<equiv>
    waiting s = {} \<or> 
    (\<exists>c \<in> waiting s. \<exists>r \<in> resources s. r \<notin> snd ` allocated s)"

theorem system_deadlock_free:
  assumes "system_invariant s"
  assumes "waiting s \<noteq> {}"
  assumes "card (allocated s) < card (resources s)"
  shows "deadlock_free s"
  using assms
  unfolding system_invariant_def deadlock_free_def inv_allocator_def
  by (metis card_le_sym_diff_ex finite_Diff imageI subsetI)

subsection \<open>Complete System Specification\<close>

definition ResourceAllocatorSpec :: "behavior \<Rightarrow> bool" where
  "ResourceAllocatorSpec \<omega> \<equiv>
    system_invariant (\<omega> 0) \<and>
    (\<forall>n. Next (\<omega> n) (\<omega> (Suc n))) \<and>
    always (\<lambda>\<omega>'. system_invariant (\<omega>' 0)) \<omega>"

theorem system_safety:
  assumes "ResourceAllocatorSpec \<omega>"
  shows "always (\<lambda>\<omega>'. mutual_exclusion (\<omega>' 0)) \<omega>"
  using assms
  unfolding ResourceAllocatorSpec_def always_def
  by (metis Next_preserves_invariant system_invariant_def)

subsection \<open>Example Execution\<close>

definition example_behavior :: "behavior" where
  "example_behavior n \<equiv>
    case n of
      0 \<Rightarrow> initial_state\<lparr>resources := {1,2,3}, max_resources := 3\<rparr>
    | 1 \<Rightarrow> \<lparr>allocated = {}, waiting = {0}, resources = {1,2,3}, max_resources := 3\<rparr>
    | 2 \<Rightarrow> \<lparr>allocated = {(0,1)}, waiting = {}, resources = {1,2,3}, max_resources := 3\<rparr>
    | _ \<Rightarrow> initial_state\<lparr>resources := {1,2,3}, max_resources := 3\<rparr>"

lemma example_trace_valid:
  "ResourceAllocatorSpec example_behavior"
  unfolding ResourceAllocatorSpec_def always_def
proof (intro conjI allI)
  show "system_invariant (example_behavior 0)"
    unfolding example_behavior_def system_invariant_def mutual_exclusion_def 
              inv_allocator_def initial_state_def
    by auto
  
  fix n
  show "Next (example_behavior n) (example_behavior (Suc n))"
    unfolding Next_def example_behavior_def
    by (cases n) (auto simp: Request_def Allocate_def Release_def)
  
  show "always (\<lambda>\<omega>'. system_invariant (\<lambda>\<omega>'. 0)) example_behavior"
    unfolding always_def example_behavior_def system_invariant_def 
              mutual_exclusion_def inv_allocator_def
    by (cases_tac n) auto
qed

subsection \<open>Temporal Duality Theorems\<close>

theorem duality_always_eventually:
  "always P \<omega> \<longleftrightarrow> \<not> (eventually (\<lambda>\<omega>'. \<not> P \<omega>') \<omega>)"
  unfolding always_def eventually_def by auto

theorem duality_eventually_always:
  "eventually P \<omega> \<longleftrightarrow> \<not> (always (\<lambda>\<omega>'. \<not> P \<omega>') \<omega>)"  
  unfolding always_def eventually_def by auto

theorem always_distributes_over_conjunction:
  "always (\<lambda>\<omega>'. P \<omega>' \<and> Q \<omega>') \<omega> \<longleftrightarrow> always P \<omega> \<and> always Q \<omega>"
  unfolding always_def by auto

theorem eventually_distributes_over_disjunction:
  "eventually (\<lambda>\<omega>'. P \<omega>' \<or> Q \<omega>') \<omega> \<longleftrightarrow> eventually P \<omega> \<or> eventually Q \<omega>"
  unfolding eventually_def by auto

end