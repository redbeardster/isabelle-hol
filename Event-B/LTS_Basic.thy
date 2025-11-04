theory LTS_Basic
  imports Main
begin

(* ===== ОСНОВНЫЕ ТИПЫ ДАННЫХ ===== *)

record ('st, 'ev) Tr =
  src :: "'st"
  dst :: "'st" 
  lbl :: "'ev"

record ('st, 'ev) LTS =
  init :: "'st set"
  trans :: "('st, 'ev) Tr set"

(* ===== ВСПОМОГАТЕЛЬНЫЕ ФУНКЦИИ ===== *)

definition outgoing :: "('st, 'ev) LTS \<Rightarrow> 'st \<Rightarrow> ('st, 'ev) Tr set" where
  "outgoing l s \<equiv> {t \<in> trans l. src t = s}"

definition accepted_events :: "('st, 'ev) LTS \<Rightarrow> 'st \<Rightarrow> 'ev set" where
  "accepted_events l s \<equiv> lbl ` (outgoing l s)"

(* ===== ДОСТИЖИМЫЕ СОСТОЯНИЯ (индуктивное определение) ===== *)

inductive_set states :: "('st, 'ev) LTS \<Rightarrow> 'st set" for l :: "('st, 'ev) LTS" where
  base: "s \<in> init l \<Longrightarrow> s \<in> states l"
| step: "\<lbrakk> s \<in> states l; t \<in> outgoing l s \<rbrakk> \<Longrightarrow> dst t \<in> states l"

(* ===== АЛФАВИТ LTS ===== *)

definition alphabet :: "('st, 'ev) LTS \<Rightarrow> 'ev set" where
  "alphabet l \<equiv> \<Union> (accepted_events l ` states l)"

(* ===== СВОЙСТВА И ЛЕММЫ ===== *)

(* 1. Начальные состояния достижимы *)
lemma init_states_subset: "init l \<subseteq> states l"
  using states.base by blast

(* 2. Достижимость через переходы *)
lemma reachable_via_transition:
  assumes "s \<in> states l" and "t \<in> outgoing l s" 
  shows "dst t \<in> states l"
  using assms states.step
    sorry 

(* 3. Алфавит содержит только события из переходов *)
lemma alphabet_subset_events:
  fixes l :: "('st, 'ev) LTS"
  shows "alphabet l \<subseteq> lbl ` trans l"
  unfolding alphabet_def accepted_events_def outgoing_def
  by auto

(* 4. Индуктивное правило для достижимых состояний *)
lemma states_induct_case[case_names base step]:
  assumes "s \<in> states l"
    and "\<And>s. s \<in> init l \<Longrightarrow> P s"
    and "\<And>s t. \<lbrakk> s \<in> states l; P s; t \<in> outgoing l s \<rbrakk> \<Longrightarrow> P (dst t)"
  shows "P s"
  using assms by (induction rule: states.induct) auto

(* ===== ПРИМЕР КОНКРЕТНОЙ LTS ===== *)

definition example_LTS :: "(nat, string) LTS" where
  "example_LTS = \<lparr>
    init = {0},
    trans = {
      \<lparr>src = 0, dst = 1, lbl = ''a''\<rparr>,
      \<lparr>src = 1, dst = 2, lbl = ''b''\<rparr>,
      \<lparr>src = 2, dst = 0, lbl = ''c''\<rparr>
    }
  \<rparr>"

(* Проверяем достижимые состояния для примера *)
lemma example_states: "states example_LTS = {0, 1, 2}"
proof
  show "states example_LTS \<subseteq> {0, 1, 2}"
  proof
    fix s assume "s \<in> states example_LTS"
    then show "s \<in> {0, 1, 2}"
      by (induction rule: states_induct_case)
         (auto simp: example_LTS_def outgoing_def)
  qed
  show "{0, 1, 2} \<subseteq> states example_LTS"
  proof
    have "0 \<in> states example_LTS" 
      by (rule states.base) (simp add: example_LTS_def)
    moreover have "1 \<in> states example_LTS"
      using \<open>0 \<in> states example_LTS\<close>
      by (rule states.step) (auto simp: example_LTS_def outgoing_def)
    moreover have "2 \<in> states example_LTS"
      using \<open>1 \<in> states example_LTS\<close>
      by (rule states.step) (auto simp: example_LTS_def outgoing_def)
    ultimately show "\<And>s. s \<in> {0,1,2} \<Longrightarrow> s \<in> states example_LTS" 
      by auto
  qed
qed

(* Алфавит для примера *)
lemma example_alphabet: "alphabet example_LTS = {''a'', ''b'', ''c''}"
  unfolding alphabet_def accepted_events_def example_states
  by (auto simp: example_LTS_def outgoing_def)

end