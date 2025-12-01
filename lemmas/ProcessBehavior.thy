theory ProcessBehavior
  imports LTL
begin

text \<open>Типы для процессов и состояний\<close>
typedecl process
datatype state = Waiting | Executing | Finished

(* text \<open>Состояние системы: каждый процесс имеет текущее состояние\<close>
record system_state =
  process_states :: "process \<Rightarrow> state"

text \<open>Критическая секция: только один процесс может находиться в состоянии Executing\<close>
definition critical_section_invariant :: "system_state \<Rightarrow> bool" where
  "critical_section_invariant s \<equiv> 
    card {p. process_states s p = Executing} \<le> 1"

text \<open>Запрос на выполнение: процесс переходит из Waiting в Executing\<close>
definition request_execution :: "process \<Rightarrow> system_state \<Rightarrow> system_state \<Rightarrow> bool" where
  "request_execution p s s' \<equiv> 
    process_states s p = Waiting \<and> process_states s' p = Executing"

text \<open>Завершение выполнения: процесс переходит из Executing в Finished\<close>
definition finish_execution :: "process \<Rightarrow> system_state \<Rightarrow> system_state \<Rightarrow> bool" where
  "finish_execution p s s' \<equiv> 
    process_states s p = Executing \<and> process_states s' p = Finished"

definition safety_property :: "process \<Rightarrow> system_state ltl" where
  "safety_property p \<equiv> 
    \<box> (LTLProp (\<lambda>s. process_states s p = Executing \<longrightarrow> critical_section_invariant s))"

definition liveness_property :: "process \<Rightarrow> system_state ltl" where
  "liveness_property p \<equiv> 
    \<diamond> (LTLProp (\<lambda>s. process_states s p = Executing))"

definition invariant_property :: "system_state ltl" where
  "invariant_property \<equiv> 
    \<box> (LTLProp critical_section_invariant)"

lemma safety_property_holds:
  assumes "\<forall>\<sigma>. ltl_sem \<sigma> invariant_property"
  shows "\<forall>\<sigma>. ltl_sem \<sigma> (safety_property p)"
  using assms
  unfolding safety_property_def invariant_property_def critical_section_invariant_def
  by auto

lemma liveness_property_holds:
  assumes "\<exists>i. process_states (\<sigma> i) p = Executing"
  shows "ltl_sem \<sigma> (liveness_property p)"
  using assms
  unfolding liveness_property_def
  by auto


lemma invariant_property_holds:
  assumes "\<forall>s. critical_section_invariant s"
  shows "\<forall>\<sigma>. ltl_sem \<sigma> invariant_property"
  using assms
  unfolding invariant_property_def critical_section_invariant_def
  by auto *)

typedecl message


text \<open>Состояние системы\<close>
record system_state =
  sent :: "(process \<times> process \<times> message) set"  (* Отправленные сообщения *)
  received :: "(process \<times> process \<times> message) set"  (* Полученные сообщения *)

text \<open>Функция для отправки сообщения\<close>
definition send_message :: "process \<Rightarrow> process \<Rightarrow> message \<Rightarrow> system_state \<Rightarrow> system_state \<Rightarrow> bool" where
  "send_message p1 p2 m s s' \<equiv> 
    s' = s\<lparr>sent := sent s \<union> {(p1, p2, m)}\<rparr>"

text \<open>Функция для получения сообщения\<close>
definition receive_message :: "process \<Rightarrow> process \<Rightarrow> message \<Rightarrow> system_state \<Rightarrow> system_state \<Rightarrow> bool" where
  "receive_message p1 p2 m s s' \<equiv> 
    (p1, p2, m) \<in> sent s \<and> s' = s\<lparr>received := received s \<union> {(p1, p2, m)}\<rparr>"


definition message_delivery :: "process \<Rightarrow> process \<Rightarrow> message \<Rightarrow> system_state ltl" where
  "message_delivery p1 p2 m \<equiv> 
    \<diamond> (LTLProp (\<lambda>s. (p1, p2, m) \<in> received s))"

definition no_message_loss :: "process \<Rightarrow> process \<Rightarrow> message \<Rightarrow> system_state ltl" where
  "no_message_loss p1 p2 m \<equiv> 
    \<box> (LTLProp (\<lambda>s. (p1, p2, m) \<in> sent s \<longrightarrow> (p1, p2, m) \<in> sent s \<or> (p1, p2, m) \<in> received s))"

(* definition message_order :: "process \<Rightarrow> process \<Rightarrow> message \<Rightarrow> message \<Rightarrow> system_state ltl" where
  "message_order p1 p2 m1 m2 \<equiv> 
    (LTLProp (\<lambda>s. (p1, p2, m1) \<in> sent s) U (LTLProp (\<lambda>s. (p1, p2, m2) \<in> sent s)) \<longrightarrow>
    (LTLProp (\<lambda>s. (p1, p2, m1) \<in> received s)) U (LTLProp (\<lambda>s. (p1, p2, m2) \<in> received s))"

definition message_order :: "process \<Rightarrow> process \<Rightarrow> message \<Rightarrow> message \<Rightarrow> system_state ltl" where
  "message_order p1 p2 m1 m2 \<equiv> 
    (LTLProp (\<lambda>s. (p1, p2, m1) \<in> sent s) U (LTLProp (\<lambda>s. (p1, p2, m2) \<in> sent s)) \<longrightarrow>
    (LTLProp (\<lambda>s. (p1, p2, m1) \<in> received s) U (LTLProp (\<lambda>s. (p1, p2, m2) \<in> received s))"
 *)


definition message_order :: "process \<Rightarrow> process \<Rightarrow> message \<Rightarrow> message \<Rightarrow> system_state ltl" where
  "message_order p1 p2 m1 m2 \<equiv> 
    LTLOr
      (LTLNot ((LTLProp (\<lambda>s. (p1, p2, m1) \<in> sent s)) U (LTLProp (\<lambda>s. (p1, p2, m2) \<in> sent s))))
      ((LTLProp (\<lambda>s. (p1, p2, m1) \<in> received s)) U (LTLProp (\<lambda>s. (p1, p2, m2) \<in> received s)))"


definition message_order :: "process \<Rightarrow> process \<Rightarrow> message \<Rightarrow> message \<Rightarrow> system_state ltl" where
  "message_order p1 p2 m1 m2 \<equiv> 
    LTLOr
      (LTLNot (LTLUntil (LTLProp (\<lambda>s. (p1, p2, m1) \<in> sent s)) (LTLProp (\<lambda>s. (p1, p2, m2) \<in> sent s))))
      (LTLUntil (LTLProp (\<lambda>s. (p1, p2, m1) \<in> received s)) (LTLProp (\<lambda>s. (p1, p2, m2) \<in> received s)))"

(* lemma message_delivery_holds:
  assumes "\<exists>i. (p1, p2, m) \<in> sent (\<sigma> i)"
  shows "ltl_sem \<sigma> (message_delivery p1 p2 m)"
  using assms
  unfolding message_delivery_def
  by auto
 *)

lemma message_delivery_holds:
  assumes "\<exists>i. (p1, p2, m) \<in> sent (\<sigma> i)"
    and "\<forall>i. (p1, p2, m) \<in> sent (\<sigma> i) \<longrightarrow> (\<exists>j\<ge>i. (p1, p2, m) \<in> received (\<sigma> j))"
  shows "ltl_sem \<sigma> (message_delivery p1 p2 m)"
  using assms
  unfolding message_delivery_def
  by auto


lemma no_message_loss_holds:
  assumes "\<forall>i. (p1, p2, m) \<in> sent (\<sigma> i) \<longrightarrow> (p1, p2, m) \<in> sent (\<sigma> i) \<or> (p1, p2, m) \<in> received (\<sigma> i)"
  shows "ltl_sem \<sigma> (no_message_loss p1 p2 m)"
  using assms
  unfolding no_message_loss_def
  by auto

(* lemma message_order_holds:
  assumes "\<forall>i. (p1, p2, m1) \<in> sent (\<sigma> i) \<longrightarrow> (\<exists>j\<ge>i. (p1, p2, m2) \<in> sent (\<sigma> j))"
    and "\<forall>i. (p1, p2, m1) \<in> received (\<sigma> i) \<longrightarrow> (\<exists>j\<ge>i. (p1, p2, m2) \<in> received (\<sigma> j))"
  shows "ltl_sem \<sigma> (message_order p1 p2 m1 m2)"
  using assms
  unfolding message_order_def
  by auto *)

(*
 lemma message_order_holds:
  assumes "\<forall>i. (p1, p2, m1) \<in> sent (\<sigma> i) \<longrightarrow> (\<exists>j\<ge>i. (p1, p2, m2) \<in> sent (\<sigma> j))"
    and "\<forall>i. (p1, p2, m1) \<in> received (\<sigma> i) \<longrightarrow> (\<exists>j\<ge>i. (p1, p2, m2) \<in> received (\<sigma> j))"
    and "\<forall>i. (p1, p2, m1) \<in> sent (\<sigma> i) \<longrightarrow> (\<exists>k\<ge>i. (p1, p2, m1) \<in> received (\<sigma> k))"
    and "\<forall>i. (p1, p2, m2) \<in> sent (\<sigma> i) \<longrightarrow> (\<exists>k\<ge>i. (p1, p2, m2) \<in> received (\<sigma> k))"
  shows "ltl_sem \<sigma> (message_order p1 p2 m1 m2)"
   using assms
    using assms
  unfolding message_order_def
  apply auto
  apply (metis le_cases) *)
 

(* 
lemma message_order_holds:
  assumes "\<forall>i. (p1, p2, m1) \<in> sent (\<sigma> i) \<longrightarrow> (\<exists>j\<ge>i. (p1, p2, m2) \<in> sent (\<sigma> j))"
    and "\<forall>i. (p1, p2, m1) \<in> received (\<sigma> i) \<longrightarrow> (\<exists>j\<ge>i. (p1, p2, m2) \<in> received (\<sigma> j))"
    and "\<forall>i. (p1, p2, m1) \<in> sent (\<sigma> i) \<longrightarrow> (\<exists>k\<ge>i. (p1, p2, m1) \<in> received (\<sigma> k))"
    and "\<forall>i. (p1, p2, m2) \<in> sent (\<sigma> i) \<longrightarrow> (\<exists>k\<ge>i. (p1, p2, m2) \<in> received (\<sigma> k))"
  shows "ltl_sem \<sigma> (message_order p1 p2 m1 m2)"
(*   unfolding message_order_def *)
 proof (intro allI impI)
  fix i
  assume "(p1, p2, m1) \<in> sent (\<sigma> i)"
  then obtain j where "j \<ge> i" and "(p1, p2, m2) \<in> sent (\<sigma> j)"
    using assms(1) by blast
  moreover obtain k1 where "k1 \<ge> i" and "(p1, p2, m1) \<in> received (\<sigma> k1)"
    using assms(3) `(p1, p2, m1) \<in> sent (\<sigma> i)` by blast
  moreover obtain k2 where "k2 \<ge> j" and "(p1, p2, m2) \<in> received (\<sigma> k2)"
    using assms(4) `(p1, p2, m2) \<in> sent (\<sigma> j)` by blast
  ultimately show "\<exists>j\<ge>i. (p1, p2, m2) \<in> received (\<sigma> j)"
    by (meson assms(2) le_trans)
qed

lemma message_order_holds:
  assumes "\<forall>i. (p1, p2, m1) \<in> sent (\<sigma> i) \<longrightarrow> (\<exists>j\<ge>i. (p1, p2, m2) \<in> sent (\<sigma> j))"
    and "\<forall>i. (p1, p2, m1) \<in> received (\<sigma> i) \<longrightarrow> (\<exists>j\<ge>i. (p1, p2, m2) \<in> received (\<sigma> j))"
    and "\<forall>i. (p1, p2, m1) \<in> sent (\<sigma> i) \<longrightarrow> (\<exists>k\<ge>i. (p1, p2, m1) \<in> received (\<sigma> k))"
    and "\<forall>i. (p1, p2, m2) \<in> sent (\<sigma> i) \<longrightarrow> (\<exists>k\<ge>i. (p1, p2, m2) \<in> received (\<sigma> k))"
  shows "ltl_sem \<sigma> (message_order p1 p2 m1 m2)"
  unfolding message_order_def
proof -
  fix i
  assume "(p1, p2, m1) \<in> sent (\<sigma> i)"
  then obtain j where "j \<ge> i" and "(p1, p2, m2) \<in> sent (\<sigma> j)"
    using assms(1) by blast
  moreover obtain k1 where "k1 \<ge> i" and "(p1, p2, m1) \<in> received (\<sigma> k1)"
    using assms(3) `(p1, p2, m1) \<in> sent (\<sigma> i)` by blast
  moreover obtain k2 where "k2 \<ge> j" and "(p1, p2, m2) \<in> received (\<sigma> k2)"
    using assms(4) `(p1, p2, m2) \<in> sent (\<sigma> j)` by blast
  ultimately show "\<exists>j\<ge>i. (p1, p2, m2) \<in> received (\<sigma> j)"
    by (meson assms(2) le_trans)
qed

 *)






end