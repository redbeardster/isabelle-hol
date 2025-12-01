theory CounterProcess
imports Main
begin
(* 
(* Тип для сообщений *)
type_synonym message = unit

(* Канал для передачи сообщений *)
channel chan: message

(* Состояние процесса: счётчик *)
record process_state =
  count :: nat

(* Начальное состояние счётчика *)
definition initial_state :: "process_state" where
  "initial_state = \<lparr> count = 0 \<rparr>"

(* Процесс, который обрабатывает сообщения *)
definition counter_process :: "process_state \<Rightarrow> process_state" where
  "counter_process s =
    (let new_count = count s + 1 in
     \<lparr> count = new_count \<rparr>)"

(* Основной процесс, который читает сообщения и обновляет состояние *)
definition main_process :: "process_state \<Rightarrow> process_state" where
  "main_process s =
    (let msg = chan.recv in (* Чтение сообщения из канала *)
     counter_process s)" (* Обновление состояния *)

(* Инвариант: счётчик всегда неотрицательный *)
definition counter_invariant :: "process_state \<Rightarrow> bool" where
  "counter_invariant s \<equiv> count s \<ge> 0"

(* Лемма: инвариант сохраняется после обработки сообщения *)
lemma counter_invariant_preserved:
  "counter_invariant s \<Longrightarrow> counter_invariant (counter_process s)"
  unfolding counter_invariant_def counter_process_def
  by simp

(* Лемма: инвариант сохраняется после выполнения основного процесса *)
lemma main_process_preserves_invariant:
  "counter_invariant s \<Longrightarrow> counter_invariant (main_process s)"
  unfolding main_process_def counter_invariant_def
  using counter_invariant_preserved
  by simp

(* Начальное состояние удовлетворяет инварианту *)
lemma initial_state_satisfies_invariant:
  "counter_invariant initial_state"
  unfolding counter_invariant_def initial_state_def
  by simp *)

type_synonym message = unit

type_synonym state = int

type_synonym channel = "message list"


definition process :: "channel \<Rightarrow> state \<Rightarrow> state" where
  "process ch cnt = (if ch \<noteq> [] then cnt + 1 else cnt)"

definition receive_message :: "channel \<Rightarrow> state \<Rightarrow> (state \<times> channel)" where
  "receive_message ch cnt = (if ch \<noteq> [] then (cnt + 1, tl ch) else (cnt, ch))"

(* Лемма, доказывающая, что значение счетчика не может быть меньше нуля *)
lemma counter_non_negative:
  assumes "cnt \<ge> 0"
  shows "fst (receive_message ch cnt) \<ge> 0"
proof -
  have "fst (receive_message ch cnt) = (if ch \<noteq> [] then cnt + 1 else cnt)"
    by (simp add: receive_message_def)
  also have "... \<ge> cnt"
    by auto
  finally show ?thesis
    using assms by auto
qed


end
