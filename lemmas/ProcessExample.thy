theory ProcessExample
  imports Main
begin

type_synonym message = unit

type_synonym state = int

type_synonym channel = "message list"

(* definition process :: "channel \<Rightarrow> state \<Rightarrow> state" where
  "process ch cnt = (if ch \<noteq> [] then cnt + 1 else cnt)"
 *)

definition receive_message :: "channel \<Rightarrow> state \<Rightarrow> (state \<times> channel)" where
  "receive_message ch cnt = (if ch \<noteq> [] then (cnt + 1, tl ch) else (cnt, ch))"

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