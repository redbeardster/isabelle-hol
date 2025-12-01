theory WorkingProtocols
  imports Main
begin

(* Упростим определение - используем более эффективный подход *)
definition packet_to_seq :: "nat list \<Rightarrow> nat" where
  "packet_to_seq xs = foldl (\<lambda>acc x. acc * 256 + x) 0 (rev xs)"

fun seq_to_packet :: "nat \<Rightarrow> nat list" where
  "seq_to_packet 0 = []"
| "seq_to_packet n = (n mod 256) # seq_to_packet (n div 256)"

fun packet_to_seq_simple :: "nat list \<Rightarrow> nat" where
  "packet_to_seq_simple [] = 0"
| "packet_to_seq_simple (x # xs) = x + 256 * packet_to_seq_simple xs"

value "packet_to_seq_simple [10]"      (* 10 *)
value "packet_to_seq_simple [10, 20]"  (* 2580 *)

(* Для больших списков используем упрощенное вычисление *)
lemma manual_computation:
  "packet_to_seq_simple [10, 20, 30] = 660510"
  by sledgehammer

(* Биективность для нового определения *)
lemma packet_bijection_simple:
  assumes "\<forall>x \<in> set xs. x < 256"
  shows "seq_to_packet (packet_to_seq_simple xs) = xs"
  using assms
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  have "packet_to_seq_simple (x # xs) = x + 256 * packet_to_seq_simple xs"
    by (simp add: packet_to_seq_simple_def)
  also have "seq_to_packet (x + 256 * packet_to_seq_simple xs) = 
             (x + 256 * packet_to_seq_simple xs) mod 256 # 
             seq_to_packet ((x + 256 * packet_to_seq_simple xs) div 256)"
    by simp
  also have "(x + 256 * packet_to_seq_simple xs) mod 256 = x"
    using Cons.prems by simp
  also have "(x + 256 * packet_to_seq_simple xs) div 256 = packet_to_seq_simple xs"
    using Cons.prems by simp
  also have "x # seq_to_packet (packet_to_seq_simple xs) = x # xs"
    using Cons by simp
  finally show ?case .
qed

end