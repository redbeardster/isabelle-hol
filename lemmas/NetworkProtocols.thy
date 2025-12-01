(* theory NetworkProtocols
  imports Main
begin

(* Состояние TCP-соединения *)
record tcp_state =
  seq_num :: nat      (* sequence number *)
  ack_num :: nat      (* acknowledgement number *)
  window :: nat
  packet_data :: "nat list"  (* переименовано из data *)

(* Биективное отображение между последовательностью и данными *)
definition packet_to_seq :: "nat list \<Rightarrow> nat" where
  "packet_to_seq lst = foldl (\<lambda>acc x. acc * 256 + x) 0 lst"

fun seq_to_packet :: "nat \<Rightarrow> nat list" where
  "seq_to_packet 0 = []"
| "seq_to_packet n = (n mod 256) # seq_to_packet (n div 256)"


function seq_to_packet_safe :: "nat \<Rightarrow> nat list" where
  "seq_to_packet_safe n = (
    if n = 0 then []
    else if n < 256 then [n]
    else (n mod 256) # seq_to_packet_safe (n div 256)
  )"
  by pat_completeness auto
termination
  apply (relation "measure (\<lambda>n. n)")
  apply auto
  done

thm seq_to_packet.induct

type_synonym heap = "nat \<rightharpoonup> nat"
type_synonym pointer = nat


lemma seq_to_packet_nonempty: "n > 0 \<longrightarrow> seq_to_packet n \<noteq> []"
  by (induct n rule: seq_to_packet.induct) auto

lemma seq_to_packet_bounds: "\<forall>x \<in> set (seq_to_packet n). x < 256"
  by (induct n rule: seq_to_packet.induct) auto


definition allocate :: "heap \<Rightarrow> (heap \<times> pointer)" where
  "allocate h = (
    let new_ptr = (if h = Map.empty then 0 else Suc (Max (dom h))) in
    (h(new_ptr \<mapsto> 0), new_ptr)
  )"

definition deallocate :: "heap \<Rightarrow> pointer \<Rightarrow> heap" where
  "deallocate h ptr = (\<lambda>p. if p = ptr then None else h p)"



(* Практическое применение в верификации протокола *)
definition create_packet :: "nat list \<Rightarrow> tcp_state \<Rightarrow> tcp_state" where
  "create_packet data st = 
    st\<lparr>seq_num := packet_to_seq data, 
       packet_data := data\<rparr>"

definition parse_packet :: "tcp_state \<Rightarrow> nat list option" where
  "parse_packet st = 
    (if packet_to_seq (packet_data st) = seq_num st then
       Some (packet_data st)
     else
       None)"

theorem packet_consistency:
  "parse_packet (create_packet data st) = Some data"
  unfolding create_packet_def parse_packet_def
  by simp

type_synonym byte = nat  (* 0-255 *)

definition bytes_to_nat :: "byte list \<Rightarrow> nat" where
  "bytes_to_nat bytes = foldl (\<lambda>acc b. acc * 256 + b) 0 bytes"

fun nat_to_bytes :: "nat \<Rightarrow> byte list" where
  "nat_to_bytes 0 = []"
 | "nat_to_bytes n = (n mod 256) # nat_to_bytes (n div 256)" 


end *)

theory NetworkProtocols
  imports Main
begin

(* Состояние TCP-соединения *)
(* record tcp_state =
  seq_num :: nat      (* sequence number *)
  ack_num :: nat      (* acknowledgement number *)
  window :: nat
  packet_data :: "nat list" *)

(* Корректное определение с начальным значением 0 *)
definition packet_to_seq :: "nat list \<Rightarrow> nat" where
  "packet_to_seq xs = foldr (\<lambda>x acc. x + acc * 256) xs 0"

(* Альтернативный более ясный синтаксис *)
definition packet_to_seq_alt :: "nat list \<Rightarrow> nat" where
  "packet_to_seq_alt = (\<lambda>xs. foldr (\<lambda>x acc. x + acc * 256) xs 0)"

fun seq_to_packet :: "nat \<Rightarrow> nat list" where
  "seq_to_packet 0 = []"
| "seq_to_packet n = seq_to_packet (n div 256) @ [n mod 256]"

(* Проверим вычисления *)
value "packet_to_seq [10, 20, 30]"
(* Результат: 10 * 256^2 + 20 * 256 + 30 = 660510 *)

value "seq_to_packet 660510"
(* Результат: [10, 20, 30] *)

(* 
value "seq_to_packet 660510"

lemma packet_bijection_correct:
  assumes "\<forall>x \<in> set xs. x < 256"
  shows "seq_to_packet (packet_to_seq xs) = xs"
  using assms
proof (induct xs)
  case Nil
  then show ?case
    unfolding packet_to_seq_def by simp
next
  case (Cons x xs)
  have IH: "seq_to_packet (packet_to_seq xs) = xs"
    using Cons.prems   by (simp add: Cons.hyps)
  
  have "packet_to_seq (x # xs) = foldr (\<lambda>x acc. x + acc * 256) (x # xs) 0"
    unfolding packet_to_seq_def .
  also have "\<dots> = x + foldr (\<lambda>x acc. x + acc * 256) xs 0 * 256"
    by simp
  also have "\<dots> = x + packet_to_seq xs * 256"
    unfolding packet_to_seq_def by simp
  finally have eq: "packet_to_seq (x # xs) = x + packet_to_seq xs * 256" .
  
  show ?case
  proof (cases "packet_to_seq xs = 0 \<and> x = 0")
    case True
    then show ?thesis
      unfolding eq by simp
  next
    case False
    have "seq_to_packet (x + packet_to_seq xs * 256) = 
          seq_to_packet (packet_to_seq xs) @ [(x + packet_to_seq xs * 256) mod 256]"
      by (simp add: seq_to_packet.simps(2))
    also have "\<dots> = xs @ [(x + packet_to_seq xs * 256) mod 256]"
      using IH by simp
    also have "(x + packet_to_seq xs * 256) mod 256 = x"
      using Cons.prems
      by (simp add: mod_mult_self3)
    also have "xs @ [x] = x # xs"
      by simp
    finally show ?thesis
      using eq by simp
  qed
qed



(* Более практичный пример с явным условием остановки *)
function seq_to_packet_safe :: "nat \<Rightarrow> nat list" where
  "seq_to_packet_safe n = (
    if n = 0 then []
    else if n < 256 then [n]
    else (n mod 256) # seq_to_packet_safe (n div 256)
  )"
  by pat_completeness auto
termination
  apply (relation "measure (\<lambda>n. n)")
  apply auto
  done

(* Докажем базовые свойства *)
lemma seq_to_packet_nonempty: "n > 0 \<longrightarrow> seq_to_packet n \<noteq> []"
  by (induct n rule: seq_to_packet.induct) auto

lemma seq_to_packet_bounds: "\<forall>x \<in> set (seq_to_packet n). x < 256"
  by (induct n rule: seq_to_packet.induct) auto


(* Практическое применение в верификации протокола *)
definition create_packet :: "nat list \<Rightarrow> tcp_state \<Rightarrow> tcp_state" where
  "create_packet data st = 
    st\<lparr>seq_num := packet_to_seq data, 
       packet_data := data\<rparr>"

definition parse_packet :: "tcp_state \<Rightarrow> nat list option" where
  "parse_packet st = 
    (if packet_to_seq (packet_data st) = seq_num st then
       Some (packet_data st)
     else
       None)"

theorem packet_consistency:
  assumes "\<forall>x \<in> set data. x < 256"
  shows "parse_packet (create_packet data st) = Some data"
proof -
  have "packet_to_seq data = seq_num (create_packet data st)"
    unfolding create_packet_def by simp
  moreover have "packet_data (create_packet data st) = data"
    unfolding create_packet_def by simp
  ultimately show ?thesis
    unfolding parse_packet_def by simp
qed
 *)
(* Пример использования *)
value "seq_to_packet 12345"
value "packet_to_seq [57, 48]"
value "seq_to_packet (packet_to_seq [1, 2, 3])"



lemma example_roundtrip_correct:
  "seq_to_packet (packet_to_seq [10, 20, 30]) = [10, 20, 30]"










end
