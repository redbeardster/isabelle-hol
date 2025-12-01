theory AbstractQueue
  imports Main
begin

(* Тип очереди *)
typedecl 'a queue

(* Операции над очередью *)
consts
  empty_queue :: "'a queue"
  enqueue :: "'a \<Rightarrow> 'a queue \<Rightarrow> 'a queue"
  dequeue :: "'a queue \<Rightarrow> ('a \<times> 'a queue)"
  is_empty :: "'a queue \<Rightarrow> bool"

(* Аксиомы для операций *)
axiomatization where
  dequeue_empty: "is_empty q \<Longrightarrow> dequeue q = undefined"
| dequeue_nonempty: "\<not> is_empty q \<Longrightarrow> dequeue q = (x, q') \<Longrightarrow> q = enqueue x q'"
| is_empty_empty: "is_empty empty_queue"
| is_empty_enqueue: "\<not> is_empty (enqueue x q)"

(* Пример использования *)
lemma "is_empty empty_queue"
  by (simp add: is_empty_empty)

lemma "\<not> is_empty (enqueue 1 empty_queue)"
  by (simp add: is_empty_enqueue)

end