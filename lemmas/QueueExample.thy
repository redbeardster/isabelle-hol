theory QueueExample
  imports Main
begin

(* Тип очереди: список элементов *)
type_synonym 'a queue = "'a list"

(* Пустая очередь *)
definition empty_queue :: "'a queue" where
  "empty_queue = []"

(* Добавление элемента в конец очереди *)
definition enqueue :: "'a \<Rightarrow> 'a queue \<Rightarrow> 'a queue" where
  "enqueue x q = q @ [x]"

(* Удаление элемента из начала очереди *)
definition dequeue :: "'a queue \<Rightarrow> ('a \<times> 'a queue)" where
  "dequeue q = (hd q, tl q)"

(* Проверка, пуста ли очередь *)
definition is_empty :: "'a queue \<Rightarrow> bool" where
  "is_empty q = (q = [])"

(* Пример использования *)
value "enqueue (1::nat) (enqueue 2 (enqueue 3 empty_queue))" (* [1, 2, 3] *)
value "dequeue (enqueue (1::nat) (enqueue 2 (enqueue 3 empty_queue)))" (* (1, [2, 3]) *)
value "is_empty empty_queue" (* True *)
value "is_empty (enqueue (1::nat) empty_queue)" (* False *)

end

