theory QueueLib
  imports "HOL-Data_Structures.Queue_Spec"
begin

(* Определение очереди на основе списка *)
definition list_queue :: "'a list \<Rightarrow> 'a queue" where
  "list_queue xs = Queue xs"

(* Пустая очередь *)
definition empty_queue :: "'a queue" where
  "empty_queue = list_queue []"

(* Добавление элемента в очередь *)
definition enqueue :: "'a \<Rightarrow> 'a queue \<Rightarrow> 'a queue" where
  "enqueue x q = list_queue (Queue.list q @ [x])"

(* Удаление элемента из очереди *)
definition dequeue :: "'a queue \<Rightarrow> ('a \<times> 'a queue)" where
  "dequeue q = (hd (Queue.list q), list_queue (tl (Queue.list q)))"

(* Проверка, пуста ли очередь *)
definition is_empty :: "'a queue \<Rightarrow> bool" where
  "is_empty q = (Queue.list q = [])"

(* Пример использования *)
value "enqueue 1 (enqueue 2 (enqueue 3 empty_queue))" (* Очередь с элементами [1, 2, 3] *)
value "dequeue (enqueue 1 (enqueue 2 (enqueue 3 empty_queue)))" (* (1, очередь с элементами [2, 3]) *)
value "is_empty empty_queue" (* True *)
value "is_empty (enqueue 1 empty_queue)" (* False *)

end