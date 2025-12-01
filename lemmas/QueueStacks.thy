theory QueueStacks
  imports Main
begin

(* Тип очереди: два стека *)
type_synonym 'a queue = "'a list \<times> 'a list"

(* Пустая очередь *)
definition empty_queue :: "nat queue" where
  "empty_queue = ([], [])"

(* Добавление элемента в очередь *)
(* definition enqueue :: "'a \<Rightarrow> 'a queue \<Rightarrow> 'a queue" where
  "enqueue x (in_stack, out_stack) = (x # in_stack, out_stack)"
 *)

definition enqueue :: "'a \<Rightarrow> 'a queue \<Rightarrow> 'a queue" where
  "enqueue x q = (case q of (in_stack, out_stack) \<Rightarrow> (x # in_stack, out_stack))"

(* Удаление элемента из очереди *)
(* definition dequeue :: "'a queue \<Rightarrow> ('a \<times> 'a queue)" where
  "dequeue (in_stack, []) = (hd (rev in_stack), ([], tl (rev in_stack)))"
| "dequeue (in_stack, x # out_stack) = (x, (in_stack, out_stack))"
 *)
definition dequeue :: "'a queue \<Rightarrow> ('a \<times> 'a queue)" where
  "dequeue q = (case q of
    (in_stack, []) \<Rightarrow> (hd (rev in_stack), ([], tl (rev in_stack)))
  | (in_stack, x # out_stack) \<Rightarrow> (x, (in_stack, out_stack)))"


(* Проверка, пуста ли очередь *)
(* definition is_empty :: "'a queue \<Rightarrow> bool" where
  "is_empty (in_stack, out_stack) = (in_stack = [] \<and> out_stack = [])"
 *)

(* Проверка, пуста ли очередь *)
definition is_empty :: "'a queue \<Rightarrow> bool" where
  "is_empty q = (case q of (in_stack, out_stack) \<Rightarrow> in_stack = [] \<and> out_stack = [])"


(* Пример использования *)
value "enqueue 3 empty_queue" (* ([3], []) *)

value "is_empty empty_queue" (* True *)




end