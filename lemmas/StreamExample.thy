theory StreamExample
  imports "HOL-Library.Stream"
begin


(*
(* Определение простого потока: последовательность натуральных чисел, начиная с 0 *)
definition nat_stream :: "nat stream" where
  "nat_stream = smap id (fromN 0)"
value "snth nat_stream 0"
*)

(* Поток натуральных чисел, начиная с 0 *)
definition nat_stream :: "nat stream" where
  "nat_stream = smap id (fromN 0)"

(* Поток, где каждый элемент увеличен на 1 *)
definition inc_stream :: "nat stream" where
  "inc_stream = smap (\<lambda>n. n + 1) nat_stream"

(* Поток, где элементы чередуются между 0 и 1 *)
definition alternating_stream :: "nat stream" where
  "alternating_stream = smap (\<lambda>n. if even n then 0 else 1) (fromN 0)"


(* 
(* Доступ к элементам потока *)
value "snth nat_stream 0" (* 0 *)
value "snth nat_stream 1" (* 1 *)
value "snth nat_stream 2" (* 2 *)

(* Определение потока, где каждый элемент увеличен на 1 *)
definition inc_stream :: "nat stream" where
  "inc_stream = smap (\<lambda>n. n + 1) nat_stream"

(* Доступ к элементам потока *)
value "snth inc_stream 0" (* 1 *)
value "snth inc_stream 1" (* 2 *)
value "snth inc_stream 2" (* 3 *)

(* Определение потока, где каждый элемент удвоен *)
definition double_stream :: "nat stream" where
  "double_stream = smap (\<lambda>n. n * 2) nat_stream"

(* Доступ к элементам потока *)
value "snth double_stream 0" (* 0 *)
value "snth double_stream 1" (* 2 *)
value "snth double_stream 2" (* 4 *)

(* Определение потока, где элементы чередуются между 0 и 1 *)
definition alternating_stream :: "nat stream" where
  "alternating_stream = smap (\<lambda>n. if even n then 0 else 1) (fromN 0)"

(* Доступ к элементам потока *)
value "snth alternating_stream 0" (* 0 *)
value "snth alternating_stream 1" (* 1 *)
value "snth alternating_stream 2" (* 0 *)
 *)
end