theory RegexExamples
  imports Main
begin

(* Тип для регулярных выражений *)
datatype 'a rexp = 
  Empty                 (* Пустое выражение *)
| Eps                   (* Пустая строка *)
| Sym 'a                (* Символ *)
| Alt "'a rexp" "'a rexp" (* Альтернатива (или) *)
| Seq "'a rexp" "'a rexp" (* Последовательность *)
| Star "'a rexp"        (* Звезда Клини *)

(* Вспомогательная функция для звезды Клини *)
primrec match_star :: "'a rexp \<Rightarrow> 'a list \<Rightarrow> bool" where
  "match_star r [] = True"  (* Пустая строка всегда соответствует звезде *)
| "match_star r (x # xs) = (match r [x] \<and> match_star r xs)"

(* Функция для проверки соответствия строки регулярному выражению *)
primrec match :: "'a rexp \<Rightarrow> 'a list \<Rightarrow> bool" where
  "match Empty _ = False"
| "match Eps xs = (xs = [])"
| "match (Sym a) xs = (xs = [a])"
| "match (Alt r1 r2) xs = (match r1 xs \<or> match r2 xs)"
| "match (Seq r1 r2) xs = (\<exists>ys zs. xs = ys @ zs \<and> match r1 ys \<and> match r2 zs)"
| "match (Star r) xs = match_star r xs"
(* Пример: Регулярное выражение для числа (последовательность цифр) *)
definition digit :: "char rexp" where
  "digit = Alt (Sym (CHR ''0'')) (Alt (Sym (CHR ''1'')) (Alt (Sym (CHR ''2'')) 
    (Alt (Sym (CHR ''3'')) (Alt (Sym (CHR ''4'')) (Alt (Sym (CHR ''5'')) 
    (Alt (Sym (CHR ''6'')) (Alt (Sym (CHR ''7'')) (Alt (Sym (CHR ''8'')) 
    (Sym (CHR ''9''))))))))))"

definition number :: "char rexp" where
  "number = Seq digit (Star digit)"

(* Проверка соответствия строки регулярному выражению *)
value "match number ''123''"  (* Результат: True *)
value "match number ''abc''"  (* Результат: False *)

lemma "match number ''123''"
  by (simp add: number_def digit_def)

lemma "\<not> match number ''abc''"
  by (simp add: number_def digit_def)

(* Определение буквы *)
definition letter :: "char rexp" where
  "letter = Alt (Sym (CHR ''a'')) (Alt (Sym (CHR ''b'')) (Sym (CHR ''c'')))"

(* Определение слова как последовательности букв *)
definition word :: "char rexp" where
  "word = Star letter"

(* Проверка соответствия строки регулярному выражению *)
value "match word ''abc''"  (* Результат: True *)
value "match word ''123''"  (* Результат: False *)


(* Определение числа с плавающей точкой *)
definition float_number :: "char rexp" where
  "float_number = Seq number (Seq (Sym (CHR ''.'')) number)"

(* Проверка соответствия строки регулярному выражению *)
value "match float_number ''3.14''"  (* Результат: True *)
value "match float_number ''abc''"  (* Результат: False *)

lemma "match float_number ''3.14''"
  by (simp add: float_number_def number_def digit_def)

lemma "\<not> match float_number ''abc''"
  by (simp add: float_number_def number_def digit_def)




end