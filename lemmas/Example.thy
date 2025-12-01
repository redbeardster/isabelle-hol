theory Example
  imports Main
begin

(* Определение locale для решетки *)
locale lattice =
  fixes le :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "\<sqsubseteq>" 50)
    and join :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<squnion>" 65)
    and meet :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<sqinter>" 70)
  assumes
    join_above: "x \<sqsubseteq> x \<squnion> y"
    and meet_below: "x \<sqinter> y \<sqsubseteq> x"
    and join_comm: "x \<squnion> y = y \<squnion> x"
    and meet_comm: "x \<sqinter> y = y \<sqinter> x"

(* Конкретный тип данных: уровни доступа *)
datatype access_level = Low | Medium | High

(* 
(* Определение порядка на уровнях доступа *)
fun le :: "access_level \<Rightarrow> access_level \<Rightarrow> bool" (infixl "\<sqsubseteq>" 50) where
  "Low \<sqsubseteq> Low = True"
| "Low \<sqsubseteq> Medium = True"
| "Low \<sqsubseteq> High = True"
| "Medium \<sqsubseteq> Medium = True"
| "Medium \<sqsubseteq> High = True"
| "High \<sqsubseteq> High = True"
| "_ \<sqsubseteq> _ = False"

(* Определение супремума (наименьший верхний уровень) *)
fun join :: "access_level \<Rightarrow> access_level \<Rightarrow> access_level" (infixl "\<squnion>" 65) where
  "Low \<squnion> x = x"
| "Medium \<squnion> Low = Medium"
| "Medium \<squnion> Medium = Medium"
| "Medium \<squnion> High = High"
| "High \<squnion> _ = High"

(* Определение инфимума (наибольший нижний уровень) *)
fun meet :: "access_level \<Rightarrow> access_level \<Rightarrow> access_level" (infixl "\<sqinter>" 70) where
  "High \<sqinter> x = x"
| "Medium \<sqinter> High = Medium"
| "Medium \<sqinter> Medium = Medium"
| "Medium \<sqinter> Low = Low"
| "Low \<sqinter> _ = Low"

(* Интерпретация: показываем, что access_level является решеткой *)
interpretation access_lattice: lattice "le" "join" "meet"
proof
  fix x y z :: access_level
  show "x \<sqsubseteq> x \<squnion> y" by (cases x; cases y; auto)
  show "x \<sqinter> y \<sqsubseteq> x" by (cases x; cases y; auto)
  show "x \<squnion> y = y \<squnion> x" by (cases x; cases y; auto)
  show "x \<sqinter> y = y \<sqinter> x" by (cases x; cases y; auto)
qed *)

(* Определение порядка на уровнях доступа *)
fun le :: "access_level \<Rightarrow> access_level \<Rightarrow> bool" (infixl "\<sqsubseteq>" 50) where
  "Low \<sqsubseteq> Low = True"
| "Low \<sqsubseteq> Medium = True"
| "Low \<sqsubseteq> High = True"
| "Medium \<sqsubseteq> Low = False"
| "Medium \<sqsubseteq> Medium = True"
| "Medium \<sqsubseteq> High = True"
| "High \<sqsubseteq> Low = False"
| "High \<sqsubseteq> Medium = False"
| "High \<sqsubseteq> High = True"

(* Определение супремума (наименьший верхний уровень) *)
fun join :: "access_level \<Rightarrow> access_level \<Rightarrow> access_level" (infixl "\<squnion>" 65) where
  "Low \<squnion> x = x"
| "Medium \<squnion> Low = Medium"
| "Medium \<squnion> Medium = Medium"
| "Medium \<squnion> High = High"
| "High \<squnion> _ = High"

(* Определение инфимума (наибольший нижний уровень) *)
fun meet :: "access_level \<Rightarrow> access_level \<Rightarrow> access_level" (infixl "\<sqinter>" 70) where
  "High \<sqinter> x = x"
| "Medium \<sqinter> High = Medium"
| "Medium \<sqinter> Medium = Medium"
| "Medium \<sqinter> Low = Low"
| "Low \<sqinter> _ = Low"


 (*
(* Докажем, что наша структура является решеткой *)
interpretation access_lattice: lattice "le" "join" "meet"
proof
  fix x y z :: access_level
  (* Проверка свойств решетки *)
  show "le x (join x y)" by (cases x; cases y; auto)
  show "le (meet x y) x" by (cases x; cases y; auto)
  show "join x y = join y x" by (cases x; cases y; auto)
  show "meet x y = meet y x" by (cases x; cases y; auto)
  (* Дополнительные свойства решетки *)
  show "le x y \<Longrightarrow> le (join x z) (join y z)" by (cases x; cases y; cases z; auto)
  show "le x y \<Longrightarrow> le (meet x z) (meet y z)" by (cases x; cases y; cases z; auto)
qed 
*)

(*
Previous proof becomes OK
*)
(*
interpretation access_lattice: lattice "le" "join" "meet"
proof
  fix x y z :: access_level
  show "x \<sqsubseteq> x \<squnion> y" by (cases x; cases y; auto)
  show "x \<sqinter> y \<sqsubseteq> x" by (cases x; cases y; auto)
  show "x \<squnion> y = y \<squnion> x" by (cases x; cases y; auto)
  show "x \<sqinter> y = y \<sqinter> x" by (cases x; cases y; auto)
qed
*)
(* 
interpretation access_lattice: lattice "le" "join" "meet"
proof
  fix x y z :: access_level
  (* Свойство: x \<sqsubseteq> x \<squnion> y *)
  show "le x (join x y)"
    by (cases x; cases y; auto)

  (* Свойство: x \<sqinter> y \<sqsubseteq> x *)
  show "le (meet x y) x"
    by (cases x; cases y; auto)

  (* Свойство: x \<squnion> y = y \<squnion> x *)
  show "join x y = join y x"
    by (cases x; cases y; auto)

  (* Свойство: x \<sqinter> y = y \<sqinter> x *)
  show "meet x y = meet y x"
    by (cases x; cases y; auto)

qed
 *)

(* Докажем, что наша структура является решеткой *)
interpretation access_lattice: lattice "le" "join" "meet"
proof
  fix x y z :: access_level
  (* Свойство: x \<sqsubseteq> x \<squnion> y *)
  show "le x (join x y)"
    by (cases x; cases y; auto)

  (* Свойство: x \<sqinter> y \<sqsubseteq> x *)
  show "le (meet x y) x"
    by (cases x; cases y; auto)

  (* Свойство: x \<squnion> y = y \<squnion> x *)
  show "join x y = join y x"
    by (cases x; cases y; auto)

  (* Свойство: x \<sqinter> y = y \<sqinter> x *)
  show "meet x y = meet y x"
    by (cases x; cases y; auto)
qed

(* Пример использования *)
value "join Low Medium"  (* Результат: Medium *)
value "meet High Medium" (* Результат: Medium *)
value "le Low High"      (* Результат: True *)





end