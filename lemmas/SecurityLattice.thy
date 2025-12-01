theory SecurityLattice
  imports Main
begin

(* 
(* Тип для уровней доступа *)
datatype access_level = Low | Medium | High

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


interpretation access_lattice: lattice "(\<sqsubseteq>)" "(\<squnion>)" "(\<sqinter>)"
proof
  fix x y z :: access_level
  (* Проверка свойств решетки *)
  show "x \<sqsubseteq> x \<squnion> y" by (cases x; cases y; auto)
  show "x \<sqinter> y \<sqsubseteq> x" by (cases x; cases y; auto)
  show "x \<squnion> y = y \<squnion> x" by (cases x; cases y; auto)
  show "x \<sqinter> y = y \<sqinter> x" by (cases x; cases y; auto)
  (* Дополнительные свойства решетки *)
  show "x \<sqsubseteq> y \<Longrightarrow> x \<squnion> z \<sqsubseteq> y \<squnion> z" by (cases x; cases y; cases z; auto)
  show "x \<sqsubseteq> y \<Longrightarrow> x \<sqinter> z \<sqsubseteq> y \<sqinter> z" by (cases x; cases y; cases z; auto)
qed

(* Пример использования *)
value "Low \<squnion> Medium"  (* Результат: Medium *)
value "High \<sqinter> Medium" (* Результат: Medium *)
value "Low \<sqsubseteq> High"    (* Результат: True *) *)

(* Тип для уровней доступа *)
datatype access_level = Low | Medium | High

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

(* Пример использования *)
value "join Low Medium"  (* Результат: Medium *)
value "meet High Medium" (* Результат: Medium *)
value "le Low High"      (* Результат: True *)



end