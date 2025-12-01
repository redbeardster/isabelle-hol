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
qed

end