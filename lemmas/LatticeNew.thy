theory LatticeNew
  imports Main
begin
(* 
locale lattice =
  fixes le :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "\<sqsubseteq>" 50)
    and join :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<squnion>" 65)
    and meet :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<sqinter>" 70)
  assumes
    join_above: "x \<sqsubseteq> x \<squnion> y"
    and meet_below: "x \<sqinter> y \<sqsubseteq> x"
    and join_comm: "x \<squnion> y = y \<squnion> x"
    and meet_comm: "x \<sqinter> y = y \<sqinter> x"


(* Тип для уровней доступа *)
datatype access_level = Low | Medium | High

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

  (* Свойство: x \<sqsubseteq> y \<Longrightarrow> x \<squnion> z \<sqsubseteq> y \<squnion> z *)
qed

(* Пример использования *)
value "join Low Medium"  (* Результат: Medium *)
value "meet High Medium" (* Результат: Medium *)
value "le Low High"      (* Результат: True *)

type_synonym 'a seq = "nat \<Rightarrow> 'a"

definition first :: "'a seq \<Rightarrow> 'a" 
  where "first s \<equiv> s 0"

definition nat_seq :: "nat seq" where
  "nat_seq = (\<lambda>n. n)"

value "nat_seq 2"

definition double_seq :: "nat seq" where
  "double_seq = (\<lambda>n. 2 * n)"

value "double_seq 3"

lemma "nat_seq n = n"
  by (simp add: nat_seq_def) *)

(* Тип для идентификаторов узлов *)
typedecl Node

(* Тип для данных (например, значения в репликах) *)
typedecl Data

(* Состояние системы: каждому узлу сопоставляется его локальное значение *)
type_synonym State = "Node \<Rightarrow> Data"


(* Обновление данных на узле *)
definition update :: "Node \<Rightarrow> Data \<Rightarrow> State \<Rightarrow> State" where
  "update node data state \<equiv> \<lambda>n. if n = node then data else state n"

(* Синхронизация данных между двумя узлами *)
definition sync :: "Node \<Rightarrow> Node \<Rightarrow> State \<Rightarrow> State" where
  "sync node1 node2 state \<equiv>
    \<lambda>n. if n = node1 then state node2
        else if n = node2 then state node1
        else state n"

(* Определение eventual consistency *)
definition eventual_consistency :: "State \<Rightarrow> bool" where
  "eventual_consistency state \<equiv>
    \<exists>d. \<forall>node. state node = d"

(* Возможные переходы системы *)
datatype Transition =
    Update Node Data
  | Sync Node Node

(* Функция перехода *)
definition step :: "Transition \<Rightarrow> State \<Rightarrow> State" where
  "step trans state \<equiv>
    case trans of
      Update node data \<Rightarrow> update node data state
    | Sync node1 node2 \<Rightarrow> sync node1 node2 state"

type_synonym Execution = "State list"

(* Проверка, что исполнение корректно *)
definition valid_execution :: "Execution \<Rightarrow> bool" where
  "valid_execution exec \<equiv>
    \<forall>i < (length exec - 1). \<exists>trans. step trans (exec ! i) = exec ! (i + 1)"

lemma sync_lemma:
  assumes "state' = sync node1 node2 state"
  shows "state' node1 = state' node2"
  sorry


(* Начальное состояние: все узлы имеют значение "A" *)
definition initial_state :: "State" where
  "initial_state \<equiv> \<lambda>n. A"

(* Пример исполнения *)
definition example_execution :: "Execution" where
  "example_execution \<equiv>
    [initial_state,
     step (Update node1 B) initial_state,
     step (Sync node1 node2) (step (Update node1 B) initial_state),
     step (Sync node2 node3) (step (Sync node1 node2) (step (Update node1 B) initial_state))]"






end