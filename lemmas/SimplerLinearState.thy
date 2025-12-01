theory SimplerLinearState
imports Main
begin

datatype linear_state = 
    S0 | S1 | S2 | S3 | S4 | S5 | DONE

(* Используем лексикографический порядок конструкторов *)
definition linear_order :: "linear_state \<Rightarrow> linear_state \<Rightarrow> bool" where
  "linear_order x y = (case (x, y) of
    (S0, S0) \<Rightarrow> False
  | (S0, _) \<Rightarrow> True
  | (S1, S0) \<Rightarrow> False
  | (S1, S1) \<Rightarrow> False
  | (S1, _) \<Rightarrow> True
  | (S2, S0) \<Rightarrow> False
  | (S2, S1) \<Rightarrow> False
  | (S2, S2) \<Rightarrow> False
  | (S2, _) \<Rightarrow> True
  | (S3, DONE) \<Rightarrow> True
  | (S3, _) \<Rightarrow> False
  | (S4, DONE) \<Rightarrow> True
  | (S4, _) \<Rightarrow> False
  | (S5, DONE) \<Rightarrow> True
  | (S5, _) \<Rightarrow> False
  | (DONE, _) \<Rightarrow> False)"

(* Или еще проще: использовать нумерацию *)
fun state_number :: "linear_state \<Rightarrow> nat" where
  "state_number S0 = 0"
| "state_number S1 = 1"  
| "state_number S2 = 2"
| "state_number S3 = 3"
| "state_number S4 = 4"
| "state_number S5 = 5"
| "state_number DONE = 6"

definition state_order :: "linear_state \<Rightarrow> linear_state \<Rightarrow> bool" where
  "state_order x y \<longleftrightarrow> state_number x < state_number y"

inductive_set simple_transitions :: "(linear_state \<times> linear_state) set" where
  "state_order s s' \<Longrightarrow> (s, s') \<in> simple_transitions"

end