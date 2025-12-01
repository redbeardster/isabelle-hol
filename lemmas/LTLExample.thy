theory LTLExample
  imports Main "HOL-Library.Linear_Temporal_Logic_on_Streams"
begin

(* datatype Transition = Toggle *)

(* 
definition toggle :: "State \<Rightarrow> State" where
  "toggle state = (case state of On \<Rightarrow> Off | Off \<Rightarrow> On)"

(* definition trajectory :: "(nat \<Rightarrow> State) \<Rightarrow> bool" where
  "trajectory \<sigma> \<equiv> \<forall>n. \<sigma> (Suc n) = toggle (\<sigma> n)"
 *)

(* Определение траектории системы как последовательности состояний *)
definition trajectory :: "State stream \<Rightarrow> bool" where
  "trajectory \<sigma> \<equiv> \<forall>n. snth \<sigma> (Suc n) = toggle (snth \<sigma> n)"


(* LTL-свойство: система всегда в конечном итоге вернется в состояние On *)
definition ltl_property :: "State stream \<Rightarrow> bool" where
  "ltl_property \<sigma> \<equiv> ev (holds (\<lambda>s. s = On)) \<sigma>"

thm State.simps

lemma "trajectory \<sigma> \<Longrightarrow> ltl_property \<sigma>"
  unfolding trajectory_def ltl_property_def
  by (smt (z3) State.exhaust State.simps(4) ev_holds_sset snth_sset toggle_def)

definition example_sequence :: "State stream" where
  "example_sequence = siterate toggle On"
 
(* Функция переключения состояния *)
definition toggle :: "State \<Rightarrow> State" where
  "toggle state = (case state of On \<Rightarrow> Off | Off \<Rightarrow> On)"

(* Определение траектории системы как последовательности состояний *)
definition trajectory :: "State stream \<Rightarrow> bool" where
  "trajectory \<sigma> \<equiv> \<forall>n. snth \<sigma> (Suc n) = toggle (snth \<sigma> n)"

(* LTL-свойство: система всегда в конечном итоге вернется в состояние On *)
definition ltl_property :: "State stream \<Rightarrow> bool" where
  "ltl_property \<sigma> \<equiv> ev (holds (\<lambda>s. s = On)) \<sigma>"

(* Пример последовательности *)
definition example_sequence :: "State stream" where
  "example_sequence = siterate toggle On"
*)

(* Определение состояний системы *)
datatype State = On | Off

(* Функция переключения состояния *)
definition toggle :: "State \<Rightarrow> State" where
  "toggle state = (case state of On \<Rightarrow> Off | Off \<Rightarrow> On)"

(* Определение траектории системы как последовательности состояний *)
definition trajectory :: "State stream \<Rightarrow> bool" where
  "trajectory \<sigma> \<equiv> \<forall>n. snth \<sigma> (Suc n) = toggle (snth \<sigma> n)"

(* Пример последовательности *)
 definition example_sequence :: "State stream" where
  "example_sequence = smap (\<lambda>n. if even n then On else Off) (fromN 0)"
 

(* definition example_sequence :: "State stream" where
  "example_sequence = scycle (smap (\<lambda>n. if even n then On else Off) (fromN 0))"
 *)
(* LTL-свойство: система всегда в конечном итоге вернется в состояние On *)

(* definition ltl_property :: "State stream \<Rightarrow> bool" where
  "ltl_property \<sigma> \<equiv> eventually (\<lambda>x. x = On) \<sigma>"
 *)

(* LTL-свойство: система всегда в конечном итоге вернется в состояние On *)
definition ltl_property :: "State stream \<Rightarrow> bool" where
  "ltl_property \<sigma> \<equiv> alw (ev (holds (\<lambda>s. s = On))) \<sigma>"

(* Доказательство свойства *)
lemma "trajectory \<sigma> \<Longrightarrow> ltl_property \<sigma>"
  unfolding trajectory_def ltl_property_def
  by (smt (verit, best) State.exhaust State.simps(4) alw_iff_sdrop ev.simps holds.elims(3) sdrop_simps(1) sdrop_stl snth.simps(2) toggle_def)



value "snth example_sequence 0" (* On *)
value "snth example_sequence 1" (* Off *)
value "snth example_sequence 2" (* On *)








end