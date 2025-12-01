theory WorkingRealTimeExample
imports Main
begin

datatype real_time_state =
    Request (req_id: nat) (deadline: nat) (arrival: nat)
  | Processing (req_id: nat) (start_time: nat) 
  | Response (req_id: nat) (completion_time: nat)
  | Timeout (req_id: nat)

type_synonym 'state trace = "nat \<Rightarrow> 'state"

fun deadline_miss_trace :: "nat \<Rightarrow> real_time_state" where
  "deadline_miss_trace 0 = Request 1 3 0"
| "deadline_miss_trace (Suc 0) = Processing 1 1"  
| "deadline_miss_trace (Suc (Suc 0)) = Processing 1 2" 
| "deadline_miss_trace (Suc (Suc (Suc 0))) = Processing 1 3" 
| "deadline_miss_trace (Suc (Suc (Suc (Suc 0)))) = Response 1 4" 
| "deadline_miss_trace _ = Timeout 1"


(* Свойства для проверки дедлайнов *)
definition is_timeout :: "real_time_state \<Rightarrow> bool" where
  "is_timeout s = (case s of Timeout _ \<Rightarrow> True | _ \<Rightarrow> False)"

definition no_deadline_misses :: "real_time_state trace \<Rightarrow> bool" where
  "no_deadline_misses tr = (\<forall>i. \<not> is_timeout (tr i))"

(* Максимально простое определение *)
definition meets_deadline_simple :: "real_time_state \<Rightarrow> bool" where
  "meets_deadline_simple s = 
     (\<forall>req_id ct. s = Response req_id ct \<longrightarrow> ct \<le> 3)"


(* Проверим нарушение дедлайна *)
lemma deadline_miss_proven:
  "\<not> meets_deadline (deadline_miss_trace 4)"
  by simp

lemma deadline_miss_def_proven:
  "\<not> meets_deadline_def (deadline_miss_trace 4)"
  by (simp add: meets_deadline_def_def)

lemma timeout_occurs:
  "deadline_miss_trace 5 = Timeout 1"
  by simp


  
  


end