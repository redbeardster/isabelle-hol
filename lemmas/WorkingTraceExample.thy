theory WorkingTraceExample
imports Main
begin

datatype system_state = 
    INITIAL
  | PROCESSING nat 
  | COMPLETED
  | ERROR string
  | HEALTHY
  | DEGRADED
  | RECOVERING

datatype tl_formula = 
    Prop "system_state \<Rightarrow> bool"    
  | Not tl_formula                 
  | And tl_formula tl_formula      
  | Or tl_formula tl_formula       
  | Always tl_formula              
  | Eventually tl_formula          
  | Implies tl_formula tl_formula  
  | Next tl_formula                
  | Until tl_formula tl_formula    

type_synonym 'state trace = "nat \<Rightarrow> 'state"

definition suffix :: "nat \<Rightarrow> 'state trace \<Rightarrow> 'state trace" where
  "suffix i tr = (\<lambda>j. tr (i + j))"

primrec eval_tl :: "tl_formula \<Rightarrow> system_state trace \<Rightarrow> bool" where
  "eval_tl (Prop P) tr = P (tr 0)"
| "eval_tl (Not \<phi>) tr = (\<not> eval_tl \<phi> tr)"
| "eval_tl (And \<phi> \<psi>) tr = (eval_tl \<phi> tr \<and> eval_tl \<psi> tr)"
| "eval_tl (Or \<phi> \<psi>) tr = (eval_tl \<phi> tr \<or> eval_tl \<psi> tr)"
| "eval_tl (Always \<phi>) tr = (\<forall>i. eval_tl \<phi> (suffix i tr))"
| "eval_tl (Eventually \<phi>) tr = (\<exists>i. eval_tl \<phi> (suffix i tr))"
| "eval_tl (Implies \<phi> \<psi>) tr = (eval_tl \<phi> tr \<longrightarrow> eval_tl \<psi> tr)"
| "eval_tl (Next \<phi>) tr = eval_tl \<phi> (suffix 1 tr)"
| "eval_tl (Until \<phi> \<psi>) tr = 
     (\<exists>i. eval_tl \<psi> (suffix i tr) \<and> (\<forall>j<i. eval_tl \<phi> (suffix j tr)))"

 definition test_trace :: "system_state trace" where
  "test_trace i = (case i of
      0 \<Rightarrow> HEALTHY
    | Suc 0 \<Rightarrow> DEGRADED
    | Suc (Suc 0) \<Rightarrow> RECOVERING
    | _ \<Rightarrow> HEALTHY)"
 

(* definition test_trace :: "system_state trace" where
  "test_trace = (\<lambda>i. 
    if i = 0 then HEALTHY
    else if i = 1 then DEGRADED  
    else if i = 2 then RECOVERING
    else HEALTHY
  )"
 *)
(* Определяем свойства *)
definition is_healthy :: "system_state \<Rightarrow> bool" where
  "is_healthy s = (s = HEALTHY)"

definition is_degraded :: "system_state \<Rightarrow> bool" where
  "is_degraded s = (s = DEGRADED)"

definition is_recovering :: "system_state \<Rightarrow> bool" where
  "is_recovering s = (s = RECOVERING)"

(* Тестируем *)
lemma test_healthy_at_0:
  "eval_tl (Prop is_healthy) test_trace"
  unfolding test_trace_def is_healthy_def suffix_def
  by simp

lemma test_eventually_degraded:
  "eval_tl (Eventually (Prop is_degraded)) test_trace"
  unfolding test_trace_def is_degraded_def suffix_def
 (*   by (smt (verit) add_cancel_left_right eval_tl.simps(1) eval_tl.simps(6) one_neq_zero suffix_def) *) 
  by (metis (mono_tags, lifting) add.right_neutral eval_tl.simps(1) eval_tl.simps(6) old.nat.simps(4) old.nat.simps(5) suffix_def)

lemma test_always_eventually_healthy:
  "eval_tl (Always (Eventually (Prop is_healthy))) test_trace"
  unfolding test_trace_def is_healthy_def suffix_def
(* proof (intro allI)
  fix i
  show "\<exists>j. test_trace (i + j) = HEALTHY"
    apply (cases "i mod 3")
    apply (rule exI[where x="0"]) apply simp
    apply (rule exI[where x="(3 - i mod 3) mod 3"]) apply simp
    apply (rule exI[where x="(3 - i mod 3) mod 3"]) apply simp
    done
qed *)


 (*  by (smt (verit, best) Nat.add_0_right add_Suc_shift add_eq_self_zero eval_tl.simps(1) eval_tl.simps(5) eval_tl.simps(6) plus_1_eq_Suc suffix_def) *)
  using system_state.exhaust by blast



end