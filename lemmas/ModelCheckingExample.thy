theory ModelCheckingExample
imports Main
begin

datatype SystemState = 
  Ready | Processing | Completed | Error

(* Правильное определение функции переходов *)
definition transitions :: "SystemState \<Rightarrow> SystemState set" where
  "transitions s = 
    (case s of
      Ready \<Rightarrow> {Processing}
    | Processing \<Rightarrow> {Completed, Error}
    | Completed \<Rightarrow> {Ready}
    | Error \<Rightarrow> {Error})"

(* Альтернативный способ через inductive *)
inductive transition :: "SystemState \<Rightarrow> SystemState \<Rightarrow> bool" (infix "\<rightarrow>" 50) where
  ready_trans: "Ready \<rightarrow> Processing"
| processing_trans1: "Processing \<rightarrow> Completed"
| processing_trans2: "Processing \<rightarrow> Error"  
| completed_trans: "Completed \<rightarrow> Ready"
| error_trans: "Error \<rightarrow> Error"

(* Предикат для eventually (в конце концов) *)
definition eventually_completes :: "SystemState \<Rightarrow> bool" where
  "eventually_completes s \<equiv> 
    \<exists>path n. path 0 = s \<and> path n = Completed \<and> 
            (\<forall>i<n. path (Suc i) \<in> transitions (path i))"


lemma model_check_completion:
  "eventually_completes Ready"
  unfolding eventually_completes_def
proof
  show "\<exists>n. (\<lambda>n::nat. case n of 0 \<Rightarrow> Ready | Suc 0  \<Rightarrow> Processing | _ \<Rightarrow> Completed) 0 = Ready \<and>
            (\<lambda>n::nat. case n of 0 \<Rightarrow> Ready | Suc 0 \<Rightarrow> Processing | _ \<Rightarrow> Completed) n = Completed \<and>
            (\<forall>i<n. (\<lambda>n::nat. case n of 0 \<Rightarrow> Ready | Suc 0 \<Rightarrow> Processing | _ \<Rightarrow> Completed) (Suc i) 
                 \<in> transitions ((\<lambda>n::nat. case n of 0 \<Rightarrow> Ready | Suc 0 \<Rightarrow> Processing | _ \<Rightarrow> Completed) i))"
  proof
    show "(\<lambda>n::nat. case n of 0 \<Rightarrow> Ready | Suc 0 \<Rightarrow> Processing | _ \<Rightarrow> Completed) 0 = Ready \<and>
          (\<lambda>n::nat. case n of 0 \<Rightarrow> Ready | Suc 0 \<Rightarrow> Processing | _ \<Rightarrow> Completed) 2 = Completed \<and>
          (\<forall>i<2. (\<lambda>n::nat. case n of 0 \<Rightarrow> Ready | Suc 0 \<Rightarrow> Processing | _ \<Rightarrow> Completed) (Suc i)
               \<in> transitions ((\<lambda>n::nat. case n of 0 \<Rightarrow> Ready | Suc 0 \<Rightarrow> Processing | _ \<Rightarrow> Completed) i))"
      unfolding transitions_def
    by (simp add: less_2_cases_iff)
  qed
qed

(* Более элегантный подход с inductive *)
inductive eventually :: "SystemState \<Rightarrow> bool" where
  completed: "eventually Completed"
| step: "s \<rightarrow> s' \<Longrightarrow> eventually s' \<Longrightarrow> eventually s"

lemma eventually_ready: "eventually Ready"
  apply (rule step[where s' = Processing])
   apply (rule ready_trans)
  apply (rule step[where s' = Completed])
   apply (rule processing_trans1)
  apply (rule completed)
  done

(* Проверка с использованием transitive closure *)
definition reaches :: "SystemState \<Rightarrow> SystemState \<Rightarrow> bool" where
  "reaches s s' \<equiv> \<exists>path n. path 0 = s \<and> path n = s' \<and> 
                          (\<forall>i<n. path (Suc i) \<in> transitions (path i))"

(* lemma ready_reaches_completed: "reaches Ready Completed"
  unfolding reaches_def
  using eventually_completes_def model_check_completion by presburger
 *)
lemma ready_reaches_completed:
  "reaches Ready Completed"
  unfolding reaches_def
proof
  (* Шаг 1: Предъявляем путь *)
  show "\<exists>n. (\<lambda>n. case n of 0 \<Rightarrow> Ready | Suc 0 \<Rightarrow> Processing | _ \<Rightarrow> Completed) 0 = Ready \<and>
            (\<lambda>n. case n of 0 \<Rightarrow> Ready | Suc 0 \<Rightarrow> Processing | _ \<Rightarrow> Completed) n = Completed \<and>
            (\<forall>i<n. (\<lambda>n. case n of 0 \<Rightarrow> Ready | Suc 0 \<Rightarrow> Processing | _ \<Rightarrow> Completed) (Suc i) 
                 \<in> transitions ((\<lambda>n. case n of 0 \<Rightarrow> Ready | Suc 0 \<Rightarrow> Processing | _ \<Rightarrow> Completed) i))"
  proof
    (* Шаг 2: Предъявляем n = 2 и проверяем условия *)
    show "(\<lambda>n. case n of 0 \<Rightarrow> Ready | Suc 0 \<Rightarrow> Processing | _ \<Rightarrow> Completed) 0 = Ready \<and>
          (\<lambda>n. case n of 0 \<Rightarrow> Ready | Suc 0 \<Rightarrow> Processing | _ \<Rightarrow> Completed) 2 = Completed \<and>
          (\<forall>i<2. (\<lambda>n. case n of 0 \<Rightarrow> Ready | Suc 0 \<Rightarrow> Processing | _ \<Rightarrow> Completed) (Suc i)
               \<in> transitions ((\<lambda>n. case n of 0 \<Rightarrow> Ready | Suc 0 \<Rightarrow> Processing | _ \<Rightarrow> Completed) i))"
      unfolding transitions_def
      by (auto simp: less_2_cases_iff)
  qed
qed



end