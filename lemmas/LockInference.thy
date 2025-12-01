theory LockInference
  imports Main 
begin

(* Типы для выражений и команд *)
type_synonym Var = string
type_synonym Lock = string

datatype Expr = 
    Var Var
  | Int int
  | Plus Expr Expr

datatype Command =
    Skip
  | Assign Var Expr
  | Seq Command Command
  | If Expr Command Command
  | While Expr Command
  | Sync Lock Command
  | WithLock Lock Command

(* Конфигурации программы *)
type_synonym State = "Var \<Rightarrow> int"
type_synonym LockState = "Lock \<Rightarrow> bool" (* true = заблокирован *)

record Configuration =
  state :: State
  lock_state :: LockState
  command :: Command

(* Типы блокировок из статьи *)
datatype LockType =
  NoLock
| SimpleLock Lock
| LockSet "Lock set"

(* Контекст типов блокировок *)
type_synonym LockEnv = "Var \<Rightarrow> LockType"

definition empty_env :: "LockEnv" where
  "empty_env = (\<lambda>_. NoLock)"

(* Операция объединения типов блокировок *)
fun lub_lock :: "LockType \<Rightarrow> LockType \<Rightarrow> LockType" where
  "lub_lock NoLock l = l"
| "lub_lock l NoLock = l"  
| "lub_lock (SimpleLock l1) (SimpleLock l2) = 
    (if l1 = l2 then SimpleLock l1 else LockSet {l1, l2})"
| "lub_lock (SimpleLock l) (LockSet ls) = LockSet (insert l ls)"
| "lub_lock (LockSet ls) (SimpleLock l) = LockSet (insert l ls)"
| "lub_lock (LockSet ls1) (LockSet ls2) = LockSet (ls1 \<union> ls2)"

(* Вычисление выражений *)
primrec eval_expr :: "State \<Rightarrow> Expr \<Rightarrow> int" where
  "eval_expr s (Var x) = s x"
| "eval_expr s (Int n) = n"
| "eval_expr s (Plus e1 e2) = eval_expr s e1 + eval_expr s e2"

(* Функция для определения типа блокировки выражения *)
primrec infer_lock_type :: "LockEnv \<Rightarrow> Expr \<Rightarrow> LockType" where
  "infer_lock_type \<Gamma> (Var x) = \<Gamma> x"
| "infer_lock_type \<Gamma> (Int n) = NoLock"
| "infer_lock_type \<Gamma> (Plus e1 e2) = 
    lub_lock (infer_lock_type \<Gamma> e1) (infer_lock_type \<Gamma> e2)"

(* Определение совместимости конфигурации с environment *)
definition compatible_env :: "State \<Rightarrow> LockState \<Rightarrow> LockEnv \<Rightarrow> bool" where
  "compatible_env s ls \<Gamma> \<equiv> 
    \<forall>x. case \<Gamma> x of
          NoLock \<Rightarrow> True
        | SimpleLock l \<Rightarrow> ls l \<longrightarrow> s x \<noteq> 0             
        | LockSet ls_set \<Rightarrow> \<forall>l \<in> ls_set. ls l \<longrightarrow> s x \<noteq> 0"
                            
(* Определение well-formed конфигурации *)
definition well_formed_conf :: "Configuration \<Rightarrow> bool" where
  "well_formed_conf conf \<equiv> 
    compatible_env (state conf) (lock_state conf) 
      (case command conf of
         Sync l c \<Rightarrow> (\<lambda>x. if x = l then SimpleLock l else NoLock)
       | _ \<Rightarrow> empty_env)"

(* Транзитивное замыкание для small_step *)
inductive many_steps :: "Configuration \<Rightarrow> Configuration \<Rightarrow> bool"  ("_ \<rightarrow>* _" [50,50] 50) where
  ms_refl: "conf \<rightarrow>* conf"
| ms_step: "\<lbrakk> small_step conf conf'; conf' \<rightarrow>* conf'' \<rbrakk> \<Longrightarrow> conf \<rightarrow>* conf''"

(* Безопасность конфигурации *)
definition safe_configuration :: "Configuration \<Rightarrow> bool" where
  "safe_configuration conf \<equiv> 
    \<forall>l. lock_state conf l \<longrightarrow> 
        (\<exists>c. command conf = Sync l c \<or> command conf = WithLock l c) \<or>
        (\<forall>conf'. \<not> small_step conf conf')"  (* deadlock только в конечных состояниях *)

(* Функция fold для блокировок *)
primrec fold_sync :: "Lock set \<Rightarrow> Command \<Rightarrow> Command" where
  "fold_sync {} cmd = cmd"
| "fold_sync (insert l ls) cmd = Sync l (fold_sync ls cmd)"

(* Вычисление множества блокировок из LockType *)
primrec locks_of :: "LockType \<Rightarrow> Lock set" where
  "locks_of NoLock = {}"
| "locks_of (SimpleLock l) = {l}"
| "locks_of (LockSet ls) = ls"

(* Основная функция трансформации программы *)
primrec transform_program :: "Command \<Rightarrow> LockEnv \<Rightarrow> Command" where
  "transform_program Skip \<Gamma> = Skip"
| "transform_program (Assign x e) \<Gamma> = Assign x e"  
| "transform_program (Seq c1 c2) \<Gamma> = 
    Seq (transform_program c1 \<Gamma>) (transform_program c2 \<Gamma>)"
| "transform_program (If e c1 c2) \<Gamma> = 
    (let \<tau> = infer_lock_type \<Gamma> e;
         trans_c1 = transform_program c1 \<Gamma>;
         trans_c2 = transform_program c2 \<Gamma>;
         inner_cmd = If e trans_c1 trans_c2
     in case \<tau> of
          NoLock \<Rightarrow> inner_cmd
        | SimpleLock l \<Rightarrow> Sync l inner_cmd
        | LockSet ls \<Rightarrow> fold_sync ls inner_cmd)"
| "transform_program (While e c) \<Gamma> = 
    (let \<tau> = infer_lock_type \<Gamma> e;
         trans_c = transform_program c \<Gamma>;
         inner_cmd = While e trans_c
     in case \<tau> of
          NoLock \<Rightarrow> inner_cmd
        | SimpleLock l \<Rightarrow> Sync l inner_cmd  
        | LockSet ls \<Rightarrow> fold_sync ls inner_cmd)"
| "transform_program (Sync l c) \<Gamma> = Sync l (transform_program c \<Gamma>)"
| "transform_program (WithLock l c) \<Gamma> = WithLock l (transform_program c \<Gamma>)"

(* Правила вывода типов для выражений *)
inductive expr_typing :: "LockEnv \<Rightarrow> Expr \<Rightarrow> LockType \<Rightarrow> bool" where
  var_typing: "expr_typing \<Gamma> (Var x) (\<Gamma> x)"
| int_typing: "expr_typing \<Gamma> (Int n) NoLock"
| plus_typing: 
    "\<lbrakk> expr_typing \<Gamma> e1 \<tau>1; expr_typing \<Gamma> e2 \<tau>2 \<rbrakk> 
     \<Longrightarrow> expr_typing \<Gamma> (Plus e1 e2) (lub_lock \<tau>1 \<tau>2)"

(* Правила вывода для команд *)
inductive cmd_typing :: "LockEnv \<Rightarrow> Command \<Rightarrow> LockEnv \<Rightarrow> bool" where
  skip_typing: "cmd_typing \<Gamma> Skip \<Gamma>"
| assign_typing:
    "\<lbrakk> expr_typing \<Gamma> e \<tau> \<rbrakk> 
     \<Longrightarrow> cmd_typing \<Gamma> (Assign x e) (\<Gamma>(x := \<tau>))"
| seq_typing:
    "\<lbrakk> cmd_typing \<Gamma> c1 \<Gamma>'; cmd_typing \<Gamma>' c2 \<Gamma>'' \<rbrakk>
     \<Longrightarrow> cmd_typing \<Gamma> (Seq c1 c2) \<Gamma>''"
| if_typing:
    "\<lbrakk> expr_typing \<Gamma> e \<tau>; 
       cmd_typing \<Gamma> c1 \<Gamma>1; 
       cmd_typing \<Gamma> c2 \<Gamma>2;
       \<forall>x. lub_lock (\<Gamma>1 x) (\<Gamma>2 x) = \<Gamma>' x \<rbrakk>
     \<Longrightarrow> cmd_typing \<Gamma> (If e c1 c2) \<Gamma>'"
| while_typing:
    "\<lbrakk> expr_typing \<Gamma> e \<tau>; cmd_typing \<Gamma> c \<Gamma>' \<rbrakk>
     \<Longrightarrow> cmd_typing \<Gamma> (While e c) \<Gamma>"
| sync_typing:
    "\<lbrakk> cmd_typing \<Gamma> c \<Gamma>' \<rbrakk>
     \<Longrightarrow> cmd_typing \<Gamma> (Sync l c) \<Gamma>'"
| withlock_typing:
    "\<lbrakk> cmd_typing \<Gamma> c \<Gamma>' \<rbrakk>
     \<Longrightarrow> cmd_typing \<Gamma> (WithLock l c) \<Gamma>'"

(* Операционная семантика *)
inductive small_step :: "Configuration \<Rightarrow> Configuration \<Rightarrow> bool" where
  assign_step:
    "small_step 
      \<lparr> state = s, lock_state = ls, command = Assign x e \<rparr>
      \<lparr> state = s(x := eval_expr s e), lock_state = ls, command = Skip \<rparr>"
| seq_step1:
    "\<lbrakk> small_step 
        \<lparr> state = s, lock_state = ls, command = c1 \<rparr>
        \<lparr> state = s', lock_state = ls', command = c1' \<rparr> \<rbrakk>
     \<Longrightarrow> small_step 
        \<lparr> state = s, lock_state = ls, command = Seq c1 c2 \<rparr>
        \<lparr> state = s', lock_state = ls', command = Seq c1' c2 \<rparr>"
| seq_step2:
    "small_step 
      \<lparr> state = s, lock_state = ls, command = Seq Skip c2 \<rparr>
      \<lparr> state = s, lock_state = ls, command = c2 \<rparr>"
| if_true:
    "eval_expr s e \<noteq> 0 \<Longrightarrow>
     small_step 
      \<lparr> state = s, lock_state = ls, command = If e c1 c2 \<rparr>
      \<lparr> state = s, lock_state = ls, command = c1 \<rparr>"
| if_false:
    "eval_expr s e = 0 \<Longrightarrow>
     small_step 
      \<lparr> state = s, lock_state = ls, command = If e c1 c2 \<rparr>
      \<lparr> state = s, lock_state = ls, command = c2 \<rparr>"
| while_step:
    "small_step 
      \<lparr> state = s, lock_state = ls, command = While e c \<rparr>
      \<lparr> state = s, lock_state = ls, command = If e (Seq c (While e c)) Skip \<rparr>"
| sync_step:
    "\<not> ls l \<Longrightarrow>
     small_step 
      \<lparr> state = s, lock_state = ls, command = Sync l c \<rparr>
      \<lparr> state = s, lock_state = ls(l := True), command = c \<rparr>"
| withlock_step:
    "ls l \<Longrightarrow>
     small_step 
      \<lparr> state = s, lock_state = ls, command = WithLock l c \<rparr>
      \<lparr> state = s, lock_state = ls(l := False), command = c \<rparr>"

(* Леммы о свойствах функций *)

lemma infer_lock_type_correct:
  "expr_typing \<Gamma> e \<tau> \<longleftrightarrow> infer_lock_type \<Gamma> e = \<tau>"
proof
  assume "expr_typing \<Gamma> e \<tau>"
  thus "infer_lock_type \<Gamma> e = \<tau>"
    by (induction rule: expr_typing.induct) auto
next
  assume "infer_lock_type \<Gamma> e = \<tau>"
  thus "expr_typing \<Gamma> e \<tau>"
    by (induction e arbitrary: \<tau>) 
       (auto intro: expr_typing.intros simp: empty_env_def)
qed

lemma lub_lock_commutative:
  "lub_lock \<tau>1 \<tau>2 = lub_lock \<tau>2 \<tau>1"
  by (induction \<tau>1 \<tau>2 rule: lub_lock.induct) auto

lemma lub_lock_associative:
  "lub_lock (lub_lock \<tau>1 \<tau>2) \<tau>3 = lub_lock \<tau>1 (lub_lock \<tau>2 \<tau>3)"
  apply (induction \<tau>1 \<tau>2 rule: lub_lock.induct)
  apply auto
  apply (metis insert_commute lub_lock.simps(4) lub_lock.simps(5) lub_lock.simps(6))
  done

lemma locks_of_lub_lock:
  "locks_of (lub_lock \<tau>1 \<tau>2) = locks_of \<tau>1 \<union> locks_of \<tau>2"
  by (induction \<tau>1 \<tau>2 rule: lub_lock.induct) auto

end