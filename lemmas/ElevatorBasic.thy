theory ElevatorBasic
  imports "HOL-TLA.TLA"
begin

(* ===== ОСНОВНЫЕ ТИПЫ И КОНСТАНТЫ ===== *)

(* Этажи: от 1 до N *)
typedecl floor
consts N :: floor  (* Верхний этаж *)

(* Направления движения *)
datatype direction = Up | Down | Stopped

(* Состояние лифта *)
consts
  current_floor :: "floor stfun"
  current_dir   :: "direction stfun"  
  buttons       :: "floor \<Rightarrow> bool stfun"  (* Нажатые кнопки *)

(* ===== ВСПОМОГАТЕЛЬНЫЕ ОПРЕДЕЛЕНИЯ ===== *)

(* Лифт на этаже f *)
definition AtFloor :: "floor \<Rightarrow> temporal" where
  "AtFloor f \<equiv> #(current_floor = f)"

(* Кнопка на этаже f нажата *)
definition ButtonPressed :: "floor \<Rightarrow> temporal" where
  "ButtonPressed f \<equiv> #(buttons f)"

(* Есть необслуженные вызовы *)
definition HasPendingRequests :: temporal where
  "HasPendingRequests \<equiv> \<exists>\<exists> f. ButtonPressed f"

(* Лифт движется в правильном направлении к этажу *)
definition MovingToward :: "floor \<Rightarrow> temporal" where
  "MovingToward f \<equiv> 
    (current_dir = Up \<and> current_floor < f) \<or>
    (current_dir = Down \<and> current_floor > f)"

(* ===== ДЕЙСТВИЯ ЛИФТА ===== *)

(* Движение вверх *)
definition MoveUp :: action where
  "MoveUp \<equiv> current_floor < N \<and> current_floor$ = current_floor + 1"

(* Движение вниз *)
definition MoveDown :: action where  
  "MoveDown \<equiv> current_floor > 1 \<and> current_floor$ = current_floor - 1"

(* Остановка на этаже *)
definition StopAtFloor :: "floor \<Rightarrow> action" where
  "StopAtFloor f \<equiv> current_floor = f \<and> buttons f \<and> buttons$ f = False"

(* ===== ОСНОВНЫЕ СВОЙСТВА ===== *)

(* Безопасность: лифт не выходит за границы *)
theorem safety_bounds:
  "\<turnstile> \<box>(1 \<le> current_floor \<and> current_floor \<le> N)"
  oops

(* Живучесть: каждый вызов eventually будет обслужен *)
theorem liveness_requests:
  "\<turnstile> ButtonPressed f \<leadsto> \<not>ButtonPressed f"
  oops

(* Прогресс: лифт всегда движется к вызовам *)
theorem progress:
  "\<turnstile> HasPendingRequests \<longrightarrow> \<diamond>(\<exists>\<exists> f. ButtonPressed f \<and> AtFloor f)"
  oops

end