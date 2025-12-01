theory SimpleElevatorOriginal
  imports "HOL-TLA.TLA"
begin

datatype floor = Floor1 | Floor2 | Floor3

consts
  current_floor :: "floor stfun"
  call_buttons :: "floor \<Rightarrow> bool stfun"

(* В TLA действия обычно определяются через примитивы *)
consts
  MoveUp :: action
  MoveDown :: action
  Stop :: action
  Request :: "floor \<Rightarrow> action"

axiomatization where
  (* Движение вверх *)
  move_up_effect: "\<turnstile> MoveUp \<longrightarrow> 
    (current_floor = Floor1 \<longrightarrow> current_floor$ = Floor2) \<and>
    (current_floor = Floor2 \<longrightarrow> current_floor$ = Floor3)" and
    
  (* Движение вниз *)
  move_down_effect: "\<turnstile> MoveDown \<longrightarrow>
    (current_floor = Floor3 \<longrightarrow> current_floor$ = Floor2) \<and>  
    (current_floor = Floor2 \<longrightarrow> current_floor$ = Floor1)" and
    
  (* Остановка - сбрасывает кнопку текущего этажа *)
  stop_effect: "\<turnstile> Stop \<longrightarrow>
    (call_buttons current_floor$ = False) \<and>
    (current_floor$ = current_floor)" and
    
  (* Запрос лифта *)
  request_effect: "\<turnstile> Request f \<longrightarrow> call_buttons f$ = True"

end