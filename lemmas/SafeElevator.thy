theory SafeElevator
  imports "HOL-TLA.TLA"
begin

datatype floor = Floor1 | Floor2 | Floor3 | Floor4 | Floor5
datatype direction = Up | Down | Stopped  
datatype door_state = Open | Closed

consts
  current_floor :: "floor stfun"
  current_dir :: "direction stfun"
  doors :: "door_state stfun"
  call_buttons :: "floor \<Rightarrow> bool stfun"
  destination_buttons :: "floor \<Rightarrow> bool stfun"

consts
  AtFloor1 :: temporal
  AtFloor2 :: temporal
  AtFloor3 :: temporal
  AtFloor4 :: temporal
  AtFloor5 :: temporal
  MovingUp :: temporal
  MovingDown :: temporal
  DoorsOpen :: temporal
  DoorsClosed :: temporal


(* Аксиомы поведения *)
axiomatization where
  (* 1. Лифт всегда на каком-то этаже *)
  always_on_floor: "\<turnstile> \<box>(AtFloor1 \<or> AtFloor2 \<or> AtFloor3 \<or> AtFloor4 \<or> AtFloor5)" and
  
  (* 2. Взаимоисключающие состояния *)
  exclusive_floors: "\<turnstile> \<not>(AtFloor1 \<and> AtFloor2) \<and> \<not>(AtFloor1 \<and> AtFloor3) " and
  exclusive_directions: "\<turnstile> \<not>(MovingUp \<and> MovingDown)" and
  exclusive_doors: "\<turnstile> \<not>(DoorsOpen \<and> DoorsClosed)" and
  
  (* 3. Безопасность движения *)
  safety_movement: "\<turnstile> \<box>((MovingUp \<or> MovingDown) \<longrightarrow> DoorsClosed)" and
  safety_doors: "\<turnstile> \<box>(DoorsOpen \<longrightarrow> (AtFloor1 \<or> AtFloor2 \<or> AtFloor3 \<or> AtFloor4 \<or> AtFloor5))"

(* 4. Живучесть *)
axiomatization where
  liveness_movement: "\<turnstile> (AtFloor1 \<longrightarrow> \<diamond>AtFloor2) \<and> (AtFloor2 \<longrightarrow> \<diamond>AtFloor1) \<and> ..." and
  liveness_doors: "\<turnstile> DoorsOpen \<leadsto> DoorsClosed \<and> DoorsClosed \<leadsto> DoorsOpen"


(* (* ===== ПРАВИЛЬНЫЕ ОПРЕДЕЛЕНИЯ ===== *)
definition AtFloor :: "floor \<Rightarrow> temporal" where
  "AtFloor f \<equiv> (\<lambda>\<sigma>. current_floor (\<sigma> 0) = f)"

definition MovingUp :: temporal where
  "MovingUp \<equiv> (\<lambda>\<sigma>. current_dir (\<sigma> 0) = Up)"

definition MovingDown :: temporal where  
  "MovingDown \<equiv> (\<lambda>\<sigma>. current_dir (\<sigma> 0) = Down)"

definition DoorsOpen :: temporal where
  "DoorsOpen \<equiv> (\<lambda>\<sigma>. doors (\<sigma> 0) = Open)"

definition DoorsClosed :: temporal where
  "DoorsClosed \<equiv> (\<lambda>\<sigma>. doors (\<sigma> 0) = Closed)"

definition CallButtonPressed :: "floor \<Rightarrow> temporal" where
  "CallButtonPressed f \<equiv> (\<lambda>\<sigma>. call_buttons f (\<sigma> 0))"
 *)
(* ===== ГАРАНТИИ БЕЗОПАСНОСТИ ===== *)

(* 1. Лифт всегда на каком-то этаже *)
theorem safety_bounds:
  "\<turnstile> \<box>(AtFloor Floor1 \<or> AtFloor Floor2 \<or> AtFloor Floor3 \<or> 
        AtFloor Floor4 \<or> AtFloor Floor5)"
  oops

(* 2. Двери открываются только на этажах *)
theorem safety_doors:
  "\<turnstile> \<box>(DoorsOpen \<longrightarrow> 
        (AtFloor Floor1 \<or> AtFloor Floor2 \<or> AtFloor Floor3 \<or>
         AtFloor Floor4 \<or> AtFloor Floor5))"
  oops

end