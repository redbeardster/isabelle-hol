theory ElevatorTLAModel
  imports "HOL-TLA.TLA"
begin

(* ===== ОСНОВНАЯ КОДИРОВКА TLA ===== *)

(* definition lift_state :: "(state \<Rightarrow> bool) \<Rightarrow> temporal" where
  "lift_state P = (\<lambda>b. P (b 0))"

(* Вспомогательные определения для удобства *)
notation lift_state ("\<up>")

(* ===== ТИПЫ ДАННЫХ ===== *)
datatype floor = Floor1 | Floor2 | Floor3 | Floor4 | Floor5
datatype direction = Up | Down | Stopped  
datatype door_state = Open | Closed

(* ===== STATE VARIABLES ===== *)
consts
  current_floor :: "state \<Rightarrow> floor"
  current_dir :: "state \<Rightarrow> direction"
  doors :: "state \<Rightarrow> door_state"
  call_buttons :: "state \<Rightarrow> floor \<Rightarrow> bool"
  destination_buttons :: "state \<Rightarrow> floor \<Rightarrow> bool"

(* ===== TEMPORAL PREDICATES через lift_state ===== *)
definition AtFloor :: "floor \<Rightarrow> temporal" where
  "AtFloor f = \<up>(\<lambda>s. current_floor s = f)"

definition MovingUp :: temporal where
  "MovingUp = \<up>(\<lambda>s. current_dir s = Up)"

definition MovingDown :: temporal where  
  "MovingDown = \<up>(\<lambda>s. current_dir s = Down)"

definition DoorsOpen :: temporal where
  "DoorsOpen = \<up>(\<lambda>s. doors s = Open)"

definition DoorsClosed :: temporal where
  "DoorsClosed = \<up>(\<lambda>s. doors s = Closed)"

definition CallButtonPressed :: "floor \<Rightarrow> temporal" where
  "CallButtonPressed f = \<up>(\<lambda>s. call_buttons s f)"

(* ===== ПРОВЕРЯЕМ РАБОТОСПОСОБНОСТЬ ===== *)

(* Простая лемма для проверки *)
lemma test_lift_state:
  shows "AtFloor Floor1 = (\<lambda>b. current_floor (b 0) = Floor1)"
  unfolding AtFloor_def lift_state_def
  by simp

(* ===== АКСИОМЫ СИСТЕМЫ ===== *)
axiomatization where
  (* 1. Лифт всегда на каком-то этаже *)
  floor_existence: "\<turnstile> \<box>(AtFloor Floor1 \<or> AtFloor Floor2 \<or> AtFloor Floor3 \<or> 
                      AtFloor Floor4 \<or> AtFloor Floor5)" and
  
  (* 2. Безопасность движения *)
  safety_movement: "\<turnstile> \<box>((MovingUp \<or> MovingDown) \<longrightarrow> DoorsClosed)" and
  
  (* 3. Безопасность дверей *)
  safety_doors: "\<turnstile> \<box>(DoorsOpen \<longrightarrow> 
                   (AtFloor Floor1 \<or> AtFloor Floor2 \<or> AtFloor Floor3 \<or>
                    AtFloor Floor4 \<or> AtFloor Floor5))"

(* ===== ТЕПЕРЬ МОЖЕМ ФОРМУЛИРОВАТЬ ТЕОРЕМЫ ===== *)

theorem elevator_safety:
  "\<turnstile> \<box>((MovingUp \<or> MovingDown) \<longrightarrow> DoorsClosed \<and> 
        (AtFloor Floor1 \<or> AtFloor Floor2 \<or> AtFloor Floor3 \<or>
         AtFloor Floor4 \<or> AtFloor Floor5))"
  using safety_movement safety_doors floor_existence
  by tla
 *)

datatype floor = Floor1 | Floor2 | Floor3 | Floor4 | Floor5

datatype direction = Up | Down | Stopped  
datatype door_state = Open | Closed

consts
  current_floor :: "floor stfun"
  current_dir :: "direction stfun"
  doors :: "door_state stfun"

(* Init ожидает state \<Rightarrow> bool, а не bool *)
definition AtFloor :: "floor \<Rightarrow> temporal" where
  "AtFloor f = Init (\<lambda>s. current_floor s = f)"



(* Проверяем *)
lemma test_at_floor:
  "AtFloor f = (\<lambda>s. current_floor (first s) = f)"
  unfolding AtFloor_def Init_def first_def
  by auto



end