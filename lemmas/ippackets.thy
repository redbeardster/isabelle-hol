theory ippackets
imports Main
begin

 
datatype tcp_state = 
    CLOSED | LISTEN | SYN_RCVD | SYN_SENT 
  | ESTABLISHED | FIN_WAIT_1 | FIN_WAIT_2 | CLOSING 
  | TIME_WAIT | CLOSE_WAIT | LAST_ACK

datatype tcp_event = 
    PASSIVE_OPEN | ACTIVE_OPEN | SYN | ACK | FIN | RST | TIMEOUT
 
 
fun tcp_transition :: "tcp_state \<Rightarrow> tcp_event \<Rightarrow> tcp_state" where
  "tcp_transition CLOSED PASSIVE_OPEN = LISTEN"
| "tcp_transition CLOSED ACTIVE_OPEN = SYN_SENT"
| "tcp_transition LISTEN SYN = SYN_RCVD"
| "tcp_transition LISTEN CLOSE = CLOSED"
| "tcp_transition SYN_RCVD ACK = ESTABLISHED"
| "tcp_transition SYN_RCVD FIN = CLOSE_WAIT"
| "tcp_transition SYN_SENT SYN = SYN_RCVD"
| "tcp_transition SYN_SENT ACK = ESTABLISHED"
| "tcp_transition ESTABLISHED FIN = FIN_WAIT_1"
| "tcp_transition FIN_WAIT_1 ACK = FIN_WAIT_2"
| "tcp_transition FIN_WAIT_2 FIN = TIME_WAIT"
| "tcp_transition CLOSE_WAIT FIN = LAST_ACK"
| "tcp_transition LAST_ACK ACK = CLOSED"
| "tcp_transition _ RST = CLOSED"
| "tcp_transition _ TIMEOUT = CLOSED"
| "tcp_transition state _ = state"

(* Тестируем - теперь точно работает! *)
value "tcp_transition CLOSED PASSIVE_OPEN"  (* LISTEN *)
value "tcp_transition LISTEN SYN"           (* SYN_RCVD *)
value "tcp_transition ESTABLISHED RST"      (* CLOSED *)
value "tcp_transition SYN_SENT ACTIVE_OPEN" (* SYN_SENT *)
value "tcp_transition FIN_WAIT_1 SYN"       (* FIN_WAIT_1 *)

(* Проверим все состояния с RST *)
value "map (\<lambda>s. tcp_transition s RST) 
           [CLOSED, LISTEN, SYN_RCVD, SYN_SENT, ESTABLISHED, 
            FIN_WAIT_1, FIN_WAIT_2, CLOSING, TIME_WAIT, CLOSE_WAIT, LAST_ACK]"
(* Все должны вернуть CLOSED *)

(* Проверим неизменяемые состояния *)
value "tcp_transition ESTABLISHED SYN"      (* ESTABLISHED *)
value "tcp_transition FIN_WAIT_1 PASSIVE_OPEN" (* FIN_WAIT_1 *)




end