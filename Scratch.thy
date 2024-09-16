theory Scratch 
  imports Main
begin

(*
datatype PRSObject = Rock | Scissors | Paper

fun beats :: " PRSObject \<Rightarrow>  PRSObject" 
  where 
 "beats Paper =  Rock" | 
 "beats Rock = Scissors" | 
 "beats Scissors = Paper" 

value "beats Paper"

fun beaten :: "PRSObject \<Rightarrow> PRSObject" where 
  "beaten Paper = Scissors" | 
  "beaten Rock = Paper" |
  "beaten Scissors = Rock"

lemma "beats (beaten x :: PRSObject) = x"
  by (metis PRSObject.distinct(1) PRSObject.distinct(3) PRSObject.distinct(5) beaten.elims beats.elims)


typedef Clock_value = "{0::nat,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23}"
  by blast


fun length :: "'a list \<Rightarrow> nat " where 
  "length [] = 0"
  | "length (x#xs) =  1 + length xs"

value "length [1::nat,2,3]"



type_synonym T = nat

axiomatization
  N  where
  NgreaterZero:  "1\<le>(N::nat)"

typedef proc = "{(1::nat).. N}"
  using NgreaterZero by auto

definition
  proc :: "nat set" where
  "proc \<equiv> {(1::nat)..N}"

definition
  procs :: "proc set" where
  "procs \<equiv> {i::proc. True}"

abbreviation "PID \<equiv> Rep_proc"

record 'ps conf =
P_State :: "proc \<Rightarrow> 'ps"

record Message =
  snd :: proc
  rcv :: proc

record MsgStatus =
  outgoing :: nat
  transit :: nat
  received :: nat
*)

datatype 'msg event = Broadcast 'msg | Deliver 'msg

consts always_10 :: "'a \<Rightarrow> nat"

axiomatization  where
Always_10:
  "\<forall>x. always_10 x = 10"

lemma "\<forall>x. always_10 x \<le> 20"
  by (simp add: Always_10) 



end


