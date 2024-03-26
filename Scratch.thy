
theory Scratch 
  imports Main
begin

datatype PRSObject = Rock | Scissors | Paper

fun beats :: " PRSObject \<Rightarrow>  PRSObject" 
  where 
 "beats Paper =  Rock" | 
 "beats Rock = Scissors" | 
 "beats  Scissors = Paper" 

value "beats Paper"

fun beaten :: "PRSObject \<Rightarrow> PRSObject" where 
  "beaten Paper = Scissors" | 
  "beaten Rock = Paper" |
  "beaten Scissors = Rock"

lemma "beats (beaten x :: PRSObject) = x"
  by (metis PRSObject.distinct(1) PRSObject.distinct(3) PRSObject.distinct(5) beaten.elims beats.elims)


lemma "(A \<and> B) \<and> C \<equiv> A \<and> (B \<and> C)" 
  by simp

lemma "((A \<longrightarrow> B) \<and> (B \<longrightarrow> C) \<longrightarrow> (A \<longrightarrow> C) )"
  by simp

end

