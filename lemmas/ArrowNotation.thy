theory ArrowNotation
imports Main
begin

datatype State = READY | WORKING | DONE

consts 
  enter_working :: "State \<Rightarrow> State"  ("_ \<hookrightarrow>\<^sub>W" [1000] 1000)
  exit_done :: "State \<Rightarrow> State"      ("_ \<hookleftarrow>\<^sub>D" [1000] 1000)

defs enter_working_def: "x \<hookrightarrow>\<^sub>W \<equiv> (if x = READY then WORKING else x)"
defs exit_done_def: "x \<hookleftarrow>\<^sub>D \<equiv> (if x = WORKING then DONE else x)"


lemma workflow_example:
  "READY \<hookrightarrow>\<^sub>W \<hookleftarrow>\<^sub>D = DONE"
  by (simp add: enter_working_def exit_done_def)

end