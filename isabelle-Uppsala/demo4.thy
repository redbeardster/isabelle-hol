theory Demo1
imports Main
begin

section{* Propositional logic *}


subsection{* Basic rules *}

text{* \<and> *}
thm conjI conjE conjunct1 conjunct2

text{* \<or> *}
thm disjI1 disjI2 disjE

text{* \<longrightarrow> *}
thm impI impE mp

text{* = (iff) *}
thm iffI iffE iffD1 iffD2

text{* \<not> *}
thm notI notE

text{* Contradictions *}
thm FalseE ccontr classical


subsection{* Examples *}

text{* a simple backward step: *}
lemma "A \<and> B"
apply(rule conjI)
oops

text{* a simple backward proof: *}
lemma "B \<and> A \<longrightarrow> A \<and> B"
apply(rule impI)
apply(rule conjI)
 apply(rule conjE)
  apply(assumption)
 apply(assumption)
apply(rule conjE)
 apply(assumption)
apply(assumption)
done

text{* a shorter version: *}
lemma "B \<and> A \<longrightarrow> A \<and> B"
apply(rule impI)
apply(rule conjE)
 apply(assumption)
apply(rule conjI)
 apply(assumption)
apply(assumption)
done

text{* Elimination rules should be applied with erule: *}
lemma "B \<and> A \<longrightarrow> A \<and> B"
apply(rule impI)
apply(erule conjE)
apply(rule conjI)
 apply(assumption)
apply(assumption)
done

(* For interactive proofs developed together with the students: *)

lemma "A \<or> B \<longrightarrow> B \<or> A"
oops

lemma "\<lbrakk> A \<longrightarrow> B; B \<longrightarrow> C \<rbrakk> \<Longrightarrow> A \<longrightarrow> C"
oops

lemma "\<not>A \<or> \<not>B \<Longrightarrow> \<not>(A \<and> B)"
oops

text{* This one is tricky! *}
lemma "\<not>(A \<and> B) \<Longrightarrow> \<not>A \<or> \<not>B"
oops


subsection{* Further useful techniques *}

text{* Of course, simple proofs are performed automatically: *}
lemma "B \<and> A \<longrightarrow> A \<and> B"
apply(blast)
done
text{* Similar to "blast": "fast" *}

text{* How to convert @{text"\<longrightarrow>"} back to @{text"\<Longrightarrow>"} automatically: *}
lemma [rule_format]: "A \<and> A \<longrightarrow> A"
apply blast
done

text{* Explicit case distinctions: *}
lemma "((P \<longrightarrow> Q) \<longrightarrow> P) \<longrightarrow> P"
apply(case_tac P)
 apply(simp)
apply(simp)
done

text{* Explicit backtracking: *}
lemma "\<lbrakk> P \<and> Q; A \<and> B \<rbrakk> \<Longrightarrow> A"
apply(erule conjE)
back
apply(assumption)
done
text{* UGLY! NOT ALLOWED IN FINAL SOLUTION! *}

text{* Implict backtracking: *}
lemma "\<lbrakk> P \<and> Q; A \<and> B \<rbrakk> \<Longrightarrow> A"
apply(erule conjE, assumption)
done

end
