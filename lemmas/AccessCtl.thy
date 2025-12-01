theory AccessCtl
imports Main
begin

type_synonym Subject = string

definition domain_subtraction :: 
  "('a \<times> 'b) set \<Rightarrow> 'a set \<Rightarrow> ('a \<times> 'b) set" 
where
  "domain_subtraction R A = R - (A \<times> UNIV)"

definition z_domain_subtraction :: 
  "('a \<times> 'b) set \<Rightarrow> 'a set \<Rightarrow> ('a \<times> 'b) set"  (infix "\<Zndres>" 65)
where
  "R \<Zndres> A = domain_subtraction R A"

(* Пример использования *)
consts SParent :: "(Subject \<times> Subject) set"
consts delSubject :: "Subject"

lemma domain_subtraction_example:
  "SParent \<Zndres> {delSubject} = {(s, p) | s p. (s, p) \<in> SParent \<and> s \<noteq> delSubject}"
  unfolding z_domain_subtraction_def domain_subtraction_def
  by auto



end