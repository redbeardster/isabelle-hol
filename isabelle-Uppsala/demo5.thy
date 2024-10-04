theory Demo2
imports Main
begin

section{* Predicate logic *}

text{* A warming up exercise: propositional logic. *}
lemma "A \<and> (B \<or> C) \<Longrightarrow> A \<and> B \<or> C"
oops

subsection{* Quantifier reasoning *}

text{* A successful proof: *}
lemma "\<forall>x. \<exists>y. x = y"
apply(rule allI)
apply(rule exI)
apply(rule refl)
done

text{* An unsuccessful proof: *}
lemma "\<exists>y. \<forall>x. x = y"
apply(rule exI)
apply(rule allI)
(* Does not work:
apply(rule refl)
*)
oops

text{* Intro and elim resoning: *}
lemma "\<exists>y. \<forall>x. P x y \<Longrightarrow> \<forall>x. \<exists>y. P x y"
(* the safe rules first: *)
apply(rule allI)
apply(erule exE)
(* now the unsafe ones: *)
apply(rule_tac x=y in exI)
apply(erule_tac x=x in allE)
apply(assumption)
done

text{* What happens if an unsafe rule is tried too early: *}
lemma "\<exists>y. \<forall>x. P x y \<Longrightarrow> \<forall>x. \<exists>y. P x y"
apply(rule allI)
apply(rule exI)
apply(erule exE)
apply(erule allE)
(* Fails now:
apply(assumption)
*)
oops

text{* Principle: First the safe rules (allI, exE: they generate
parameters), then the unsafe rules (allE, exI: they generate
unknowns). *}


subsection{* Proof methods*}

subsubsection{* Renaming *}

text{* Renaming parameters: *}
lemma "\<And>x y z. P x y z"
apply(rename_tac a b)
oops

text{* Choosing your own names for convenience: *}
lemma "xs \<noteq> [] \<longrightarrow> P xs"
apply(induct_tac xs)
apply simp
apply(rename_tac elem rest)
oops;

text{* Rename to avoid names chosen by Isabelle: *}
lemma "ALL x. P x \<Longrightarrow> ALL x. ALL x. P x"
apply(rule allI)
apply(rule allI)
apply(rename_tac X)
apply(erule_tac x=X in allE)
apply assumption
done

subsubsection{*More instantiation examples*}

text{* Instantiating allE: *}
lemma "ALL xs. xs@ys = zs \<Longrightarrow> ys=zs"
thm allE
apply(erule_tac x = "[]" in allE)
apply(simp)
done

text{* Instantiating exI: *}
lemma "EX n. P(f n) \<Longrightarrow> EX m. P m"
apply(erule exE)
thm exI
apply(rule_tac x = "f n" in exI)
apply assumption
done

text{* Instantiation removes ambiguity: *}
lemma "\<lbrakk> A & B; C & D \<rbrakk> \<Longrightarrow> D"
thm conjE
apply(erule_tac P = "C" in conjE)
(* without instantiation, the wrong one is chosen (first) *)
apply assumption
done

subsubsection{* Forward reasoning *}

lemma "A \<and> B \<Longrightarrow> \<not> \<not> A"
thm conjunct1
apply(drule conjunct1)
apply blast
done

thm dvd_add dvd_refl
thm dvd_add[OF dvd_refl dvd_refl]

subsubsection{* Clarification *}

lemma "\<forall>x y. P x y & Q x y & R x y"
apply(intro allI conjI)
oops

lemma "\<forall>x y. P x y & Q x y & R x y"
apply(clarify)
oops

lemma "\<forall>x y. x = 5 \<and> y = 7 \<and> y < z \<longrightarrow> P(x+y::nat)"
apply(clarsimp)
oops

end
