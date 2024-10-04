theory Demo2
imports Main
begin

subsection{*Inductive definition of finite sets*}

inductive_set Fin :: "'a set set" where
emptyI:  "{} : Fin" |
insertI: "A : Fin ==> insert a A : Fin"

subsection{*Inductive definition of the even numbers*}

inductive_set Ev :: "nat set" where
ZeroI: "0 : Ev" |
Add2I: "n : Ev ==> Suc(Suc n) : Ev"

text{* Using the introduction rules: *}
lemma "Suc(Suc(Suc(Suc 0))) \<in> Ev"
apply(rule Add2I)
apply(rule Add2I)
apply(rule ZeroI)
done

text{*A simple inductive proof: *}
lemma "n:Ev ==> n+n : Ev"
apply(erule Ev.induct)
 apply(simp)
 apply(rule Ev.ZeroI)
apply(simp)
apply(rule Ev.Add2I)
apply(rule Ev.Add2I)
apply(assumption)
done

text{* You can also use the rules for Ev as conditional simplification
rules. This can shorten proofs considerably.  \emph{Warning}:
conditional rules can lead to nontermination of the simplifier.  The
rules for Ev are OK because the premises are always `smaller' than the
conclusion. The list of rules for Ev is contained in Ev.intrs.  *}

declare Ev.intros[simp]

text{* A shorter proof: *}

lemma "n:Ev ==> n+n : Ev"
apply(erule Ev.induct)
apply(auto)
done

text{* Nice example, but overkill: don't need assumption @{prop"n \<in>
Ev"} because @{prop"n+n \<in> Ev"} is true for all @{text n}.

However, here we really need the assumptions: *}

lemma "[| m:Ev; n:Ev |] ==> m+n : Ev"
apply(erule Ev.induct)
apply(auto)
done

text{* An inductive proof of @{prop"1 \<notin> Ev"}: *}

lemma "n \<in> Ev \<Longrightarrow> n \<noteq> 1"
apply(erule Ev.induct)
apply(auto)
done

text{* The general case: *}
lemma "n \<in> Ev \<Longrightarrow> \<not>(\<exists>k. n = 2*k+1)"
apply(erule Ev.induct)
 apply(simp)
apply arith
done

subsection{* Proofs about finite sets *}

text{* Above we declared @{text Ev.intrs} as simplification rules.
Now we declare @{text Fin.intrs} as introduction rules (via attribute
``intro''). Then fast and blast use them automatically.*}

declare Fin.intros [intro]

lemma "[| A : Fin; B : Fin |] ==> A \<union> B : Fin";
apply(erule Fin.induct)
apply(auto)
done

lemma "[| A : Fin; B \<subseteq> A |] ==> B : Fin"
apply(erule Fin.induct)

txt{* The base case looks funny: why is the premise not @{prop"B \<subseteq> {}"}?
Because @{prop"B \<subseteq> A"} was not part of the conclusion we prove.
Relief: pull @{prop"B \<subseteq> A"} into the conclusion with the help of @{text"\<longrightarrow>"}.
*}
oops

lemma "A : Fin ==> B <= A --> B : Fin"
apply(erule Fin.induct)
apply(auto)
txt{* The same old problem: we need to quantify @{text B}. *}
oops

lemma "A : Fin ==> \<forall>B. B \<subseteq> A --> B : Fin"
apply(erule Fin.induct)
 thm subset_empty
 apply(simp add: subset_empty)
 apply(rule Fin.emptyI)
apply(rule allI)
apply(rule impI)
apply(simp add:subset_insert_iff split:split_if_asm)
apply(drule_tac A = B in insert_Diff)
apply(erule subst)
apply(blast)
done

subsection{*Inductive definition of AVL trees*}

datatype tree = Tip | Br tree tree

inductive_set AVL :: "(tree * nat)set" where
"(Tip,0) : AVL" |
"\<lbrakk> (t,m) : AVL; (u,n) : AVL; m=n | m = n+1 | n = m+1 \<rbrakk> \<Longrightarrow>
 (Br t u, max m n + 1) : AVL"

text{* We prove a lower bound for the number of internal nodes in an
AVL tree of height h. *}

fun fib1 :: "nat => nat" where
"fib1 0 = 0" |
"fib1 (Suc 0) = 1" |
"fib1 (Suc (Suc x)) = fib1 x + fib1 (Suc x) + 1"

lemma fib1_Suc: "fib1(Suc n) \<le> 2*fib1(n) + 1"
apply(induct n rule: fib1.induct)
apply auto
done

lemma "(t,h) : AVL \<Longrightarrow> fib1 h \<le> size t"
apply(induct rule:AVL.induct)
 apply simp
apply(erule disjE)
 apply simp
 apply(cut_tac n=n in fib1_Suc)
 apply arith
apply(erule disjE)
 apply (simp add:max_def)
apply (simp add:max_def)
done

end
