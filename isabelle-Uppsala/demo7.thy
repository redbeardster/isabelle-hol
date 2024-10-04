theory Demo1
imports Main
begin

section{*Logic*}

subsection{*Propositional logic*}

subsubsection{*Introduction rules*}


lemma "A \<longrightarrow> A"
proof (rule impI)
  assume a: "A"
  show "A" by(rule a)
qed

text{* \isakeyword{proof} *}

lemma "A \<longrightarrow> A"
proof
  assume a: A
  show A by(rule a)
qed

text{* \isakeyword{.} *}

lemma "A \<longrightarrow> A"
proof
  assume "A"
  show "A" .
qed

text{* \isakeyword{by} *}

lemma "A \<longrightarrow> A \<and> A"
proof
  assume "A"
  show "A \<and> A" by(rule conjI)
qed

text{* \isakeyword{..} *}

lemma "A \<longrightarrow> A \<and> A"
proof
  assume "A"
  show "A \<and> A" ..
qed


subsubsection{*Elimination rules*}


lemma "A \<and> B \<longrightarrow> B \<and> A"
proof
  assume AB: "A \<and> B"
  show "B \<and> A"
  proof (rule conjE[OF AB])  
    assume "A" "B"
    show ?thesis ..
  qed
qed


lemma "A \<and> B \<longrightarrow> B \<and> A"
proof
  assume AB: "A \<and> B"
  from AB show "B \<and> A"
  proof
    assume "A" "B"
    show ?thesis ..
  qed
qed

text{* @{text this}, \isakeyword{then}, \isakeyword{thus} *}

lemma "A \<and> B \<longrightarrow> B \<and> A"
proof
  assume "A \<and> B"
  from this show "B \<and> A"
  proof
    assume "A" "B"
    show ?thesis ..
  qed
qed


lemma "A \<and> B \<longrightarrow> B \<and> A"
proof
  assume ab: "A \<and> B"
  from ab have a: "A" ..
  from ab have b: "B" ..
  from b a show "B \<and> A" ..
qed



subsection{*More constructs*}


text{* \isakeyword{hence}, \isakeyword{with} *}

lemma "\<not> (A \<and> B) \<longrightarrow> \<not> A \<or> \<not> B"
proof
  assume n: "\<not> (A \<and> B)"
  show "\<not> A \<or> \<not> B"
  proof (rule ccontr)
    assume nn: "\<not> (\<not> A \<or> \<not> B)"
    have "\<not> A"
    proof
      assume "A"
      have "\<not> B"
      proof
        assume "B"
        have "A \<and> B" ..
        from n this show False ..
      qed
      hence "\<not> A \<or> \<not> B" ..
      with nn show False ..
    qed
    hence "\<not> A \<or> \<not> B" ..
    with nn show False ..
  qed
qed


text{* Interactive exercise: *}

lemma "A & (B | C) \<longrightarrow> (A & B) | (A & C)"
oops

subsection{*Avoiding duplication*}


lemma "A \<and> B \<Longrightarrow> B \<and> A"
proof
  assume "A \<and> B" thus "B" ..
next
  assume "A \<and> B" thus "A" ..
qed


lemma "large_A \<and> large_B \<Longrightarrow> large_B \<and> large_A"
      (is "?AB \<Longrightarrow> ?B \<and> ?A")
proof
  assume "?AB" thus "?B" ..
next
  assume "?AB" thus "?A" ..
qed


lemma assumes AB: "large_A \<and> large_B"
  shows "large_B \<and> large_A" (is "?B \<and> ?A")
proof
  from AB show "?B" ..
next
  from AB show "?A" ..
qed


lemma assumes AB: "large_A \<and> large_B"
  shows "large_B \<and> large_A" (is "?B \<and> ?A")
using AB
proof
  assume "?A" "?B" show ?thesis ..
qed


lemma assumes AB: "A \<or> B" shows "B \<or> A"
proof -     -- "-  =  do nothing"
  from AB show ?thesis
  proof
    assume A show ?thesis ..
  next
    assume B show ?thesis ..
  qed
qed


subsection{*Predicate calculus*}

text{* \isakeyword{fix} *}

lemma assumes P: "\<forall>x. P x" shows "\<forall>x. P(f x)"
proof                       
  fix a
  from P show "P(f a)" ..  
qed

text{* Proof text can only refer to global constants, free variables
in the lemma, and local names introduced via \isakeyword{fix} or
\isakeyword{obtain}. *}

lemma assumes Pf: "\<exists>x. P(f x)" shows "\<exists>y. P y"
proof -
  from Pf show ?thesis
  proof              
    fix x
    assume "P(f x)"
    show ?thesis ..  
  qed
qed


lemma assumes Pf: "\<exists>x. P(f x)" shows "\<exists>y. P y"
proof -
  from Pf obtain x where "P(f x)" ..
  thus "\<exists>y. P y" ..
qed


lemma assumes ex: "\<exists>x. \<forall>y. P x y" shows "\<forall>y. \<exists>x. P x y"
proof
  fix y
  from ex obtain x where "\<forall>y. P x y" ..
  hence "P x y" ..
  thus "\<exists>x. P x y" ..
qed


subsection{*Making bigger steps*}

theorem "\<exists>S. S \<notin> range (f :: 'a \<Rightarrow> 'a set)"
proof
  let ?S = "{x. x \<notin> f x}"
  show "?S \<notin> range f"
  proof
    assume "?S \<in> range f"
    then obtain y where fy: "?S = f y" ..
    show False
    proof cases
      assume "y \<in> ?S"
      with fy show False by blast
    next
      assume "y \<notin> ?S"
      with fy show False by blast
    qed
  qed
qed


theorem "\<exists>S. S \<notin> range (f :: 'a \<Rightarrow> 'a set)"
proof
  let ?S = "{x. x \<notin> f x}"
  show "?S \<notin> range f"
  proof
    assume "?S \<in> range f"
    then obtain y where fy: "?S = f y" ..
    show False
    proof cases
      assume "y \<in> ?S"
      hence "y \<notin> f y"   by simp
      hence "y \<notin> ?S"    by(simp add:fy)
      thus False         by contradiction
    next
      assume "y \<notin> ?S"
      hence "y \<in> f y"   by simp
      hence "y \<in> ?S"    by(simp add:fy)
      thus False         by contradiction
    qed
  qed
qed


text{* Interactive exercise: *}

lemma "EX x. P x \<longrightarrow> (ALL x. P x)"
oops


subsection{*Further refinements*}


subsubsection{*\isakeyword{obtain}*}


lemma assumes A: "\<exists>x y. P x y \<and> Q x y" shows "R"
proof -
  from A obtain x y where P: "P x y" and Q: "Q x y"  by blast
oops


subsubsection{*Combining proof styles*}


lemma "A \<longrightarrow> (A \<longrightarrow> B) \<longrightarrow> B"
proof
  assume "A"
  thus "(A \<longrightarrow>B) \<longrightarrow> B"
    apply -                 -- "make all incoming facts assumptions"
    apply(rule impI)
    apply(erule mp)
    apply assumption
    done
qed

end
