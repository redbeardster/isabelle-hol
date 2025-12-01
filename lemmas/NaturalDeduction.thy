theory NaturalDeduction
imports Main
begin

(* Объявим несколько простых пропозициональных переменных *)
notepad
begin
  fix A B C D :: bool
 assume "A" and "B"
  then have "A \<and> B" by (rule conjI)  (* \<and>I *)

  assume "A \<and> B"
  then have "A" by (rule conjE)      (* \<and>E₁ *)
  moreover from \<open>A \<and> B\<close> have "B" by (rule conjE)  (* \<and>E₂ *)
  
 assume "A \<longrightarrow> B" and "B \<longrightarrow> C"
  have "A \<longrightarrow> C"
  proof
    assume "A"                          (* [A]¹ *)
    with \<open>A \<longrightarrow> B\<close> have "B" by (rule mp)  (* \<rightarrow>E *)
    with \<open>B \<longrightarrow> C\<close> show "C" by (rule mp)  (* \<rightarrow>E *)
  qed           

 assume "A \<longrightarrow> B" and "A"
  then have "B" by (rule mp)  (* \<rightarrow>E *)

 assume "A"
  then have "A \<or> B" by (rule disjI1)  (* \<or>I₁ *)

  assume "B"  
  then have "A \<or> B" by (rule disjI2)  (* \<or>I₂ *)

(* 
 assume "A \<or> B"
  moreover
  { assume "A" have "C"  by (simp add: \<open>A \<and> B\<close> \<open>A \<longrightarrow> C\<close>) }  (* Первый случай *)
  moreover
  { assume "B" have "C"  by (simp add: \<open>A \<and> B\<close> \<open>A \<longrightarrow> C\<close>) }  (* Второй случай *)
  ultimately have "C" by blast    (* \<or>E *) *)

assume "A \<or> B" and "A \<longrightarrow> C" and "B \<longrightarrow> C"
  moreover
  { assume "A" 
    with \<open>A \<longrightarrow> C\<close> have "C" by (rule mp) }  (* Явное применение Modus Ponens *)
  moreover
  { assume "B" 
    with \<open>B \<longrightarrow> C\<close> have "C" by (rule mp) }  (* Явное применение Modus Ponens *)
  ultimately have "C" by blast


  assume "A \<or> \<not>A"
  have "A \<longrightarrow> A"
  proof
    assume "A"
    show "A" by fact
  qed

have "\<not>(A \<and> \<not>A)"
  proof
    assume "A \<and> \<not>A"
    then have "A" by (rule conjE)
    from \<open>A \<and> \<not>A\<close> have "\<not>A" by (rule conjE)
    with \<open>A\<close> show False by simp
  qed

 assume "A" and "\<not>A"
  then have False by simp

 assume "\<not>\<not>A"
  then have "A" by (rule notnotD)  (* DNE *)

 have "(A \<longrightarrow> B) \<and> (B \<longrightarrow> A) \<longleftrightarrow> (A \<longleftrightarrow> B)"
  proof
    assume "(A \<longrightarrow> B) \<and> (B \<longrightarrow> A)"
    then show "A \<longleftrightarrow> B"  by linarith
  next
    assume "A \<longleftrightarrow> B"
    then show "(A \<longrightarrow> B) \<and> (B \<longrightarrow> A)" by simp
  qed

  have "\<forall>x. P x \<longrightarrow> P x"
  proof
    fix x          (* Берем произвольный x *)
    show "P x \<longrightarrow> P x"
    proof
      assume "P x"
      show "P x" by fact
    qed
  qed

  assume "P a"
  then have "\<exists>x. P x" by (rule exI)  (* \<exists>I *)


end

lemma trans_imp: "(A \<longrightarrow> B) \<longrightarrow> (B \<longrightarrow> C) \<longrightarrow> (A \<longrightarrow> C)"
proof
  assume "A \<longrightarrow> B"
  show "(B \<longrightarrow> C) \<longrightarrow> (A \<longrightarrow> C)"
  proof
    assume "B \<longrightarrow> C"
    show "A \<longrightarrow> C"
    proof
      assume "A"
      with \<open>A \<longrightarrow> B\<close> have "B" by (rule mp)
      with \<open>B \<longrightarrow> C\<close> show "C" by (rule mp)
    qed
  qed
qed


end