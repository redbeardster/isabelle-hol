theory Demo2
imports Main
begin

section{*Case distinction and induction*}


subsection{*Case distinction*}


lemma "\<not> A \<or> A"
proof cases
  assume "A" thus ?thesis ..
next
  assume "\<not> A" thus ?thesis ..
qed


lemma "\<not> A \<or> A"
proof (cases "A")
  case True thus ?thesis ..
next
  case False thus ?thesis ..
qed


declare length_tl[simp del]
lemma "length(tl xs) = length xs - 1"
proof (cases xs)
  case Nil thus ?thesis by simp
next
  case Cons thus ?thesis by simp
qed


subsection{*Structural induction*}


lemma "(\<Sum>i\<le>n. i) = n*(n+1::nat) div 2"
by (induct n, simp_all)


lemma "(\<Sum>i\<le>n. i) = n*(n+1::nat) div 2" (is "?P n")
proof (induct n)
  show "?P 0" by simp
next
  fix n assume "?P n"
  thus "?P(Suc n)" by simp
qed


lemma "(\<Sum>i\<le>n. i) = n*(n+1::nat) div 2"
proof (induct n)
  case 0 show ?case by simp
next
  case Suc thus ?case by simp
qed


lemma fixes n::nat shows "n < n*n + 1"
proof (induct n)
  case 0 show ?case by simp
next
  case (Suc i) thus "Suc i < Suc i * Suc i + 1" by simp
qed


subsection{*Induction formulae involving @{text"\<And>"} or @{text"\<Longrightarrow>"}*}


lemma assumes A: "(\<And>n. (\<And>m. m < n \<Longrightarrow> P m) \<Longrightarrow> P n)"
  shows "P(n::nat)"
proof (rule A)
  show "\<And>m. m < n \<Longrightarrow> P m"
  proof (induct n)
    case 0 thus ?case by simp
  next
    case (Suc n)   
    show ?case    
    proof cases
      assume eq: "m = n"
      from Suc and A have "P n" by blast
      with eq show "P m" by simp
    next
      assume "m \<noteq> n"
      with Suc have "m < n" by arith
      thus "P m" by(rule Suc)
    qed
  qed
qed


lemma assumes A: "(\<And>n. (\<And>m. m < n \<Longrightarrow> P m) \<Longrightarrow> P n)"
  shows "P(n::nat)"
proof (rule A)
  show "\<And>m. m < n \<Longrightarrow> P m"
  proof (induct n)
    fix m::nat assume "m < 0" thus "P m" by simp
  next
    fix n m
    assume IH: "\<And>m. m < n \<Longrightarrow> P m"
       and less: "m < Suc n"
    show "P m"
    proof cases
      assume eq: "m = n"
      from A IH have "P n" by blast
      with eq show "P m" by simp
    next
      assume "m \<noteq> n"
      with less have "m < n" by arith
      thus "P m" by(rule IH)
    qed
  qed
qed


subsection{*Rule induction*}


inductive Ev :: "nat => bool" where
Ev0:  "Ev 0" |
Ev2:  "Ev n \<Longrightarrow> Ev(n+2)"

declare Ev.intros [simp]


lemma "Ev n \<Longrightarrow> \<exists>k. n = 2*k"
proof (induct rule: Ev.induct)
  case Ev0 thus ?case by simp
next
  case Ev2 thus ?case by arith
qed


lemma assumes n: "Ev n" shows "\<exists>k. n = 2*k"
using n proof induct
  case Ev0 thus ?case by simp
next
  case Ev2 thus ?case by arith
qed


lemma assumes n: "Ev n" shows "\<exists>k. n = 2*k"
using n proof induct
  case Ev0 thus ?case by simp
next
  case (Ev2 m)
  then obtain k where "m = 2*k" by blast
  hence "m+2 = 2*(k+1)" by simp
  thus "\<exists>k. m+2 = 2*k" ..
qed


subsection{*Induction with fun*}

fun rot :: "'a list \<Rightarrow> 'a list" where
"rot [] = []" |
"rot [x] = [x]" |
"rot (x#y#zs) = y # rot(x#zs)"


lemma "xs \<noteq> [] \<Longrightarrow> rot xs = tl xs @ [hd xs]"
proof (induct xs rule: rot.induct)
  case 1 thus ?case by simp
next
  case 2 show ?case by simp
next
  case (3 a b cs)
  have "rot (a # b # cs) = b # rot(a # cs)" by simp
  also have "\<dots> = b # tl(a # cs) @ [hd(a # cs)]" by(simp add:3)
  also have "\<dots> = tl (a # b # cs) @ [hd (a # b # cs)]" by simp
  finally show ?case .
qed


lemma "xs \<noteq> [] \<Longrightarrow> rot xs = tl xs @ [hd xs]"
by (induct xs rule: rot.induct, simp_all)


subsection{*Calculational reasoning*}


thm mono_def

lemma assumes monof: "mono(f::int\<Rightarrow>int)"
          and monog: "mono(g::int\<Rightarrow>int)"
      shows "mono(\<lambda>i. f i + g i)"
proof --"rule monoI used automatically"
  fix i j :: int
  assume A: "i \<le> j"
  have "f i \<le> f j" using A monof by(simp add:mono_def)
  moreover
  have "g i \<le> g j" using A monog by(simp add:mono_def)
  ultimately show "f i + g i \<le> f j + g j" by arith
qed

declare ring_simps [simp]

lemma fixes x::int shows "(x+y)*(x-y) = x*x - y*y"
proof -
  have "(x+y)*(x-y) = x*(x-y) + y*(x-y)" by simp
  also have "\<dots> = x*x-x*y + y*x-y*y" by simp
  also have "\<dots> = x*x - y*y" by simp
  finally show ?thesis .
qed

lemma dvd_minus:
  assumes du: "(d::int) dvd u"
  assumes dv: "d dvd v"
  shows  "d dvd u - v"
proof -
  from du obtain ku where "u = d * ku" by(fastsimp simp: dvd_def)
  moreover
  from dv obtain kv where "v = d * kv" by(fastsimp simp: dvd_def)
  ultimately have "u - v =  d * ku - d * kv" by simp
  also have "\<dots> = d * (ku - kv)" by simp
  finally show ?thesis by(simp del:right_diff_distrib)
qed


subsection{* Monotonicity reasoning *}

lemma fixes a :: int shows "(a+b)\<twosuperior> \<le> 2*(a\<twosuperior> + b\<twosuperior>)"
proof -
       have "(a+b)\<twosuperior> \<le> (a+b)\<twosuperior> + (a-b)\<twosuperior>"  by(simp add:zero_le_power2)
  also have "(a+b)\<twosuperior> \<le> a\<twosuperior> + b\<twosuperior> + 2*a*b"  by(simp add:numeral_2_eq_2)
  also have "(a-b)\<twosuperior> = a\<twosuperior> + b\<twosuperior> - 2*a*b"  by(simp add:numeral_2_eq_2)
  finally show ?thesis by simp
qed


end
