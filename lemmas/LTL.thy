theory LTL
  imports Main
begin
(* 
text \<open>Определение типа для темпоральных формул\<close>
datatype 'a ltl = 
    LTLProp 'a
  | LTLNot "'a ltl"
  | LTLAnd "'a ltl" "'a ltl"
  | LTLOr "'a ltl" "'a ltl"
  | LTLImplies "'a ltl" "'a ltl"
  | LTLNext "'a ltl"
  | LTLUntil "'a ltl" "'a ltl"
  | LTLAlways "'a ltl"
  | LTLEventually "'a ltl"

text \<open>Семантика LTL\<close>
fun ltl_sem :: "('a \<Rightarrow> bool) stream \<Rightarrow> 'a ltl \<Rightarrow> bool" where
  "ltl_sem \<sigma> (LTLProp p) = p (shd \<sigma>)"
| "ltl_sem \<sigma> (LTLNot \<phi>) = (\<not> ltl_sem \<sigma> \<phi>)"
| "ltl_sem \<sigma> (LTLAnd \<phi> \<psi>) = (ltl_sem \<sigma> \<phi> \<and> ltl_sem \<sigma> \<psi>)"
| "ltl_sem \<sigma> (LTLOr \<phi> \<psi>) = (ltl_sem \<sigma> \<phi> \<or> ltl_sem \<sigma> \<psi>)"
| "ltl_sem \<sigma> (LTLImplies \<phi> \<psi>) = (ltl_sem \<sigma> \<phi> \<longrightarrow> ltl_sem \<sigma> \<psi>)"
| "ltl_sem \<sigma> (LTLNext \<phi>) = ltl_sem (stl \<sigma>) \<phi>"
| "ltl_sem \<sigma> (LTLUntil \<phi> \<psi>) = (\<exists>i. ltl_sem (sdrop i \<sigma>) \<psi> \<and> (\<forall>j<i. ltl_sem (sdrop j \<sigma>) \<phi>))"
| "ltl_sem \<sigma> (LTLAlways \<phi>) = (\<forall>i. ltl_sem (sdrop i \<sigma>) \<phi>)"
| "ltl_sem \<sigma> (LTLEventually \<phi>) = (\<exists>i. ltl_sem (sdrop i \<sigma>) \<phi>)"

text \<open>Пример: оператор Always (\<box>)\<close>
abbreviation LTLAlways_notation ("\<box> _" [90] 90) where
  "\<box> \<phi> \<equiv> LTLAlways \<phi>"

text \<open>Пример: оператор Eventually (\<diamond>)\<close>
abbreviation LTLEventually_notation ("\<diamond> _" [90] 90) where
  "\<diamond> \<phi> \<equiv> LTLEventually \<phi>" *)
(* 

text \<open>Определение типа для темпоральных формул\<close>
datatype 'a ltl = 
    LTLProp 'a
  | LTLNot "'a ltl"
  | LTLAnd "'a ltl" "'a ltl"
  | LTLOr "'a ltl" "'a ltl"
  | LTLImplies "'a ltl" "'a ltl"
  | LTLNext "'a ltl"
  | LTLUntil "'a ltl" "'a ltl"
  | LTLAlways "'a ltl"
  | LTLEventually "'a ltl"

text \<open>Семантика LTL\<close>
fun ltl_sem :: "(nat \<Rightarrow> 'a) \<Rightarrow> 'a ltl \<Rightarrow> bool" where
  "ltl_sem \<sigma> (LTLProp p) = p (\<sigma> 0)"
| "ltl_sem \<sigma> (LTLNot \<phi>) = (\<not> ltl_sem \<sigma> \<phi>)"
| "ltl_sem \<sigma> (LTLAnd \<phi> \<psi>) = (ltl_sem \<sigma> \<phi> \<and> ltl_sem \<sigma> \<psi>)"
| "ltl_sem \<sigma> (LTLOr \<phi> \<psi>) = (ltl_sem \<sigma> \<phi> \<or> ltl_sem \<sigma> \<psi>)"
| "ltl_sem \<sigma> (LTLImplies \<phi> \<psi>) = (ltl_sem \<sigma> \<phi> \<longrightarrow> ltl_sem \<sigma> \<psi>)"
| "ltl_sem \<sigma> (LTLNext \<phi>) = ltl_sem (\<lambda>n. \<sigma> (n + 1)) \<phi>"
| "ltl_sem \<sigma> (LTLUntil \<phi> \<psi>) = (\<exists>i. ltl_sem (\<lambda>n. \<sigma> (n + i)) \<psi> \<and> (\<forall>j<i. ltl_sem (\<lambda>n. \<sigma> (n + j)) \<phi>))"
| "ltl_sem \<sigma> (LTLAlways \<phi>) = (\<forall>i. ltl_sem (\<lambda>n. \<sigma> (n + i)) \<phi>)"
| "ltl_sem \<sigma> (LTLEventually \<phi>) = (\<exists>i. ltl_sem (\<lambda>n. \<sigma> (n + i)) \<phi>)"

text \<open>Пример: оператор Always (\<box>)\<close>
abbreviation LTLAlways_notation ("\<box> _" [90] 90) where
  "\<box> \<phi> \<equiv> LTLAlways \<phi>"

text \<open>Пример: оператор Eventually (\<diamond>)\<close>
abbreviation LTLEventually_notation ("\<diamond> _" [90] 90) where
  "\<diamond> \<phi> \<equiv> LTLEventually \<phi>"
 *)


text \<open>Определение типа для темпоральных формул\<close>
datatype 'a ltl = 
    LTLProp "'a \<Rightarrow> bool"  (* Предикат, зависящий от состояния *)
  | LTLNot "'a ltl"
  | LTLAnd "'a ltl" "'a ltl"
  | LTLOr "'a ltl" "'a ltl"
  | LTLImplies "'a ltl" "'a ltl"
  | LTLNext "'a ltl"
  | LTLUntil "'a ltl" "'a ltl"
  | LTLAlways "'a ltl"
  | LTLEventually "'a ltl"

text \<open>Семантика LTL\<close>
fun ltl_sem :: "(nat \<Rightarrow> 'a) \<Rightarrow> 'a ltl \<Rightarrow> bool" where
  "ltl_sem \<sigma> (LTLProp p) = p (\<sigma> 0)"  (* p — это предикат, применяемый к текущему состоянию *)
| "ltl_sem \<sigma> (LTLNot \<phi>) = (\<not> ltl_sem \<sigma> \<phi>)"
| "ltl_sem \<sigma> (LTLAnd \<phi> \<psi>) = (ltl_sem \<sigma> \<phi> \<and> ltl_sem \<sigma> \<psi>)"
| "ltl_sem \<sigma> (LTLOr \<phi> \<psi>) = (ltl_sem \<sigma> \<phi> \<or> ltl_sem \<sigma> \<psi>)"
| "ltl_sem \<sigma> (LTLImplies \<phi> \<psi>) = (ltl_sem \<sigma> \<phi> \<longrightarrow> ltl_sem \<sigma> \<psi>)"
| "ltl_sem \<sigma> (LTLNext \<phi>) = ltl_sem (\<lambda>n. \<sigma> (n + 1)) \<phi>"
| "ltl_sem \<sigma> (LTLUntil \<phi> \<psi>) = (\<exists>i. ltl_sem (\<lambda>n. \<sigma> (n + i)) \<psi> \<and> (\<forall>j<i. ltl_sem (\<lambda>n. \<sigma> (n + j)) \<phi>))"
| "ltl_sem \<sigma> (LTLAlways \<phi>) = (\<forall>i. ltl_sem (\<lambda>n. \<sigma> (n + i)) \<phi>)"
| "ltl_sem \<sigma> (LTLEventually \<phi>) = (\<exists>i. ltl_sem (\<lambda>n. \<sigma> (n + i)) \<phi>)"

text \<open>Пример: оператор Always (\<box>)\<close>
abbreviation LTLAlways_notation ("\<box> _" [90] 90) where
  "\<box> \<phi> \<equiv> LTLAlways \<phi>"

text \<open>Пример: оператор Eventually (\<diamond>)\<close>
abbreviation LTLEventually_notation ("\<diamond> _" [90] 90) where
  "\<diamond> \<phi> \<equiv> LTLEventually \<phi>"



end