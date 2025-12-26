theory MinimalDeadlockProof
imports Main
begin

datatype process = P1 | P2
datatype pstate = Ready | Waiting process

type_synonym System = "(process \<times> pstate) set"

inductive step :: "System \<Rightarrow> System \<Rightarrow> bool" (infix "\<rightarrow>" 50) where
  "\<lbrakk>(p, Ready) \<in> S; (q, Ready) \<in> S\<rbrakk> 
   \<Longrightarrow> S \<rightarrow> (S - {(p, Ready)}) \<union> {(p, Waiting q)}"

definition deadlock :: "System \<Rightarrow> bool" where
  "deadlock S \<equiv> (\<not> (\<exists>T. S \<rightarrow> T)) \<and> (\<exists>p q. (p, Waiting q) \<in> S)"

section \<open>Пример дедлока\<close>

definition dl_system :: System where
  "dl_system = {(P1, Waiting P2), (P2, Waiting P1)}"

section \<open>Еще более простой подход\<close>

lemma simple_deadlock_proof: "deadlock dl_system"
proof -
  have "dl_system = {(P1, Waiting P2), (P2, Waiting P1)}"
    by (simp add: dl_system_def)  
  show ?thesis
    unfolding deadlock_def
  proof (intro conjI)
    show "\<not> (\<exists>T. dl_system \<rightarrow> T)"
    proof
      assume "\<exists>T. dl_system \<rightarrow> T"
      then obtain T where "dl_system \<rightarrow> T" ..
      thus False
        using step.induct dl_system_def  by (metis empty_iff insert_iff prod.inject pstate.distinct(1) step.cases)
    qed    
    show "\<exists>p q. (p, Waiting q) \<in> dl_system"
      by (auto simp: dl_system_def)
  qed
qed

end