theory AdversaryModel
  imports AIRSyntax ExpressionSemantics (*TODO remove dependency on Step*)
begin

section \<open>The Adversary Model\<close>

subsection \<open>Adversary parts of the system state\<close>

text \<open>The adversary cannot observe any speculative part of the system state\<close>

abbreviation \<open>pc\<^sub>0 s \<equiv> the (pc s 0)\<close>

lemma architecural_pc\<^sub>0: 
  assumes \<open>\<not>speculating s\<close>
    shows \<open>\<rho> s = pc\<^sub>0 s\<close>
  using assms by (auto simp add: speculating_def)

lemma architecural_pc\<^sub>0_comp: 
  assumes \<open>\<not>speculating s\<^sub>1\<close> and \<open>\<not>speculating s\<^sub>2\<close>
    shows \<open>\<rho> s\<^sub>1 = \<rho> s\<^sub>2 \<longleftrightarrow> pc\<^sub>0 s\<^sub>1 = pc\<^sub>0 s\<^sub>2\<close>
  using assms by (auto simp add: speculating_def)

abbreviation \<open>\<iota>\<^sub>0 s \<equiv> the (\<Pi> s (pc\<^sub>0 s))\<close>
abbreviation \<open>\<Delta>\<^sub>0 s \<equiv> the (\<Delta> s 0)\<close>

lemma architecural_\<Delta>\<^sub>0_comp: 
  assumes \<open>\<not>speculating s\<^sub>1\<close> and \<open>\<not>speculating s\<^sub>2\<close>
    shows \<open>\<Delta>\<^sub>n s\<^sub>1 = \<Delta>\<^sub>n s\<^sub>2 \<longleftrightarrow> \<Delta>\<^sub>0 s\<^sub>1 = \<Delta>\<^sub>0 s\<^sub>2\<close>
  using assms by (auto simp add: speculating_def)
   

abbreviation \<open>\<mu>\<^sub>0 s \<equiv> the (\<mu> s 0)\<close> (* TODO make this nicer (the adversary cannot observe non readable addresses at 0)*)

lemma architecural_\<mu>\<^sub>0_comp: 
  assumes \<open>\<not>speculating s\<^sub>1\<close> and \<open>\<not>speculating s\<^sub>2\<close>
    shows \<open>\<mu>\<^sub>n s\<^sub>1 = \<mu>\<^sub>n s\<^sub>2 \<longleftrightarrow> \<mu>\<^sub>0 s\<^sub>1 = \<mu>\<^sub>0 s\<^sub>2\<close>
  using assms by (auto simp add: speculating_def)


abbreviation
  \<mu>\<^sub>0\<^sub>r\<^sub>e\<^sub>a\<^sub>d :: \<open>MachineState \<Rightarrow> Addr\<^sub>\<mu> \<Rightarrow> Const\<close> where
  \<open>\<mu>\<^sub>0\<^sub>r\<^sub>e\<^sub>a\<^sub>d s a \<equiv> (\<mu>\<^sub>0 s a)\<close>

lemma \<mu>\<^sub>0\<^sub>r\<^sub>e\<^sub>a\<^sub>d_equiv_ns: \<open>n s = 0 \<Longrightarrow> \<mu>\<^sub>0\<^sub>r\<^sub>e\<^sub>a\<^sub>d s = \<mu>\<^sub>r\<^sub>e\<^sub>a\<^sub>d s\<close> 
  by (simp)

abbreviation
  \<mu>\<^sub>0\<^sub>w\<^sub>r\<^sub>i\<^sub>t\<^sub>e :: \<open>MachineState \<Rightarrow> Addr\<^sub>\<mu> \<Rightarrow> Const \<Rightarrow> DataMemoryState\<close> where
  \<open>\<mu>\<^sub>0\<^sub>w\<^sub>r\<^sub>i\<^sub>t\<^sub>e s a v \<equiv> (\<mu> s)(0 \<mapsto> \<mu>\<^sub>n\<^sub>w\<^sub>r\<^sub>i\<^sub>t\<^sub>e a v (\<mu>\<^sub>0 s))\<close>

lemma \<mu>\<^sub>0\<^sub>w\<^sub>r\<^sub>i\<^sub>t\<^sub>e_equiv_ns: \<open>n s = 0 \<Longrightarrow> \<mu>\<^sub>0\<^sub>w\<^sub>r\<^sub>i\<^sub>t\<^sub>e s a v = \<mu>\<^sub>w\<^sub>r\<^sub>i\<^sub>t\<^sub>e s a v\<close>
  by simp


lemma pc\<^sub>0_pc_no_spec: \<open>\<not>speculating s \<Longrightarrow> pc\<^sub>0 s = \<rho> s\<close>
  by (simp add: speculating_def)

lemma \<iota>\<^sub>0_\<iota>_no_spec: \<open>\<not>speculating s \<Longrightarrow> \<iota>\<^sub>0 s = \<iota> s\<close>
  by (simp add: pc\<^sub>0_pc_no_spec)

lemma \<Delta>\<^sub>0_\<Delta>_no_spec: \<open>\<not>speculating s \<Longrightarrow> \<Delta>\<^sub>0 s = the (\<Delta> s (n s))\<close>
  by (simp add: speculating_def)

lemma \<mu>\<^sub>0_\<mu>_no_spec: \<open>\<not>speculating s \<Longrightarrow> \<mu>\<^sub>0 s = the (\<mu> s (n s))\<close>
  by (simp add: speculating_def)



lemma \<mu>_implies_\<mu>\<^sub>0: \<open>\<mu> s\<^sub>1 = \<mu> s\<^sub>2 \<Longrightarrow> \<mu>\<^sub>0 s\<^sub>1 = \<mu>\<^sub>0 s\<^sub>2\<close>
  by (simp)

lemma \<Delta>_implies_\<Delta>\<^sub>0: \<open>\<Delta> s\<^sub>1 = \<Delta> s\<^sub>2 \<Longrightarrow> \<Delta>\<^sub>0 s\<^sub>1 = \<Delta>\<^sub>0 s\<^sub>2\<close>
  by (simp)

lemma pc_implies_pc\<^sub>0: \<open>pc s\<^sub>1 = pc s\<^sub>2 \<Longrightarrow> pc\<^sub>0 s\<^sub>1 = pc\<^sub>0 s\<^sub>2\<close>
  by (simp)

lemma ns_pc\<^sub>0_\<rho>_ptr_equal: \<open>\<lbrakk>\<not>speculating s\<^sub>1; \<not>speculating s\<^sub>2; pc\<^sub>0 s\<^sub>1 = pc\<^sub>0 s\<^sub>2\<rbrakk> \<Longrightarrow> \<rho> s\<^sub>1 = \<rho> s\<^sub>2\<close>
  by (simp add: speculating_def)

lemma ns_pc\<^sub>0_\<rho>_equal: \<open>\<lbrakk>\<not>speculating s\<^sub>1; \<not>speculating s\<^sub>2; pc\<^sub>0 s\<^sub>1 = pc\<^sub>0 s\<^sub>2\<rbrakk> \<Longrightarrow> \<rho> s\<^sub>1 = \<rho> s\<^sub>2\<close>
  by (simp add: pc\<^sub>0_pc_no_spec)

lemma ns_pc\<^sub>0_pc_equal: 
  assumes \<open>\<not>speculating s\<^sub>1\<close>
      and \<open>\<not>speculating s\<^sub>2\<close>
      and \<open>wfs s\<^sub>1\<close>
      and \<open>wfs s\<^sub>2\<close>
      and \<open>pc\<^sub>0 s\<^sub>1 = pc\<^sub>0 s\<^sub>2\<close>
    shows \<open>pc s\<^sub>1 = pc s\<^sub>2\<close>
proof -
  have not_none: \<open>pc s\<^sub>1 0 \<noteq> None \<and> pc s\<^sub>2 0 \<noteq> None\<close>
    using assms(3-4) by (auto simp add: wfs_def wfpc_def Let_def)
  have pc_zero_equal: \<open>pc s\<^sub>1 0 = pc s\<^sub>2 0\<close>
    using assms by (simp add: speculating_def not_none option.expand)
  have pc_not_zero_equal: \<open>\<forall>n. n > 0 \<longrightarrow> pc s\<^sub>1 n = pc s\<^sub>2 n\<close>
    by (simp add: assms(1) assms(2) assms(3) assms(4) ns_pc_s_equal)
  show ?thesis
    using assms by (metis gr_implies_not0 linorder_neqE_nat n_pc_implies_pc_equal pc_not_zero_equal 
                          pc_zero_equal)
qed


lemma eval_exp_same_\<Delta>\<^sub>0_equiv:
  assumes \<open>\<not>speculating s\<^sub>1 \<and> \<not>speculating s\<^sub>2\<close>
      and \<open>\<Delta>\<^sub>0 s\<^sub>1 = \<Delta>\<^sub>0 s\<^sub>2\<close>
      and \<open>wfs s\<^sub>1 \<and> wfs s\<^sub>2\<close>
    shows \<open>(\<lbrakk>e\<rbrakk>(\<Delta>\<^sub>n s\<^sub>1)) = (\<lbrakk>e\<rbrakk>(\<Delta>\<^sub>n s\<^sub>2))\<close>
proof - 
  have \<open>\<Delta> s\<^sub>1 0 = \<Delta> s\<^sub>2 0\<close>
    using assms(2, 3) by (auto simp add: wfs_def wf\<Delta>_def)
  then show ?thesis 
    using assms by (auto simp add: speculating_def)
qed


subsection \<open>Trusted Program and Confidential States\<close>

(* Return all public memory in p\<^sub>\<mu>, ie not the memory in the secret set *)
definition \<open>\<P>\<^sub>\<T> s \<equiv> {v . (\<forall>a. a \<notin> \<S>\<^sub>\<T> s \<longrightarrow> v = (\<mu>\<^sub>0\<^sub>r\<^sub>e\<^sub>a\<^sub>d s a))}\<close> 




(* High Instruction executed in state s in the trusted set of addresses *)



subsection \<open>State operations\<close>


subsubsection \<open>High operation (op$_{\<H>s}$) \<close>

type_synonym state_instr = \<open>Instr option\<close>
type_synonym state_public_mem = \<open>64 word set\<close>
type_synonym high_operation = \<open>(state_instr \<times> state_public_mem)\<close>
type_synonym trace = \<open>MachineState list\<close>

abbreviation bot :: \<open>Instr option\<close> (\<open>\<bottom>\<close>)
  where \<open>\<bottom> \<equiv> (None::Instr option)\<close>

definition inst\<^sub>\<T> :: \<open>MachineState \<Rightarrow> state_instr\<close> where
\<open>inst\<^sub>\<T> s \<equiv>
  let \<rho> = pc\<^sub>0 s in
    if \<rho> \<in> \<T>\<^sub>\<rho> s
    then \<Pi> s \<rho>
    else None
\<close>

text \<open>inst\<T> always indexes defined program memory\<close>

lemma inst\<^sub>\<T>_NotHaltTrusted_NotNone: 
  assumes \<open>wfs s\<close>
    and \<open>\<not>halting (pc\<^sub>0 s) (\<Pi> s)\<close>
    and \<open>pc\<^sub>0 s \<in> \<T>\<^sub>\<rho> s\<close>
  shows \<open>inst\<^sub>\<T> s \<noteq> \<bottom>\<close>
  using assms by (auto simp add: inst\<^sub>\<T>_def halting\<^sub>p\<^sub>r\<^sub>e\<^sub>d_def halting_def wfs_def wf\<T>\<^sub>\<rho>_def)
  

text \<open>Returns the Instruction executed in state s if the Instruction's address is in the trusted
      set of addresses and the public memory of that state (. This is extended to traces (\<pi>).\<close>

definition \<open>op\<^sub>\<H>_sub s \<equiv> (inst\<^sub>\<T> s, \<P>\<^sub>\<T> s)\<close>

consts op\<^sub>\<H> :: \<open>'a \<Rightarrow> 'b\<close>

overloading
  op\<^sub>\<H>\<^sub>s \<equiv> \<open>op\<^sub>\<H> :: MachineState \<Rightarrow> high_operation\<close>
  op\<^sub>\<H>\<^sub>\<pi> \<equiv> \<open>op\<^sub>\<H> :: trace \<Rightarrow> high_operation list\<close>
begin

fun op\<^sub>\<H>\<^sub>s :: \<open>MachineState \<Rightarrow> high_operation\<close> where 
\<open>op\<^sub>\<H>\<^sub>s s = op\<^sub>\<H>_sub s\<close>

fun op\<^sub>\<H>\<^sub>\<pi> :: \<open>trace \<Rightarrow> high_operation list\<close> where 
\<open>op\<^sub>\<H>\<^sub>\<pi> \<pi> = map op\<^sub>\<H>_sub \<pi>\<close>

end

lemma op\<^sub>\<H>\<^sub>_\<pi>_eq_append_s_eq:
  assumes \<open>((op\<^sub>\<H> (\<pi>\<^sub>1::trace))::high_operation list) = op\<^sub>\<H> (\<pi>\<^sub>2::trace)\<close>
      and \<open>((op\<^sub>\<H> s\<^sub>1)::high_operation) = op\<^sub>\<H> s\<^sub>2\<close>
    shows \<open>((op\<^sub>\<H> (\<pi>\<^sub>1 @ [s\<^sub>1]))::high_operation list) = op\<^sub>\<H> (\<pi>\<^sub>2 @ [s\<^sub>2])\<close>
  using assms by force

lemma op\<^sub>\<H>_\<pi>_eq_append_s'_eq:
  assumes \<open>((op\<^sub>\<H> ((\<pi>\<^sub>1 @ [s\<^sub>1])::trace))::high_operation list) = op\<^sub>\<H> ((\<pi>\<^sub>2 @ [s\<^sub>2])::trace)\<close>
      and \<open>((op\<^sub>\<H> s\<^sub>1')::high_operation) = op\<^sub>\<H> s\<^sub>2'\<close>
    shows \<open>((op\<^sub>\<H> (\<pi>\<^sub>1 @ [s\<^sub>1, s\<^sub>1']))::high_operation list) = op\<^sub>\<H> (\<pi>\<^sub>2 @ [s\<^sub>2, s\<^sub>2'])\<close>
  using assms by force

lemma fst_op\<^sub>\<H>_inst\<^sub>\<T>: \<open>inst\<^sub>\<T> s = fst ((op\<^sub>\<H> s)::high_operation)\<close>
  by (auto simp add: op\<^sub>\<H>_sub_def)

subsubsection \<open>Low operation (op$_{\<L>s}$) \<close>

type_synonym low_operation = \<open>state_instr\<close>

text \<open>Returns the Instruction executed in state s if the Instruction's address is not in the trusted
      set of addresses. This is extended to traces (\<pi>).\<close>

definition \<open>op\<^sub>\<L>_sub s \<equiv>
  let \<rho> = pc\<^sub>0 s in
    if halting \<rho> (\<Pi> s) \<or> \<rho> \<in> \<T>\<^sub>\<rho> s
    then None
    else \<Pi> s \<rho>
\<close>

consts op\<^sub>\<L> :: \<open>'a \<Rightarrow> 'b\<close>

overloading
  op\<^sub>\<L>\<^sub>s \<equiv> \<open>op\<^sub>\<L> :: MachineState \<Rightarrow> low_operation\<close>
  op\<^sub>\<L>\<^sub>\<pi> \<equiv> \<open>op\<^sub>\<L> :: trace \<Rightarrow> low_operation list\<close>
begin

fun op\<^sub>\<L>\<^sub>s :: \<open>MachineState \<Rightarrow> low_operation\<close> where 
\<open>op\<^sub>\<L>\<^sub>s s = op\<^sub>\<L>_sub s\<close>

fun op\<^sub>\<L>\<^sub>\<pi> :: \<open>trace \<Rightarrow> low_operation list\<close> where 
\<open>op\<^sub>\<L>\<^sub>\<pi> \<pi> = map op\<^sub>\<L>_sub \<pi>\<close>

end

lemma op\<^sub>\<L>_\<pi>_eq_append_s_eq:
  assumes \<open>((op\<^sub>\<L> (\<pi>\<^sub>1::trace))::low_operation list) = op\<^sub>\<L> (\<pi>\<^sub>2::trace)\<close>
      and \<open>((op\<^sub>\<L> s\<^sub>1)::low_operation) = op\<^sub>\<L> s\<^sub>2\<close>
    shows \<open>((op\<^sub>\<L> (\<pi>\<^sub>1 @ [s\<^sub>1]))::low_operation list) = op\<^sub>\<L> (\<pi>\<^sub>2 @ [s\<^sub>2])\<close>
  using assms by force

lemma op\<^sub>\<L>_\<pi>_eq_append_s'_eq:
  assumes \<open>((op\<^sub>\<L> ((\<pi>\<^sub>1 @ [s\<^sub>1])::trace))::low_operation list) = op\<^sub>\<L> ((\<pi>\<^sub>2 @ [s\<^sub>2])::trace)\<close>
      and \<open>((op\<^sub>\<L> s\<^sub>1')::low_operation) = op\<^sub>\<L> s\<^sub>2'\<close>
    shows \<open>((op\<^sub>\<L> (\<pi>\<^sub>1 @ [s\<^sub>1, s\<^sub>1']))::low_operation list) = op\<^sub>\<L> (\<pi>\<^sub>2 @ [s\<^sub>2, s\<^sub>2'])\<close>
  using assms by force



text \<open>op$_\<L>$ always indexes defined program memory\<close>

lemma op\<^sub>\<L>_NotHaltNotTrusted_NotNone: 
  assumes \<open>wfs s\<close>
      and \<open>\<not>halting (pc\<^sub>0 s) (\<Pi> s)\<close>
      and \<open>pc\<^sub>0 s \<notin> \<T>\<^sub>\<rho> s\<close>
    shows \<open>op\<^sub>\<L> s \<noteq> \<bottom>\<close>
  using assms by (auto simp add: wfs_def halting\<^sub>p\<^sub>r\<^sub>e\<^sub>d_def halting_def wf\<T>\<^sub>\<rho>_def Let_def op\<^sub>\<L>_sub_def)

(* some lemmas *)


lemma op\<^sub>\<L>_not_inst\<^sub>\<T>_s: \<open>op\<^sub>\<L> s \<noteq> \<bottom> \<Longrightarrow> inst\<^sub>\<T> s = \<bottom>\<close>
  by (auto simp add: inst\<^sub>\<T>_def op\<^sub>\<L>_sub_def Let_def)

lemma inst\<^sub>\<T>_not_op\<^sub>\<L>_s: \<open>inst\<^sub>\<T> s \<noteq> \<bottom> \<Longrightarrow> op\<^sub>\<L> s = \<bottom>\<close>
  by (auto simp add: inst\<^sub>\<T>_def op\<^sub>\<L>_sub_def Let_def)

text \<open>Safety: If the program halts then neither a low or high Instruction is executed.\<close>

lemma op\<^sub>\<H>\<^sub>\<L>_Halt_None: \<open>halting (pc\<^sub>0 s) (\<Pi> s) \<Longrightarrow> op\<^sub>\<L> s = \<bottom> \<and> inst\<^sub>\<T> s = \<bottom>\<close>
  by (auto simp add: inst\<^sub>\<T>_def op\<^sub>\<L>_sub_def Let_def halting_def)


text \<open>Safety: If the program is not halting either a low or (exclusive) high Instruction is executing.\<close>

lemma op\<^sub>\<L>_NotHalt_\<H>or\<L>:
  assumes \<open>wfs s\<close>
  and \<open>\<not>halting (pc\<^sub>0 s) (\<Pi> s)\<close>
shows \<open>\<not>((op\<^sub>\<L> s = \<bottom> \<and> inst\<^sub>\<T> s = \<bottom>) \<or> (op\<^sub>\<L> s \<noteq> \<bottom> \<and> inst\<^sub>\<T> s \<noteq> \<bottom>))\<close>
  apply (cases \<open>pc\<^sub>0 s \<notin> \<T>\<^sub>\<rho> s\<close>)
  apply auto
  using assms op\<^sub>\<L>_NotHaltNotTrusted_NotNone apply auto[1]  
  apply (auto simp add: assms inst\<^sub>\<T>_NotHaltTrusted_NotNone)
  by (simp_all add: op\<^sub>\<L>_sub_def inst\<^sub>\<T>_def Let_def)

lemma inst\<^sub>\<T>_op\<^sub>\<L>_NotHalt_NotSame:
  assumes \<open>wfs s\<close>
  and \<open>\<not>halting (pc\<^sub>0 s) (\<Pi> s)\<close>
shows \<open>op\<^sub>\<L> s = \<bottom> \<longleftrightarrow> inst\<^sub>\<T> s \<noteq> \<bottom>\<close>
  using assms by (meson op\<^sub>\<L>_NotHalt_\<H>or\<L>)

lemma inst\<^sub>\<T>_op\<^sub>\<L>_NotHalt_NotSame2:
  assumes \<open>wfs s\<close>
  and \<open>\<not>halting (pc\<^sub>0 s) (\<Pi> s)\<close>
shows \<open>op\<^sub>\<L> s \<noteq> \<bottom> \<longleftrightarrow> inst\<^sub>\<T> s = \<bottom>\<close>
  using assms inst\<^sub>\<T>_op\<^sub>\<L>_NotHalt_NotSame by auto


text \<open>Convenient lemmas for the above using 2 and 4 traces.\<close>

lemma op\<^sub>\<L>2_NotHalt_\<L>None_\<H>NotNone:
  assumes \<open>op\<^sub>\<L> s\<^sub>1 = op\<^sub>\<L> s\<^sub>2\<close>
  and \<open>\<not>halting (pc\<^sub>0 s\<^sub>1) (\<Pi> s\<^sub>1)\<close>
  and \<open>\<not>halting (pc\<^sub>0 s\<^sub>2) (\<Pi> s\<^sub>2)\<close>
  and \<open>wfs s\<^sub>1\<close>
  and \<open>wfs s\<^sub>2\<close>
shows \<open>(op\<^sub>\<L> s\<^sub>1 = \<bottom> \<and> op\<^sub>\<L> s\<^sub>2 = \<bottom>) \<longleftrightarrow> (inst\<^sub>\<T> s\<^sub>1 \<noteq> None \<and> inst\<^sub>\<T> s\<^sub>2 \<noteq> None)\<close>  
  using assms op\<^sub>\<L>_NotHalt_\<H>or\<L> by meson

lemma op\<^sub>\<L>2_NotHalt_\<L>NotNone_\<H>None:
  assumes \<open>op\<^sub>\<L> s\<^sub>1 = op\<^sub>\<L> s\<^sub>2\<close>
  and \<open>\<not>halting (pc\<^sub>0 s\<^sub>1) (\<Pi> s\<^sub>1)\<close>
  and \<open>\<not>halting (pc\<^sub>0 s\<^sub>2) (\<Pi> s\<^sub>2)\<close>
  and \<open>wfs s\<^sub>1\<close>
  and \<open>wfs s\<^sub>2\<close>
shows \<open>(op\<^sub>\<L> s\<^sub>1 \<noteq> \<bottom> \<and> op\<^sub>\<L> s\<^sub>2 \<noteq> \<bottom>) \<longleftrightarrow> (inst\<^sub>\<T> s\<^sub>1 = None \<and> inst\<^sub>\<T> s\<^sub>2 = None)\<close>  
  using assms op\<^sub>\<L>_NotHalt_\<H>or\<L> by meson

lemma op\<^sub>\<L>4_NotHalt_\<L>None_\<H>NotNone:
  assumes \<open>op\<^sub>\<L> s\<^sub>1 = op\<^sub>\<L> s\<^sub>2\<close>
  and \<open>op\<^sub>\<L> s\<^sub>1 = op\<^sub>\<L> s\<^sub>3\<close>
  and \<open>op\<^sub>\<L> s\<^sub>1 = op\<^sub>\<L> s\<^sub>4\<close>
  and \<open>\<not>halting (pc\<^sub>0 s\<^sub>1) (\<Pi> s\<^sub>1)\<close>
  and \<open>\<not>halting (pc\<^sub>0 s\<^sub>2) (\<Pi> s\<^sub>2)\<close>
  and \<open>\<not>halting (pc\<^sub>0 s\<^sub>3) (\<Pi> s\<^sub>3)\<close>
  and \<open>\<not>halting (pc\<^sub>0 s\<^sub>4) (\<Pi> s\<^sub>4)\<close>
  and \<open>wfs s\<^sub>1\<close>
  and \<open>wfs s\<^sub>2\<close>
  and \<open>wfs s\<^sub>3\<close>
  and \<open>wfs s\<^sub>4\<close>
  and \<open>op\<^sub>\<L> s\<^sub>1 = None\<close>
shows \<open>(op\<^sub>\<L> s\<^sub>1 = \<bottom> \<and> op\<^sub>\<L> s\<^sub>2 = \<bottom> \<and> op\<^sub>\<L> s\<^sub>3 = \<bottom> \<and> op\<^sub>\<L> s\<^sub>4 = \<bottom>) 
        \<longleftrightarrow> (inst\<^sub>\<T> s\<^sub>1 \<noteq> None \<and> inst\<^sub>\<T> s\<^sub>2 \<noteq> None \<and> inst\<^sub>\<T> s\<^sub>3 \<noteq> None \<and> inst\<^sub>\<T> s\<^sub>4 \<noteq> None)\<close>  
  using assms by (metis inst\<^sub>\<T>_op\<^sub>\<L>_NotHalt_NotSame)

lemma op\<^sub>\<L>4_NotHalt_\<L>NotNone_\<H>None:
  assumes \<open>op\<^sub>\<L> s\<^sub>1 = op\<^sub>\<L> s\<^sub>2\<close>
  and \<open>op\<^sub>\<L> s\<^sub>1 = op\<^sub>\<L> s\<^sub>3\<close>
  and \<open>op\<^sub>\<L> s\<^sub>1 = op\<^sub>\<L> s\<^sub>4\<close>
  and \<open>\<not>halting (pc\<^sub>0 s\<^sub>1) (\<Pi> s\<^sub>1)\<close>
  and \<open>\<not>halting (pc\<^sub>0 s\<^sub>2) (\<Pi> s\<^sub>2)\<close>
  and \<open>\<not>halting (pc\<^sub>0 s\<^sub>3) (\<Pi> s\<^sub>3)\<close>
  and \<open>\<not>halting (pc\<^sub>0 s\<^sub>4) (\<Pi> s\<^sub>4)\<close>
  and \<open>wfs s\<^sub>1\<close>
  and \<open>wfs s\<^sub>2\<close>
  and \<open>wfs s\<^sub>3\<close>
  and \<open>wfs s\<^sub>4\<close>
shows \<open>(op\<^sub>\<L> s\<^sub>1 \<noteq> \<bottom> \<and> op\<^sub>\<L> s\<^sub>2 \<noteq> \<bottom> \<and> op\<^sub>\<L> s\<^sub>3 \<noteq> \<bottom> \<and> op\<^sub>\<L> s\<^sub>4 \<noteq> \<bottom>) 
        \<longleftrightarrow> (inst\<^sub>\<T> s\<^sub>1 = None \<and> inst\<^sub>\<T> s\<^sub>2 = None \<and> inst\<^sub>\<T> s\<^sub>3 = None \<and> inst\<^sub>\<T> s\<^sub>4 = None)\<close>
  using assms by (metis inst\<^sub>\<T>_op\<^sub>\<L>_NotHalt_NotSame)


subsection \<open>Adversary Observations\<close>

text \<open>Low equivalence refers to how a low component in a system model must not be able to
distinguish between secret states of the high component. This can also be extended to traces such 
that every state within two traces is low equivalent. 

An adversary cannot observe speculative states (n > 0) as these cannot be output (except through 
side channels) and can only execute Instructions in a non trusted state (\<rho> \<notin> \<T>\<rho>). They can therefore
read all non-speculative register and memory values () where the memory values must be attacker 
readable (). The branch predictor state and trace of past Instruction and data memory accesses is 
trivial to access.\<close>


(* TODO correct the adversary memory image and \<or> inst\<^sub>\<T> s' = None*)
definition low_equiv_sub :: \<open>MachineState \<Rightarrow> MachineState \<Rightarrow> bool\<close> where
\<open>low_equiv_sub s\<^sub>1 s\<^sub>2 = (
    ((\<not>speculating s\<^sub>1 \<or> \<not>speculating s\<^sub>2) \<and> (inst\<^sub>\<T> s\<^sub>1 = None))
    \<longrightarrow> (\<Delta>\<^sub>0 s\<^sub>1 = \<Delta>\<^sub>0 s\<^sub>2
        \<and> (\<forall>a . a \<in> \<U>rd s\<^sub>1 \<longrightarrow> \<mu>\<^sub>0\<^sub>r\<^sub>e\<^sub>a\<^sub>d s\<^sub>1 a = \<mu>\<^sub>0\<^sub>r\<^sub>e\<^sub>a\<^sub>d s\<^sub>2 a)
        \<and> \<omega> s\<^sub>1 = \<omega> s\<^sub>2
        \<and> \<beta> s\<^sub>1 = \<beta> s\<^sub>2)
)\<close>

consts low_equiv :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close> (infixl \<open>\<approx>\<^sub>\<L>\<close> 100)

overloading
  low_equiv_s \<equiv> \<open>low_equiv :: MachineState \<Rightarrow> MachineState \<Rightarrow> bool\<close>
  low_equiv_\<pi> \<equiv> \<open>low_equiv :: trace \<Rightarrow> trace \<Rightarrow> bool\<close>
begin

fun low_equiv_s :: \<open>MachineState \<Rightarrow> MachineState \<Rightarrow> bool\<close> where 
\<open>low_equiv_s s\<^sub>1 s\<^sub>2 = low_equiv_sub s\<^sub>1 s\<^sub>2\<close>

fun low_equiv_\<pi> :: \<open>trace \<Rightarrow> trace \<Rightarrow> bool\<close> where 
\<open>low_equiv_\<pi> \<pi>\<^sub>1 \<pi>\<^sub>2 = list_all2 (low_equiv_sub) \<pi>\<^sub>1 \<pi>\<^sub>2\<close>

end

lemma low_equiv_s_simp:
  assumes \<open>(s\<^sub>1::MachineState) \<approx>\<^sub>\<L> s\<^sub>2\<close>
    shows \<open>
((\<not>speculating s\<^sub>1 \<or> \<not>speculating s\<^sub>2) \<and> (inst\<^sub>\<T> s\<^sub>1 = None))
    \<longrightarrow> (\<Delta>\<^sub>0 s\<^sub>1 = \<Delta>\<^sub>0 s\<^sub>2
        \<and> (\<forall>a . a \<in> \<U>rd s\<^sub>1 \<longrightarrow> \<mu>\<^sub>0\<^sub>r\<^sub>e\<^sub>a\<^sub>d s\<^sub>1 a = \<mu>\<^sub>0\<^sub>r\<^sub>e\<^sub>a\<^sub>d s\<^sub>2 a)
        \<and> \<omega> s\<^sub>1 = \<omega> s\<^sub>2
        \<and> \<beta> s\<^sub>1 = \<beta> s\<^sub>2)\<close>
  using assms low_equiv_sub_def by auto

abbreviation not_low_equiv :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close>
    (infixl \<open>!\<approx>\<^sub>\<L>\<close> 100) where
\<open>(x !\<approx>\<^sub>\<L> y) \<equiv> (\<not>(x \<approx>\<^sub>\<L> y))\<close>

lemma low_equiv_s_not_low:
  assumes \<open>op\<^sub>\<L> s\<^sub>1 \<noteq> \<bottom>\<close>
      and \<open>(\<not>speculating s\<^sub>1 \<or> \<not>speculating s\<^sub>2)\<close>
      and \<open>s\<^sub>1 \<approx>\<^sub>\<L> s\<^sub>2\<close>
    shows \<open>\<Delta>\<^sub>0 s\<^sub>1 = \<Delta>\<^sub>0 s\<^sub>2
           \<and> (\<forall>a . a \<in> \<U>rd s\<^sub>1 \<longrightarrow> \<mu>\<^sub>0\<^sub>r\<^sub>e\<^sub>a\<^sub>d s\<^sub>1 a = \<mu>\<^sub>0\<^sub>r\<^sub>e\<^sub>a\<^sub>d s\<^sub>2 a)
           \<and> \<omega> s\<^sub>1 = \<omega> s\<^sub>2
           \<and> \<beta> s\<^sub>1 = \<beta> s\<^sub>2\<close>
  by (meson assms(1) assms(2) assms(3) inst\<^sub>\<T>_not_op\<^sub>\<L>_s low_equiv_s.elims(2) low_equiv_sub_def)

lemma low_equiv_s_spec_triv:
  assumes \<open>speculating s\<^sub>1 \<and> speculating s\<^sub>2\<close>
    shows \<open>s\<^sub>1 \<approx>\<^sub>\<L> s\<^sub>2\<close>
  using assms low_equiv_sub_def by auto

lemma low_equiv_s_op_high:
  assumes \<open>inst\<^sub>\<T> s\<^sub>1 \<noteq> \<bottom>\<close>
    shows \<open>s\<^sub>1 \<approx>\<^sub>\<L> s\<^sub>2\<close>
    using assms low_equiv_sub_def by auto

lemma low_equiv_s_not_op_low:
  assumes \<open>op\<^sub>\<L> s\<^sub>1 = \<bottom>\<close>
      and \<open>wfs s\<^sub>1\<close>
      and \<open>\<not>halting (pc\<^sub>0 s\<^sub>1) (\<Pi> s\<^sub>1)\<close>
    shows \<open>s\<^sub>1 \<approx>\<^sub>\<L> s\<^sub>2\<close>
  using assms low_equiv_s_op_high op\<^sub>\<L>_NotHalt_\<H>or\<L> by blast

lemma low_equiv_s_in_t: \<open>length \<pi>\<^sub>1 = length (\<pi>\<^sub>2::trace) 
\<Longrightarrow> \<pi>\<^sub>1 \<approx>\<^sub>\<L> \<pi>\<^sub>2 = (\<forall>i . i < length \<pi>\<^sub>1 \<longrightarrow> \<pi>\<^sub>1 ! i \<approx>\<^sub>\<L> (\<pi>\<^sub>2 ! i))\<close>
  by (simp add: list_all2_conv_all_nth)


lemma eval_exp_bool_same_low_equiv_inst\<^sub>\<T>_None_equiv:
  assumes \<open>\<not>speculating s\<^sub>1 \<and> \<not>speculating s\<^sub>2\<close>
      and \<open>inst\<^sub>\<T> s\<^sub>1 = None\<close>
      and \<open>s\<^sub>1 \<approx>\<^sub>\<L> s\<^sub>2\<close>
    shows \<open>(\<lbrakk>e\<rbrakk>(\<Delta>\<^sub>n s\<^sub>1)) \<longleftrightarrow> (\<lbrakk>e\<rbrakk>(\<Delta>\<^sub>n s\<^sub>2))\<close>
  using assms by (metis \<Delta>\<^sub>0_\<Delta>_no_spec low_equiv_s.simps low_equiv_sub_def)

lemma eval_exp_bool_same_low_equiv_op\<^sub>\<L>_equiv:
  assumes \<open>\<not>speculating s\<^sub>1 \<and> \<not>speculating s\<^sub>2\<close>
      and \<open>op\<^sub>\<L> s\<^sub>1 \<noteq> \<bottom>\<close>
      and \<open>s\<^sub>1 \<approx>\<^sub>\<L> s\<^sub>2\<close>
    shows \<open>(\<lbrakk>e\<rbrakk>(\<Delta>\<^sub>n s\<^sub>1)) \<longleftrightarrow> (\<lbrakk>e\<rbrakk>(\<Delta>\<^sub>n s\<^sub>2))\<close>
  using assms by (meson eval_exp_bool_same_low_equiv_inst\<^sub>\<T>_None_equiv inst\<^sub>\<T>_not_op\<^sub>\<L>_s)




(* Move to adversary lemma*)
lemma low_equiv_append:
  \<open>(\<pi>\<^sub>1::trace) \<approx>\<^sub>\<L> \<pi>\<^sub>2 \<Longrightarrow> \<pi>\<^sub>1' \<approx>\<^sub>\<L> \<pi>\<^sub>2' \<Longrightarrow> (\<pi>\<^sub>1 @ \<pi>\<^sub>1') \<approx>\<^sub>\<L> (\<pi>\<^sub>2 @ \<pi>\<^sub>2')\<close>
  by (simp add: list_all2_appendI)

lemma low_equiv_append1:
  \<open>(\<pi>\<^sub>1::trace) \<approx>\<^sub>\<L> \<pi>\<^sub>2 \<Longrightarrow> s\<^sub>1 \<approx>\<^sub>\<L> s\<^sub>2 \<Longrightarrow> (\<pi>\<^sub>1 @ [s\<^sub>1]) \<approx>\<^sub>\<L> (\<pi>\<^sub>2 @ [s\<^sub>2])\<close>
  by (simp add: list_all2_appendI)

lemma low_equiv_append2:
  \<open>((\<pi>\<^sub>1::trace) @ [s\<^sub>1]) \<approx>\<^sub>\<L> (\<pi>\<^sub>2 @ [s\<^sub>2]) \<Longrightarrow> s\<^sub>1' \<approx>\<^sub>\<L> s\<^sub>2' \<Longrightarrow> (\<pi>\<^sub>1 @ [s\<^sub>1, s\<^sub>1']) \<approx>\<^sub>\<L> (\<pi>\<^sub>2 @ [s\<^sub>2, s\<^sub>2'])\<close>
  using low_equiv_append1 by fastforce

lemma step4_spec_s\<^sub>3_s\<^sub>4_triv_low_equiv:
  assumes \<open>speculating s\<^sub>3 \<and> speculating s\<^sub>4\<close>
    shows \<open>(s\<^sub>3::MachineState) \<approx>\<^sub>\<L> s\<^sub>4\<close>
  using assms by (auto simp add: low_equiv_sub_def)















subsection \<open>Adversary Constraints\<close>

subsubsection \<open>Conformant Store Addresses\<close>

definition \<open>conformantStoreAddr s\<^sub>i \<longleftrightarrow> 
  (\<not>speculating s\<^sub>i \<and> op\<^sub>\<L> s\<^sub>i \<noteq> \<bottom>)
    \<longrightarrow> (case \<iota> s\<^sub>i of Store e\<^sub>1 _ \<Rightarrow> (\<lbrakk>e\<^sub>1\<rbrakk>(\<Delta>\<^sub>0 s\<^sub>i)) \<in> \<U>wr s\<^sub>i | _ \<Rightarrow> True)\<close>

definition \<open>conformantStoreAddrs \<pi> \<longleftrightarrow> (\<forall>s\<^sub>i. s\<^sub>i \<in> set \<pi> \<longrightarrow> conformantStoreAddr s\<^sub>i)\<close>


definition \<open>liststep xs P \<longleftrightarrow> (\<forall>i j. j = Suc i \<longrightarrow> j < length xs \<longrightarrow> P (xs ! i) (xs ! j))\<close>

lemma pair_append_P: \<open>liststep (xs @ [x]) P 
  \<Longrightarrow> P x x'
  \<Longrightarrow> liststep (xs @ [x, x']) P\<close>
  apply (simp only: liststep_def)
  apply (induction xs)
  apply (auto simp add: nth_Cons split: nat.split)
  by (metis append_is_Nil_conv hd_append2 hd_conv_nth length_append_singleton length_greater_0_conv 
            list.size(3) nth_append_length old.nat.simps(4)) (fastforce)


subsubsection \<open>Conformant Entrypoints\<close>

definition \<open>conformantEntrypoint s s' \<longleftrightarrow> 
  (inst\<^sub>\<T> s = \<bottom> \<and> inst\<^sub>\<T> s' \<noteq> None \<longrightarrow> pc\<^sub>0 s' = \<E>\<P> s)\<close>

definition \<open>conformantEntrypoints \<pi> \<longleftrightarrow> liststep \<pi> conformantEntrypoint\<close>

lemma conformantEntrypoints_append: \<open>conformantEntrypoints (\<pi> @ [s]) 
  \<Longrightarrow> conformantEntrypoint s s'
  \<Longrightarrow> conformantEntrypoints (\<pi> @ [s, s'])\<close>
  apply (simp add: conformantEntrypoints_def)
  by (simp add: pair_append_P)

(* TODO understand this: For all \<pi>\<^sub>i *)
(**      \<not>speculating \<pi>\<^sub>i \<and> \<not>speculating \<pi>\<^sub>j
      \<longrightarrow> (\<forall>k . i < k \<and> k < j \<longrightarrow> speculating (nth \<pi> k))*)



subsubsection \<open>Conformant Stutter\<close>

definition \<open>conformantStutter s\<^sub>s s\<^sub>n\<^sub>s s\<^sub>n\<^sub>s' \<longleftrightarrow> (speculating s\<^sub>s \<longrightarrow> s\<^sub>n\<^sub>s = s\<^sub>n\<^sub>s')\<close>

definition \<open>conformantStutterPair pair pair' \<longleftrightarrow> 
  (let (s\<^sub>s, s\<^sub>n\<^sub>s) = pair; (s\<^sub>s', s\<^sub>n\<^sub>s') = pair' in conformantStutter s\<^sub>s s\<^sub>n\<^sub>s s\<^sub>n\<^sub>s')\<close>

definition \<open>conformantStutters \<pi>\<^sub>s \<pi>\<^sub>n\<^sub>s \<longleftrightarrow> liststep (zip \<pi>\<^sub>s \<pi>\<^sub>n\<^sub>s) conformantStutterPair\<close>

lemma conformantStutter_equiv:
  \<open>conformantStutterPair (s\<^sub>s, s\<^sub>n\<^sub>s) (s\<^sub>s', s\<^sub>n\<^sub>s') = conformantStutter s\<^sub>s s\<^sub>n\<^sub>s s\<^sub>n\<^sub>s'\<close>
  by (simp add: conformantStutterPair_def)

lemma conformantStutterPair_append: 
  assumes \<open>conformantStutters (\<pi>\<^sub>s @ [s\<^sub>s]) (\<pi>\<^sub>n\<^sub>s @ [s\<^sub>n\<^sub>s])\<close>
  and \<open>conformantStutterPair (s\<^sub>s, s\<^sub>n\<^sub>s) (s\<^sub>s', s\<^sub>n\<^sub>s')\<close>
  and \<open>length \<pi>\<^sub>s = length \<pi>\<^sub>n\<^sub>s\<close>
shows \<open>conformantStutters (\<pi>\<^sub>s @ [s\<^sub>s, s\<^sub>s']) (\<pi>\<^sub>n\<^sub>s @ [s\<^sub>n\<^sub>s, s\<^sub>n\<^sub>s'])\<close>
  using assms apply (simp add: conformantStutters_def)
  by (simp add: pair_append_P)

lemma conformantStutter_append: \<open>conformantStutters (\<pi>\<^sub>s @ [s\<^sub>s]) (\<pi>\<^sub>n\<^sub>s @ [s\<^sub>n\<^sub>s]) 
  \<Longrightarrow> conformantStutter s\<^sub>s s\<^sub>n\<^sub>s s\<^sub>n\<^sub>s'
  \<Longrightarrow> length \<pi>\<^sub>s = length \<pi>\<^sub>n\<^sub>s
  \<Longrightarrow> conformantStutters (\<pi>\<^sub>s @ [s\<^sub>s, s\<^sub>s']) (\<pi>\<^sub>n\<^sub>s @ [s\<^sub>n\<^sub>s, s\<^sub>n\<^sub>s'])\<close>
  by (simp add: conformantStutters_def conformantStutter_equiv pair_append_P)




















subsubsection \<open>Model of conformancy\<close>


text \<open>A trace is conformant if there is no speculation in the first state and the trusted component
has been initialized. Every state must also satisfy the conformantStoreAddress and 
conformantEntrypoints predicates\<close>


definition \<open>conformant \<pi> \<equiv>
  let \<pi>\<^sub>0 = (hd \<pi>) in
    \<not> speculating \<pi>\<^sub>0
    \<and> conformantStoreAddrs \<pi>
    \<and> conformantEntrypoints \<pi>
\<close>


(* Lift *)
definition \<open>speculates \<pi> \<longleftrightarrow> 
  (\<exists>s. s \<in> set \<pi> \<and> speculating s)\<close>

text \<open>Prove that \<not>speculates \<pi> is equivalent to the paper syntax\<close>

lemma \<open>\<not>speculates \<pi> \<longleftrightarrow> (\<forall>s. s \<in> set \<pi> \<longrightarrow> \<not>speculating s)\<close>
  by (simp add: speculates_def)

text \<open>Prove we can append speculating and non speculating states to the trace predicate\<close>

lemma speculates_append: \<open>\<not>speculates \<pi> \<Longrightarrow> speculating s \<Longrightarrow> speculates (\<pi> @ [s])\<close>
  by (metis last_in_set snoc_eq_iff_butlast speculates_def)

lemma not_speculates_append: \<open>\<not>speculates \<pi> \<and> \<not>speculating s \<longleftrightarrow> \<not>speculates (\<pi> @ [s])\<close>
  by (auto simp add: speculates_def)

lemma not_speculates_append2: \<open>\<not>speculates \<pi> \<and> \<not>speculates \<pi> \<and> \<not>speculating s \<and> \<not>speculating s' 
    \<longleftrightarrow> \<not>speculates (\<pi> @ [s, s'])\<close>
  by (auto simp add: speculates_def)


definition \<open>mispredicts \<pi> \<longleftrightarrow> 
  (\<exists>s. s \<in> set \<pi> \<and> mispred (n s) (\<beta> s) (pc s))\<close>

text \<open>Prove that \<not>mispredicts \<pi> is equivalent to the paper syntax\<close>

lemma \<open>\<not>mispredicts \<pi> \<longleftrightarrow> (\<forall>s. s \<in> set \<pi> \<longrightarrow> \<not>mispred (n s) (\<beta> s) (pc s))\<close>
  by (simp add: mispredicts_def)


definition conformantTPOD :: 
\<open>trace \<Rightarrow> trace \<Rightarrow> trace \<Rightarrow> trace \<Rightarrow> bool\<close> 
  where
\<open>conformantTPOD \<pi>\<^sub>1 \<pi>\<^sub>2 \<pi>\<^sub>3 \<pi>\<^sub>4 \<equiv>
  conformant \<pi>\<^sub>1 \<and>
  conformant \<pi>\<^sub>2 \<and>
  conformant \<pi>\<^sub>3 \<and>
  conformant \<pi>\<^sub>4 \<and>
  \<not>mispredicts \<pi>\<^sub>1 \<and> 
  \<not>mispredicts \<pi>\<^sub>2 \<and>
  mispredicts \<pi>\<^sub>3 \<and>
  mispredicts \<pi>\<^sub>4 \<and>
  (((op\<^sub>\<L> \<pi>\<^sub>1)::low_operation list) = op\<^sub>\<L> \<pi>\<^sub>2 \<and> ((op\<^sub>\<L> \<pi>\<^sub>1)::low_operation list) = op\<^sub>\<L> \<pi>\<^sub>3 \<and> ((op\<^sub>\<L> \<pi>\<^sub>1)::low_operation list) = op\<^sub>\<L> \<pi>\<^sub>4) \<and>
  (((op\<^sub>\<H> \<pi>\<^sub>1)::high_operation list) = op\<^sub>\<H> \<pi>\<^sub>3 \<and> ((op\<^sub>\<H> \<pi>\<^sub>2)::high_operation list) = op\<^sub>\<H> \<pi>\<^sub>4) \<and>
  (\<pi>\<^sub>1 \<approx>\<^sub>\<L> \<pi>\<^sub>2 \<and> ((hd \<pi>\<^sub>3) \<approx>\<^sub>\<L> (hd \<pi>\<^sub>4)))
\<close>


end
