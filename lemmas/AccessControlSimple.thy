theory AccessControlSimple
imports Main
begin

datatype role = User | Admin | Guest
datatype operation = Read | Write | Execute | Delete

type_synonym user_id = string
type_synonym permission = "role \<Rightarrow> operation \<Rightarrow> bool"

record system_state =
  users :: "user_id \<rightharpoonup> role"
  files :: "string \<rightharpoonup> (user_id \<times> bool)"
  perms :: permission

fun has_access :: "system_state \<Rightarrow> user_id \<Rightarrow> operation \<Rightarrow> string \<Rightarrow> bool" where
  "has_access sys user action file = 
    (case (users sys user, files sys file) of
       (Some role, Some (owner, is_public)) \<Rightarrow>
         if perms sys role action then
           if action = Read \<and> is_public then True
           else user = owner
         else False
     | _ \<Rightarrow> False)"


definition default_perms :: permission where
  "default_perms = (\<lambda>role action.
    (role = Admin) \<or> 
    (role = User \<and> (action = Read \<or> action = Write)) \<or> 
    (role = Guest \<and> action = Read))"

definition test_system :: system_state where
  "test_system = \<lparr>
    users = [''alice'' \<mapsto> User, ''bob'' \<mapsto> User, ''admin'' \<mapsto> Admin, ''visitor'' \<mapsto> Guest],
    files = [''public.txt'' \<mapsto> (''alice'', True), 
             ''secret.txt'' \<mapsto> (''alice'', False),
             ''bob_file.txt'' \<mapsto> (''bob'', False)] ,
    perms = default_perms 
  \<rparr>"

value "has_access test_system ''alice'' Read ''public.txt''"      (* True *)
value "has_access test_system ''bob'' Write ''secret.txt''"       (* False *)
value "has_access test_system ''admin'' Delete ''bob_file.txt''"  (* True *)
value "has_access test_system ''visitor'' Write ''public.txt''"   (* False *)
value "has_access test_system ''visitor'' Read ''public.txt''"


definition example_partial :: "nat \<rightharpoonup> nat" where
  "example_partial = Map.empty"

definition my_map :: "nat \<rightharpoonup> string" where
  "my_map = [1 \<mapsto> ''one'', 2 \<mapsto> ''two'']"

value "my_map 1"  (* Some ''one'' *)
value "my_map 3"  (* None *)


value "(example_partial(1 \<mapsto> 5)) 1"  (* Some 5 *)
value "(example_partial(1 \<mapsto> 5)) 3" 

lemma "has_access test_system ''visitor'' Read ''public.txt''"
  by (simp add: has_access.simps test_system_def default_perms_def)

lemma visitor_can_read_public:
  "has_access test_system ''visitor'' Read ''public.txt''"
proof -
  have "users test_system ''visitor'' = Some Guest"
    unfolding test_system_def by simp
  moreover have "files test_system ''public.txt'' = Some (''alice'', True)"
    unfolding test_system_def by simp
  moreover have "default_perms Guest Read = True"
    unfolding default_perms_def by simp
  ultimately show ?thesis
    by (simp add: has_access.simps test_system_def)
qed

definition user_policy :: "user_id \<Rightarrow> operation \<Rightarrow> string \<Rightarrow> bool" where
  "user_policy user op file = 
     (case users test_system user of
        Some role \<Rightarrow> 
          (case files test_system file of
             Some (owner, is_public) \<Rightarrow>
               perms test_system role op \<and>
               (if op = Read then is_public else user = owner)
           | None \<Rightarrow> False)
      | None \<Rightarrow> False)"

theorem policy_consistency:
  "\<forall>user1 user2 op file.
     users test_system user1 = users test_system user2 \<longrightarrow>
     has_access test_system user1 op file = has_access test_system user2 op file"
  unfolding has_access.simps test_system_def
  by auto

theorem guest_restrictions_simple:
  "\<forall>user fname. 
     users test_system user = Some Guest \<longrightarrow>
     (has_access test_system user Read fname \<longleftrightarrow> 
        (\<exists>owner. files test_system fname = Some (owner, True))) \<and>
     (\<forall>op. op \<noteq> Read \<longrightarrow> \<not> has_access test_system user op fname)"
  unfolding has_access.simps test_system_def default_perms_def
  apply (intro allI impI conjI)
    apply (auto split: option.split_asm if_split_asm)[1]
   apply (auto split: option.split_asm if_split_asm)[1]
   done

 theorem user_restrictions:
  "\<forall>user fname. 
     users test_system user = Some User \<longrightarrow>
     (has_access test_system user Read fname \<longleftrightarrow> 
        (\<exists>owner is_public. files test_system fname = Some (owner, is_public) \<and> 
         (is_public \<or> user = owner))) \<and>
     (has_access test_system user Write fname \<longleftrightarrow> 
        (\<exists>owner is_public. files test_system fname = Some (owner, is_public) \<and> 
         user = owner)) \<and>
     (\<forall>op. op \<noteq> Read \<and> op \<noteq> Write \<longrightarrow> \<not> has_access test_system user op fname)"
  unfolding has_access.simps test_system_def default_perms_def
  apply (intro allI impI conjI)
  apply (auto split: option.split_asm if_split_asm)[1]
  by fastforce
 

 (* theorem user_restrictions_simple:
  "\<forall>user fname. 
     users test_system user = Some User \<longrightarrow>
     (has_access test_system user Read fname \<longleftrightarrow> 
        (\<exists>owner is_public. files test_system fname = Some (owner, is_public) \<and> 
         (is_public \<or> user = owner))) \<and>
     (has_access test_system user Write fname \<longleftrightarrow> 
        (\<exists>owner is_public. files test_system fname = Some (owner, is_public) \<and> 
         user = owner)) \<and>
     (\<forall>op. op \<noteq> Read \<and> op \<noteq> Write \<longrightarrow> \<not> has_access test_system user op fname)"
  unfolding has_access.simps test_system_def default_perms_def
  by (auto split: option.split_asm if_split_asm operation.split_asm)
  *)

lemma user_read_access:
  "\<forall>user fname. 
     users test_system user = Some User \<longrightarrow>
     (has_access test_system user Read fname \<longleftrightarrow> 
        (\<exists>owner is_public. files test_system fname = Some (owner, is_public) \<and> 
         (is_public \<or> user = owner)))"
  unfolding has_access.simps test_system_def default_perms_def
  by (auto split: option.split_asm if_split_asm)

lemma user_write_access:
  "\<forall>user fname. 
     users test_system user = Some User \<longrightarrow>
     (has_access test_system user Write fname \<longleftrightarrow> 
        (\<exists>owner is_public. files test_system fname = Some (owner, is_public) \<and> 
         user = owner))"
  unfolding has_access.simps test_system_def default_perms_def
  by (auto split: option.split_asm if_split_asm)

lemma user_no_other_access:
  "\<forall>user fname op. 
     users test_system user = Some User \<longrightarrow> 
     op \<noteq> Read \<and> op \<noteq> Write \<longrightarrow>
     \<not> has_access test_system user op fname"
  unfolding has_access.simps test_system_def default_perms_def
  by (auto split: option.split_asm if_split_asm operation.split_asm)

(* theorem user_restrictions_combined:
  "\<forall>user fname. 
     users test_system user = Some User \<longrightarrow>
     (has_access test_system user Read fname \<longleftrightarrow> 
        (\<exists>owner is_public. files test_system fname = Some (owner, is_public) \<and> 
         (is_public \<or> user = owner))) \<and>
     (has_access test_system user Write fname \<longleftrightarrow> 
        (\<exists>owner is_public. files test_system fname = Some (owner, is_public) \<and> 
         user = owner)) \<and>
     (\<forall>op. op \<noteq> Read \<and> op \<noteq> Write \<longrightarrow> \<not> has_access test_system user op fname)"
  by (auto simp: user_read_access user_write_access user_no_other_access)
  
 *)

theorem user_restrictions_combined:
  "\<forall>user fname. 
     users test_system user = Some User \<longrightarrow>
     (has_access test_system user Read fname \<longleftrightarrow> 
        (\<exists>owner is_public. files test_system fname = Some (owner, is_public) \<and> 
         (is_public \<or> user = owner))) \<and>
     (has_access test_system user Write fname \<longleftrightarrow> 
        (\<exists>owner is_public. files test_system fname = Some (owner, is_public) \<and> 
         user = owner)) \<and>
     (\<forall>op. op \<noteq> Read \<and> op \<noteq> Write \<longrightarrow> \<not> has_access test_system user op fname)"
proof (intro allI impI)
  fix user fname
  assume user_role: "users test_system user = Some User"
  
  have read_part: "has_access test_system user Read fname \<longleftrightarrow> 
                   (\<exists>owner is_public. files test_system fname = Some (owner, is_public) \<and> 
                    (is_public \<or> user = owner))"
    using user_read_access user_role by blast
  
  have write_part: "has_access test_system user Write fname \<longleftrightarrow> 
                    (\<exists>owner is_public. files test_system fname = Some (owner, is_public) \<and> 
                     user = owner)"
    using user_write_access user_role by blast
  
  have other_part: "\<forall>op. op \<noteq> Read \<and> op \<noteq> Write \<longrightarrow> \<not> has_access test_system user op fname"
    using user_no_other_access user_role by blast
  
  show "(has_access test_system user Read fname \<longleftrightarrow> 
          (\<exists>owner is_public. files test_system fname = Some (owner, is_public) \<and> 
           (is_public \<or> user = owner))) \<and>
        (has_access test_system user Write fname \<longleftrightarrow> 
          (\<exists>owner is_public. files test_system fname = Some (owner, is_public) \<and> 
           user = owner)) \<and>
        (\<forall>op. op \<noteq> Read \<and> op \<noteq> Write \<longrightarrow> \<not> has_access test_system user op fname)"
    using read_part write_part other_part by blast
qed





end