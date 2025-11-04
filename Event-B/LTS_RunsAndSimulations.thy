theory LTS_RunsAndSimulations
  imports LTS_Basic
begin

(* ===== ТРАССЫ (RUNS) ===== *)

record ('st, 'ev) Run =
  trns :: "('st \<times> 'ev) list"
  fins :: "'st"

definition append_tr :: "('st, 'ev) Run \<Rightarrow> ('st, 'ev) Tr \<Rightarrow> ('st, 'ev) Run" where
  "append_tr run t \<equiv> \<lparr> 
    trns = (trns run) @ [(fins run, lbl t)],
    fins = dst t 
  \<rparr>"

(* Индуктивное определение множества трасс LTS *)
inductive_set runs :: "('st, 'ev) LTS \<Rightarrow> ('st, 'ev) Run set" for l :: "('st, 'ev) LTS" where
  start: "s \<in> init l \<Longrightarrow> \<lparr> trns = [], fins = s \<rparr> \<in> runs l"
| step: "\<lbrakk> r \<in> runs l; t \<in> outgoing l (fins r) \<rbrakk> \<Longrightarrow> append_tr r t \<in> runs l"

(* ===== ЛЕММЫ О ТРАССАХ ===== *)

lemma runs_start_initial:
  assumes "r \<in> runs l"
  shows "(if trns r = [] then fins r else fst (hd (trns r))) \<in> init l"
  using assms
  by (induction rule: runs.induct) auto

lemma run_steps:
  assumes "r \<in> runs l" and "i < length (trns r)"
  shows "\<lparr> 
    src = fst (trns r ! i),
    dst = (if Suc i < length (trns r) then fst (trns r ! Suc i) else fins r),
    lbl = snd (trns r ! i)
  \<rparr> \<in> trans l"
  using assms
proof (induction r arbitrary: i rule: runs.induct)
  case (start s)
  then show ?case by simp
next
  case (step r t)
  show ?case
  proof (cases i)
    case (Suc j)
    with step show ?thesis
      by (auto simp: append_tr_def nth_append)
  qed (auto simp: append_tr_def)
qed

lemma states_runs: "states l = fins ` (runs l)"
proof
  show "states l \<subseteq> fins ` runs l"
  proof
    fix s assume "s \<in> states l"
    then show "s \<in> fins ` runs l"
    proof (induction rule: states.induct)
      case (base s)
      then show ?case
        by (metis runs.start Run.surjective image_eqI)
    next
      case (step s t)
      then obtain r where "r \<in> runs l" and "fins r = s"
        by auto
      with step have "append_tr r t \<in> runs l" and "fins (append_tr r t) = dst t"
        by (auto simp: append_tr_def runs.step)
      then show ?case by auto
    qed
  qed
  show "fins ` runs l \<subseteq> states l"
  proof
    fix s assume "s \<in> fins ` runs l"
    then obtain r where "r \<in> runs l" and "s = fins r"
      by auto
    then show "s \<in> states l"
      by (induction rule: runs.induct)
         (auto simp: states.base states.step append_tr_def)
  qed
qed

(* ===== ТРАССЫ (TRACES) ===== *)

type_synonym 'ev Trace = "'ev list"

definition trace_of :: "('st, 'ev) Run \<Rightarrow> 'ev Trace" where
  "trace_of run \<equiv> map snd (trns run)"

definition traces :: "('st, 'ev) LTS \<Rightarrow> 'ev Trace set" where
  "traces l \<equiv> trace_of ` (runs l)"

(* ===== СИМУЛЯЦИИ МЕЖДУ LTS ===== *)

definition sim_transition :: "('st \<times> 'st) set \<Rightarrow> (('st, 'ev) Tr \<times> ('st, 'ev) Tr) set" where
  "sim_transition r \<equiv> { (t, t') | t t'. 
    (src t, src t') \<in> r \<and> (dst t, dst t') \<in> r \<and> lbl t = lbl t' }"

definition simulation :: "('st \<times> 'st) set \<Rightarrow> (('st, 'ev) LTS \<times> ('st, 'ev) LTS) set" where
  "simulation r \<equiv> { (l, l') | l l'. 
    (\<forall>s \<in> init l. \<exists>s' \<in> init l'. (s, s') \<in> r) \<and>
    (\<forall>(s, s') \<in> r. \<forall>t \<in> outgoing l s. \<exists>t' \<in> outgoing l' s'. (t, t') \<in> sim_transition r) }"

definition simulated :: "('st, 'ev) LTS \<Rightarrow> ('st, 'ev) LTS \<Rightarrow> bool" (infix "\<preceq>" 50) where
  "l \<preceq> l' \<equiv> \<exists>r. (l, l') \<in> simulation r"

(* ===== СТРУКТУРНЫЕ СВОЙСТВА СИМУЛЯЦИЙ ===== *)

lemma simulation_identity: 
  "(Id :: (('st, 'ev) LTS \<times> ('st, 'ev) LTS) set) \<subseteq> simulation (Id :: ('st \<times> 'st) set)"
  unfolding simulation_def sim_transition_def outgoing_def
  by auto

lemma simulation_composition:
  assumes "(l, l') \<in> simulation r" and "(l', l'') \<in> simulation r'"
  shows "(l, l'') \<in> simulation (r O r')"
proof -
  from assms obtain r_def r'_def where
    sim1: "(l, l') \<in> simulation r" and
    sim2: "(l', l'') \<in> simulation r'"
    by auto
  
  show ?thesis
    unfolding simulation_def
  proof safe
    fix s assume "s \<in> init l"
    with sim1 obtain s' where "s' \<in> init l'" and "(s, s') \<in> r"
      unfolding simulation_def by blast
    with sim2 obtain s'' where "s'' \<in> init l''" and "(s', s'') \<in> r'"
      unfolding simulation_def by blast
    then show "\<exists>s''\<in>init l''. (s, s'') \<in> r O r'"
      using \<open>(s, s') \<in> r\<close> by blast
  next
    fix s s'' assume "(s, s'') \<in> r O r'"
    then obtain s' where "(s, s') \<in> r" and "(s', s'') \<in> r'"
      by auto
    
    fix t assume "t \<in> outgoing l s"
    with sim1 \<open>(s, s') \<in> r\<close> obtain t' where 
      "t' \<in> outgoing l' s'" and "(t, t') \<in> sim_transition r"
      unfolding simulation_def by blast
    
    with sim2 \<open>(s', s'') \<in> r'\<close> obtain t'' where
      "t'' \<in> outgoing l'' s''" and "(t', t'') \<in> sim_transition r'"
      unfolding simulation_def by blast
    
    show "\<exists>t''\<in>outgoing l'' s''. (t, t'') \<in> sim_transition (r O r')"
    proof
      show "t'' \<in> outgoing l'' s''" by fact
      show "(t, t'') \<in> sim_transition (r O r')"
        using \<open>(t, t') \<in> sim_transition r\<close> \<open>(t', t'') \<in> sim_transition r'\<close>
        unfolding sim_transition_def
        by auto (metis relcomp.relcompI)
    qed
  qed
qed

lemma simulates_reflexive: "l \<preceq> l"
  unfolding simulated_def
  using simulation_identity by auto

lemma simulates_transitive: 
  assumes "l \<preceq> l'" and "l' \<preceq> l''"
  shows "l \<preceq> l''"
  using assms unfolding simulated_def
  by (metis simulation_composition)

(* ===== СИМУЛЯЦИИ ТРАСС ===== *)

definition sim_run :: "('st \<times> 'st) set \<Rightarrow> (('st, 'ev) Run \<times> ('st, 'ev) Run) set" where
  "sim_run r \<equiv> { (run, run') | run run'. 
    length (trns run) = length (trns run') \<and>
    (\<forall>i < length (trns run). 
      (fst (trns run ! i), fst (trns run' ! i)) \<in> r \<and>
      snd (trns run ! i) = snd (trns run' ! i)) \<and>
    (fins run, fins run') \<in> r }"

theorem sim_run:
  assumes "(l, l') \<in> simulation r" and "run \<in> runs l"
  shows "\<exists>run' \<in> runs l'. (run, run') \<in> sim_run r"
  using assms
proof (induction run rule: runs.induct)
  case (start s)
  then obtain s' where "s' \<in> init l'" and "(s, s') \<in> r"
    unfolding simulation_def by blast
  then have "\<lparr>trns = [], fins = s'\<rparr> \<in> runs l'"
    by (rule runs.start)
  moreover have "(\<lparr>trns = [], fins = s\<rparr>, \<lparr>trns = [], fins = s'\<rparr>) \<in> sim_run r"
    using \<open>(s, s') \<in> r\<close>
    unfolding sim_run_def by auto
  ultimately show ?case by blast
next
  case (step r t)
  then obtain run' where 
    run'_in: "run' \<in> runs l'" and 
    sim: "(r, run') \<in> sim_run r_rel"
    by auto
  
  have "t \<in> outgoing l (fins r)"
    using step by simp
  moreover have "(fins r, fins run') \<in> r_rel"
    using sim unfolding sim_run_def by auto
  ultimately obtain t' where
    t'_in: "t' \<in> outgoing l' (fins run')" and
    t_sim: "(t, t') \<in> sim_transition r_rel"
    using assms(1) unfolding simulation_def by blast
  
  define run'' where "run'' = append_tr run' t'"
  
  have "run'' \<in> runs l'"
    using run'_in t'_in unfolding run''_def
    by (rule runs.step)
  
  moreover have "(append_tr r t, run'') \<in> sim_run r_rel"
  proof -
    from sim have 
      len_eq: "length (trns r) = length (trns run')" and
      states_sim: "\<forall>i<length (trns r). (fst (trns r ! i), fst (trns run' ! i)) \<in> r_rel" and
      events_eq: "\<forall>i<length (trns r). snd (trns r ! i) = snd (trns run' ! i)" and
      final_sim: "(fins r, fins run') \<in> r_rel"
      unfolding sim_run_def by auto
    
    from t_sim have 
      src_sim: "(src t, src t') \<in> r_rel" and
      dst_sim: "(dst t, dst t') \<in> r_rel" and
      lbl_eq: "lbl t = lbl t'"
      unfolding sim_transition_def by auto
    
    show ?thesis
      unfolding sim_run_def run''_def append_tr_def
    proof safe
      show "length (trns r @ [(fins r, lbl t)]) = length (trns run' @ [(fins run', lbl t')])"
        using len_eq by simp
      
      fix i assume "i < length (trns r @ [(fins r, lbl t)])"
      then consider (trns) "i < length (trns r)" | (final) "i = length (trns r)"
        by (auto simp: less_Suc_eq)
      then show "(fst ((trns r @ [(fins r, lbl t)]) ! i), 
                 fst ((trns run' @ [(fins run', lbl t')]) ! i)) \<in> r_rel"
        and "snd ((trns r @ [(fins r, lbl t)]) ! i) = 
             snd ((trns run' @ [(fins run', lbl t')]) ! i)"
      proof cases
        case trns
        with states_sim events_eq show ?thesis
          by (auto simp: nth_append)
      next
        case final
        with src_sim lbl_eq final_sim show ?thesis
          by (auto simp: nth_append)
      qed
      
      show "(dst t, dst t') \<in> r_rel"
        using dst_sim by simp
    qed
  qed
  
  ultimately show ?case by blast
qed

(* ===== СВОЙСТВА ТРАСС ПРИ СИМУЛЯЦИИ ===== *)

lemma sim_run_trace_eq:
  assumes "(run, run') \<in> sim_run r"
  shows "trace_of run = trace_of run'"
  using assms
  unfolding sim_run_def trace_of_def
  by (auto intro!: nth_equalityI)

theorem sim_traces:
  assumes "(l, l') \<in> simulation r" and "tr \<in> traces l"
  shows "tr \<in> traces l'"
proof -
  from assms(2) obtain run where
    "run \<in> runs l" and "tr = trace_of run"
    unfolding traces_def by auto
  
  with assms(1) obtain run' where
    "run' \<in> runs l'" and "(run, run') \<in> sim_run r"
    by (auto dest: sim_run)
  
  then have "tr = trace_of run'"
    using \<open>tr = trace_of run\<close> by (auto intro: sim_run_trace_eq)
  
  with \<open>run' \<in> runs l'\<close> show ?thesis
    unfolding traces_def by auto
qed

corollary simulated_traces: 
  assumes "l \<preceq> l'"
  shows "traces l \<subseteq> traces l'"
  using assms sim_traces
  unfolding simulated_def by blast

end