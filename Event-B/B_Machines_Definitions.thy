theory B_Machines_Definitions
  imports LTS_Basic LTS_RunsAndSimulations
begin

(* === 4.1 B-МАШИНЫ === *)

record ('st, 'ev) B_machine =
  lts :: "('st, 'ev) LTS"
  invariant :: "'st \<Rightarrow> bool"

definition sound_B_machine :: "('st, 'ev) B_machine \<Rightarrow> bool" where
  "sound_B_machine m \<equiv> \<forall>s \<in> states (lts m). invariant m s"

theorem machine_po:
  assumes "\<forall>s \<in> init (lts m). invariant m s"
    and "\<forall>t \<in> trans (lts m). invariant m (src t) \<longrightarrow> invariant m (dst t)"
  shows "sound_B_machine m"
  oops

(* === 4.2 B-РЕФАЙНМЕНТЫ === *)

record ('st, 'ev) B_refinement =
  abstract :: "('st, 'ev) LTS"
  concrete :: "('st, 'ev) LTS" 
  invariant :: "'st \<times> 'st \<Rightarrow> bool"

definition sound_B_refinement :: "('st, 'ev) B_refinement \<Rightarrow> bool" where
  "sound_B_refinement r \<equiv> 
    (concrete r, abstract r) \<in> simulation_B (Collect (invariant r))"

lemma refinement_sim:
  assumes "sound_B_refinement r"
  shows "concrete r \<preceq>\<^sub>B abstract r"
  oops

(* Структурные свойства *)
definition refinement_id :: "('st, 'ev) LTS \<Rightarrow> ('st, 'ev) B_refinement" where
  "refinement_id l \<equiv> \<lparr>
    abstract = l,
    concrete = l, 
    invariant = (\<lambda>(s, t). s = t)
  \<rparr>"

lemma refinement_id: "sound_B_refinement (refinement_id l)"
  oops

definition refinement_compose :: 
  "('st, 'ev) B_refinement \<Rightarrow> ('st, 'ev) B_refinement \<Rightarrow> ('st, 'ev) B_refinement" where
  "refinement_compose r r' \<equiv> \<lparr>
    abstract = abstract r,
    concrete = concrete r',
    invariant = \<lambda>p. p \<in> Collect (invariant r') O Collect (invariant r)
  \<rparr>"

lemma refinement_compose_sound:
  assumes "sound_B_refinement r" "sound_B_refinement r'"
    and "concrete r = abstract r'"
  shows "sound_B_refinement (refinement_compose r r')"
  oops

(* === B-ДИЗАЙНЫ И РАЗРАБОТКИ === *)

type_synonym ('st, 'ev) B_design = "('st, 'ev) B_refinement list"

definition sound_B_design :: "('st, 'ev) B_design \<Rightarrow> bool" where
  "sound_B_design refs \<equiv> \<forall>i < length refs.
    sound_B_refinement (refs ! i) \<and>
    (Suc i < length refs \<longrightarrow> concrete (refs ! i) = abstract (refs ! (Suc i)))"

lemma design_sim:
  assumes "sound_B_design refs" and "refs \<noteq> []"
  shows "concrete (last refs) \<preceq>\<^sub>B abstract (hd refs)"
  oops

record ('st, 'ev) B_development =
  spec :: "('st, 'ev) B_machine"
  design :: "('st, 'ev) B_design"

definition sound_B_development :: "('st, 'ev) B_development \<Rightarrow> bool" where
  "sound_B_development dev \<equiv>
    sound_B_machine (spec dev) \<and>
    sound_B_design (design dev) \<and>
    (design dev \<noteq> [] \<longrightarrow> lts (spec dev) = abstract (hd (design dev)))"

theorem development_sim:
  assumes "sound_B_development d" and "design d \<noteq> []"
  shows "concrete (last (design d)) \<preceq>\<^sub>B lts (spec d)"
  oops

(* === КОМПОЗИЦИЯ КОМПОНЕНТОВ (INCLUDES) === *)

record ('st, 'ev) Includes =
  lts :: "('st, 'ev) LTS"
  sync_st :: "'st \<Rightarrow> 'st" 
  sync_ev :: "'ev \<Rightarrow> 'ev option"

definition sound_includes :: "('st, 'ev) LTS \<Rightarrow> ('st, 'ev) Includes \<Rightarrow> bool" where
  "sound_includes A I \<equiv>
    let C = lts I; \<pi> = sync_st I; \<sigma> = sync_ev I in
    \<pi> ` (init A) \<subseteq> init C \<and>
    (\<forall>t \<in> trans A. case \<sigma>(lbl t) of
      None \<Rightarrow> \<pi>(src t) = \<pi>(dst t)
    | Some e \<Rightarrow> \<lparr>src = \<pi>(src t), dst = \<pi>(dst t), lbl = e\<rparr> \<in> trans C)"

theorem includes_states:
  assumes "s \<in> states A" and "sound_includes A I" 
  shows "sync_st I s \<in> states (lts I)"
  oops

definition interaction_trns :: 
  "('st, 'ev) LTS \<Rightarrow> ('st, 'ev) Includes \<Rightarrow> ('st \<times> 'ev) list \<Rightarrow> ('st \<times> 'ev) list" where
  "interaction_trns A I seq \<equiv>
    map (\<lambda>(s, e). (sync_st I s, the (sync_ev I e)))
        (filter (\<lambda>(s, e). sync_ev I e \<noteq> None) seq)"

definition interaction :: 
  "('st, 'ev) LTS \<Rightarrow> ('st, 'ev) Includes \<Rightarrow> ('st, 'ev) Run \<Rightarrow> ('st, 'ev) Run" where
  "interaction A I run \<equiv> \<lparr>
    trns = interaction_trns A I (trns run),
    fins = sync_st I (fins run)
  \<rparr>"

theorem interaction_runs:
  assumes "r \<in> runs A" and "sound_includes A I"
  shows "interaction A I r \<in> runs (lts I)"
  oops

theorem interaction_traces:
  assumes "tr \<in> traces A" and "sound_includes A I"
  shows "map (the \<circ> sync_ev I) (filter (\<lambda>e. sync_ev I e \<noteq> None) tr) \<in> traces (lts I)"
  oops

end