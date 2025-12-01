theory KubernetesCluster
  imports Main "HOL-Library.FSet" "HOL-Library.Finite_Map"
begin

(* Типы данных *)
type_synonym DeploymentName = string
type_synonym NodeName = string
type_synonym PodId = nat

record Pod =
  deployment :: DeploymentName
  node :: NodeName
  id :: PodId

type_synonym DeploymentState = "DeploymentName \<Rightarrow> nat"
type_synonym PodSet = "Pod fset"
type_synonym ServiceSet = "DeploymentName fset"

(* Состояние системы *)
record State =
  deployments :: DeploymentState
  pods :: PodSet
  services :: ServiceSet
  configmaps :: "string fset"
  secrets :: "string fset"

(* Константы *)
definition MaxReplicas :: nat where "MaxReplicas = 3"
definition NodeSet :: "NodeName fset" where "NodeSet = {|''node1'', ''node2''|}"

(* Инварианты *)
definition TypeInvariant :: "State \<Rightarrow> bool" where
  "TypeInvariant s \<equiv>
    (\<forall>d. deployments s d \<le> MaxReplicas) \<and>
    (\<forall>d. deployments s d \<ge> card (ffilter (\<lambda>p. deployment p = d) (pods s))) \<and>
    fBall (services s) (\<lambda>s. s \<in> {|''nginx-service''|})"

definition NoOrphanedPods :: "State \<Rightarrow> bool" where
  "NoOrphanedPods s \<equiv>
    fBall (pods s) (\<lambda>p. deployment p \<in> {|''nginx-deployment''|})"

definition NodeCapacity :: "State \<Rightarrow> bool" where
  "NodeCapacity s \<equiv>
    fBall NodeSet (\<lambda>n. card (ffilter (\<lambda>p. node p = n) (pods s)) \<le> MaxReplicas)"

(* Действия *)
definition ScaleUp :: "DeploymentName \<Rightarrow> State \<Rightarrow> State \<Rightarrow> bool" where
  "ScaleUp d s s' \<equiv>
    deployments s d < MaxReplicas \<and>
    deployments s' = (deployments s)(d := deployments s d + 1) \<and>
    pods s' = pods s \<and> services s' = services s"

definition ScaleDown_v1 :: "DeploymentName \<Rightarrow> State \<Rightarrow> State \<Rightarrow> bool" where
  "ScaleDown_v1 d s s' \<equiv>
    deployments s d > 0 \<and>
    card (ffilter (\<lambda>p. deployment p = d) (pods s)) = 0 \<and>
    deployments s' = (deployments s)(d := deployments s d - 1) \<and>
    pods s' = pods s \<and> services s' = services s"

(* Начальное состояние *)
definition InitState :: State where
  "InitState = \<lparr>
    deployments = (\<lambda>_. 0)(''nginx-deployment'' := 0),
    pods = {||},
    services = {|''nginx-service''|},
    configmaps = {||},
    secrets = {||}
  \<rparr>"

(* Доказательство инвариантов *)
lemma invariant_preservation:
  assumes "TypeInvariant s"
  assumes "ScaleUp d s s'"
  shows "TypeInvariant s'"
  unfolding TypeInvariant_def
proof
  from assms show "\<forall>d. deployments s' d \<le> MaxReplicas"
    unfolding ScaleUp_def TypeInvariant_def by auto
next
  from assms show "\<forall>d. deployments s' d \<ge> card (ffilter (\<lambda>p. deployment p = d) (pods s'))"
    unfolding ScaleUp_def TypeInvariant_def by auto
qed

theorem safety_proof:
  assumes reachable: "s \<in> reachable_states InitState"
  shows "TypeInvariant s \<and> NoOrphanedPods s \<and> NodeCapacity s"
  using assms
  by (induction rule: reachable_states.induct)
     (auto simp: TypeInvariant_def NoOrphanedPods_def NodeCapacity_def 
                 ScaleUp_def ScaleDown_v1_def)

end