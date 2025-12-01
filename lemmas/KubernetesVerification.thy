theory KubernetesVerification
imports Main "HOL-Library.Code_Target_Nat"
begin

(* Базовые типы ресурсов *)
record ResourceRequests =
  cpu :: nat
  memory :: nat  
  storage :: nat

(* Классы приоритетов *)
datatype PriorityClass = System | High | Medium | Low

(* QoS классы из Z3 *)
datatype QoSClass = BestEffort | Burstable | Guaranteed

(* Taints и Tolerations *)
record Taint =
  taint_key :: string
  taint_value :: string  
  taint_effect :: string

record Toleration =
  toleration_key :: string
  toleration_value :: string
  toleration_operator :: string
  toleration_effect :: string

(* Сетевые политики *)
type_synonym LabelSelector = "(string \<times> string) list"

record NetworkPolicyRule =
  rule_name :: string
  pod_selector :: LabelSelector
  allowed_ports :: "nat list"
  allowed_protocols :: "string list"

record NetworkPolicy =
  policy_name :: string
  policy_namespace :: string
  ingress_rules :: "NetworkPolicyRule list"
  egress_rules :: "NetworkPolicyRule list"

(* HPA спецификация *)
record HPASpec =
  hpa_deployment :: string
  hpa_min_replicas :: nat
  hpa_max_replicas :: nat  
  hpa_target_cpu :: nat
  hpa_current_cpu :: nat

(* Storage *)
record StorageClass =
  sc_name :: string
  sc_provisioner :: string
  sc_parameters :: "(string \<times> string) list"

record VolumeClaim =
  vc_name :: string
  vc_storage_class :: string
  vc_size :: nat
  vc_access_modes :: "string list"

(* Pod спецификация *)
record PodSpec =
  pod_name :: string
  pod_deployment :: string
  pod_priority :: PriorityClass
  pod_qos_class :: QoSClass
  pod_requests :: ResourceRequests
  pod_limits :: ResourceRequests
  pod_tolerations :: "Toleration list"
  pod_node_selector :: LabelSelector
  pod_volume_claims :: "VolumeClaim list"
  pod_labels :: LabelSelector

record PodInstance = 
  pod_spec :: PodSpec
  pod_node :: string
  pod_status :: string

(* Node информация *)
record NodeInfo =
  node_name :: string
  node_capacity :: ResourceRequests
  node_allocated :: ResourceRequests
  node_taints :: "Taint list"
  node_labels :: LabelSelector

(* Deployment спецификация *)
record DeploymentSpec =
  deployment_name :: string
  deployment_min_replicas :: nat
  deployment_max_replicas :: nat
  deployment_current_replicas :: nat
  deployment_labels :: LabelSelector

(* Namespace квоты *)
record NamespaceQuota =
  quota_name :: string
  quota_limits :: ResourceRequests
  quota_used :: ResourceRequests

(* Состояние кластера *)
record ClusterState =
  cluster_deployments :: "DeploymentSpec list"
  cluster_pods :: "PodInstance list"
  cluster_nodes :: "NodeInfo list"  
  cluster_namespaces :: "NamespaceQuota list"
  cluster_hpas :: "HPASpec list"
  cluster_network_policies :: "NetworkPolicy list"
  cluster_storage_classes :: "StorageClass list"

(* === ВСПОМОГАТЕЛЬНЫЕ ФУНКЦИИ === *)

(* Проверка соответствия toleration и taint *)
definition toleration_matches_taint :: "Toleration \<Rightarrow> Taint \<Rightarrow> bool" where
  "toleration_matches_taint tol taint \<longleftrightarrow>
    (toleration_key tol = taint_key taint \<or> toleration_operator tol = ''Exists'') \<and>
    (toleration_value tol = taint_value taint \<or> toleration_operator tol = ''Exists'') \<and>  
    (toleration_effect tol = taint_effect taint \<or> toleration_effect tol = '''')"

(* Проверка что pod tolerates все taints узла *)
definition pod_tolerates_node_taints :: "PodSpec \<Rightarrow> NodeInfo \<Rightarrow> bool" where
  "pod_tolerates_node_taints pod node \<longleftrightarrow>
    (\<forall>taint \<in> set (node_taints node). 
      \<exists>tol \<in> set (pod_tolerations pod). toleration_matches_taint tol taint)"

(* Поиск deployment по имени *)
definition find_deployment :: "string \<Rightarrow> DeploymentSpec list \<Rightarrow> DeploymentSpec option" where
  "find_deployment name deployments =
    List.find (\<lambda>dep. deployment_name dep = name) deployments"

(* === ОСНОВНЫЕ ПРОВЕРКИ КЛАСТЕРА === *)

(* Высокая доступность *)
definition high_availability_maintained :: "ClusterState \<Rightarrow> bool" where
  "high_availability_maintained state \<longleftrightarrow>
    (let critical_services = [''frontend'', ''backend'', ''database'']
     in (\<forall>service \<in> set critical_services.
          (\<exists>dep \<in> set (cluster_deployments state). 
            deployment_name dep = service \<and> 
            deployment_current_replicas dep \<ge> deployment_min_replicas dep)))"

(* Соблюдение квот ресурсов *)
definition resource_quotas_respected :: "ClusterState \<Rightarrow> bool" where
  "resource_quotas_respected state \<longleftrightarrow>
    (\<forall>quota \<in> set (cluster_namespaces state).
      cpu (quota_used quota) \<le> cpu (quota_limits quota) \<and>
      memory (quota_used quota) \<le> memory (quota_limits quota) \<and>  
      storage (quota_used quota) \<le> storage (quota_limits quota))"

(* Гарантии QoS для system-priority подов *)
definition qos_guarantees_maintained :: "ClusterState \<Rightarrow> bool" where
  "qos_guarantees_maintained state \<longleftrightarrow>
    (\<forall>pod \<in> set (cluster_pods state).
      if pod_priority (pod_spec pod) = System then
        cpu (pod_requests (pod_spec pod)) = cpu (pod_limits (pod_spec pod)) \<and>
        memory (pod_requests (pod_spec pod)) = memory (pod_limits (pod_spec pod)) \<and>
        storage (pod_requests (pod_spec pod)) = storage (pod_limits (pod_spec pod))
      else True)"

(* Проверка что узел может принять под *)
definition node_can_schedule_pod :: "NodeInfo \<Rightarrow> PodInstance \<Rightarrow> bool" where
  "node_can_schedule_pod node pod \<longleftrightarrow>
    (let new_cpu = cpu (node_allocated node) + cpu (pod_requests (pod_spec pod));
         new_memory = memory (node_allocated node) + memory (pod_requests (pod_spec pod));
         new_storage = storage (node_allocated node) + storage (pod_requests (pod_spec pod))
     in new_cpu \<le> cpu (node_capacity node) \<and>
        new_memory \<le> memory (node_capacity node) \<and>
        new_storage \<le> storage (node_capacity node) \<and>
        pod_tolerates_node_taints (pod_spec pod) node \<and>
        (\<forall>(k, v) \<in> set (pod_node_selector (pod_spec pod)). (k, v) \<in> set (node_labels node)))"

(* Все поды запланированы *)
definition all_pods_scheduled :: "ClusterState \<Rightarrow> bool" where
  "all_pods_scheduled state \<longleftrightarrow>
    (\<forall>pod \<in> set (cluster_pods state).
      if pod_status pod = ''Running'' then
        \<exists>node \<in> set (cluster_nodes state). 
          node_name node = pod_node pod \<and> node_can_schedule_pod node pod
      else True)"

(* Проверка HPA ограничений *)
definition hpa_constraints_satisfied :: "HPASpec \<Rightarrow> DeploymentSpec \<Rightarrow> bool" where
  "hpa_constraints_satisfied hpa deployment \<longleftrightarrow>
    deployment_name deployment = hpa_deployment hpa \<and>
    deployment_current_replicas deployment \<ge> hpa_min_replicas hpa \<and>
    deployment_current_replicas deployment \<le> hpa_max_replicas hpa \<and>
    (hpa_current_cpu hpa \<le> hpa_target_cpu hpa \<or> 
     deployment_current_replicas deployment < hpa_max_replicas hpa)"

(* Проверка HPA ограничений для всего кластера *)
definition hpa_constraints_maintained :: "ClusterState \<Rightarrow> bool" where
  "hpa_constraints_maintained state \<longleftrightarrow>
    (\<forall>hpa \<in> set (cluster_hpas state).
      case find_deployment (hpa_deployment hpa) (cluster_deployments state) of
        Some dep \<Rightarrow> hpa_constraints_satisfied hpa dep
      | None \<Rightarrow> False)"

(* === Z3-СТИЛЬ УНИВЕРСАЛЬНЫЕ ИНВАРИАНТЫ === *)

(* 1. Инвариант безопасности HPA (forall h HPA) *)
definition hpa_safety_invariant :: "ClusterState \<Rightarrow> bool" where
  "hpa_safety_invariant state \<longleftrightarrow>
    (\<forall>hpa \<in> set (cluster_hpas state).
      \<exists>dep \<in> set (cluster_deployments state).
        deployment_name dep = hpa_deployment hpa \<and>
        deployment_current_replicas dep \<ge> hpa_min_replicas hpa \<and>
        deployment_current_replicas dep \<le> hpa_max_replicas hpa \<and>
        (hpa_current_cpu hpa \<le> hpa_target_cpu hpa \<or> 
         deployment_current_replicas dep < hpa_max_replicas hpa))"

(* 2. Инвариант консистентности QoS (forall p Pod) *)
definition qos_consistency_invariant :: "ClusterState \<Rightarrow> bool" where
  "qos_consistency_invariant state \<longleftrightarrow>
    (\<forall>pod \<in> set (cluster_pods state).
      case pod_qos_class (pod_spec pod) of
        Guaranteed \<Rightarrow>
          cpu (pod_requests (pod_spec pod)) = cpu (pod_limits (pod_spec pod)) \<and>
          memory (pod_requests (pod_spec pod)) = memory (pod_limits (pod_spec pod)) \<and>
          storage (pod_requests (pod_spec pod)) = storage (pod_limits (pod_spec pod))
      | Burstable \<Rightarrow>
          cpu (pod_requests (pod_spec pod)) > 0 \<or> memory (pod_requests (pod_spec pod)) > 0  
      | BestEffort \<Rightarrow> True)"

(* 3. Инвариант балансировки нагрузки (forall n Node) *)
definition load_balancing_invariant :: "ClusterState \<Rightarrow> bool" where
  "load_balancing_invariant state \<longleftrightarrow>
    (\<forall>node \<in> set (cluster_nodes state).
      cpu (node_allocated node) * 100 \<ge> cpu (node_capacity node) * 20 \<and>
      memory (node_allocated node) * 100 \<ge> memory (node_capacity node) * 20)"

(* 4. Расширенная высокая доступность *)
definition enhanced_high_availability :: "ClusterState \<Rightarrow> bool" where
  "enhanced_high_availability state \<longleftrightarrow>
    (let critical_services = [''frontend'', ''backend'', ''database'', ''cache'']
     in (\<forall>service \<in> set critical_services.
          \<exists>dep \<in> set (cluster_deployments state).
            deployment_name dep = service \<and> 
            deployment_current_replicas dep \<ge> deployment_min_replicas dep))"

(* 5. Инвариант безопасности приоритетов *)
definition priority_safety_invariant :: "ClusterState \<Rightarrow> bool" where
  "priority_safety_invariant state \<longleftrightarrow>
    (\<forall>pod \<in> set (cluster_pods state).
      if pod_status pod = ''Running'' then
        \<exists>node \<in> set (cluster_nodes state).
          node_name node = pod_node pod \<and>
          cpu (node_capacity node) \<ge> cpu (node_allocated node) + cpu (pod_requests (pod_spec pod)) \<and>
          memory (node_capacity node) \<ge> memory (node_allocated node) + memory (pod_requests (pod_spec pod))
      else True)"

(* Композитный инвариант *)
definition universal_invariants_maintained :: "ClusterState \<Rightarrow> bool" where
  "universal_invariants_maintained state \<longleftrightarrow>
    hpa_safety_invariant state \<and>
    qos_consistency_invariant state \<and>
    load_balancing_invariant state \<and>
    enhanced_high_availability state \<and>
    priority_safety_invariant state"

(* Определение полной корректности кластера *)
definition cluster_correct :: "ClusterState \<Rightarrow> bool" where
  "cluster_correct state \<longleftrightarrow>
     high_availability_maintained state \<and>
     resource_quotas_respected state \<and>
     qos_guarantees_maintained state \<and>
     all_pods_scheduled state \<and>
     hpa_constraints_maintained state \<and>
     universal_invariants_maintained state"

(* === ПРИМЕР КЛАСТЕРА === *)

definition example_cluster :: ClusterState where
  "example_cluster = \<lparr>
    cluster_deployments = [
      \<lparr> deployment_name = ''frontend'', deployment_min_replicas = 3, 
         deployment_max_replicas = 10, deployment_current_replicas = 3,
         deployment_labels = [] \<rparr>,
      \<lparr> deployment_name = ''backend'', deployment_min_replicas = 2,
         deployment_max_replicas = 8, deployment_current_replicas = 2, 
         deployment_labels = [] \<rparr>,
      \<lparr> deployment_name = ''database'', deployment_min_replicas = 2,
         deployment_max_replicas = 4, deployment_current_replicas = 2,
         deployment_labels = [] \<rparr>,
      \<lparr> deployment_name = ''cache'', deployment_min_replicas = 2,
         deployment_max_replicas = 8, deployment_current_replicas = 3,
         deployment_labels = [] \<rparr>
    ],
    cluster_pods = [],
    cluster_nodes = [
      \<lparr> node_name = ''node1'', 
         node_capacity = \<lparr> cpu = 4000, memory = 8192, storage = 100000 \<rparr>,
         node_allocated = \<lparr> cpu = 1200, memory = 2048, storage = 1000 \<rparr>,
         node_taints = [], 
         node_labels = [] \<rparr>,
      \<lparr> node_name = ''node2'',
         node_capacity = \<lparr> cpu = 8000, memory = 16384, storage = 100000 \<rparr>, 
         node_allocated = \<lparr> cpu = 4000, memory = 8192, storage = 7000 \<rparr>,
         node_taints = [],
         node_labels = [] \<rparr>,
      \<lparr> node_name = ''node3'',
         node_capacity = \<lparr> cpu = 4000, memory = 8192, storage = 80000 \<rparr>,
         node_allocated = \<lparr> cpu = 1000, memory = 2048, storage = 1000 \<rparr>,
         node_taints = [],
         node_labels = [] \<rparr>
    ],
    cluster_namespaces = [
      \<lparr> quota_name = ''production'', 
         quota_limits = \<lparr> cpu = 10000, memory = 16384, storage = 200000 \<rparr>,
         quota_used = \<lparr> cpu = 3700, memory = 7888, storage = 58000 \<rparr> \<rparr>
    ],
    cluster_hpas = [
      \<lparr> hpa_deployment = ''frontend'', hpa_min_replicas = 3, hpa_max_replicas = 10,
         hpa_target_cpu = 80, hpa_current_cpu = 65 \<rparr>,
      \<lparr> hpa_deployment = ''backend'', hpa_min_replicas = 2, hpa_max_replicas = 8,
         hpa_target_cpu = 75, hpa_current_cpu = 60 \<rparr>
    ],
    cluster_network_policies = [],
    cluster_storage_classes = []
  \<rparr>"

(* === ЛЕММЫ И ТЕОРЕМЫ === *)

(* Лемма: Пример кластера поддерживает высокую доступность *)
lemma example_high_availability:
  "high_availability_maintained example_cluster"
  unfolding high_availability_maintained_def example_cluster_def
  by auto

(* Лемма: Пример кластера соблюдает квоты ресурсов *)
lemma example_resource_quotas:
  "resource_quotas_respected example_cluster"
  unfolding resource_quotas_respected_def example_cluster_def
  by auto

(* Лемма: HPA безопасность выполняется *)
lemma example_hpa_safety:
  "hpa_safety_invariant example_cluster"
  unfolding hpa_safety_invariant_def example_cluster_def
  by auto

(* Лемма: Расширенная высокая доступность выполняется *)
lemma example_enhanced_ha:
  "enhanced_high_availability example_cluster"
  unfolding enhanced_high_availability_def example_cluster_def
  by auto

(* Лемма: Балансировка нагрузки выполняется *)
lemma example_load_balancing:
  "load_balancing_invariant example_cluster"
  unfolding load_balancing_invariant_def example_cluster_def
  by auto

(* Лемма: QoS консистентность выполняется *)
lemma example_qos_consistency:
  "qos_consistency_invariant example_cluster"
  unfolding qos_consistency_invariant_def example_cluster_def
  by auto

(* Лемма: Безопасность приоритетов выполняется *)
lemma example_priority_safety:
  "priority_safety_invariant example_cluster"
  unfolding priority_safety_invariant_def example_cluster_def
  by auto

(* Лемма: Пример кластера удовлетворяет всем универсальным инвариантам *)
lemma example_universal_invariants:
  "universal_invariants_maintained example_cluster"
  unfolding universal_invariants_maintained_def
  apply (rule conjI)
  apply (rule example_hpa_safety)
  apply (rule conjI)
  apply (rule example_qos_consistency)
  apply (rule conjI)
  apply (rule example_load_balancing)
  apply (rule conjI)
  apply (rule example_enhanced_ha)
  apply (rule example_priority_safety)
  done

(* Лемма: HPA ограничения выполняются *)
lemma example_hpa_constraints:
  "hpa_constraints_maintained example_cluster"
  unfolding hpa_constraints_maintained_def example_cluster_def
            find_deployment_def hpa_constraints_satisfied_def
  by auto

(* Лемма: QoS гарантии выполняются *)
lemma example_qos_guarantees:
  "qos_guarantees_maintained example_cluster"
  unfolding qos_guarantees_maintained_def example_cluster_def
  by auto

(* Лемма: Все поды запланированы *)
lemma example_all_pods_scheduled:
  "all_pods_scheduled example_cluster"
  unfolding all_pods_scheduled_def example_cluster_def
  by auto

(* Главная теорема: Пример кластера полностью корректен *)
theorem example_cluster_correct:
  "cluster_correct example_cluster"
  unfolding cluster_correct_def
  apply (rule conjI)
  apply (rule example_high_availability)
  apply (rule conjI)
  apply (rule example_resource_quotas)
  apply (rule conjI)
  apply (rule example_qos_guarantees)
  apply (rule conjI)
  apply (rule example_all_pods_scheduled)
  apply (rule conjI)
  apply (rule example_hpa_constraints)
  apply (rule example_universal_invariants)
  done

(* === ТЕОРЕМЫ О СВОЙСТВАХ === *)

(* Лемма: Универсальные инварианты подразумевают высокую доступность *)
lemma invariants_imply_high_availability:
  assumes "universal_invariants_maintained state"
  shows "high_availability_maintained state"
  using assms
  unfolding universal_invariants_maintained_def 
            enhanced_high_availability_def
            high_availability_maintained_def
  by auto

(* Лемма: Универсальные инварианты подразумевают HPA безопасность *)
lemma invariants_imply_hpa_safety:
  assumes "universal_invariants_maintained state"
  shows "hpa_safety_invariant state"
  using assms
  unfolding universal_invariants_maintained_def
  by simp

(* Лемма: Универсальные инварианты подразумевают QoS консистентность *)
lemma invariants_imply_qos_consistency:
  assumes "universal_invariants_maintained state"
  shows "qos_consistency_invariant state"
  using assms
  unfolding universal_invariants_maintained_def
  by simp

(* Лемма: Универсальные инварианты подразумевают балансировку нагрузки *)
lemma invariants_imply_load_balancing:
  assumes "universal_invariants_maintained state"
  shows "load_balancing_invariant state"
  using assms
  unfolding universal_invariants_maintained_def
  by simp

(* Лемма: Универсальные инварианты подразумевают безопасность приоритетов *)
lemma invariants_imply_priority_safety:
  assumes "universal_invariants_maintained state"
  shows "priority_safety_invariant state"
  using assms
  unfolding universal_invariants_maintained_def
  by simp

(* Корректная теорема: Универсальные инварианты подразумевают базовые свойства *)
theorem invariants_imply_basic_properties:
  assumes "universal_invariants_maintained state"
  shows "high_availability_maintained state \<and> 
         hpa_safety_invariant state \<and>
         qos_consistency_invariant state \<and>
         load_balancing_invariant state \<and>
         priority_safety_invariant state"
  using assms
  by (auto simp: invariants_imply_high_availability
                 invariants_imply_hpa_safety
                 invariants_imply_qos_consistency
                 invariants_imply_load_balancing
                 invariants_imply_priority_safety)

(* Альтернативная формулировка *)
theorem invariants_imply_basic_correctness:
  assumes "universal_invariants_maintained state"
  shows "high_availability_maintained state"
  using assms by (rule invariants_imply_high_availability)

(* === ДОПОЛНИТЕЛЬНЫЕ ПРИМЕРЫ === *)

(* Пример кластера с подами *)
definition example_cluster_with_pods :: ClusterState where
  "example_cluster_with_pods = 
    example_cluster\<lparr>cluster_pods := [
      \<lparr> pod_spec = \<lparr> pod_name = ''system-monitor'', pod_deployment = ''monitoring'',
                     pod_priority = System, pod_qos_class = Guaranteed,
                     pod_requests = \<lparr> cpu = 200, memory = 256, storage = 1000 \<rparr>,
                     pod_limits = \<lparr> cpu = 200, memory = 256, storage = 1000 \<rparr>,
                     pod_tolerations = [], pod_node_selector = [],
                     pod_volume_claims = [], pod_labels = [] \<rparr>,
         pod_node = ''node1'', pod_status = ''Running'' \<rparr>
    ]\<rparr>"

(* Лемма: Кластер с подами удовлетворяет QoS консистентности *)
lemma example_with_pods_qos_consistency:
  "qos_consistency_invariant example_cluster_with_pods"
  unfolding qos_consistency_invariant_def example_cluster_with_pods_def
            example_cluster_def
  by auto

(* Лемма: Кластер с подами удовлетворяет безопасности приоритетов *)
lemma example_with_pods_priority_safety:
  "priority_safety_invariant example_cluster_with_pods"
  unfolding priority_safety_invariant_def example_cluster_with_pods_def
            example_cluster_def
  by auto

end