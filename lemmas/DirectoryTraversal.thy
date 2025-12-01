theory DirectoryTraversal
imports Main
begin

(* Определяем базовые типы для файловой системы *)
type_synonym path = "string"
type_synonym filename = "string"

datatype fs_entry = 
  File filename 
| Directory filename "fs_entry list"
 
(* Простейший случай: состояние = одно число *)
type_synonym state = int

(* Подход 1: программа как отношение *)
definition hoare_triple_rel :: 
  "(state \<Rightarrow> bool) \<Rightarrow> (state \<times> state \<Rightarrow> bool) \<Rightarrow> (state \<Rightarrow> bool) \<Rightarrow> bool"  ("\<lbrace>_\<rbrace>/ _/ \<lbrace>_\<rbrace>\<^sub>r" [0,0,0] 100) 
where
  "\<lbrace>P\<rbrace> S \<lbrace>Q\<rbrace>\<^sub>r \<equiv> \<forall>\<sigma> \<sigma>'. P \<sigma> \<and> S (\<sigma>, \<sigma>') \<longrightarrow> Q \<sigma>'"

(* Программа: увеличить на 1 *)
definition increment_rel :: "state \<times> state \<Rightarrow> bool" where
  "increment_rel \<equiv> \<lambda>(\<sigma>, \<sigma>'). \<sigma>' = \<sigma> + 1"

lemma increment_example:
  "\<lbrace>\<lambda>\<sigma>. \<sigma> = 5\<rbrace> increment_rel \<lbrace>\<lambda>\<sigma>'. \<sigma>' = 6\<rbrace>\<^sub>r"
  unfolding hoare_triple_rel_def increment_rel_def
  by simp
 
(* definition total_hoare_triple :: 
  "('state \<Rightarrow> bool) \<Rightarrow> 'state \<Rightarrow> ('state \<Rightarrow> 'state \<Rightarrow> bool) \<Rightarrow> bool" 
  ("\<lbrace>_\<rbrace>/ _/ \<lbrace>_\<rbrace>\<^sub>t" [0,0,0] 100) where
  "\<lbrace>P\<rbrace> s \<lbrace>Q\<rbrace>\<^sub>t \<equiv> \<lbrace>P\<rbrace> s \<lbrace>Q\<rbrace> \<and> (\<forall>\<sigma>. P \<sigma> \<longrightarrow> (\<exists>\<sigma>'. s \<sigma> \<sigma>'))" 
 *)

(* (* Базовое определение для частичной корректности *)
definition hoare_triple :: 
  "('state \<Rightarrow> bool) \<Rightarrow> ('state \<Rightarrow> 'state \<Rightarrow> bool) \<Rightarrow> ('state \<Rightarrow> bool) \<Rightarrow> bool" 
  ("\<lbrace>_\<rbrace>/ _/ \<lbrace>_\<rbrace>" [0,0,0] 100) 
where
  "\<lbrace>P\<rbrace> S \<lbrace>Q\<rbrace> \<equiv> \<forall>\<sigma> \<sigma>'. P \<sigma> \<and> S \<sigma> \<sigma>' \<longrightarrow> Q \<sigma>'"

(* Тотальная корректность: частичная корректность + гарантия завершения *)
definition total_hoare_triple :: 
  "('state \<Rightarrow> bool) \<Rightarrow> ('state \<Rightarrow> 'state \<Rightarrow> bool) \<Rightarrow> ('state \<Rightarrow> bool) \<Rightarrow> bool"  ("\<lbrace>_\<rbrace>/ _/ \<lbrace>_\<rbrace>\<^sub>t" [0,0,0] 100) 
where
  "\<lbrace>P\<rbrace> S \<lbrace>Q\<rbrace>\<^sub>t \<equiv> \<lbrace>P\<rbrace> S \<lbrace>Q\<rbrace> \<and> (\<forall>\<sigma>. P \<sigma> \<longrightarrow> (\<exists>\<sigma>'. S \<sigma> \<sigma>'))" *)



end