(*<*)
theory sol05
  imports 
    Complex_Main 
    "~~/src/HOL/Library/Tree"
begin
(*>*)

  
text {* \ExerciseSheet{5}{26.~5.~2017} *}

text \<open>
  \<^item> Import \<open>Complex_Main\<close> and \<open>"~~/src/HOL/Library/Tree"\<close>! 
  \<^item> For this exercise sheet (and homework!), you are not allowed to use sledgehammer! 
    Proofs using the \<open>smt, metis, meson, or moura\<close> methods are forbidden!
\<close>

text \<open>
  \Exercise{Estimating power-of-two by factorial}
  Prove that, for all natural numbers $n>3$, we have $2^n < n!$.
  We have already prepared the proof skeleton for you.
\<close>  
lemma exp_fact_estimate: "n>3 \<Longrightarrow> (2::nat)^n < fact n"
proof (induction n)
  case 0 then show ?case by auto
next
  case (Suc n)
  assume IH: "3 < n \<Longrightarrow> (2::nat) ^ n < fact n"  
  assume PREM: "3 < Suc n"  
  show "(2::nat) ^ Suc n < fact (Suc n)"
    text \<open>Fill in a proof here. Hint: Start with a case distinction 
      whether \<open>n>3\<close> or \<open>n=3\<close>. \<close>
  (*<*)  
  proof -    
    from PREM have "n>3 \<or> n=3" by auto
    then show "(2::nat) ^ Suc n < fact (Suc n)" 
    proof    
      assume GT: "n>3"
      from IH[OF GT] have "(2::nat) * 2 ^ n < fact n + fact n" by simp
      also have "\<dots> \<le> fact n + n*fact n" using GT by simp 
      finally have "2 * 2 ^ n < fact n + n * fact n" .
      then show "(2::nat) ^ Suc n < fact (Suc n)" 
        by simp
    next          
      assume "n=3"
      thus ?case by (simp add: eval_nat_numeral)
    qed
  qed    
  (*>*)
qed
    
text \<open>
  \vspace{1em}
  {\bfseries Warning!}
  Make sure that your numerals have the right type, otherwise 
  proofs will not work! To check the type of a numeral, hover the mouse over 
  it with pressed CTRL (Mac: CMD) key. Example:
\<close>
lemma "2^n \<le> 2^Suc n"  
  apply auto oops -- \<open>Leaves the subgoal \<open>2 ^ n \<le> 2 * 2 ^ n\<close>\<close>
  text \<open>You will find out that the numeral \<open>2\<close> has type @{typ 'a}, 
    for which you do not have any ordering laws. So you have to 
    manually restrict the numeral's type to, e.g., @{typ nat}.\<close>
lemma "(2::nat)^n \<le> 2^Suc n" by simp -- \<open>Note: Type inference will 
  infer \<open>nat\<close> for the unannotated numeral, too. Use CTRL+hover to double check!\<close>
  
text \<open>
  \vspace{1em}
\<close>    
    
text \<open>\Exercise{Sum Squared is Sum of Cubes}
  \<^item> Define a recursive function $sumto~f~n = \sum_{i=0\ldots n} f(i)$.
  \<^item> Show that $\left(\sum_{i=0\ldots n}i\right)^2 = \sum_{i=0\ldots n} i^3$.
\<close>    
    
    
fun sumto :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat" 
(*<*)  
where
"sumto f 0 = 0" |
"sumto f (Suc n) = sumto f n + f(Suc n)"
(*>*)

text \<open>You may need the following lemma:\<close>
lemma sum_of_naturals: "2 * sumto (\<lambda>x. x) n = n * Suc n"
  by (induction n) auto


lemma "sumto (\<lambda>x. x) n ^ 2 = sumto (\<lambda>x. x^3) n"
proof (induct n)
  case 0 show ?case by simp
next
  case (Suc n)
  assume IH: "(sumto (\<lambda>x. x) n)\<^sup>2 = sumto (\<lambda>x. x ^ 3) n"  
  note [simp] = algebra_simps -- \<open>Extend the simpset only in this block\<close>
  show "(sumto (\<lambda>x. x) (Suc n))\<^sup>2 = sumto (\<lambda>x. x ^ 3) (Suc n)" 
  text \<open>Insert a proof here\<close>
  (*<*)  
  proof -  
    have "sumto (\<lambda>x. x) (Suc n) ^ 2 = (sumto (\<lambda>x. x) n + (n+1))^2"
      by (simp)
    also have "\<dots> = sumto (\<lambda>x. x) n ^ 2 + (2 * sumto (\<lambda>x. x) n * (n+1) + (n+1)^2)"
      by (simp add: numeral_eq_Suc)
    also have "\<dots> = sumto (\<lambda>x. x^3) n + 2 * sumto (\<lambda>x. x) n * (n+1) + (n+1)^2"
      using IH by (simp)
    also have "\<dots> = sumto (\<lambda>x. x^3) n + n * Suc n * (n+1) + (n+1)^2"
      by (simp add: sum_of_naturals)
    also have "\<dots> = sumto (\<lambda>x. x^3) n + (n+1)^3"
      by (simp add: numeral_eq_Suc)
    also have "... = sumto (\<lambda>x. x^3) (Suc n)" by (simp)
    finally show ?thesis .
  qed
  (*>*)  
qed
    
text \<open>
  \Exercise{Paths in Graphs}
  A graph is described by its adjacency matrix, i.e., \<open>G :: 'a \<Rightarrow> 'a \<Rightarrow> bool\<close>.

  Define a predicate \<open>path G u p v\<close> that is true if \<open>p\<close> is a path from
  \<open>u\<close> to \<open>v\<close>, i.e., \<open>p\<close> is a list of nodes, not including \<open>u\<close>, such that 
  the nodes on the path are connected with edges.
  In other words, \<open>path G u (p\<^sub>1\<dots>p\<^sub>n) v\<close>, iff \<open>G u p\<^sub>1\<close>, \<open>G p\<^sub>i p\<^sub>i\<^sub>+\<^sub>1\<close>, 
  and \<open>p\<^sub>n = v\<close>. For the empty path (\<open>n=0\<close>), we have \<open>u=v\<close>.
\<close>    

fun path :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a \<Rightarrow> bool" 
(*<*)  
  where
  "path G u [] v \<longleftrightarrow> u=v"
| "path G u (x#xs) v \<longleftrightarrow> G u x \<and> path G x xs v"  
(*>*)  
    
text \<open>Test cases\<close>
definition "nat_graph x y \<longleftrightarrow> y=Suc x" 
value \<open>path nat_graph 2 [] 2\<close>  
value \<open>path nat_graph 2 [3,4,5] 5\<close>  
value \<open>\<not> path nat_graph 3 [3,4,5] 6\<close>  
value \<open>\<not> path nat_graph 2 [3,4,5] 6\<close>  
  
text \<open>Show the following lemma, that decomposes paths. Register it as simp-lemma.\<close>
lemma path_append[simp]: "path G u (p1@p2) v \<longleftrightarrow> (\<exists>w. path G u p1 w \<and> path G w p2 v)"  
(*<*)  
  by (induction p1 arbitrary: u) auto  
(*>*)    
  
text \<open>
  Show that, for a non-distinct path from \<open>u\<close> to \<open>v\<close>, 
  we find a longer non-distinct path from \<open>u\<close> to \<open>v\<close>.
  Note: This can be seen as a simple pumping-lemma, 
  allowing to pump the length of the path.

  Hint: Theorem @{thm [source] not_distinct_decomp}.
\<close>  
lemma pump_nondistinct_path:
  assumes P: "path G u p v"  
  assumes ND: "\<not>distinct p"  
  shows "\<exists>p'. length p' > length p \<and> \<not>distinct p' \<and> path G u p' v"  
(*<*)    
proof -    
  from not_distinct_decomp[OF ND]
  obtain xs ys zs y where [simp]: "p = xs @ y # ys @ y # zs" by auto
  from P have 1: "path G u (xs@y#ys@y#ys@y#zs) v"
    by auto
      
  have 2: "length (xs@y#ys@y#ys@y#zs) > length p" "\<not>distinct (xs@y#ys@y#ys@y#zs)"
    by auto
  
  from 1 2 show ?thesis by blast
qed      
(*>*)      

  
(*<*)  (* Not part of exercise sheet *)
lemma long_path_nd:
  assumes "finite V"
  assumes "set l \<subseteq> V"  
  assumes "length l > card V"  
  shows "\<not>distinct l"  
  by (metis assms card_mono distinct_card leD)  
      
lemma path_subset_V:
  assumes "\<forall>x y. G x y \<longrightarrow> x\<in>V \<and> y\<in>V"
  assumes "path G u p v"
  shows "set p \<subseteq> V"  
  using assms 
  by (induction p arbitrary: u) auto
    
lemma pump_long_path:
  assumes FIN: "finite V"
  assumes SUB: "\<forall>x y. G x y \<longrightarrow> x\<in>V \<and> y\<in>V"
  assumes PATH: "path G u p v"
  assumes LEN: "length p > card V"  
  shows "\<exists>p'. length p' > length p \<and> path G u p' v"
proof -
  note 1 = path_subset_V[OF SUB PATH]
  note 2 = long_path_nd[OF FIN 1 LEN]
  note 3 = pump_nondistinct_path[OF PATH 2]
  then show ?thesis by blast  
qed  
(*>*)    

(*<*)
end
(*>*)
