(* Template for exercise and homework.
 * IF YOU USE THIS FOR HOMEWORK, PLEASE DELETE THE EXERCISE PARTS THAT ARE
 * NOT REQUIRED FOR HOMEWORK SOLUTION, AND MAKE SURE THAT THE REST DOES NOT 
 * CONTAIN ANY \<open>sorry\<close>s!
 *)

(*<*)
theory tmpl05
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
    sorry  
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
  where "sumto _ _ = undefined"

text \<open>You may need the following lemma:\<close>
lemma sum_of_naturals: "2 * sumto (\<lambda>x. x) n = n * Suc n"
  sorry (* by (induction n) auto  The proof should work by induction, auto
    if your sum-to function is defined straight-forwardly. 
    Otherwise, you may want to reconsider your definition of sumto.*)


lemma "sumto (\<lambda>x. x) n ^ 2 = sumto (\<lambda>x. x^3) n"
proof (induct n)
  case 0 show ?case sorry (* by simp Should be trivial.  *)
next
  case (Suc n)
  assume IH: "(sumto (\<lambda>x. x) n)\<^sup>2 = sumto (\<lambda>x. x ^ 3) n"  
  note [simp] = algebra_simps -- \<open>Extend the simpset only in this block\<close>
  show "(sumto (\<lambda>x. x) (Suc n))\<^sup>2 = sumto (\<lambda>x. x ^ 3) (Suc n)" 
  text \<open>Insert a proof here\<close>
    sorry
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
  where "path _ _ _ _ = undefined"
    
text \<open>Test cases\<close>
definition "nat_graph x y \<longleftrightarrow> y=Suc x" 
value \<open>path nat_graph 2 [] 2\<close>  
value \<open>path nat_graph 2 [3,4,5] 5\<close>  
value \<open>\<not> path nat_graph 3 [3,4,5] 6\<close>  
value \<open>\<not> path nat_graph 2 [3,4,5] 6\<close>  
  
text \<open>Show the following lemma, that decomposes paths. Register it as simp-lemma.\<close>
lemma path_append[simp]: "path G u (p1@p2) v \<longleftrightarrow> (\<exists>w. path G u p1 w \<and> path G w p2 v)"  
  sorry
  
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
  oops
  

text \<open>
  \NumHomework{Estimate for Number of Leafs}{June 2}
  Recall: Use Isar, proofs using 
    \<open>metis, smt, meson, or moura\<close> (as generated by sledgehammer) are forbidden!

  Define a function to count the number of leafs in a binary tree:
\<close>
fun num_leafs :: "'a tree \<Rightarrow> nat" where
  "num_leafs _ = undefined"
  
text \<open>
  Start by showing the following auxiliary lemma:
\<close>  
lemma auxl:
  assumes IHl: "num_leafs l \<le> 2 ^ height l" and IHr: "num_leafs r \<le> 2 ^ height r"
    and lr: "height l \<le> height r"
  shows "num_leafs(Node l x r) \<le> 2 ^ height(Node l x r)"
  oops
    
text \<open>Also show the symmetric statement. Hint: Copy-paste-adjust! \<close>  
lemma auxr:
  assumes IHl: "num_leafs l \<le> 2 ^ height l" and IHr: "num_leafs r \<le> 2 ^ height r"
    and rl: "\<not> height l \<le> height r"
  shows "num_leafs(Node l x r) \<le> 2 ^ height(Node l x r)"
  oops
  
text \<open>Finally, show that we can estimate the number of leafs in a tree as follows:\<close>  
lemma "num_leafs t \<le> 2^height t"
proof (induction t)
  case Leaf show ?case sorry (* by auto should be straightforward. *)
next
  case (Node l x r)
  assume IHl: "num_leafs l \<le> 2 ^ height l"  
  assume IHr: "num_leafs r \<le> 2 ^ height r"  
  show "num_leafs \<langle>l, x, r\<rangle> \<le> 2 ^ height \<langle>l, x, r\<rangle>"
  text \<open>Fill in your proof here\<close>  
    sorry
qed  
  
    
text \<open>
  \NumHomework{Simple Paths}{June 2}
  This homework is worth 5 bonus points.

  A simple path is a path without loops, or, in other words, a path 
  where no node occurs twice. (Note that the first node of the path is 
  not included, such that there may be a simple path from \<open>u\<close> to \<open>u\<close>.)

  Show that for every path, there is a corresponding simple path:
\<close>    
lemma exists_simple_path:
  assumes "path G u p v"    
  shows "\<exists>p'. path G u p' v \<and> distinct p'"  
  using assms  
proof (induction p rule: length_induct)
  case (1 p)
  assume IH: "\<forall>pp. length pp < length p \<longrightarrow> path G u pp v 
                  \<longrightarrow> (\<exists>p'. path G u p' v \<and> distinct p')"  
  assume PREM: "path G u p v"
  show "\<exists>p'. path G u p' v \<and> distinct p'" 
  text \<open>Fill in your proof here.\<close>  
    sorry
qed

(*<*)
end
(*>*)
