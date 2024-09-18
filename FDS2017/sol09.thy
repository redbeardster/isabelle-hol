(*<*)
theory sol09
  imports "../../../Public/Thys/Trie1"
begin
(*>*)  
text {* \ExerciseSheet{9}{23.~6.~2017} *}

text \<open>\Exercise{Union Function on Tries}
  Define a function to merge two tries and show its correctness
\<close>  
fun union :: "trie \<Rightarrow> trie \<Rightarrow> trie" 
(*<*)  
  where
  "union Leaf t = t"
| "union t Leaf = t"  
| "union (Node v (l,r)) (Node v' (l',r')) = (
    Node (v \<or> v') (union l l', union r r'))"  
(*>*)  
  
(*<*)  
lemma [simp]: "union t Leaf = t" by (cases t) auto
(*>*)    
  
lemma "isin (union a b) x = isin a x \<or> isin b x"
(*<*)  
  apply (induction a b arbitrary: x rule: union.induct)
  apply (auto split: list.split)
  done  
(*>*)    
  
text \<open>
  \Exercise{Intermediate Abstraction Level for Patricia Tries}

  We introduce an abstraction level in between tries and Patricia tries:
  A node with only a single non-leaf successor is represented as an unary node.

  Via unary nodes, this implementation already introduces a notion of common prefix,
  but does not yet summarize runs of multiple prefixes into a list.
\<close>
  
datatype itrie = LeafI | UnaryI bool itrie | BinaryI bool "itrie * itrie"

fun abs_itrie :: "itrie \<Rightarrow> trie" -- \<open>Abstraction to tries\<close>  
  where
  "abs_itrie LeafI = Leaf"
| "abs_itrie (UnaryI True t) = Node False (Leaf, abs_itrie t)"
| "abs_itrie (UnaryI False t) = Node False (abs_itrie t, Leaf)"
| "abs_itrie (BinaryI v (l,r)) = Node v (abs_itrie l, abs_itrie r)"  
  
text \<open>Refine the union function to intermediate tries\<close>
fun unionI :: "itrie \<Rightarrow> itrie \<Rightarrow> itrie" 
(*<*)  
  where
  "unionI LeafI t = t"
| "unionI t LeafI = t"
| "unionI (UnaryI False t) (UnaryI False t') = UnaryI False (unionI t t')"
| "unionI (UnaryI True t) (UnaryI True t') = UnaryI True (unionI t t')"
| "unionI (UnaryI True t) (UnaryI False t') = BinaryI False (t',t)"
| "unionI (UnaryI False t) (UnaryI True t') = BinaryI False (t,t')"
| "unionI (BinaryI v (l,r)) (BinaryI v' (l',r')) = (
    BinaryI (v\<or>v') (unionI l l', unionI r r')
  )"  
| "unionI (UnaryI False t) (BinaryI v' (l',r')) = BinaryI v' (unionI t l', r')"
| "unionI (UnaryI True t) (BinaryI v' (l',r')) = BinaryI v' (l', unionI t r')"
| "unionI (BinaryI v (l,r)) (UnaryI False t') = BinaryI v (unionI l t', r)"
| "unionI (BinaryI v (l,r)) (UnaryI True t') = BinaryI v (l, unionI r t')"
  
lemma [simp]: "unionI t LeafI = t" by (cases t) auto
  
(*>*)  
  
(*<*)  
lemma "abs_itrie (unionI t1 t2) = union (abs_itrie t1) (abs_itrie t2)"
  apply (induction t1 t2 rule: unionI.induct)
  apply (auto)
  done  
(*>*)

text \<open>Next, we define an abstraction function from Patricia tries to intermediate tries.
  Note that we need to install a custom measure function to get the termination proof through!
\<close>
(*<*)  
fun size1P :: "ptrie \<Rightarrow> nat" where
  "size1P LeafP = 0"
| "size1P (NodeP ps v (l,r)) = 1 + size ps + size1P l + size1P r"
  
lemma [measure_function]: "is_measure size1P" by (rule is_measure_trivial) 
(*>*)  
    
fun absI_ptrie :: "ptrie \<Rightarrow> itrie" where
  "absI_ptrie LeafP = LeafI"  
| "absI_ptrie (NodeP [] v (l,r)) = BinaryI v (absI_ptrie l, absI_ptrie r)"
| "absI_ptrie (NodeP (x#xs) v (l,r)) = UnaryI x (absI_ptrie (NodeP xs v (l,r)))"
  

text \<open>Warmup: Show that abstracting Patricia tries over intermediate 
  tries to tries is the same as abstracting directly to tries.\<close>  
lemma "abs_itrie o absI_ptrie = abs_ptrie"
(*<*)  
proof (rule ext, simp)  
  fix t
  show "abs_itrie (absI_ptrie t) = abs_ptrie t"
    by (induction t rule: absI_ptrie.induct) auto  
qed    
(*>*)  
    
  
  
text \<open>Refine the union function to Patricia tries.

  Hint: First figure out how a Patricia trie that 
    correspond to a leaf/unary/binary node looks like. 
    Then translate @{const \<open>unionI\<close>} equation by equation!

  More precisely, try to find terms \<open>unaryP\<close> and \<open>binaryP\<close> such that
    @{term [display] "absI_ptrie (unaryP k t) = UnaryI k (absI_ptrie t)"}
    @{term [display] "absI_ptrie (binaryP v (l,r)) = BinaryI v (absI_ptrie l, absI_ptrie r)"}

  You will encounter a small problem with \<open>unaryP\<close>. Which one?
\<close>
  
(*<*)    
value "absI_ptrie (NodeP [] v (l,r))"
value "absI_ptrie (NodeP (p#ps) v (l,r))"
    
text \<open>Note: Appending unary nodes to leafs cannot be modeled concretely! \<close>  
fun unaryP :: "bool \<Rightarrow> ptrie \<Rightarrow> ptrie" where
  "unaryP x (NodeP xs v lr) = NodeP (x#xs) v lr"
  
lemma unaryP_refines[simp]: "t\<noteq>LeafP \<Longrightarrow> absI_ptrie (unaryP k t) = UnaryI k (absI_ptrie t)"    
  by (cases t) auto
    
abbreviation "binaryP v lr \<equiv> NodeP [] v lr"
lemma "absI_ptrie (binaryP v (l,r)) = BinaryI v (absI_ptrie l, absI_ptrie r)"
  by simp
    
(*>*)    
    
fun unionP :: "ptrie \<Rightarrow> ptrie \<Rightarrow> ptrie" 
(*<*)  
  where
  "unionP LeafP t = t"
| "unionP t LeafP = t"
| "unionP (NodeP (False#ps\<^sub>1) v\<^sub>1 t\<^sub>1) (NodeP (False#ps\<^sub>2) v\<^sub>2 t\<^sub>2) = unaryP False (unionP (NodeP ps\<^sub>1 v\<^sub>1 t\<^sub>1) (NodeP ps\<^sub>2 v\<^sub>2 t\<^sub>2))"
| "unionP (NodeP (True#ps\<^sub>1) v\<^sub>1 t\<^sub>1) (NodeP (True#ps\<^sub>2) v\<^sub>2 t\<^sub>2) = unaryP True (unionP (NodeP ps\<^sub>1 v\<^sub>1 t\<^sub>1) (NodeP ps\<^sub>2 v\<^sub>2 t\<^sub>2))"
| "unionP (NodeP (True#ps\<^sub>1) v\<^sub>1 t\<^sub>1) (NodeP (False#ps\<^sub>2) v\<^sub>2 t\<^sub>2) = NodeP [] False (NodeP ps\<^sub>2 v\<^sub>2 t\<^sub>2, NodeP ps\<^sub>1 v\<^sub>1 t\<^sub>1)"
| "unionP (NodeP (False#ps\<^sub>1) v\<^sub>1 t\<^sub>1) (NodeP (True#ps\<^sub>2) v\<^sub>2 t\<^sub>2) = NodeP [] False (NodeP ps\<^sub>1 v\<^sub>1 t\<^sub>1, NodeP ps\<^sub>2 v\<^sub>2 t\<^sub>2)"
| "unionP (NodeP [] v\<^sub>1 (l\<^sub>1,r\<^sub>1)) (NodeP [] v\<^sub>2 (l\<^sub>2,r\<^sub>2)) = (NodeP [] (v\<^sub>1\<or>v\<^sub>2) (unionP l\<^sub>1 l\<^sub>2, unionP r\<^sub>1 r\<^sub>2))"  
| "unionP (NodeP (False#ps\<^sub>1) v\<^sub>1 t\<^sub>1) (NodeP [] v\<^sub>2 (l\<^sub>2,r\<^sub>2)) = NodeP [] v\<^sub>2 (unionP (NodeP ps\<^sub>1 v\<^sub>1 t\<^sub>1) l\<^sub>2, r\<^sub>2)"
| "unionP (NodeP (True#ps\<^sub>1) v\<^sub>1 t\<^sub>1) (NodeP [] v\<^sub>2 (l\<^sub>2,r\<^sub>2)) = NodeP [] v\<^sub>2 (l\<^sub>2, unionP (NodeP ps\<^sub>1 v\<^sub>1 t\<^sub>1) r\<^sub>2)"
| "unionP (NodeP [] v\<^sub>1 (l\<^sub>1,r\<^sub>1)) (NodeP (False#ps\<^sub>2) v\<^sub>2 t\<^sub>2) = NodeP [] v\<^sub>1 (unionP l\<^sub>1 (NodeP ps\<^sub>2 v\<^sub>2 t\<^sub>2), r\<^sub>1)"
| "unionP (NodeP [] v\<^sub>1 (l\<^sub>1,r\<^sub>1)) (NodeP (True#ps\<^sub>2) v\<^sub>2 t\<^sub>2) = NodeP [] v\<^sub>1 (l\<^sub>1, unionP r\<^sub>1 (NodeP ps\<^sub>2 v\<^sub>2 t\<^sub>2))"
(*>*)  

(*<*)  
lemma [simp]: "t\<noteq>LeafP \<Longrightarrow> unaryP k t \<noteq> LeafP" by (cases t) auto
  
lemma [simp]: "unionP t\<^sub>1 t\<^sub>2 = LeafP \<longleftrightarrow> (t\<^sub>1 = LeafP \<and> t\<^sub>2 = LeafP)"
  by (induction t\<^sub>1 t\<^sub>2 rule: unionP.induct) auto  
(*>*)  
  
lemma "absI_ptrie (unionP t\<^sub>1 t\<^sub>2) = unionI (absI_ptrie t\<^sub>1) (absI_ptrie t\<^sub>2)"
(*<*)  
  by (induction t\<^sub>1 t\<^sub>2 rule: unionP.induct) auto  
(*>*)  
    
(*<*)
end
(*>*)
