(*<*)
theory tmpl09
  imports "../../Material/Thys/Trie1"
begin
(*>*)  
text {* \ExerciseSheet{9}{23.~6.~2017} *}

text \<open>\Exercise{Union Function on Tries}
  Define a function to merge two tries and show its correctness
\<close>  
fun union :: "trie \<Rightarrow> trie \<Rightarrow> trie" 
  where "union _ _ = undefined"
  
lemma "isin (union a b) x = isin a x \<or> isin b x"
  sorry  
    
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
  where "unionI _ _ = undefined"

text \<open>Next, we define an abstraction function from Patricia tries to intermediate tries.
  Note that we need to install a custom measure function to get the termination proof through!
\<close>
fun size1P :: "ptrie \<Rightarrow> nat" where
  "size1P LeafP = 0"
| "size1P (NodeP ps v (l,r)) = 1 + size ps + size1P l + size1P r"
  
lemma [measure_function]: "is_measure size1P" by (rule is_measure_trivial) 
    
fun absI_ptrie :: "ptrie \<Rightarrow> itrie" where
  "absI_ptrie LeafP = LeafI"  
| "absI_ptrie (NodeP [] v (l,r)) = BinaryI v (absI_ptrie l, absI_ptrie r)"
| "absI_ptrie (NodeP (x#xs) v (l,r)) = UnaryI x (absI_ptrie (NodeP xs v (l,r)))"
  

text \<open>Warmup: Show that abstracting Patricia tries over intermediate 
  tries to tries is the same as abstracting directly to tries.\<close>  
lemma "abs_itrie o absI_ptrie = abs_ptrie"
  sorry    
  
  
text \<open>Refine the union function to Patricia tries.

  Hint: First figure out how a Patricia trie that 
    correspond to a leaf/unary/binary node looks like. 
    Then translate @{const \<open>unionI\<close>} equation by equation!

  More precisely, try to find terms \<open>unaryP\<close> and \<open>binaryP\<close> such that
    @{term [display] "absI_ptrie (unaryP k t) = UnaryI k (absI_ptrie t)"}
    @{term [display] "absI_ptrie (binaryP v (l,r)) = BinaryI v (absI_ptrie l, absI_ptrie r)"}

  You will encounter a small problem with \<open>unaryP\<close>. Which one?
\<close>
  
    
fun unionP :: "ptrie \<Rightarrow> ptrie \<Rightarrow> ptrie" 
  where "unionP _ _ = undefined"
  
lemma "absI_ptrie (unionP t\<^sub>1 t\<^sub>2) = unionI (absI_ptrie t\<^sub>1) (absI_ptrie t\<^sub>2)"
  sorry
    
text \<open>
  \NumHomework{Shrunk Trees}{30.~6.~2017}

  Have a look at the @{const delete2} function for tries. It maintains a 
  ``shrunk'' - property on tries. Identify this property, define a predicate 
  for it, and show that it is indeed maintained by empty, insert, and delete2!
\<close>    

fun shrunk :: "trie \<Rightarrow> bool" where "shrunk _ = undefined"

lemma "shrunk Leaf" sorry
  
lemma "shrunk t \<Longrightarrow> shrunk (insert ks t)" sorry
    
lemma "shrunk t \<Longrightarrow> shrunk (delete2 ks t)" sorry
    
  
text \<open>
  \NumHomework{Refining Delete}{30.~6.~2017}

  Refine the delete function to intermediate tries and further down 
  to Patricia tries.
\<close>    
    
fun deleteI :: "bool list \<Rightarrow> itrie \<Rightarrow> itrie" where
  "deleteI _ _ = undefined"
  
lemma "abs_itrie (deleteI ks t) = delete ks (abs_itrie t)" sorry
    
fun pdelete :: "bool list \<Rightarrow> ptrie \<Rightarrow> ptrie"
  where  
  "pdelete _ _ = undefined"
  
lemma "absI_ptrie (pdelete ks t) = deleteI ks (absI_ptrie t)"  sorry
    
(*<*)
end
(*>*)
