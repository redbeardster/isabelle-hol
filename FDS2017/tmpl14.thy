text {* \ExerciseSheet{14}{28.~7.~2017} *}
theory tmpl14
imports 
  "~~/src/HOL/Library/Multiset"
  "~~/src/HOL/Library/Code_Target_Nat"
  "~~/src/HOL/Library/RBT"
  "~~/src/HOL/Library/Char_ord"
  "~~/src/HOL/Library/Code_Char"
begin

  
  text \<open>
    \Exercise{Word Frequency --- Down to ML code}

    Your task is to develop a program that reads a corpus and
    prints the words in the corpus together with their frequencies,
    sorted by descending frequencies.

    Except input and output, your program shall be formalized in Isabelle/HOL.
    A corpus is described as @{typ \<open>'a list\<close>}, 
    and the result is described by @{typ \<open>('a \<times> nat) list\<close>}
  \<close>  

  text \<open>The frequency of a word in a corpus can be specified as:\<close>
  definition freq :: "'a list \<Rightarrow> 'a \<Rightarrow> nat"
    where "freq ws = count (mset ws)"
    
  text \<open>
    Specify a predicate that characterizes a correct result.
    Note: If words have the same frequency, any order is allowed.
  \<close>  
  consts is_freq_list :: "'a list \<Rightarrow> ('a \<times> nat) list \<Rightarrow> bool" 

  text \<open>Tests:\<close>  
  lemma \<open>is_freq_list [''a'',''b'',''b'',''c'',''c''] [(''c'',2),(''b'',2),(''a'',1)]\<close>  
    oops
  lemma \<open>is_freq_list [''a'',''b'',''b'',''c'',''c''] [(''b'',2),(''c'',2),(''a'',1)]\<close>  
    oops
  lemma \<open>\<not>is_freq_list [''a'',''b'',''b'',''c'',''c''] [(''b'',2),(''c'',3),(''a'',1)]\<close>  
    oops
  lemma \<open>\<not>is_freq_list [''a'',''b'',''b'',''c'',''c''] [(''a'',1),(''c'',2),(''b'',2)]\<close>  
    oops
  lemma \<open>\<not>is_freq_list [''a'',''b'',''b'',''c'',''c''] [(''b'',2),(''c'',2),(''b'',2),(''a'',1)]\<close>
    oops
      
      
  section \<open>Refinement \#1\<close>  
  (* Refinement #1: Fold over word list and maintain current frequency *)  
  text \<open>Compute a function from words to their frequency by folding 
    over the corpus, starting with @{term \<open>\<lambda>_. 0::nat\<close>}. \<close>  

  consts incr1 :: "'a \<Rightarrow> ('a \<Rightarrow> nat) \<Rightarrow> 'a \<Rightarrow> nat"
  definition "freq1 ws \<equiv> fold incr1 ws (\<lambda>_. 0)"  
    
  lemma freq1_correct[simp]: "freq1 ws = freq ws"
    oops

  section \<open>Refinement \#2\<close>  
  (* Refinement #2: Frequency map by RBT *)
  text \<open>
    Use red black trees to implement the mapping from words to frequencies.
    Words that do not occur in the corpus must not be mapped!

    Use the RBT implementation from \<open>HOL/Library/RBT\<close>!
    It provides, e.g., @{const RBT.empty}, @{const RBT.lookup}, @{const RBT.insert}.
  \<close>  
  definition abs_fm :: "('a::linorder,nat) rbt \<Rightarrow> 'a \<Rightarrow> nat" where
    "abs_fm t k \<equiv> case RBT.lookup t k of None \<Rightarrow> 0 | Some v \<Rightarrow> v"
  definition inv_fm :: "('a::linorder,nat) rbt \<Rightarrow> bool" where
    "inv_fm t \<equiv> (0 \<notin> ran (RBT.lookup t))"
    
  lemma empty2_correct[simp]:
    "abs_fm RBT.empty = (\<lambda>_. 0)" "inv_fm RBT.empty"
    oops
    
  definition incr2 :: "'a::linorder \<Rightarrow> ('a, nat) rbt \<Rightarrow> ('a, nat) rbt"
    where "incr2 k t = t"
      
  lemma incr2_correct[simp]:
    "inv_fm t \<Longrightarrow> abs_fm (incr2 k t) = incr1 k (abs_fm t)"
    "inv_fm t \<Longrightarrow> inv_fm (incr2 k t)"
    oops
      
  text \<open> Now we have refined the operations, we can refine the algorithm that uses the operations:\<close>
  definition "freq2 ws \<equiv> fold incr2 ws RBT.empty"  
      
  lemma freq2_correct[simp]: "abs_fm (freq2 ws) = freq1 ws" "inv_fm (freq2 ws)"
    oops
      
    
  subsection \<open>Extracting Result from RBT\<close>
  text \<open>Extract the desired result 
    --- list of pairs of words and their frequencies, sorted by frequency --- 
    from the red black tree. Use @{const RBT.entries}.
  \<close>  
      
  definition fsort :: "'a::linorder list \<Rightarrow> ('a \<times> nat) list"
    where "fsort ws \<equiv> []"

     
  text \<open>Prove that your function is correct. 
    Hint: You will need to prove some auxiliary lemmas on standard list functions.
      Use \<open>find_theorems\<close> to search for existing lemmas.
    Hint: A lemma of the form @{text \<open>RBT.lookup (freq2 ws) w = Some f \<longleftrightarrow> \<dots>\<close>},
      derived from @{text \<open>freq2_correct freq1_correct\<close>} may be useful!
  \<close>  
  lemma fsort_correct: "is_freq_list ws (fsort ws)"
    oops


  section \<open>Code Generation\<close>    
  text \<open>Now we can use Isabelle/HOL's code generator to actually extract
    functional code from our Isabelle formalization.
    
    First, we derive a specialized versions with strings:
  \<close>    
  definition fsort_string :: "String.literal list \<Rightarrow> (String.literal \<times> nat) list"
    where "fsort_string \<equiv> fsort"
      
  text \<open>Then we can use the code generator in different ways.\<close>    
      
  text \<open>By the value command\<close>
  value [code] "fsort_string [STR ''foo'', STR ''bar'', STR ''foo'', STR ''bara'']"
      
  text \<open>Export code to file\<close>  
  export_code fsort_string in SML module_name Fsort file "export.sml"
  text \<open>We can load the file into JEdit's ML IDE: \<close>  
  SML_file "export.sml"
  text \<open>And use it from within some wrapper code for parsing a corpus and printing the result: \<close>  
  SML_file "fsort.sml"

  text \<open>Use code directly with Isabelle's builtin ML interpreter 
    \begin{verbatim}
  ML_val {* see template file *}  
    \end{verbatim}
  \<close>
  (* Directly as Isabelle/ML command *)  
  ML_val \<open>
    (* Read file to string *)
    fun file_to_string name = let
      val f = TextIO.openIn name
      val s = TextIO.inputAll f
      val _ = TextIO.closeIn f
    in s end

    fun fs fname = @{code fsort_string}
      (String.tokens (not o Char.isAlpha) (String.map (Char.toLower) (file_to_string fname)))

    val r1 = fs "/home/lammich/MASC-3.0.0/data/written/non-fiction/CUP2.txt"
    val r2 = fs "/home/lammich/MASC-3.0.0/data/written/twitter/tweets2.txt"
  \<close>  

  text \<open>The code generator also supports other target languages\<close>  
  export_code fsort_string in Haskell
  export_code fsort_string in Scala
  export_code fsort_string in OCaml
  
(*<*)    
end
(*>*)
