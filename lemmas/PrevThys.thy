theory PrevThys
imports Main
begin


(*
(*
datatype PRSObject = Rock | Scissors | Paper

fun beats :: " PRSObject \<Rightarrow>  PRSObject" 
  where 
 "beats Paper =  Rock" | 
 "beats Rock = Scissors" | 
 "beats Scissors = Paper" 

value "beats Paper"

fun beaten :: "PRSObject \<Rightarrow> PRSObject" where 
  "beaten Paper = Scissors" | 
  "beaten Rock = Paper" |
  "beaten Scissors = Rock"

lemma "beats (beaten x :: PRSObject) = x"
  by (metis PRSObject.distinct(1) PRSObject.distinct(3) PRSObject.distinct(5) beaten.elims beats.elims)


typedef Clock_value = "{0::nat,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23}"
  by blast

fun length :: "'a list \<Rightarrow> nat " where 
  "length [] = 0"
  | "length (x#xs) =  1 + length xs"

value "length [1::nat,2,3]"

type_synonym T = nat

axiomatization
  N  where
  NgreaterZero:  "1\<le>(N::nat)"

typedef proc = "{(1::nat).. N}"
  using NgreaterZero by auto

definition
  proc :: "nat set" where
  "proc \<equiv> {(1::nat)..N}"

definition
  procs :: "proc set" where
  "procs \<equiv> {i::proc. True}"

abbreviation "PID \<equiv> Rep_proc"

record 'ps conf =
P_State :: "proc \<Rightarrow> 'ps"

record Message =
  snd :: proc
  rcv :: proc

record MsgStatus =
  outgoing :: nat
  transit :: nat
  received :: nat
 
datatype 'msg event = Broadcast 'msg | Deliver 'msg

consts always_10 :: "'a \<Rightarrow> nat"

axiomatization  where
Always_10:
  "\<forall>x. always_10 x = 10"

lemma "\<forall>x. always_10 x \<le> 20"
  by (simp add: Always_10) 

value "hd [1::nat, 2]"
value "3 \<in> {1,2,3::nat}"
value "insert 3 {1, 2::nat}"

typedecl real_world (\<open>\<^url>\<close>)

typedef '\<alpha> io = "UNIV :: (\<^url> \<Rightarrow> '\<alpha> \<times> \<^url>) set"
  by simp

fun count :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
"count y [] = 0" |
"count y (x # xs) = (if x = y then Suc(count y xs) else count y xs)"

lemma count_less: "count y xs \<le> length xs"
  apply (induction xs)
  apply(auto)
  done
*)

definition
  "vbits\<equiv>{8,16,24,32,40,48,56,64,72,80,88,96,104,112,120,128,
          136,144,152,160,168,176,184,192,200,208,216,224,232,240,248,256}"

lemma vbits_ge_0: "(x::nat)\<in>vbits \<Longrightarrow> x>0" 
    unfolding vbits_def 
    apply auto
    done

lemma vbits_max:
  assumes "b1 \<in> vbits"
    and "b2 \<in> vbits"
  shows "(max b1 b2) \<in> vbits"
   proof -
  consider (b1) "max b1 b2 = b1" | (b2) "max b1 b2 = b2" by (metis max_def)
  then show ?thesis
  proof cases
    case b1
    then show ?thesis using assms(1) by simp
  next
    case b2
    then show ?thesis using assms(2) by simp
  qed
  qed 

abbreviation Proc :: "'p set"
  where "Proc \<equiv> (UNIV :: 'p set)"

definition A :: "nat set" where
  "A = {1, 2, 3}"

function mysum :: "nat \<Rightarrow> nat \<Rightarrow> nat"
where
"mysum i N = (if i > N then 0 else i + mysum (Suc i) N)"
  by pat_completeness auto

termination mysum
  apply (relation "measure (\<lambda>(i,N). N + 1 - i)")
  apply blast
  by force
  
value "mysum 0 10"

function foo :: "nat \<Rightarrow> nat \<Rightarrow> nat"
where
  "foo i N = (if i > N
    then (if N = 0 then 0 else foo 0 (N - 1))
    else i + foo (Suc i) N)"
  by pat_completeness auto

termination
  by (relation "measures [\<lambda>(i, N). N, \<lambda>(i,N). N + 1 - i]") auto

value "foo 1 20"

function even :: "nat \<Rightarrow> bool"
and odd :: "nat \<Rightarrow> bool"
where
"even 0 = True"
| "odd 0 = False"
| "even (Suc n) = odd n"
| "odd (Suc n) = even n"
by pat_completeness auto

termination
  by (relation "measure (\<lambda>x. case x of Inl n \<Rightarrow> n | Inr n \<Rightarrow> n)") auto

value "even 4"

lemma even_odd_mod2:
"even n = (n mod 2 = 0)"
"odd n = (n mod 2 = 1)"
   apply (induct n and n rule: even_odd.induct)
   apply simp_all
   apply arith
   apply arith
  done

value "sorted [1,2,3::nat]"

fun list_to_option :: "'a list \<Rightarrow> 'a option"
where
  "list_to_option [x] = Some x"
  | "list_to_option _ = None"

thm list_to_option.cases

fun_cases list_to_option_SomeE[elim]: "list_to_option xs = Some y"

thm list_to_option_SomeE

datatype P3 = T | F | X

fun And :: "P3 \<Rightarrow> P3 \<Rightarrow> P3"
where
"And T p = p"
| "And p T = p"
| "And p F = F"
| "And F p = F"
| "And X X = X"

thm And.simps

value "And F T"

function And2 :: "P3 \<Rightarrow> P3 \<Rightarrow> P3"
where
"And2 T p = p"
| "And2 p T = p"
| "And2 p F = F"
| "And2 F p = F"
| "And2 X X = X"

apply pat_completeness
by auto
termination by (relation "{}") simp

datatype 'a option = None | Some 'a

lemma "\<forall> x. P x \<longrightarrow> P x"
  apply (rule allI)
  by (rule impI)

lemma "E \<and> V \<Longrightarrow> V \<and> E"
  by auto



type_synonym number = nat
type_synonym gate = "bool \<Rightarrow> bool \<Rightarrow> bool"
type_synonym ('a, 'b) alist = "('a \<times> 'b) list"

record ('st,'ev) Tr =
  src :: 'st
  dst :: 'st
  lbl :: 'ev

record ('st, 'ev) LTS =
  init :: "'st set"
  trans :: "('st, 'ev) Tr set"
 

definition outgoing where 
  "outgoing l s \<equiv> {t \<in> trans l . src t = s}"

definition accepted_events where 
  "accepted_events l s \<equiv> lbl ` (outgoing l s)"

inductive_set states for l :: "('st, 'ev) LTS" 
    where
      base : "s \<in> init l \<Longrightarrow> s \<in> states l"
    | step : "\<lbrakk> s \<in> states l ; t \<in> outgoing l s \<rbrakk> \<Longrightarrow> dst t \<in> states l"

record ('st, 'ev) Run =
  trns :: "('st \<times> 'ev) list"
  fins :: 'st

definition append_tr 
  where
    "append_tr run t \<equiv>
  (| trns = (trns run) @ [(fins run, lbl t)], fins = dst t |)"

inductive_set runs for l :: "('st, 'ev) LTS"
  where
    start : "s \<in> init l \<Longrightarrow> (| trns = [], fins = s |) \<in> runs l"
  | step : "\<lbrakk> r \<in> runs l ; t \<in> outgoing l (fins r ) \<rbrakk> \<Longrightarrow> append_tr r t \<in> runs l"

(*
  Nice proof
*)
 lemma "runs-start-initial":
  assumes "r \<in> runs l"
  shows 
    "(if trns r = [] then fins r else fst (hd (trns r ))) \<in> init l"
   using assms
proof (induction rule: runs.induct)
  case (start s)
  then show ?case by simp
next
  case (step r t)
  then show ?case
  proof (cases "trns r = []")
    case True
    with step show ?thesis  by (simp add: append_tr_def)
  next
    case False
    with step show ?thesis     by (simp add: append_tr_def)
  qed
qed


thm "runs_def"

(* lemma "run-steps":
  assumes "r \<in> runs l \<and> i < length (trns r )"
  shows "(| src = fst (trns r ! i ),
      dst = (if Suc i < length (trns r ) then fst (trns r ! (Suc i ))
    else fins r ),
  lbl = snd (trns r ! i ) |) \<in> trans l"
   using assms 
proof (induction rule: runs.induct)
  case (start s)
  then show ?case by simp
next
  case (step r' t)
  show ?case
  proof (cases "i < length (trns r')")
    case True
    with step.IH show ?thesis
      by (auto simp add: nth_append)
  next
    case False
    with step.hyps have "i = length (trns r')"
      by auto
    with step.hyps show ?thesis
      by (auto simp add: nth_append outgoing_def)
  qed
qed *)


lemma "states-runs": "states l = fins ` (runs l)"
  sorry
(*   proof
  show "states l \<subseteq> fins ` (runs l)"
  proof
    fix s
    assume "s \<in> states l"
    then show "s \<in> fins ` (runs l)"
    proof (induction rule: states.induct)
      case (base s)
      then show ?case
        by (metis Run.select_convs(2) imageI runs.start)
    next
      case (step s t)
      then obtain r where "r \<in> runs l" and "fins r = s"
        by blast
      then have "append_tr r t \<in> runs l"
        using runs.step step.hyps(2) by blast
      then show ?case
        by (metis Run.select_convs(2) append_tr_def image_iff)
    qed
  qed
next
  show "fins ` (runs l) \<subseteq> states l"
  proof
    fix s
    assume "s \<in> fins ` (runs l)"
    then obtain r where "r \<in> runs l" and "fins r = s"
      by blast
    then show "s \<in> states l"
    proof (induction rule: runs.induct)
      case (start s)
      then show ?case
        by (simp add: states.base)
    next
      case (step r t)
      then show ?case
        by (metis fins.simps states.step)
    qed
  qed
qed *)

(* proof
  show "states l \<subseteq> fins ` (runs l)"
  proof
    fix s
    assume "s \<in> states l"
    then show "s \<in> fins ` (runs l)"
    proof (induction rule: states.induct)
      case (base s)
      then show ?case
      by (metis Run.select_convs(2) imageI runs.start)
    next
      case (step s t)
      then obtain r where "r \<in> runs l" and "fins r = s"
        by blast
      then have "append_tr r t \<in> runs l"
        using runs.step step.hyps(2) by blast
      then show ?case
      by (metis Run.select_convs(2) append_tr_def image_iff)
    qed
  qed
next
  show "fins ` (runs l) \<subseteq> states l"
  proof
    fix s
    assume "s \<in> fins ` (runs l)"
    then obtain r where "r \<in> runs l" and "fins r = s"
      by blast
    then show "s \<in> states l"
    proof (induction rule: runs.induct)
      case (start s)
      then show ?case
        by (simp add: states.base)
    next
      case (step r t)
      then show ?case
        by (metis append_tr_def fins.simps states.step)
    qed
  qed
qed
 *)  

(* 
proof
  show "states l \<subseteq> fins ` (runs l)"
  proof
    fix s
    assume "s \<in> states l"
    then show "s \<in> fins ` (runs l)"
    proof (induction rule: states.induct)
      case (base s)
      then show ?case
      by (metis Run.select_convs(2) imageI runs.start)
    next
      case (step s t)
      then obtain r where "r \<in> runs l" and "fins r = s"
        by blast
      then have "append_tr r t \<in> runs l"
        using runs.step step.hyps(2) by blast
      then show ?case
      by (metis Run.select_convs(2) append_tr_def image_iff)
    qed
  qed
next
  show "fins ` (runs l) \<subseteq> states l"
  proof
    fix s
    assume "s \<in> fins ` (runs l)"
    then obtain r where "r \<in> runs l" and "fins r = s"
      by blast
    then show "s \<in> states l"
    proof (induction rule: runs.induct)
      case (start s)
      then show ?case
        by (simp add: states.base)
    next
      case (step r t)
      then show ?case
        by try
    qed
  qed
qed
 *)

(*
proof
  show "states l \<subseteq> fins ` (runs l)"
  proof
    fix s
    assume "s \<in> states l"
    then show "s \<in> fins ` (runs l)"
    proof (induction rule: states.induct)
      case (base s)
      then show ?case
      proof -
        have "(| trns = [], fins = s |) \<in> runs l"
          using runs.start base.hyps  by metis
        then show ?thesis
        by force
      qed
    next
      case (step s t)
      then obtain r where "r \<in> runs l" and "fins r = s"
        by blast
      then have "append_tr r t \<in> runs l"
        using runs.step step.hyps(2) by blast
      then show ?case

      by (metis Run.select_convs(2) append_tr_def image_iff)
    qed
  qed
next
  show "fins ` (runs l) \<subseteq> states l"
  proof
    fix s
    assume "s \<in> fins ` (runs l)"
    then obtain r where "r \<in> runs l" and "fins r = s"
      by blast
    then show "s \<in> states l"
    proof (induction rule: runs.induct)
      case (start s)
      then show ?case
        by (simp add: states.base)
    next
      case (step r t)
      then show ?case
        by (metis append_tr_def states.step)
    qed
  qed
qed

*)

(* proof
  show "states l \<subseteq> fins ` (runs l)"
  proof
    fix s
    assume "s \<in> states l"
    then show "s \<in> fins ` (runs l)"
    proof (induction rule: states.induct)
      case (base s)
      then show ?case
      proof -
        have "(| trns = [], fins = s |) \<in> runs l"
          using runs.start base.hyps by metis
        then show ?thesis
        by force
      qed
    next
      case (step s t)
      then obtain r where "r \<in> runs l" and "fins r = s"
        by blast
      then have "append_tr r t \<in> runs l"
        using runs.step step.hyps(2) by blast
      then show ?case
      by (metis Run.select_convs(2) append_tr_def image_iff)
    qed
  qed
next
  show "fins ` (runs l) \<subseteq> states l"
  proof
    fix s
    assume "s \<in> fins ` (runs l)"
    then obtain r where "r \<in> runs l" and "fins r = s"
      by blast
    then show "s \<in> states l"
    proof (induction rule: runs.induct)
      case (start s)
      then show ?case
        by (simp add: states.base)
    next
      case (step r t)
      then have "fins r \<in> states l"
        using step.IH by 
      moreover have "t \<in> outgoing l (fins r)"
        using step.hyps(2) by blast
      ultimately show ?case
        using states.step by blast
    qed
  qed
qed
 *)

(* lemma 
  shows "{(x,y) . x \<in> {0..<n} \<and> y \<in> {0..<n} \<and> x = y} = {(x,x) |x. x < n}"
  sorry
 *)

   
lemma "(\<forall>  x. (x \<in> A) = (x \<in> B)) \<Longrightarrow> A = B"
  by auto

lemma "\<lbrakk>P x; x \<in> A \<rbrakk> \<Longrightarrow> \<exists> x\<in>A. P x"
  by blast
  
lemma "(\<forall> x. f x = g x) \<Longrightarrow> f = g"
  by auto


(*  definition isInSet:: "nat \<Rightarrow> nat set \<Rightarrow> bool" 
  where 
    "isInSet x natset = x in natset"
 *)

locale happens_before = preorder hb_weak hb
  for hb_weak :: "'a \<Rightarrow> 'a \<Rightarrow> bool"  (infix "\<preceq>" 50)
  and hb :: "'a \<Rightarrow> 'a \<Rightarrow> bool"       (infix "\<prec>" 50) +
  fixes interp :: "'a \<Rightarrow> 'b \<rightharpoonup> 'b" ("\<langle>_\<rangle>" [0] 1000)
begin

definition concurrent :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<parallel>" 50) where
  "s1 \<parallel> s2 \<equiv> \<not> (s1 \<prec> s2) \<and> \<not> (s2 \<prec> s1)"

lemma concurrentI [intro!]: "\<not> (s1 \<prec> s2) \<Longrightarrow> \<not> (s2 \<prec> s1) \<Longrightarrow> s1 \<parallel> s2"
  by (auto simp: concurrent_def)

lemma concurrentD1 [dest]: "s1 \<parallel> s2 \<Longrightarrow> \<not> (s1 \<prec> s2)"
  by (auto simp: concurrent_def)

lemma concurrentD2 [dest]: "s1 \<parallel> s2 \<Longrightarrow> \<not> (s2 \<prec> s1)"
  by (auto simp: concurrent_def)

lemma concurrent_refl [intro!, simp]: "s \<parallel> s"
  by (auto simp: concurrent_def)

lemma concurrent_comm: "s1 \<parallel> s2 \<longleftrightarrow> s2 \<parallel> s1"
  by (auto simp: concurrent_def)

definition concurrent_set :: "'a \<Rightarrow> 'a list \<Rightarrow> bool" where
  "concurrent_set x xs \<equiv> \<forall>y \<in> set xs. x \<parallel> y"

lemma concurrent_set_empty [simp, intro!]:
  "concurrent_set x []"
  by (auto simp: concurrent_set_def)

lemma concurrent_set_ConsE [elim!]:
  assumes "concurrent_set a (x#xs)"
      and "concurrent_set a xs \<Longrightarrow> concurrent x a \<Longrightarrow> G"
    shows "G"
  using assms by (auto simp: concurrent_set_def)

lemma concurrent_set_ConsI [intro!]:
  "concurrent_set a xs \<Longrightarrow> concurrent a x \<Longrightarrow> concurrent_set a (x#xs)"
  by (auto simp: concurrent_set_def)

lemma concurrent_set_appendI [intro!]:
  "concurrent_set a xs \<Longrightarrow> concurrent_set a ys \<Longrightarrow> concurrent_set a (xs@ys)"
  by (auto simp: concurrent_set_def)

lemma concurrent_set_Cons_Snoc [simp]:
  "concurrent_set a (xs@[x]) = concurrent_set a (x#xs)"
  by (auto simp: concurrent_set_def)

inductive hb_consistent :: "'a list \<Rightarrow> bool" where
  [intro!]: "hb_consistent []" |
  [intro!]: "\<lbrakk> hb_consistent xs; \<forall>x \<in> set xs. \<not> y \<prec> x \<rbrakk> \<Longrightarrow> hb_consistent (xs @ [y])"
end

lemma set_eqI:
  assumes "\<And>x. x \<in> A \<longleftrightarrow> x \<in> B"
  shows "A = B"
  using assms by blast

type_synonym uid = nat
type_synonym name = nat
type_synonym path = "name list"
datatype perm =   Readable  | Writable  | Executable  
type_synonym perms = "perm set"

record att =
  owner :: uid
  others :: perms

value "{1,2,3::nat} \<subseteq> {1,2,3,4,5,6::nat}"
value "set [1,2,3::nat]"

type_synonym user_id = nat
type_synonym object_id = nat
type_synonym capability = "user_id \<times> object_id \<Rightarrow> bool"

definition is_valid_cap :: "user_id \<Rightarrow> object_id \<Rightarrow> capability \<Rightarrow> bool" where
"is_valid_cap uid oid cap \<equiv> cap (uid, oid)"

definition can_access :: "user_id \<Rightarrow> object_id \<Rightarrow> capability \<Rightarrow> bool" where
"can_access uid oid cap \<equiv> \<exists>owner. is_valid_cap owner oid cap \<and>
  (owner = uid \<or> cap (uid, owner))"

definition secure_system :: "capability set \<Rightarrow> bool" where
"secure_system caps \<equiv> \<forall>uid oid1 oid2 cap1 cap2. is_valid_cap uid oid1 cap1 \<and>
  is_valid_cap uid oid2 cap2 \<and> oid1 \<noteq> oid2 \<and> \<not>can_access uid oid2 cap1 \<and>
  \<not>can_access uid oid1 cap2 \<longrightarrow> \<not>(cap1 = cap2)"

(* locale graph =
  fixes E :: "('v \<times> 'v) set"
definition (in graph) "V \<equiv> Range E \<union> Domain E" *)

definition "my_set \<equiv> {1::nat, 2, 3}"
definition "my_fun x \<equiv> x + 1"

value "my_fun ` my_set"

definition "double_set S \<equiv> (\<lambda>x. 2 * x) ` S"

lemma "double_set {1::nat, 2, 3} = {2, 4, 6}"
  unfolding double_set_def
  by auto

lemma "finite S \<Longrightarrow> finite (f ` S)"
  by (rule finite_imageI)

(* definition "partial_order R  \<equiv> (\<forall>x. R x x) \<and> (\<forall>x y. R x y \<and> R y x \<longrightarrow> x = y) \<and> (\<forall>x y z. R x y \<and> R y z \<longrightarrow> R x z)" *)

(* 
lemma example_the:
  assumes "\<exists>!x. x \<in> set xs \<and> x = 3"
  shows "THE x. x \<in> set xs \<and> (x = 3) = 3"
 *)

(* lemma example_the:
  assumes "\<exists>!x. x \<in> set xs \<and> x = (3::nat)"
  shows "THE x. x \<in> set xs \<and> x = (3::nat) = 3"
  using assms by auto
 *)


(* lemma example_the_applied:
  assumes "xs = [1, 2, 3]"
  shows "(THE x::nat . (x = 3) \<and> x \<in> set xs) = 3 "
proof -
  from assms have "\<exists>!x. x \<in> set xs \<and> x = 3"
    by auto
  then show ?thesis
       by blast
qed
 *)

lemma example_the_applied:
  assumes "xs = [1, 2, 3]"
  shows "(THE x::nat. (x = 3) \<and> x \<in> set xs) = 3"
(* proof -
  from assms have "\<exists>!x::nat. x \<in> set xs \<and> x = 3"
    by auto
  then show ?thesis
    by blast
qed *)

  using assms by auto (* the proof is pretty simple *)

lemma "0 = (THE x::nat. (x \<ge> 0 \<and> x \<le> 0))"
  (*the proof*)
  using theI[of \<open>\<lambda>x::nat. (x \<ge> 0 \<and> x \<le> 0)\<close> 0]
  by auto


lemma "\<lbrakk> P \<longrightarrow> Q; P\<rbrakk> \<Longrightarrow> Q"
  by auto


*)
(* 

lemma example: "A \<and> B \<Longrightarrow> True"
proof
  assume "A \<and> B"
  then obtain A and B by auto
  qed


definition test_set :: "nat set" where
  "test_set = {0, 1, 2}"

definition test_step :: "nat set \<Rightarrow> nat set" where
  "test_step S = S \<union> {x + 1 | x. x \<in> S}"

value "test_step {}"

value "test_step {0}"
value "test_step {0,1}"
value "test_step {0,1, 2}"
value "test_step {0,1}"

record system_state =
  nodes :: "nat set"
  messages :: "nat set" 
  processed :: "nat set"

definition total_messages :: "system_state \<Rightarrow> nat" where
  "total_messages s = card (messages s) + card (processed s)"

definition process_message :: "nat \<Rightarrow> system_state \<Rightarrow> system_state" where
  "process_message msg s = 
    \<lparr>nodes = nodes s, 
     messages = messages s - {msg},
     processed = processed s \<union> {msg}\<rparr>"
 *)
(* theorem message_conservation:
  assumes "msg \<in> messages s"
  shows "total_messages (process_message msg s) = total_messages s"

proof -
  (* Ключевое наблюдение: множества messages и processed изменяются биективно *)
  let ?f = "\<lambda>m. if m = msg then msg else m"
  
  have "bij_betw ?f (messages s) ((messages s - {msg}) \<union> {msg})"
    unfolding bij_betw_def inj_on_def
    using assms by auto
    
  have "card (messages s) = card (messages s - {msg}) + 1"
    using assms by (simp add: card_Diff_subset)
  
  have "card (processed s \<union> {msg}) = card (processed s) + 1"
    using assms by (simp add: card_insert_if)
    
  show ?thesis
    unfolding total_messages_def process_message_def
    by simp
qed *)

lemma 
  assumes "sorted xs" and "sorted ys" and "\<forall>x\<in>set xs. \<forall>y\<in>set ys. x \<le> y"
  shows "sorted (xs @ ys)"
  using assms by (simp add: sorted_append)

fun sorted' :: "('a :: linorder) list \<Rightarrow> bool" where
  "sorted' [] = True"
| "sorted' [x] = True"
| "sorted' (x # y # zs) = (x \<le> y \<and> sorted' (y # zs))"

lemma "sorted' xs = sorted xs"
proof (induction xs rule: sorted'.induct)
  case 1
  show ?case by simp 
next
  case (2 x)
  show ?case by simp 
next
  case (3 x y zs)
  assume IH: "sorted' (y # zs) = sorted (y # zs)"  
  have "sorted' (x # y # zs) = (x \<le> y \<and> sorted' (y # zs))"
    by (simp only: sorted'.simps(3))
  also have "... = (x \<le> y \<and> sorted (y # zs))"
    by (simp only: IH)
  also have "... = sorted (x # y # zs)"
    using sorted_simps(2) by fastforce  
  finally show ?case .
qed


lemma "sorted' xs = sorted xs"
proof (induction xs rule: sorted'.induct)
  case 1
  show ?case by simp 
next
  case (2 x)
  show ?case by simp 
next
  case (3 x y zs)
  assume IH: "sorted' (y # zs) = sorted (y # zs)"  
  show ?case    
  using IH by force 
qed

(* export_code sorted'  in SML module_name MyModule file "my_module.sml" *)

(* Пример: система с состояниями и переходами *)
datatype system_state = 
    INITIAL
  | PROCESSING nat 
  | COMPLETED
  | ERROR string

(* Индуктивное определение допустимых переходов *)
inductive_set system_transitions :: "(system_state \<times> system_state) set" where
  init_to_processing: 
    "(INITIAL, PROCESSING 0) \<in> system_transitions"
| processing_step: 
    "(PROCESSING n, PROCESSING (n+1)) \<in> system_transitions"
| processing_to_completed: 
    "(PROCESSING 5, COMPLETED) \<in> system_transitions"  
| error_anywhere: 
    "(s, ERROR msg) \<in> system_transitions"

(* ПРАВИЛЬНАЯ лемма: нет непосредственных циклов в PROCESSING *)
lemma no_immediate_processing_loop:
  "\<not> (\<exists>n. (PROCESSING n, PROCESSING n) \<in> system_transitions)"
proof
  assume "\<exists>n. (PROCESSING n, PROCESSING n) \<in> system_transitions"
  then obtain n where "(PROCESSING n, PROCESSING n) \<in> system_transitions"
    by blast
  thus False
    by (cases rule: system_transitions.cases) auto
qed

(* Система не только не застревает, но и движется к завершению *)
theorem processing_monotonic_progress:
  "\<forall>n. \<exists>s'. (PROCESSING n, s') \<in> system_transitions \<and> 
          (s' = COMPLETED \<or> s' = ERROR ''done'' \<or> 
           (\<exists>k. s' = PROCESSING k \<and> k > n))"  
  using system_transitions.error_anywhere by blast

theorem processing_monotonic_progress1:
  "\<forall>n. \<exists>s'. (PROCESSING n, s') \<in> system_transitions \<and> 
          (s' = COMPLETED \<or> s' = ERROR ''done'' \<or> 
           (\<exists>k. s' = PROCESSING k \<and> k > n))"
  by (auto intro!: system_transitions.intros)




lemma zero_steps: "(PROCESSING 2, PROCESSING 2) \<in> system_transitions\<^sup>*"
  by (rule rtrancl_refl)  


lemma one_step: "(PROCESSING 2, PROCESSING 3) \<in> system_transitions\<^sup>*"
proof -
  have "(PROCESSING 2, PROCESSING 3) \<in> system_transitions"
     by (metis nat_1_add_1 numeral_Bit1 numerals(1) system_transitions.processing_step)
  then show ?thesis
    by  auto
qed

(* \<^sup>*  — рефлексивное транзитивное замыкание (0 или более шагов) *)
lemma "\<forall>s. (s, s) \<in> system_transitions\<^sup>*" 
  by auto

axiomatization where
  AG: "CTL_AG P = (\<forall>path. path 0 \<in> initial_states \<longrightarrow> 
                   (\<forall>i. P (path i)))"
axiomatization where
  EF: "CTL_EF P = (\<exists>path. path 0 \<in> initial_states \<and> 
                   (\<exists>i. P (path i)))"

(* Линейная временная логика (LTL) *)
definition LTL_always :: "(system_state \<Rightarrow> bool) \<Rightarrow> bool" where
  "LTL_always P = (\<forall>path. path 0 \<in> initial_states \<longrightarrow> 
                   (\<forall>i. P (path i)))"

definition initial_states :: "system_state set" where
  "initial_states = {s. s = INITIAL}"


(* Достижимые состояния *)
definition reachable_states :: "system_state set" where  
  "reachable_states = {s. (INITIAL, s) \<in> system_transitions\<^sup>*}"

(* Терминальные состояния (без исходящих переходов) *)
definition terminal_states :: "system_state set" where
  "terminal_states = {s. \<not> (\<exists>s'. (s, s') \<in> system_transitions)}"


datatype finite_state = S1 | S2 | S3 | S4 | Done

(* Определяем переходы *)
inductive_set finite_transitions :: "(finite_state \<times> finite_state) set" where
  step1: "(S1, S2) \<in> finite_transitions"
| step2: "(S2, S3) \<in> finite_transitions"
| step3: "(S3, S4) \<in> finite_transitions"
| step4: "(S4, Done) \<in> finite_transitions"

(* Терминальные состояния *)
definition new_terminal_states :: "finite_state set" where
  "new_terminal_states = {s. \<not> (\<exists>s'. (s, s') \<in> finite_transitions)}"

(* Состояния, из которых достижимо терминальное *)
definition progressing_states :: "system_state set" where
  "progressing_states = {s. \<exists>t \<in> terminal_states. (s, t) \<in> system_transitions\<^sup>*}"

(* Образ множества состояний *)
definition Image :: "system_state set \<Rightarrow> system_state set" where
  "Image S = {s'. \<exists>s \<in> S. (s, s') \<in> system_transitions}"

 lemma lfp_property:
  "lfp (\<lambda>X. initial_states \<union> Image X) = reachable_states"
  using AG by blast

(* Наибольшая фиксированная точка для коиндукции *)  
(* lemma gfp_property:
  "gfp (\<lambda>X. {s. \<exists>s'. (s, s') \<in> system_transitions \<and> s' \<in> X}) = 
   {s. \<exists>inf_path. inf_path 0 = s \<and> \<forall>i. (inf_path i, inf_path (i+1)) \<in> system_transitions}"
 *)

lemma gfp_property:
  "gfp (\<lambda>X. {s. \<exists>s'. (s, s') \<in> system_transitions \<and> s' \<in> X}) = 
   {s. \<exists>inf_path. inf_path 0 = s \<and> (\<forall>i. (inf_path i, inf_path (i+1)) \<in> system_transitions)}"
  sorry



lemma "system_transitions^= = Id \<union> system_transitions"
  by auto

(* coinductive infinite_path :: "system_state stream \<Rightarrow> bool" where
  "(shd s, shd (stl s)) \<in> system_transitions \<Longrightarrow> 
   infinite_path (stl s) \<Longrightarrow> infinite_path s"
 *)

(* Максимальный путь (не может быть продолжен) *)
definition maximal_path :: "system_state list \<Rightarrow> bool" where
  "maximal_path path = (
    path \<noteq> [] \<and>
    (\<forall>i < length path - 1. (path!i, path!(i+1)) \<in> system_transitions) \<and>
    last path \<in> terminal_states
  )"

definition deterministic :: bool where
  "deterministic = (\<forall>s s1 s2. (s, s1) \<in> system_transitions \<and> 
                             (s, s2) \<in> system_transitions \<longrightarrow> s1 = s2)"


lemma "\<not> deterministic"   
(* Наша система недетерминирована из-за ERROR *)
  unfolding deterministic_def
  using system_transitions.error_anywhere by fastforce

(* Живость (liveness) *)
definition always_eventually_terminates :: bool where
  "always_eventually_terminates = 
   (\<forall>s \<in> reachable_states. \<exists>t \<in> terminal_states. (s, t) \<in> system_transitions\<^sup>*)"

(* lemma "always_eventually_terminates"
  unfolding always_eventually_terminates_def
  by blast
 *)

(* Прообраз *)
definition preImage :: "system_state set \<Rightarrow> system_state set" where  
  "preImage S = {s. \<exists>s' \<in> S. (s, s') \<in> system_transitions}"

(* Пример: *)
lemma "Image {PROCESSING 0} = {PROCESSING 1}"
   using AG by auto

(* Неподвижные точки *)
definition invariant :: "system_state set \<Rightarrow> bool" where
  "invariant I = (initial_states \<subseteq> I \<and> Image I \<subseteq> I)"

(* "Всегда в будущем P" *)
definition always_eventually :: "(system_state \<Rightarrow> bool) \<Rightarrow> bool" where
  "always_eventually P = (\<forall>s \<in> reachable_states. \<exists>s'. (s, s') \<in> system_transitions\<^sup>* \<and> P s')"

(* "Никогда не P" *)  
definition never :: "(system_state \<Rightarrow> bool) \<Rightarrow> bool" where
  "never P = (\<forall>s \<in> reachable_states. \<not> P s)"

(* "В конце концов всегда P" *)
definition eventually_always :: "(system_state \<Rightarrow> bool) \<Rightarrow> bool" where
  "eventually_always P = (\<exists>s \<in> reachable_states. \<forall>s'. (s, s') \<in> system_transitions\<^sup>* \<longrightarrow> P s')"





lemma "\<not> (s, s) \<in> system_transitions\<^sup>+"      
  using AG by blast

lemma "(PROCESSING 0, PROCESSING 2) \<in> system_transitions\<^sup>+"
  by (metis One_nat_def Suc_eq_plus1 nat_1_add_1 r_r_into_trancl system_transitions.processing_step)

lemma "system_transitions^= = Id \<union> system_transitions"
  by auto


lemma "(s, s') \<in> system_transitions\<inverse> \<longleftrightarrow> (s', s) \<in> system_transitions"
  by auto

lemma "(s, s') \<in> (system_transitions\<^sup>*)\<inverse> \<longleftrightarrow> (s', s) \<in> system_transitions\<^sup>*"
  by auto


(* 
datatype progress_state =
    START
  | PHASE1 nat  
  | PHASE2 nat  
  | FINAL

(* Отношение, гарантирующее прогресс *)
inductive_set progress_transitions :: "(progress_state \<times> progress_state) set" where
  start_phase1: "(START, PHASE1 0) \<in> progress_transitions"
| phase1_step:  "(PHASE1 n, PHASE1 (n+1)) \<in> progress_transitions"
| phase1_to_2:  "(PHASE1 5, PHASE2 0) \<in> progress_transitions"
| phase2_step:  "(PHASE2 n, PHASE2 (n+1)) \<in> progress_transitions"  
| phase2_final: "(PHASE2 3, FINAL) \<in> progress_transitions"

lemma no_regression:
  assumes "(s, s') \<in> progress_transitions\<^sup>*"
  assumes "(s', s'') \<in> progress_transitions\<^sup>*" 
  shows "\<not> (s'' = s \<and> s \<noteq> s')" 
  using assms
  using AG by blast
 *)

codatatype 'a stream = SCons (shd: 'a) (stl: "'a stream")

(* coinductive always_eventually :: "('a \<Rightarrow> bool) \<Rightarrow> 'a stream \<Rightarrow> bool" where
  "P (shd s) \<Longrightarrow> always_eventually P (stl s) \<Longrightarrow> always_eventually P s"
 *)
(* Утверждение: система всегда в конечном счете восстанавливается *)
(* lemma system_recovery:
  "always_eventually (\<lambda>s. s = HEALTHY) faulty_system_stream"
  using AG by blast
 *)

theorem processing_never_stuck:
  "\<forall>n. \<exists>s'. (PROCESSING n, s') \<in> system_transitions \<and> 
          (s' \<noteq> PROCESSING n)"
proof
  fix n
  show "\<exists>s'. (PROCESSING n, s') \<in> system_transitions \<and> s' \<noteq> PROCESSING n"
  proof (cases "n < 5")
    case True
    then show ?thesis  using system_transitions.error_anywhere by auto
  next
    case False
    then show ?thesis  using system_transitions.error_anywhere by auto
  qed
qed




end