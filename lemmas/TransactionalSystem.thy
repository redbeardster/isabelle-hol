theory TransactionalSystem
imports Main
begin

section \<open>Транзакционная система с возвратом состояний\<close>

subsection \<open>Базовые типы и определения\<close>

type_synonym Key = string
type_synonym Value = string
type_synonym Timestamp = nat


type_synonym Database = "(Key \<times> (Value \<times> Timestamp)) list"

record TransactionState =
  original_db :: Database
  current_db :: Database  
  log :: "(string \<times> Timestamp) list"
  start_time :: Timestamp

type_synonym RollbackAction = "TransactionState \<Rightarrow> TransactionState"
type_synonym TransactionResult = "TransactionState \<times> RollbackAction"

definition lookup :: "Key \<Rightarrow> Database \<Rightarrow> (Value \<times> Timestamp) option" where
  "lookup k db = map_of db k"

definition update_db :: "Key \<Rightarrow> Value \<Rightarrow> Database \<Rightarrow> Database" where
  "update_db k v db = (k, (v, 0)) # filter (\<lambda>(k', _). k' \<noteq> k) db"

definition string_add :: "Value \<Rightarrow> Value \<Rightarrow> Value" where
  "string_add a b = (case (a, b) of 
    (x, y) \<Rightarrow> if x = [] then y else if y = [] then x else x @ ''+'' @ y)"

definition string_sub :: "Value \<Rightarrow> Value \<Rightarrow> Value" where  
  "string_sub a b = (case (a, b) of
    (x, y) \<Rightarrow> if x = y then ''0'' else x @ ''-'' @ y)"

subsection \<open>Базовые операции с возвратом\<close>


definition begin_transaction :: "Database \<Rightarrow> TransactionState" where
  "begin_transaction db = \<lparr>
    original_db = db,
    current_db = db,
    log = [],
    start_time = 0
  \<rparr>"


definition commit_transaction :: "TransactionState \<Rightarrow> Database" where
  "commit_transaction transaction = current_db transaction"


definition insert_with_rollback :: "Key \<Rightarrow> Value \<Rightarrow> TransactionState \<Rightarrow> TransactionResult" where
  "insert_with_rollback k v transaction = (
    let current_time = start_time transaction + 1 in
    let new_db = (k, (v, current_time)) # filter (\<lambda>(k', _). k' \<noteq> k) (current_db transaction) in
    let new_transaction = transaction\<lparr> 
      current_db := new_db,
      log := (''INSERT '' @ k, current_time) # log transaction,
      start_time := current_time
    \<rparr> in
    let rollback_action = \<lambda>_. transaction in
    (new_transaction, rollback_action)
  )"

  
definition delete_with_rollback :: "Key \<Rightarrow> TransactionState \<Rightarrow> TransactionResult" where
  "delete_with_rollback k transaction = (
    let current_time = start_time transaction + 1 in
    case find (\<lambda>(k', _). k' = k) (current_db transaction) of
      None \<Rightarrow> (transaction, \<lambda>_. transaction)
    | Some (k, (v, t)) \<Rightarrow>
        let new_db = filter (\<lambda>(k', _). k' \<noteq> k) (current_db transaction) in
        let new_transaction = transaction\<lparr>
          current_db := new_db,
          log := (''DELETE '' @ k, current_time) # log transaction,
          start_time := current_time
        \<rparr> in
        let rollback_action = \<lambda>current. 
          current\<lparr> current_db := (k, (v, t)) # current_db current \<rparr>
        in
        (new_transaction, rollback_action)
  )"

subsection \<open>Композиция транзакций\<close>


definition compose_transactions :: 
  "(TransactionState \<Rightarrow> TransactionResult) \<Rightarrow> 
   (TransactionState \<Rightarrow> TransactionResult) \<Rightarrow> 
   (TransactionState \<Rightarrow> TransactionResult)" 
where
  "compose_transactions op1 op2 initial_state = (
    case op1 initial_state of
      (state1, rollback1) \<Rightarrow>
        case op2 state1 of
          (state2, rollback2) \<Rightarrow>
            (state2, \<lambda>s. rollback1 (rollback2 s))
  )"


fun transaction_sequence :: 
  "(TransactionState \<Rightarrow> TransactionResult) list \<Rightarrow> 
   (TransactionState \<Rightarrow> TransactionResult)" 
where
  "transaction_sequence [] = (\<lambda>s. (s, \<lambda>_. s))"
| "transaction_sequence (op # ops) = compose_transactions op (transaction_sequence ops)"

subsection \<open>Пример транзакции\<close>

definition test_database :: Database where
  "test_database = [
    (''temp_data'', (''old_value'', 1)),
    (''config'', (''settings'', 1)),
    (''user0'', (''Bob'', 1))
  ]"


definition example_transaction :: "Database \<Rightarrow> Database \<times> RollbackAction" where
  "example_transaction initial_db = (
    let start_state = begin_transaction initial_db in
    case insert_with_rollback ''user1'' ''Alice'' start_state of
      (state_after_insert, rollback_insert) \<Rightarrow>
        case delete_with_rollback ''temp_data'' state_after_insert of
          (final_state, rollback_delete) \<Rightarrow>
            let committed_db = commit_transaction final_state in
            let overall_rollback = \<lambda>s. rollback_insert (rollback_delete s) in
            (committed_db, overall_rollback)
  )"

subsection \<open>Компенсирующие действия для сложных операций\<close>

type_synonym CompensatingAction = "TransactionState \<Rightarrow> TransactionState"


definition transfer_money :: 
  "Key \<Rightarrow> Key \<Rightarrow> Value \<Rightarrow> TransactionState \<Rightarrow> TransactionState \<times> CompensatingAction" 
where
  "transfer_money from_acc to_acc amount transaction = (
    let current_time = start_time transaction + 1 in
    case (lookup from_acc (current_db transaction), lookup to_acc (current_db transaction)) of
      (Some (from_balance, _), Some (to_balance, _)) \<Rightarrow>
        let new_from_balance = string_sub from_balance amount in
        let new_to_balance = string_add to_balance amount in
        let new_db = update_db from_acc new_from_balance 
                   (update_db to_acc new_to_balance (current_db transaction)) in
        let new_transaction = transaction\<lparr>
          current_db := new_db,
          log := (''TRANSFER '' @ from_acc @ ''to'' @ to_acc @ '':'' @ amount, current_time) # log transaction,
          start_time := current_time
        \<rparr> in
        let compensating_action = \<lambda>current. 
          current\<lparr> current_db := update_db from_acc from_balance 
                         (update_db to_acc to_balance (current_db current)) \<rparr>
        in
        (new_transaction, compensating_action)
    | _ \<Rightarrow> (transaction, \<lambda>_. transaction)
  )"


definition test_accounts :: Database where
  "test_accounts = [
    (''account1'', (''100'', 1)),
    (''account2'', (''50'', 1))
  ]"

subsection \<open>Свойства и доказательства\<close>

lemma begin_transaction_preserves_db:
  "original_db (begin_transaction db) = db"
  by (simp add: begin_transaction_def)


lemma insert_adds_to_log:
  "insert_with_rollback k v transaction = (new_state, rollback) \<Longrightarrow>
   \<exists>entry. set (log new_state) = {entry} \<union> set (log transaction) \<and> 
           fst entry = ''INSERT '' @ k"
  unfolding insert_with_rollback_def
  by (auto simp: Let_def split: if_splits)


lemma delete_adds_to_log:
  "delete_with_rollback k transaction = (new_state, rollback) \<Longrightarrow>
   k \<in> set (map fst (current_db transaction)) \<Longrightarrow>
   \<exists>entry. set (log new_state) = {entry} \<union> set (log transaction) \<and> 
           fst entry = ''DELETE '' @ k"
  unfolding delete_with_rollback_def
(*   by (auto simp: Let_def split: option.splits) *)
  using Let_def option.split 
  apply clarsimp
(*   by metis *)
  sorry


lemma demonstration_example:
  "let initial_db = test_database in
   let (final_db, rollback_action) = example_transaction initial_db in
   \<exists>user1_entry. lookup ''user1'' final_db = Some (user1_entry, 2) \<and>
                \<not> (\<exists>temp_entry. lookup ''temp_data'' final_db = Some temp_entry)"
  unfolding test_database_def example_transaction_def 
            begin_transaction_def insert_with_rollback_def 
            delete_with_rollback_def commit_transaction_def
            lookup_def
  apply (auto simp: Let_def)
  sorry


lemma money_transfer_demonstration:
  "let start = begin_transaction test_accounts in
   case transfer_money ''account1'' ''account2'' ''30'' start of
     (new_state, compensate) \<Rightarrow>
       \<exists>new_acc1 new_acc2. 
         lookup ''account1'' (current_db new_state) = Some (new_acc1, 2) \<and>
         lookup ''account2'' (current_db new_state) = Some (new_acc2, 2) \<and>
         new_acc1 = ''100-30'' \<and> new_acc2 = ''50+30''"
  unfolding test_accounts_def begin_transaction_def 
            transfer_money_def lookup_def update_db_def
            string_add_def string_sub_def
  apply (auto simp: Let_def)
  done

subsection \<open>Расширенная система с вложенными транзакциями\<close>


definition nested_transaction :: "Database \<Rightarrow> Database \<times> RollbackAction" where
  "nested_transaction initial_db = (
    let start_state = begin_transaction initial_db in
    case insert_with_rollback ''nested1'' ''value1'' start_state of
      (state1, rollback1) \<Rightarrow>
        case insert_with_rollback ''nested2'' ''value2'' state1 of
          (state2, rollback2) \<Rightarrow>
            let committed_db = commit_transaction state2 in
            let overall_rollback = \<lambda>s. rollback1 (rollback2 s) in
            (committed_db, overall_rollback)
  )"


lemma nested_transaction_demo:
  "let initial_db = test_database in
   let (final_db, rollback_action) = nested_transaction initial_db in
   lookup ''nested1'' final_db \<noteq> None \<and> 
   lookup ''nested2'' final_db \<noteq> None"
  unfolding test_database_def nested_transaction_def
            begin_transaction_def insert_with_rollback_def
            commit_transaction_def lookup_def
  apply (auto simp: Let_def)
  done

subsection \<open>Утилиты для отладки\<close>


definition print_transaction_state :: "TransactionState \<Rightarrow> string" where
  "print_transaction_state state = (
    ''Original DB keys: '' @ show (map fst (original_db state)) @
    '' | Current DB keys: '' @ show (map fst (current_db state)) @
    '' | Log entries: '' @ show (map fst (log state))
  )"


definition transaction_integrity_ok :: "TransactionState \<Rightarrow> bool" where
  "transaction_integrity_ok state = (
    distinct (map fst (current_db state)) \<and>
    (\<forall>(op, time) \<in> set (log state). time \<le> start_time state)
  )"

lemma example_integrity:
  "transaction_integrity_ok (begin_transaction test_database)"
  unfolding transaction_integrity_ok_def begin_transaction_def 
            test_database_def
  by auto

end