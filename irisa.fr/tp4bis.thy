theory tp4bis
imports Main table
begin
datatype expression= Constant int | Variable string | Sum expression expression | Sub expression expression

type_synonym symTable= "(string, int) table"

fun evalE:: "expression \<Rightarrow> symTable \<Rightarrow> int"
where
"evalE (Constant s) e = s" |
"evalE (Variable s) e= (case (table.assoc s e) of None \<Rightarrow> -1 | Some(y) \<Rightarrow> y)" |
"evalE (Sum e1 e2) e= ((evalE e1 e) + (evalE e2 e))" |
"evalE (Sub e1 e2) e= ((evalE e1 e) - (evalE e2 e))" 

definition "expr1= (Sum (Variable ''x'') (Sub (Constant (-1)) (Sum (Variable ''x'') (Variable ''y''))))"
definition "expr2= (Sum (Constant (-1)) (Sub  (Variable ''x'')(Sum (Variable ''y'') (Variable ''x'') )))"

definition "stex1= [(''x'',2),(''y'',-3)]"

value "evalE expr1 stex1"
value "evalE expr2 stex1"

type_synonym varNbOccurrence= "(string, int) table"
type_synonym compiledExp = "(int * varNbOccurrence)"

end