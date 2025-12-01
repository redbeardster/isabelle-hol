theory MyBits
  imports Main 

begin

datatype bit = Zero | One

definition bit_add :: "bit \<Rightarrow> bit \<Rightarrow> bit" where
  "bit_add x y = (case (x, y) of
    (Zero, Zero) \<Rightarrow> Zero
  | (Zero, One)  \<Rightarrow> One
  | (One,  Zero) \<Rightarrow> One
  | (One,  One)  \<Rightarrow> One)"

definition bit_mult :: "bit \<Rightarrow> bit \<Rightarrow> bit" where
  "bit_mult x y = (case (x, y) of
    (Zero, _) \<Rightarrow> Zero
  | (_, Zero) \<Rightarrow> Zero
  | (One,  One) \<Rightarrow> One)"


value "bit_mult One One"

lemma "bit_add x y = bit_add y x"
  by (cases x; cases y) (simp_all add: bit_add_def)

lemma  "bit_add (bit_add x y) z = bit_add x (bit_add y z)"
  by (cases x; cases y; cases z) (simp_all add: bit_add_def)

lemma "bit_mult x y = bit_mult y x"
  by (cases x; cases y) (simp_all add: bit_mult_def)

lemma "bit_add One x = One"
  by (cases x) (simp_all add: bit_add_def)


end