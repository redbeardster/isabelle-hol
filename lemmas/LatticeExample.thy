theory LatticeExample
  imports Main
begin

(* Определение частичного порядка *)
locale partial_order =
  fixes le :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "\<sqsubseteq>" 50)
  assumes refl: "x \<sqsubseteq> x"
    and antisym: "x \<sqsubseteq> y \<Longrightarrow> y \<sqsubseteq> x \<Longrightarrow> x = y"
    and trans: "x \<sqsubseteq> y \<Longrightarrow> y \<sqsubseteq> z \<Longrightarrow> x \<sqsubseteq> z"

begin

(* Пример свойства: если x \<sqsubseteq> y и y \<sqsubseteq> z, то x \<sqsubseteq> z *)
lemma example_trans: "x \<sqsubseteq> y \<Longrightarrow> y \<sqsubseteq> z \<Longrightarrow> x \<sqsubseteq> z"
  using trans by blast
end

locale lattice = partial_order +
  fixes sup :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<squnion>" 65)
    and inf :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<sqinter>" 70)
  assumes sup_ge1: "x \<sqsubseteq> x \<squnion> y"
    and sup_ge2: "y \<sqsubseteq> x \<squnion> y"
    and sup_least: "x \<sqsubseteq> z \<Longrightarrow> y \<sqsubseteq> z \<Longrightarrow> x \<squnion> y \<sqsubseteq> z"
    and inf_le1: "x \<sqinter> y \<sqsubseteq> x"
    and inf_le2: "x \<sqinter> y \<sqsubseteq> y"
    and inf_greatest: "z \<sqsubseteq> x \<Longrightarrow> z \<sqsubseteq> y \<Longrightarrow> z \<sqsubseteq> x \<sqinter> y"
begin

(* Пример свойства: идемпотентность supremum *)
lemma sup_idem: "x \<squnion> x = x"
proof -
  have "x \<sqsubseteq> x \<squnion> x" by (rule sup_ge1)
  moreover have "x \<squnion> x \<sqsubseteq> x" by (rule sup_least) (rule refl, rule refl)
  ultimately show ?thesis by (simp add: local.antisym)
qed


(* Доказательство ассоциативности supremum *)
lemma sup_assoc: "(x \<squnion> y) \<squnion> z = x \<squnion> (y \<squnion> z)"
proof (rule antisym)
  show "(x \<squnion> y) \<squnion> z \<sqsubseteq> x \<squnion> (y \<squnion> z)"
  proof (rule sup_least)
    show "x \<squnion> y \<sqsubseteq> x \<squnion> (y \<squnion> z)"
    proof (rule sup_least)
      show "x \<sqsubseteq> x \<squnion> (y \<squnion> z)" by (rule sup_ge1)
      show "y \<sqsubseteq> x \<squnion> (y \<squnion> z)" using local.sup_ge1 local.sup_ge2 local.trans by blast
    qed
    show "z \<sqsubseteq> x \<squnion> (y \<squnion> z)"  using local.sup_ge2 local.trans by blast
  qed
  show "x \<squnion> (y \<squnion> z) \<sqsubseteq> (x \<squnion> y) \<squnion> z"
  proof (rule sup_least)
    show "x \<sqsubseteq> (x \<squnion> y) \<squnion> z" using local.sup_ge1 local.trans by blast
    show "y \<squnion> z \<sqsubseteq> (x \<squnion> y) \<squnion> z"
    proof (rule sup_least)
      show "y \<sqsubseteq> (x \<squnion> y) \<squnion> z" using local.sup_ge1 local.sup_ge2 local.trans by blast
      show "z \<sqsubseteq> (x \<squnion> y) \<squnion> z" by (rule sup_ge2)
    qed
  qed
qed





end
