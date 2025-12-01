theory Test
  imports Main 
(*  "HOL-Hoare.Hoare_Logic" *)
begin


lemma basic_hoare:
  assumes "!!s. s ''x'' > (0::nat)"
  shows "!!s. (s(''y'' := s ''x'' + 1)) ''y'' > 1"
  using assms by fast


lemma simple_implication:
  fixes x :: nat
  assumes "x > 0"
  shows "x + 1 > 1"
  using assms by simp



end