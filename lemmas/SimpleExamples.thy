theory SimpleExamples
   imports
    IMP2.IMP2
begin
  
 program_spec example1
  assumes "True"
  ensures "x = 5"
  defines \<open>
    x = 5
  \<close>
  apply vcg
  apply auto
  done

program_spec example2
  assumes "a \<ge> 0"
  ensures "x = a \<or> x = -a"
  defines \<open>
    if (a \<ge> 0) {
      x = a
    } else {
      x = -a
    }
  \<close>
  apply vcg
  apply auto
  done 

lemma fact_nat_step: 
  assumes "i \<ge> 0" 
  shows "fact (nat i) * (i + 1) = fact (nat (i + 1))"
proof -
  have "fact (nat (i + 1)) = fact (Suc (nat i))"
    using assms by (simp add: nat_add_distrib)
  also have "\<dots> = fact (nat i) * Suc (nat i)"
    by simp
  also have "Suc (nat i) = nat (i + 1)"
    using assms by simp
  finally show ?thesis
  by (metis add.commute assms int_eq_iff nat_mult_distrib of_nat_Suc of_nat_fact zero_le_mult_iff)
qed



(* 
program_spec array_sum
  assumes "n \<ge> 0"
  ensures "s = (\<Sum>i=0..<n. a[i])"
  defines \<open>
    s = 0;
    i = 0;
    while (i < n)
      @invariant \<open>s = (\<Sum>j=0..<i. a[j]) \<and> 0 \<le> i \<and> i \<le> n\<close>
    {
      s = s + a[i];
      i = i + 1
    }
  \<close>
  apply vcg
    apply (simp add: sum.lessThan_Suc_shift)
    apply simp
  done

program_spec find_max
  assumes "n > 0"
  ensures "max_val = Max (set (take n a))"
  defines \<open>
    max_val = a[0];
    i = 1;
    while (i < n)
      @invariant \<open>max_val = Max (set (take i a)) \<and> 0 < i \<and> i \<le> n\<close>
    {
      if (a[i] > max_val) {
        max_val = a[i]
      };
      i = i + 1
    }
  \<close>
  apply vcg
    apply (auto simp: take_Suc_conv_app_nth max_def)
  done

program_spec swap
  assumes "True"
  ensures "x = b \<and> y = a"
  defines \<open>
    tmp = x;
    x = y;
    y = tmp
  \<close>
  apply vcg
  apply simp
  apply auto
  sorry

program_spec fibonacci
  assumes "n \<ge> 0"
  ensures "f = fib n"
  defines \<open>
    if (n == 0) {
      f = 0
    } else if (n == 1) {
      f = 1
    } else {
      a = 0;
      b = 1;
      i = 2;
      while (i \<le> n)
        @invariant \<open>a = fib (i-2) \<and> b = fib (i-1) \<and> 2 \<le> i \<and> i \<le> n + 1\<close>
      {
        f = a + b;
        a = b;
        b = f;
        i = i + 1
      }
    }
  \<close>
  apply vcg
    apply (simp add: fib_simps)
    apply (simp add: fib_simps)
    apply auto
  done


 *)

end