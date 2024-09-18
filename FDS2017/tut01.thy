theory tut01 
imports Main
begin
  find_theorems "_ - (_::nat) = _" name: simp

  value "int ((3::nat) * 1000)"
  
  lemma "(10::nat) > 0" by simp
    
  term "op +"    
  lemma nat_add_commute: "a+(b::nat) = b+a"
    by simp    
      
  thm nat_add_commute    
    
  lemma nat_add_assoc: "(a::nat) + (b+c) = (a+b)+c" by simp 
      
      
  typ "nat list"    
      
  term "[1,3,4,5,1]"  

  fun count :: "'a list \<Rightarrow> 'a \<Rightarrow> nat" where
    "count [] _ = 0"
  | "count (x#xs) y = (if x=y then 1+count xs y else count xs y)" 

  value "int (count ([1,2,3,4,5,6,2,2,2,2,2::nat] @ replicate 71 6) 6)"  

  value "length [1,2,3,1]"
    
    
  lemma "count xs x \<le> length xs"  
    apply (induction xs)
    apply simp
    apply ()  
      
      
    done

  fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
    "snoc [] a = [a]"
  | "snoc (x#xs) a = x # snoc xs a" 

  value "snoc [1,2,(3::int)] 5"  
    
  fun reverse :: "'a list \<Rightarrow> 'a list" where
    "reverse [] = []" 
  | "reverse (x#xs) = snoc (reverse xs) x" 
    
  value "reverse [1,2,3,4::int]"  
    
  lemma aux: "reverse (snoc xs x) = x # reverse xs" 
    apply (induction xs)
    apply auto  
    done
    
    
  lemma "reverse (reverse xs) = xs"
    apply (induction xs)
    apply (auto simp: aux)
    done  
    
end
  