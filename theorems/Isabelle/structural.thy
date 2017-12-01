theory structural
  imports HOL
begin

primrec sum :: "nat \<Rightarrow> nat" 
  where
  | "sum 0 = 0" 
  | "sum (Suc n) = Suc n + sum n"

lemma "sum n + sum n = n*(Suc n)"
  apply(induct_tac n)
  apply(auto)
  done


theorem sum_of_naturals: "2 * (\<Sum>i::nat=0..n. i) = n * (n + 1)"
  (is "?P n" is "?S n = _")
proof (induct n)
  show "?P 0" by simp
next
  fix n have "?S (n + 1) = ?S n + 2 * (n + 1)"
    by simp
  also assume "?S n = n * (n + 1)"
  also have "\<dots> + 2 * (n + 1) = (n + 1) * (n + 2)"
    by simp
  finally show "?P (Suc n)"
    by simp
qed

datatype 'nat = 0 | Suc nat

end