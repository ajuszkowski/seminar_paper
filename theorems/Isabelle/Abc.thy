theory Abc
  imports Main
begin

fun fib :: "nat \<Rightarrow> nat"
where
"fib 0 = 1"
| "fib (Suc 0) = 1"
| "fib (Suc (Suc n)) = fib n + fib (Suc n)"

fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add 0 n = n" |
"add (Suc m) n = Suc(add m n)"

  
primrec nth_member :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
  where
      "nth_member a_0 d 0 = a_0"
    | "nth_member a_0 d (Suc p) = d + (nth_member a_0 d p)"

theorem "(nth_member a_0 d n) = a_0 + d * n"
  apply (induct n)
  apply (auto)
  done

value "nth_member a_0 d 3"

primrec nth_sum :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
  where
      "nth_sum a_0 d 0 = nth_member a_0 d 0"
    | "nth_sum a_0 d (Suc p) = (nth_sum a_0 d p) + (nth_member a_0 d (Suc p))"

value "nth_sum a_0 d 3"


primrec sum :: "nat \<Rightarrow> nat" 
  where
    "sum 0 = 0" 
  | "sum (Suc n) = Suc n + sum n"

lemma "sum n + sum n = n*(Suc n)"
  apply(induct_tac n)
  apply(auto)
  done

theorem sum_of_naturals: "2 * (\<Sum>i::nat=0..n. i) = n * (n + 1)"
  (is "?P n" 
   is "?Sum n = _")
proof (induct n)
  show "?P 0" by simp
next
  fix n have "?Sum (n + 1) = ?Sum n + 2 * (n + 1)"
    by simp
  also assume "?Sum n = n * (n + 1)"
  also have "\<dots> + 2 * (n + 1) = (n + 1) * (n + 2)"
    by simp
  finally show "?P (Suc n)"
    by simp
qed


(* theorem sum_of_members: "2 * (\<Sum>k::nat=0..n . nth_member a_0 d k) = (2 * a_0 + d * n) * (n + 1)" *)
theorem sum_of_members: "2 * (nth_sum a_0 d n) = (2 * a_0 + d * n) * (n + 1)"
  (is "?P n")
  proof (induct n)
    show "?P 0" by simp
    value "?P 0"
  next
    fix n have "2 * (nth_sum a_0 d (n + 1)) = (2 * a_0 + d * (n + 1) ) * (n + 2)" by simp
    