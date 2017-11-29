theory Scratch
  imports HOL
begin

fun fib :: "nat \<Rightarrow> nat"
where
| "fib 0 = 1"
| "fib (Suc 0) = 1"
| "fib (Suc (Suc n)) = fib n + fib (Suc n)"

value fib 3