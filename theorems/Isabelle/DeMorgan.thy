theory DeMorgan
  imports HOL
begin

lemma DeMorgan: "~(A /\ B)=(~A \/ ~B)"
proof (rule ccontr)
