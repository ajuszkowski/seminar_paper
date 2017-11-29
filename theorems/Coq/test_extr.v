
Require Import Coq.omega.Omega.
Require Coq.Logic.Classical.


Fixpoint range_sum (n: nat) : nat :=
  match n with
    | 0 => 0
    | S p => range_sum p + (S p)
end.
Compute range_sum 3.

Lemma range_sum_successor_lemma: forall n: nat, range_sum (n + 1) = range_sum n + (n + 1).
Proof.
  intros.
  induction n.
  - simpl; reflexivity.
  - simpl. omega.
Qed.

Theorem SimpleArithProgressionSumFormula_Coq: forall n,
  2 * range_sum n = n * (n + 1).
Proof.
  intros.
  induction n.
  - simpl; reflexivity.
  - rewrite -> Nat.mul_add_distr_l.
    rewrite -> Nat.mul_1_r.
    rewrite -> (Nat.mul_succ_l n).
    rewrite <- (Nat.add_1_r n).
    rewrite -> range_sum_successor_lemma.
    omega.
Qed.


Extraction Language Haskell
Extraction "divalg.hs" divalg
