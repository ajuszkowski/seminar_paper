Require Import Coq.omega.Omega.
Require Coq.Logic.Classical.
Require Extraction.
Extraction Language Ocaml.



Module ArithmeticProgression.

Fixpoint arsum (n: nat) : nat :=
  match n with
    | 0 => 0
    | S p => arsum p + (S p)
end.
Print arsum.
Compute arsum 3.

Lemma arsum_successor_lemma: forall n: nat, arsum (n + 1) = arsum n + (n + 1).
Proof.
  intros.
  induction n.
  - simpl; reflexivity.
  - simpl; omega.
Qed.


Theorem SimpleArithProgressionSumFormula_Coq: forall n,
  2 * arsum n = n * (n + 1).
Proof.
  intros.
  induction n.
  - simpl; reflexivity.
  - rewrite -> Nat.mul_add_distr_l.
    rewrite -> Nat.mul_1_r.
    rewrite -> (Nat.mul_succ_l n).
    rewrite <- (Nat.add_1_r n).
    rewrite -> arsum_successor_lemma.
    omega.
Qed.

Extraction Language Haskell.

Extraction arsum.
Extraction arsum_successor_lemma.
Extraction SimpleArithProgressionSumFormula_Coq.