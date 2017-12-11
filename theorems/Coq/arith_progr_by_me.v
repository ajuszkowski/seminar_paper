(* Require Import Coq.Arith.Arith. *)

Require Import Coq.omega.Omega.
Require Coq.Logic.Classical.

Section ArithmeticProgression.

(* formula for n-th member of arith progression (zero-based indexer => n+1 th member) *)
Fixpoint nth_member (a_0 d n: nat) : nat :=
  match n with
    | 0 => a_0
    | S p => d + (nth_member a_0 d p)
end.
Compute nth_member 3 2 4.

Theorem nth_member_formula : forall a_0 d n: nat,
  (nth_member a_0 d n) = a_0 + d * n.
Proof.
  intros.
  induction n; simpl.
  - rewrite -> Nat.mul_0_r.
    rewrite -> Nat.add_0_r.
    reflexivity.
  - induction n; rewrite -> IHn.
    + rewrite -> Nat.mul_0_r.
      rewrite -> Nat.add_0_r.
      rewrite -> Nat.mul_1_r.
      rewrite -> Nat.add_comm.
      reflexivity.
    + rewrite <- Nat.add_1_l.
      rewrite -> (Nat.mul_succ_r d (1 + n)).
      omega.
Qed.

Theorem bool_fn_applied_thrice :
  forall (f : bool -> bool) (b : bool),
  f (f (f b)) = f b.
Proof.
  intros f b.
  destruct b.
  destruct (f true) eqn:eq. rewrite eq. rewrite eq. reflexivity.
  destruct (f false) eqn:eq1. apply eq. apply eq1.
  destruct (f false) eqn:eq.
  destruct (f true) eqn:eq1. apply eq1. apply eq.
  rewrite eq. rewrite eq. reflexivity.
Qed.


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
    rewrite -> range_sum_succ.
    omega.
Qed.



(*
Check classic.
    (* assert ( n=0 \/ n<>0 ). { apply classic. }
    destruct IHn. *)
    + subst. simpl. omega.
    + assert (n>0). { destruct n. exfalso. apply H0. reflexivity. omega. }
      assert (H2 := H1).
      apply (memlem a_0 d) in H2. (* Here and 1 command below: I guess, that's what I needed *)
      rewrite H2.
      assert (H3 := H1).
      apply IHn in H1.
      rewrite H1.
      simpl.
      Search minus.
      rewrite <- minus_n_O.
      apply arithlem.
      assumption.
Qed.

(*
 simpl in H. destruct n.
    + simpl. omega. (* why doesn't inversion 1>0 work here? *)
    + simpl. omega. reflexivity.
*)

(* optional section with same questions *)

(* formula for sum of n first members of arith progr *)
Fixpoint sum_progr (a_0 d n: nat) : nat :=
  match n with
    | 0 => 0
    | 1 => a_0
    | S p => (member a_0 d (S p)) + (sum_progr a_0 d p)
end.

Check sum_progr.
Print sum_progr.
Compute sum_progr 3 2 4.

Theorem sum_formula : (forall a_0 d n: nat, n > 0 -> (sum_progr a_0 d n) = a_0 + d * n).
Proof.
  intros a_0 d n H_n_positive.
  (* same here. But I think the proof of 'nth_member' would be enought for this example. *)

  (*
  induction d. induction a_0.
  - simpl. induction n. reflexivity.
  - simpl. rewrite <- plus_Sn_m.  rewrite <- plus_n_O. reflexivity.
  - simpl. rewrite <- mult_n_O. rewrite <- plus_n_O. reflexivity.
  - rewrite <- mult_n_Sm.
  *)

Abort.

*)



(*Lemma nth_member_lemma : forall a_0 d n : nat,
    nth_member a_0 d (S n) = d + (nth_member a_0 d n).
Proof.
  intros. induction n.
  - simpl. reflexivity.
  - simpl. omega.
Qed.

Lemma sum_mul_distr_lemma : forall d n : nat,
    d + d * S n = d * S (S n).
Proof.
  intros.
  rewrite <- Nat.add_1_l.
  rewrite -> Nat.mul_add_distr_l.
  rewrite -> (Nat.mul_succ_r d (1 + n)).
  rewrite -> Nat.add_assoc.
  rewrite -> Nat.mul_add_distr_l. 
  omega.
Qed.
*)