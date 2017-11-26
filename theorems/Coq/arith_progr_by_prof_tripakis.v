(* Require Import Coq.Arith.Arith. *)

Require Import Coq.omega.Omega.
Require Coq.Logic.Classical.

Section ArithmeticProgression.

(* formula for n-th member of arith progr *)
Fixpoint member (a_0 d n: nat) : nat :=
  match n with
    | 0 => 0
    | 1 => a_0
    | S p => d + (member a_0 d p)
end.
Check member.
Print member.
Compute member 3 2 4.

Fixpoint member' (a_0 d n: nat) : nat :=
  match n with
    | 0 => 0
    | S p => match p with
              | 0 => a_0
              | S q => d + (member a_0 d q)
end end.

Lemma memlem : forall a_0 d n : nat, n>0 ->
    member a_0 d (S n) = d + (member a_0 d n).
Proof.
  intros. induction n.
  - inversion H. 
  - simpl. omega. 
Qed.

Lemma arithlem : forall a_0 d n : nat, n>0 ->
  d + (a_0 + d * (n - 1)) = a_0 + d * n.
Proof.
  intros. destruct n. inversion H.
  simpl. rewrite <- minus_n_O.
Search plus.
  rewrite <- mult_n_Sm.
  omega.
Qed.

 Axiom classic : forall P:Prop, P \/ ~ P.

Theorem nth_member : (forall a_0 d n: nat, n > 0 -> (member a_0 d n) = a_0 + d * (n - 1)).
Proof.
  intros.
  induction n.
  - inversion H.
  - Check classic.
    assert ( n=0 \/ n<>0 ). { apply classic. }
    destruct H0.
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

