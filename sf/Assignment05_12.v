Require Export Assignment05_11.

(* problem #12: 10 points *)




(** 2 stars (false_beq_nat)  *)
Theorem false_beq_nat : forall n m : nat,
     n <> m ->
     beq_nat n m = false.
Proof.
  assert (f : forall P : Prop, False -> P).
    intros P HF.
    inversion HF.

  intros n.
  induction n.
    induction m.
      intros H. unfold not in H. simpl. apply f. apply H. reflexivity.
      simpl. reflexivity.
    intros m H. unfold not in H. unfold not in IHn. induction m.
      simpl. reflexivity.
      simpl. apply IHn. intros H1. apply H. rewrite H1. reflexivity.
Qed.
(** [] *)




