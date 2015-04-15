Require Export Assignment05_12.

(* problem #13: 10 points *)



(** 2 stars, optional (beq_nat_false)  *)
Theorem beq_nat_false : forall n m,
  beq_nat n m = false -> n <> m.
Proof.
  assert (f : forall P : Prop, False -> P).
    intros P HF.
    inversion HF.

  intros n.
  induction n.
    induction m.
      intros H. unfold not. inversion H.
      intros H. unfold not. intros H1. inversion H1.
    intros m H. unfold not. intros H1. rewrite H1 in H. rewrite <- beq_nat_refl in H. inversion H.
Qed.
(** [] *)



