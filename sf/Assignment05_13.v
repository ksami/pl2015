Require Export Assignment05_12.

(* problem #13: 10 points *)



(** 2 stars, optional (beq_nat_false)  *)
Theorem beq_nat_false : forall n m,
  beq_nat n m = false -> n <> m.
Proof.
  assert (f : forall P : Prop, False -> P).
    intros P HF.
    inversion HF.

  intros n m.
  unfold not.
  destruct beq_nat.
    intros H.
    induction n.
      intros Hm.
    intros Hnm.
    inversion Hnm.
    apply f.

  (* //TODO *)

Qed.
(** [] *)



