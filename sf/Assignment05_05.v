Require Export Assignment05_04.

(* problem #05: 10 points *)


(** 1 star, optional (or_distributes_over_and)  *)
Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros.
  split.
    intros H.
    inversion H.
      split.
        apply or_introl. apply H0.
        apply or_introl. apply H0.
      split.
        inversion H0.
          apply or_intror. apply H1.
          apply or_intror. apply H0.
    intros H.
    inversion H.
    inversion H0.
      apply or_introl. apply H2.
      inversion H1.
        apply or_introl. apply H3.
        apply or_intror. split. apply H2. apply H3.
Qed.
(** [] *)


