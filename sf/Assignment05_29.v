Require Export Assignment05_28.

(* problem #29: 10 points *)





(** 2 stars, optional (le_exercises)  *)
(** Here are a number of facts about the [<=] and [<] relations that
    we are going to need later in the course.  The proofs make good
    practice exercises. *)

Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
  intros m n o.
  intros H0.
  inversion H0.
    intros Hn. apply Hn.
    intros HSm0. induction HSm0.
      rewrite H2. apply H0.
      apply le_S. apply IHHSm0. apply H2.
Qed.