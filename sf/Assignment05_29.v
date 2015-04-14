Require Export Assignment05_28.

(* problem #29: 10 points *)





(** 2 stars, optional (le_exercises)  *)
(** Here are a number of facts about the [<=] and [<] relations that
    we are going to need later in the course.  The proofs make good
    practice exercises. *)

Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
  intros m n o.
  intros H0 H1.
  induction H0.
    apply H1.
    inversion H1.
      apply le_S. apply H0.
      apply le_S. 
(* //TODO *)
Qed.