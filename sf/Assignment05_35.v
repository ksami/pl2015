Require Export Assignment05_34.

(* problem #35: 10 points *)

Theorem lt_S : forall n m,
  n < m ->
  n < S m.
Proof.
  unfold lt.
  intros n m.
  intros H.
  inversion H.
    apply le_S. apply le_n.
    apply le_S. rewrite H2. apply H.
Qed.

