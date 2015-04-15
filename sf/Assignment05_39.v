Require Export Assignment05_38.

(* problem #39: 10 points *)

Theorem ble_nat_false : forall n m,
  ble_nat n m = false -> ~(n <= m).
Proof.
  induction n.
    induction m.
      intros H. inversion H.
      intros H. inversion H.
    induction m.
      intros H. unfold not. intros HSn. inversion HSn.
      simpl. intros H. unfold not. intros HSn. apply Sn_le_Sm__n_le_m in HSn. generalize dependent HSn. apply IHn. apply H.
Qed.
(** [] *)

