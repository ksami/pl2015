Require Export Assignment05_36.

(* problem #37: 10 points *)
Theorem le_ble_nat : forall n m,
  n <= m ->
  ble_nat n m = true.
Proof.
  (* Hint: This may be easiest to prove by induction on [m]. *)
  induction n.
    induction m.
      intros H. simpl. reflexivity.
      intros H. simpl. reflexivity.
    induction m.
      intros H. inversion H.
      intros H. simpl. apply Sn_le_Sm__n_le_m in H. apply IHn. apply H.
Qed.

