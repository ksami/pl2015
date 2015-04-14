Require Export Assignment05_36.

(* problem #37: 10 points *)

Lemma ble_n_n : forall n,
  ble_nat n n = true.
Proof.
  induction n.
    simpl. reflexivity.
    simpl. apply IHn.
Qed.

Theorem le_ble_nat : forall n m,
  n <= m ->
  ble_nat n m = true.
Proof.
  (* Hint: This may be easiest to prove by induction on [m]. *)
  intros n m.
  induction m.
    intros H. inversion H. simpl. reflexivity.
    intros H. inversion H.
      simpl. apply ble_n_n.
(* //TODO *)
Qed.

