Require Export Assignment05_35.

(* problem #36: 10 points *)

Theorem ble_nat_true : forall n m,
  ble_nat n m = true -> n <= m.
Proof. 
  induction n.
    induction m.
      intros H. apply le_n.
      intros H. apply O_le_n.
    induction m.
      intros H. simpl in H. inversion H.
      intros H. simpl in H. apply n_le_m__Sn_le_Sm. apply IHn. apply H.
Qed.

