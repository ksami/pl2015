Require Export Assignment05_35.

(* problem #36: 10 points *)

Theorem ble_nat_true : forall n m,
  ble_nat n m = true -> n <= m.
Proof. 
  SearchAbout ble_nat.
  intros n m.
  intros H.
  induction n.
    apply O_le_n.
    induction m.
      simpl in H. inversion H.
      




  induction n.
    intros H. apply O_le_n.
    induction m.
      intros H. simpl in H. inversion H.
      
      (* //TODO *)
Qed.

