Require Export Assignment05_31.

(* problem #32: 10 points *)

Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof. 
  intros n m H.
  induction n.
    apply O_le_n.
    apply le_S in IHn. apply H.

  induction H.
    apply le_n.
    apply le_n.
    inversion H2.
  (* //TODO *)

  apply n_le_m__Sn_le_Sm in H.
Qed.

