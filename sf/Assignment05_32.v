Require Export Assignment05_31.

(* problem #32: 10 points *)

Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof. 
  intros n m H.
  inversion H.
    apply le_n.
    generalize dependent H2. apply le_trans. apply le_S. apply le_n.
Qed.

