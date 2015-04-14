Require Export Assignment05_33.

(* problem #34: 10 points *)

Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof. 
  unfold lt. 
  intros n1 n2 m.
  intros H.
  inversion H.
  {
    split.
      apply n_le_m__Sn_le_Sm. apply le_plus_l.
      apply n_le_m__Sn_le_Sm. rewrite -> plus_comm with (n:=n1) (m:=n2). apply le_plus_l.
  }
  {
    split.
      rewrite H2. generalize dependent H. apply le_trans. apply n_le_m__Sn_le_Sm. apply le_plus_l.
      rewrite H2. generalize dependent H. apply le_trans. apply n_le_m__Sn_le_Sm. rewrite -> plus_comm with (n:=n1) (m:=n2). apply le_plus_l.
  }
Qed.

