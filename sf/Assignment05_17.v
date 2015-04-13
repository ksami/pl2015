Require Export Assignment05_16.

(* problem #17: 10 points *)





(** 3 stars (b_timesm)  *)
Theorem b_timesm: forall n m, beautiful n -> beautiful (m*n).
Proof.
  intros n m.
  intros Hn.
  induction m.
    simpl. apply b_0.
    simpl. apply b_sum with (n:=n) (m:=m*n).
      apply Hn.
      apply IHm.
Qed.
(** [] *)




