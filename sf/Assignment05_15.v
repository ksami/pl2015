Require Export Assignment05_14.

(* problem #15: 10 points *)



(** 1 star (double_even)  *)
Theorem double_even : forall n,
  ev (double n).
Proof.
  intros n.
  induction n.
    simpl. apply ev_0.
    inversion IHn.
      induction H0.
      apply ev_0 in IHn.
      destruct n.
        simpl. apply ev_SS. apply ev_0.
        inversion H0.

  (* //TODO *)
        
Qed.
(** [] *)




