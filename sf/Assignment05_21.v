Require Export Assignment05_20.

(* problem #21: 10 points *)





(** 2 stars (ev_sum)  *)

Theorem ev_sum : forall n m,
   ev n -> ev m -> ev (n+m).
Proof. 
  intros n m.
  intros Hn Hm.
  induction Hn.
    apply Hm.
    induction Hm.
      apply ev_SS. apply IHHn.
      simpl. apply ev_SS. apply IHHn.
Qed.
(** [] *)





