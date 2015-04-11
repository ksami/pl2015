Require Export Assignment05_07.

(* problem #08: 10 points *)



(** 2 stars, advanced (double_neg_inf)  *)
Theorem double_neg_inf: forall (P: Prop),
  P -> ~~P.
Proof.
  intros P.
  intros HP.
  unfold not.
  intros H.
  apply H.
  apply HP.
Qed.
(** [] *)



