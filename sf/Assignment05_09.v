Require Export Assignment05_08.

(* problem #09: 10 points *)



(** 2 stars (contrapositive)  *)
Theorem contrapositive : forall P Q : Prop,
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q.
  intros H.
  unfold not.
  intros H1.
  intros HP.
  apply H1.
  apply H.
  apply HP.
Qed.
(** [] *)



