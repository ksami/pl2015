Require Export Assignment05_17.

(* problem #18: 10 points *)





(** 1 star (gorgeous_plus13)  *)
Theorem gorgeous_plus13: forall n, 
  gorgeous n -> gorgeous (13+n).
Proof.
  intros n Hn.
  apply g_plus5.
  apply g_plus5.
  apply g_plus3.
  apply Hn.
Qed.
(** [] *)




