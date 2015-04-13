Require Export Assignment05_18.

(* problem #19: 10 points *)




(** 2 stars (gorgeous_sum)  *)
Theorem gorgeous_sum : forall n m,
  gorgeous n -> gorgeous m -> gorgeous (n + m).
Proof.
  intros n m.
  intros Hn Hm.
  induction Hn.
    simpl. apply Hm.
    apply g_plus3. apply IHHn.
    apply g_plus5. apply IHHn.
Qed.
(** [] *)


