Require Export Assignment05_19.

(* problem #20: 10 points *)








(** 3 stars, advanced (beautiful__gorgeous)  *)
Theorem beautiful__gorgeous : forall n, beautiful n -> gorgeous n.
Proof.
  intros n H.
  induction H.
    apply g_0.
    apply g_plus3. apply g_0.
    apply g_plus5. apply g_0.
    induction H0.

    induction IHbeautiful1.
      apply IHbeautiful1.

      apply g_plus3.
      apply IHIHbeautiful1. 


(* //TODO *)



      apply IHbeautiful2.
      apply g_plus3. apply IHIHbeautiful1. induction n.
        apply b_0.
        apply b_sum
Qed.
(** [] *)




