Require Export Assignment08_12.

(* problem #13: 10 points *)

(** **** Exercise: 3 stars (CIf_congruence)  *)
Theorem CIf_congruence : forall b b' c1 c1' c2 c2',
  bequiv b b' -> cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv (IFB b THEN c1 ELSE c2 FI) (IFB b' THEN c1' ELSE c2' FI).
Proof.
  intros b b' c1 c1' c2 c2' Hb Hc1 Hc2 st st'.
  unfold bequiv in Hb.
  split; intros H.
    inversion H.
    subst.
    apply E_IfTrue.
      rewrite Hb in H5. apply H5.
      apply Hc1 in H6. apply H6.
    apply E_IfFalse.
      rewrite Hb in H5. apply H5.
      apply Hc2 in H6. apply H6.

    inversion H.
    subst.
    apply E_IfTrue.
      rewrite <- Hb in H5. apply H5.
      apply Hc1 in H6. apply H6.
    apply E_IfFalse.
      rewrite <- Hb in H5. apply H5.
      apply Hc2 in H6. apply H6.
Qed.

(*-- Check --*)
Check CIf_congruence : forall b b' c1 c1' c2 c2',
  bequiv b b' -> cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv (IFB b THEN c1 ELSE c2 FI) (IFB b' THEN c1' ELSE c2' FI).

