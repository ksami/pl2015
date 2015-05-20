Require Export Assignment08_11.

(* problem #12: 10 points *)

(** **** Exercise: 3 stars, optional (CSeq_congruence)  *)
Theorem CSeq_congruence : forall c1 c1' c2 c2',
  cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv (c1;;c2) (c1';;c2').
Proof. 
  intros c1 c1' c2 c2'.
  intros H1 H2.
  intros st st'.
  split.
    intros H.
    inversion H.
    subst.
    apply E_Seq with st'0.
      unfold cequiv in H1. apply H1 in H4. apply H4.
      unfold cequiv in H2. apply H2 in H7. apply H7.

    intros H.
    inversion H.
    subst.
    apply E_Seq with st'0.
      unfold cequiv in H1. apply H1 in H4. apply H4.
      unfold cequiv in H2. apply H2 in H7. apply H7.
Qed.

(*-- Check --*)
Check CSeq_congruence : forall c1 c1' c2 c2',
  cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv (c1;;c2) (c1';;c2').

