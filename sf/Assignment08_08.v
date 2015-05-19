Require Export Assignment08_07.

(* problem #08: 10 points *)

(** **** Exercise: 3 stars (swap_if_branches)  *)
(** Show that we can swap the branches of an IF by negating its
    condition *)

Theorem swap_if_branches: forall b e1 e2,
  cequiv
    (IFB b THEN e1 ELSE e2 FI)
    (IFB BNot b THEN e2 ELSE e1 FI).
Proof.
  intros b e1 e2 st st'.
  split.
    intros H.
    inversion H.
      subst.
      apply E_IfFalse.
      induction b; try reflexivity;
        try inversion H5;
        try (inversion H5; simpl; rewrite H1; reflexivity).
        apply H6.
      
      subst.
      apply E_IfTrue.
      induction b; try reflexivity;
        try inversion H5;
        try (inversion H5; simpl; rewrite H1; reflexivity).
        apply H6.


    intros H.
    inversion H.
      subst.
      apply E_IfFalse.
        induction b; try reflexivity;
        try inversion H5;
        try (simpl; apply negb_true_iff in H1; apply H1).
        apply H6.

      subst.
      apply E_IfTrue.
        induction b; try reflexivity;
        try inversion H5;
        try (simpl; apply negb_false_iff in H1; apply H1).
        apply H6.
Qed.

(*-- Check --*)
Check swap_if_branches: forall b e1 e2,
  cequiv
    (IFB b THEN e1 ELSE e2 FI)
    (IFB BNot b THEN e2 ELSE e1 FI).s

