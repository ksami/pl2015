Require Export Assignment08_06.

(* problem #07: 10 points *)

(** **** Exercise: 2 stars (IFB_false)  *)
Theorem IFB_false: forall b c1 c2,
  bequiv b BFalse  ->
  cequiv 
    (IFB b THEN c1 ELSE c2 FI) 
    c2.
Proof.
  intros b c1 c2 H.
  unfold cequiv.
  intros st st'.
  split.
    unfold bequiv in H.
    intros H1.
    (* //TODO *)
    inversion H1.
    generalize H6.
    apply E_IfTrue.


  exact FILL_IN_HERE.
Qed.

(*-- Check --*)
Check IFB_false: forall b c1 c2,
  bequiv b BFalse  ->
  cequiv 
    (IFB b THEN c1 ELSE c2 FI) 
    c2.

