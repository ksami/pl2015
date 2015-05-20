Require Export Assignment08_18.

(* problem #19: 10 points *)

Lemma constfold_0plus_sound:
  ctrans_sound constfold_0plus.
Proof.
  unfold ctrans_sound.
  intros c.
  unfold constfold_0plus.
  split; intros H.
    apply fold_constants_com_sound in H.    
    apply optimize_0plus_com_sound in H.
    apply H.

    apply fold_constants_com_sound.
    apply optimize_0plus_com_sound.
    apply H.
Qed.

(*-- Check --*)
Check constfold_0plus_sound:
  ctrans_sound constfold_0plus.
