Require Export Assignment08_16.

(* problem #17: 10 points *)
Lemma optimize_0plus_bexp_sound:
  btrans_sound optimize_0plus_bexp.
Proof.
  unfold btrans_sound.
  intros b.
  unfold bequiv.
  intros st.
  induction b;
    try reflexivity;
    try (simpl; rewrite <- optimize_0plus_aexp_sound; rewrite <- optimize_0plus_aexp_sound; reflexivity).
    simpl. rewrite <- IHb. reflexivity.
    simpl. rewrite <- IHb1. rewrite <- IHb2. reflexivity.
Qed.

(*-- Check --*)
Check optimize_0plus_bexp_sound:
  btrans_sound optimize_0plus_bexp.

