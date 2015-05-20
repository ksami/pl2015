Require Export Assignment08_15.

(* problem #16: 10 points *)

Lemma optimize_0plus_aexp_sound:
  atrans_sound optimize_0plus_aexp.
Proof.
  unfold atrans_sound.
  intros a.
  induction a;
    try (simpl; apply refl_aequiv).
    destruct a1.
      destruct n.
        unfold aequiv. simpl. apply IHa2.
        unfold aequiv. unfold aequiv in IHa2. 
        simpl. intros st. rewrite IHa2.
        (* //TODO*)
Qed.

(*-- Check --*)
Check optimize_0plus_aexp_sound:
  atrans_sound optimize_0plus_aexp.

