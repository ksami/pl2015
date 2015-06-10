Require Export Assignment11_00.

(* problem #01: 10 points *)

(** **** Exercise: 2 stars (some_term_is_stuck)  *)
Example some_term_is_stuck :
  exists t, stuck t.
Proof.
  exists (tiszero tfalse).
  unfold stuck.
  split.
    unfold normal_form.
    unfold not.
    intros H.
    inversion H.
    inversion H0.
    inversion H2.

    unfold not.
    intros H.
    inversion H.
    inversion H0.
    inversion H0.
Qed.

(*-- Check --*)
Check some_term_is_stuck :
  exists t, stuck t.

