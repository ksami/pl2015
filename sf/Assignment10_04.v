Require Export Assignment10_03.

(* problem #04: 10 points *)

(** **** Exercise: 1 star, optional (test_multistep_3)  *)
Lemma test_multistep_3:
      P (C 0) (C 3)
   ==>*
      P (C 0) (C 3).
Proof.
  apply multi_refl.
Qed.

(*-- Check --*)
Check test_multistep_3:
      P (C 0) (C 3)
   ==>*
      P (C 0) (C 3).

