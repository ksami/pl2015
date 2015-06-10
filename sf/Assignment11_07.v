Require Export Assignment11_06.

(* problem #07: 10 points *)

(** **** Exercise: 1 star (normalize_ex)  *)
Theorem normalize_ex : exists e',
  (AMult (ANum 3) (AMult (ANum 2) (ANum 1))) / empty_state 
  ==>a* e'.
Proof.
  exists (ANum 6).
  eapply multi_step. auto. simpl.
  eapply multi_step. auto. simpl.
  apply multi_refl.
Qed.

(*-- Check --*)
Check normalize_ex : exists e',
  (AMult (ANum 3) (AMult (ANum 2) (ANum 1))) / empty_state 
  ==>a* e'.

