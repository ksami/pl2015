Require Export Assignment09_10.

(* problem #11: 10 points *)

(** **** Exercise: 3 stars, advanced, optional (is_wp_formal)  *)
(** Prove formally using the definition of [hoare_triple] that [Y <= 4]
   is indeed the weakest precondition of [X ::= Y + 1] with respect to
   postcondition [X <= 5]. *)
Theorem is_wp_example :
  is_wp (fun st => st Y <= 4)
    (X ::= APlus (AId Y) (ANum 1)) (fun st => st X <= 5).
Proof.
(* //TODO *)
(*
  unfold is_wp.
  split.
    unfold hoare_triple.
    intros st st' H H1.
    inversion H. subst.
    unfold update. simpl.
    omega.

    unfold hoare_triple.
    intros P' H st H1.
*)
exact FILL_IN_HERE.
Qed.

(*-- Check --*)
Check is_wp_example :
  is_wp (fun st => st Y <= 4)
    (X ::= APlus (AId Y) (ANum 1)) (fun st => st X <= 5).

