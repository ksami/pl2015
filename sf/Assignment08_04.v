Require Export Assignment08_03.

(* problem #04: 10 points *)

(** **** Exercise: 4 stars (no_whiles_terminating)  *)
(** Imp programs that don't involve while loops always terminate.
    State and prove a theorem [no_whiles_terminating] that says this. *)

(* Hint *)
Check andb_true_iff.

Theorem no_whiles_terminate: forall c st
    (NOWHL: no_whiles c = true),
  exists st', c / st || st'.
Proof.
  exact FILL_IN_HERE.
Qed.
(*  intros c st H.
  induction c.
    exists st. apply E_Skip.
    exists (update st i (aeval st a)). apply E_Ass. reflexivity.
    inversion H. apply andb_true_iff in H1. elim H1. intros Hc1 Hc2. apply IHc1 in Hc1. apply IHc2 in Hc2.
(* //TODO *)
*)

(*-- Check --*)
Check no_whiles_terminate: forall c st
    (NOWHL: no_whiles c = true),
  exists st', c / st || st'.

