Require Export Assignment05_38.

(* problem #39: 10 points *)

Theorem ble_nat_false : forall n m,
  ble_nat n m = false -> ~(n <= m).
Proof.
  intros n m.
  intros H.
  induction n.
  SearchAbout not.
  (* //TODO *)
Qed.
(** [] *)

