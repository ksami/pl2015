Require Export Assignment07_04.

(* problem #05: 10 points *)

(** **** Exercise: 1 star (update_eq)  *)
Theorem update_eq : forall n x st,
  (update st x n) x = n.
Proof.
  intros n x st.
  induction x.
  induction n.
    unfold update.
    induction n0.
      simpl. reflexivity.
      apply eq_id.
    apply eq_id.
Qed.
(** [] *)

