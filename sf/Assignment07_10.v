Require Export Assignment07_09.

(* problem #10: 10 points *)

(** **** Exercise: 3 stars (update_permute)  *)
Theorem update_permute : forall n1 n2 x1 x2 x3 st,
  x2 <> x1 -> 
  (update (update st x2 n1) x1 n2) x3 = (update (update st x1 n2) x2 n1) x3.
Proof.
  intros n1 n2 x1 x2 x3 st.
  intros H.
  unfold update.
  destruct eq_id_dec.
    rewrite e in H. generalize H. rewrite neq_id. intros H1. reflexivity. apply H.
    reflexivity.
Qed.
(** [] *)

