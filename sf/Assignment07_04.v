Require Export Assignment07_03.

(* problem #04: 10 points *)

(** **** Exercise: 1 star, optional (neq_id)  *)
Lemma neq_id : forall (T:Type) x y (p q:T), x <> y -> 
               (if eq_id_dec x y then p else q) = q. 
Proof.
  intros T x y p q.
  unfold not.
  intros H.
  destruct (eq_id_dec x y).
    apply ex_falso_quodlibet. apply H. apply e.
    reflexivity.
Qed.
(** [] *)

