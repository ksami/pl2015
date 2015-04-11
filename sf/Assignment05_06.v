Require Export Assignment05_05.

(* problem #06: 10 points *)


(** 2 stars, optional (orb_false)  *)
Theorem orb_prop : forall b c,
  orb b c = true -> b = true \/ c = true.
Proof.
  intros b c.
  intros H.
  destruct b.
  Case "b=true". destruct c.
    left. reflexivity. left. reflexivity.
  Case "b=false". destruct c.
    right. reflexivity. inversion H.
Qed.


