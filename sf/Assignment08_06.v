Require Export Assignment08_05.

(* problem #06: 10 points *)

(** **** Exercise: 2 stars (skip_right)  *)
(** Prove that adding a SKIP after a command results in an equivalent
    program *)

Theorem skip_right: forall c,
  cequiv 
    (c;; SKIP) 
    c.
Proof.
  intros c.
  unfold cequiv.
  split.
    intros H. inversion H. subst.
    inversion H2. subst. assumption. subst.
    (* //TODO *)
    exact FILL_IN_HERE.
Qed.

(*-- Check --*)
Check skip_right: forall c,
  cequiv 
    (c;; SKIP) 
    c.

