Require Export Assignment06_01.

(* problem #02: 10 points *)

(** **** Exercise: 3 stars, optional (not_exists_dist)  *)
(** (The other direction of this theorem requires the classical "law
    of the excluded middle".) *)

Theorem not_exists_dist :
  excluded_middle ->
  forall (X:Type) (P : X -> Prop),
    ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
  intros H.
  unfold excluded_middle in H.
  intros X P.
  intros H1.
  intros x.
  unfold not in H1.
  assert (H2: P x \/ ~P x).
    apply H.
  inversion H2.
    apply H0.
    unfold not in H0. apply ex_falso_quodlibet. apply H1. exists x. apply H0.
Qed.
(** [] *)

