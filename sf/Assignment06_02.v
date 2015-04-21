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
  (* //TODO *)
  intros H.
  unfold excluded_middle in H.
  unfold not in H.
  unfold not.
  intros X P.
  intros H1.
  intros x.
  exists 
Qed.
(** [] *)

