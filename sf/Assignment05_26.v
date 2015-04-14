Require Export Assignment05_25.

(* problem #26: 10 points *)











(** 3 star (even__ev)  
    Note that proving [even__ev] directly is hard.
    You might find it easier to prove [even__ev_strong] first
    and then prove [even__ev] using it.
*)

Lemma even__ev_strong: forall n : nat, 
  (even (pred n) -> ev (pred n)) /\ (even n -> ev n).
Proof.
  intros n.
  induction n.
    split.
      intros H. simpl. apply ev_0.
      intros H. apply ev_0.
      
    split.
      simpl. apply IHn.
      assert (h: even (S n)=even (pred n)).
(* //TODO *)

Qed.
(** [] *)


