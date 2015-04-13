Require Export Assignment05_11.

(* problem #12: 10 points *)




(** 2 stars (false_beq_nat)  *)
Theorem false_beq_nat : forall n m : nat,
     n <> m ->
     beq_nat n m = false.
Proof.
  assert (f : forall P : Prop, False -> P).
    intros P HF.
    inversion HF.

  intros n m H.
  induction n.
    induction m.
      unfold not in H. simpl. apply f. apply H. reflexivity.
      simpl. reflexivity.
      unfold not in H. induction . apply H.








  unfold not in H.
  destruct beq_nat.
    destruct n.
      induction m.
          apply f.
          apply H.
          reflexivity.
          
          apply f. apply H.
          apply f.

(* //TODO *)

Qed.
(** [] *)




