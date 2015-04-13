Require Export Assignment05_27.

(* problem #28: 30 points *)


(** 4 stars (palindromes)  *)
(** A palindrome is a sequence that reads the same backwards as
    forwards.

    - Define an inductive proposition [pal] on [list X] that
      captures what it means to be a palindrome. (Hint: You'll need
      three cases.  Your definition should be based on the structure
      of the list; just having a single constructor
        c : forall l, l = rev l -> pal l
      may seem obvious, but will not work very well.)
 
    - Prove [pal_app_rev] that 
       forall l, pal (l ++ rev l).
    - Prove [pal_rev] that 
       forall l, pal l -> l = rev l.
*)

Inductive pal {X: Type} : list X -> Prop :=
  | pal_nil : pal []
  | pal_c : forall l, l = rev l -> pal l
  | pal_spl : forall l1 l2, l1 = l2 -> pal (l1 ++ l2)
.

Theorem pal_app_rev: forall (X: Type) (l: list X),
  pal (l ++ rev l).
Proof.
  intros X l.
  induction l.
    apply pal_spl. simpl. reflexivity.

(* //TODO *)

  apply pal_spl.
  apply pal_c.
  induction l.
    apply pal_nil.
    inversion IHl.
      apply pal_c. simpl. reflexivity.
      apply pal_c. simpl. rewrite <- H. unfold snoc. reflexivity.
Qed.

Theorem pal_rev: forall (X: Type) (l: list X),
  pal l -> l = rev l.
Proof.
  (* FILL IN HERE *) admit.
Qed.

(** [] *)




