Require Export Assignment06_05.

(* problem #06: 20 points *)

(** **** Exercise: 4 stars, advanced (no_repeats)  *)
(** The following inductively defined proposition... *)

Inductive appears_in {X:Type} (a:X) : list X -> Prop :=
  | ai_here : forall l, appears_in a (a::l)
  | ai_later : forall b l, appears_in a l -> appears_in a (b::l).

(** ...gives us a precise way of saying that a value [a] appears at
    least once as a member of a list [l]. 

    Here's a pair of warm-ups about [appears_in].
*)

Lemma appears_in_app : forall (X:Type) (xs ys : list X) (x:X), 
     appears_in x (xs ++ ys) -> appears_in x xs \/ appears_in x ys.
Proof.
  intros X xs ys x.
  induction xs.
    intros H. simpl in H. right. apply H.
    SearchAbout or.
    intros H. simpl in H. inversion H.
      left. apply ai_here.
      apply IHxs in H1. inversion H1.
        left. apply ai_later. apply H3.
        right. apply H3.
Qed.

Lemma app_appears_in : forall (X:Type) (xs ys : list X) (x:X), 
     appears_in x xs \/ appears_in x ys -> appears_in x (xs ++ ys).
Proof.
  intros X xs ys x.
  intros H.
  induction xs.
    inversion H.
      inversion H0.
      simpl. apply H0.
    inversion H.
      inversion H0.
        simpl. apply ai_here.
        simpl. apply ai_later. apply IHxs. left. apply H2.
      simpl. apply ai_later. apply IHxs. right. apply H0.
Qed.

