Require Export Assignment09_11.

(* problem #12: 10 points *)

(** **** Exercise: 2 stars, advanced (hoare_asgn_weakest)  *)
(** Show that the precondition in the rule [hoare_asgn] is in fact the
    weakest precondition. *)

Theorem hoare_asgn_weakest : forall Q X a,
  is_wp (Q [X |-> a]) (X ::= a) Q.
Proof.
  unfold is_wp.
  intros Q X a.
  split.
    apply hoare_asgn.

    intros P'.
    unfold assert_implies.
    intros H st H1.
    unfold assn_sub.
    unfold hoare_triple in H.
    apply H with st.
    apply E_Ass. reflexivity. assumption.
Qed.

(*-- Check --*)
Check hoare_asgn_weakest : forall Q X a,
  is_wp (Q [X |-> a]) (X ::= a) Q.
