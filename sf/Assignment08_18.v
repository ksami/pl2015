
Require Export Assignment08_17.

(* problem #18: 10 points *)

Lemma optimize_0plus_com_sound:
  ctrans_sound optimize_0plus_com.
Proof.
  exact FILL_IN_HERE.
(*  unfold ctrans_sound.
  intros c.
  intros st st'.
  induction c.
    split; intros H.
      inversion H. simpl. rewrite H2 in H. apply H.
      inversion H. apply E_Skip.
    
    split; intros H.
      inversion H. subst. apply E_Ass. rewrite <- optimize_0plus_aexp_sound. reflexivity.
      inversion H. subst. apply E_Ass. rewrite optimize_0plus_aexp_sound. reflexivity.

    split; intros H.
      inversion H. subst. simpl. apply E_Seq with st'0.
        inversion IHc1.*)
        (* //TODO *)
Qed.

(*-- Check --*)
Check optimize_0plus_com_sound:
  ctrans_sound optimize_0plus_com.

