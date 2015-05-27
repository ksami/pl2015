Require Export Assignment09_01.

(* problem #02: 10 points *)

Theorem assn_sub_ex2:
  {{ (fun st => 0 <= st X /\ st X <= 5) [X |-> ANum 3] }}
     X ::= ANum 3
  {{ fun st => 0 <= st X /\ st X <= 5 }}.
Proof.
  unfold hoare_triple.
  intros st st' H H1.
  inversion H. subst.
  unfold assn_sub in H1.
  assumption.
Qed.

(*-- Check --*)
Check assn_sub_ex2:
  {{ (fun st => 0 <= st X /\ st X <= 5) [X |-> ANum 3] }}
     X ::= ANum 3
  {{ fun st => 0 <= st X /\ st X <= 5 }}.

