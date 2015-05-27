Require Export Assignment09_03.

(* problem #04: 10 points *)

(** **** Exercise: 2 stars (hoare_asgn_example4)  *)
(** Translate this "decorated program" into a formal proof:
                   {{ True }} ->>
                   {{ 1 = 1 }}
    X ::= 1;;
                   {{ X = 1 }} ->>
                   {{ X = 1 /\ 2 = 2 }}
    Y ::= 2
                   {{ X = 1 /\ Y = 2 }}
*)

Example hoare_asgn_example4 :
  {{fun st => True}} (X ::= (ANum 1);; Y ::= (ANum 2)) 
  {{fun st => st X = 1 /\ st Y = 2}}.
Proof.
exact FILL_IN_HERE.
(*  eapply hoare_seq.
  unfold hoare_triple.
  intros st st' H H1.
  split.
    inversion H. subst.
    inversion H. subst.
    inversion H2. subst.
    simpl in H6.*)
(* //TODO *)
Qed.

(*-- Check --*)
Check hoare_asgn_example4 :
  {{fun st => True}} (X ::= (ANum 1);; Y ::= (ANum 2)) 
  {{fun st => st X = 1 /\ st Y = 2}}.

