Require Export Assignment05_24.

(* problem #25: 10 points *)









(** 3 stars, optional (ev_plus_plus)  *)
(** Here's an exercise that just requires applying existing lemmas.  No
    induction or even case analysis is needed, but some of the rewriting
    may be tedious. 
    Hint: You can use [plus_comm], [plus_assoc], [double_plus], [double_even], [ev_sum], [ev_ev__ev].
*)
Check plus_comm.
Check plus_assoc. 
Check double_plus.
Check double_even.
Check ev_sum.
Check ev_ev__ev.

Theorem ev_plus_plus : forall n m p,
  ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
  intros n m p.
  intros Hnm Hnp.
  apply ev_ev__ev with (n:=n) (m:=m) in Hnm.
  apply ev_ev__ev with (n:=n) (m:=p) in Hnp.
  apply ev_sum.
    apply Hnm.
    apply Hnp.
  
    
   
   apply ev_ev__ev with (n:=(m+p)) (m:=(m+p)). 
    rewrite <- plus_assoc.
    rewrite -> plus_comm with (n:=p) (m:=(m+p)).
    rewrite -> plus_assoc.
    rewrite -> plus_assoc.
    rewrite <- double_plus.
    rewrite <- plus_assoc.
    rewrite <- double_plus.
    apply ev_sum.
      apply double_even.
      apply double_even.
      (* //TODO *)
    
Qed.
(** [] *)


