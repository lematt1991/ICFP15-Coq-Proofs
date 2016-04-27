Require Import fullImpliesPartial. 
Require Import partialImpliesFull. 

(*specifies that T is a source program*)
Fixpoint initialPool T :=
  match T with
      |Single(noTXThread id e) => True
      |_ => False
  end. 

(*specifies that T has reached a terminal state*)
Fixpoint Done T :=
  match T with
      |Single(noTXThread id v) => value v
      |Par T1 T2 => Done T1 /\ Done T2
      |_ => False
  end. 

(*if T is done and T' is ahead of T, then T = T'*)
Theorem DoneAheadOf : forall H T T', 
                   Done T -> AheadOf H T T' ->
                   T = T'. 
Proof.
  intros. induction H1. 
  {inv H0; auto. }
  {inv H0. }
  {inv H0. rewrite IHAheadOf1; auto. rewrite IHAheadOf2; auto. }
Qed. 

(*the initial pool can trivially be rewound*)
Theorem rewindInitPool : forall T H, 
    initialPool T -> exists C, poolRewind C H T. 
Proof.
  intros. destruct T.
  {destruct t; inv H0. exists (S n). constructor. auto. }
  {inv H0. }
Qed. 

(*If T is an initial pool, then it is trivially ahead of itself*)
Theorem AheadOfInitPool : forall H T, initialPool T -> AheadOf H T T. 
Proof.
  intros. destruct T.
  {destruct t; inv H0. constructor. }
  {inv H0. }
Qed. 


(*partial abort and full abort are equivalent*)
Theorem partialEqFull : forall H T C' H' T', 
    initialPool T -> Done T' ->
    exists C, (p_multistep C H T C' H' T' <-> 
          f_multistep C H T C' H' T'). 
Proof.
  intros. copy H0. apply rewindInitPool with(H := H) in H0. 
  invertHyp. exists x. split; intros. 
  {apply partialImpliesFullMulti; auto. }
  {eapply fullImpliesPartialMulti in H3. invertHyp.
   copy H5. apply DoneAheadOf in H5; auto. subst x0. eauto. auto.
   eauto. eapply AheadOfInitPool; auto. }
Qed. 











