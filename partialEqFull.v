Require Import fullImpliesPartial. 
Require Import partialImpliesFull. 

(*specifies that T is a source program*)
Fixpoint initialPool T :=
  match T with
      |Single(None,nil,e) => True
      |_ => False
  end. 

(*specifies that T has reached a terminal state*)
Fixpoint Done T :=
  match T with
      |Single(None,nil,v) => value v
      |Par T1 T2 => Done T1 /\ Done T2
      |_ => False
  end. 

(*if T is done and T' is ahead of T, then T = T'*)
Theorem DoneAheadOf : forall H T T', 
                   Done T -> poolAheadOf H T T' ->
                   T = T'. 
Proof.
  intros. induction H1. 
  {inv H1. auto. inv H0. }
  {inv H0. rewrite IHpoolAheadOf1; auto. rewrite IHpoolAheadOf2; auto. }
Qed. 

(*the initial pool can trivially be rewound*)
Theorem rewindInitPool : forall T C H, 
                           initialPool T -> poolRewind C H T. 
Proof.
  intros. destruct T. destruct t. destruct p. destruct o. 
  inv H0. destruct l. constructor. inv H0. inv H0. 
Qed. 

(*If T is an initial pool, then it is trivially ahead of itself*)
Theorem AheadOfInitPool : forall H T, initialPool T -> poolAheadOf H T T. 
Proof.
  intros. destruct T. destruct t. destruct p. destruct o. 
  inv H0. destruct l. repeat constructor. inv H0. inv H0. 
Qed. 

(*partial abort and full abort are equivalent*)
Theorem partialEqFull : forall C H T C' H' T', 
                          initialPool T -> Done T' ->
                          (p_multistep C H T C' H' T' <-> 
                           f_multistep C H T C' H' T'). 
Proof.
  intros. split; intros. 
  {apply partialImpliesFullMulti. auto. apply rewindInitPool. auto. }
  {eapply fullImpliesPartialMulti in H2. invertHyp.
   copy H4. apply DoneAheadOf in H4; auto. subst x. eauto. apply AheadOfInitPool. 
   auto. apply rewindInitPool. auto. }
Qed. 











