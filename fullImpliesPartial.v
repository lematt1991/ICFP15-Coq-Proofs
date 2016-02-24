Require Export stepPreservesRewind.  
  
(*AheadOf H t1 t2: t2 is in t1's future with respect to heap H*)
Inductive AheadOf H : thread -> thread -> Prop :=
|noTXAheadOf : forall e, AheadOf H (None, nil, e) (None, nil, e)
|inTXAheadOf : forall S e0 L L' e e', 
                 replay H (Some(S,e0),L,e) (Some(S,e0),L',e') ->
                 AheadOf H (Some(S,e0),L,e) (Some(S,e0),L',e').

(*Generalizes the previous relation to thread pools*)
Inductive poolAheadOf H : pool -> pool -> Prop := 
|SingleAheadOf : forall t t', AheadOf H t t' -> poolAheadOf H (Single t) (Single t')
|ParAheadOf : forall T1 T2 T1' T2', 
           poolAheadOf H T1 T1' -> poolAheadOf H T2 T2' -> 
           poolAheadOf H (Par T1 T2) (Par T1' T2'). 

(*
 * If we can replay from one state to another and the first state is
 * invalid, then the second one must be too
 *)
Theorem replayInvalid : forall H S e0 L e L' e' S' eA LA, 
                          replay H (Some(S,e0),L,e) (Some(S,e0),L',e') ->
                          validate S L H S' (abort eA LA) ->
                          exists eA' LA', validate S L' H S' (abort eA' LA').
Proof.
  intros. dependent induction H0; eauto. 
  {inv H0; eauto. 
   {assert(validate S (readItem l E v::L) H S' (abort eA LA)).
    eapply validateAbortPropogate; eauto. eapply IHreplay in H0; eauto. }
   {assert(validate S (readItem l E v::L) H S' (abort eA LA)).
    eapply validateAbortPropogate; eauto. eapply IHreplay in H0; eauto. }
   {assert(validate S (writeItem l v::L) H S' (abort eA LA)).
    eapply validateAbortPropogate; eauto. eapply IHreplay in H0; eauto. }
  }
Qed. 

(*
 * If we can rewind/replay from one state to another and the final state is invalid,
 * then it must also be possible to rewind/replay to the portion that is still
 * valid as determined by validate 
 *)         
Theorem rewindValidPortion : forall S L H S' e' L' e0 e, 
                               rewind H (Some(S,e0),nil,e0) (Some(S,e0),L,e) ->
                               validate S L H S' (abort e' L') ->
                               rewind H (Some(S,e0),nil,e0) (Some(S,e0),L',e').
Proof.
  intros. dependent induction H0. 
  {inv H1. }
  {inv H1; eauto. 
   {inv H2. 
    {eapply IHrewind; eauto. }
    {lookupSame. omega. }
   }
   {inv H2. 
    {eapply IHrewind; eauto. }
    {eapply decomposeEq in H10. subst. auto. }
   }
   {inv H2. eauto. }
  }
Qed. 

(**
 * AheadOf holds under an extended heap if everything in the extension has a 
 * timestamp greater tan the transactions read version
 *)
Theorem AheadOfExtension : forall H H' S t e0 L e C, 
                      AheadOf H t (Some(S,e0),L,e) -> S < C ->
                      Forall (fun x : location * term * stamp => getStamp x = C) H' ->
                      AheadOf (H'++H) t (Some(S,e0),L,e).
Proof.
  intros. inv H0. 
  econstructor. eapply replayHeapExtension; eauto.  
Qed. 

(*generalize to thread pools*)
Theorem poolAheadOfExtension : forall H H' T1 T2 C,
                    poolAheadOf H T1 T2 -> 
                    Forall (fun x : location * term * stamp => getStamp x = C) H' ->
                    poolRewind C H T2 ->
                    poolAheadOf (H'++H) T1 T2.
Proof.
  intros. induction H0. 
  {constructor. inv H2. 
   {inv H0. constructor. }
   {eapply AheadOfExtension; eauto. }
  }
  {inv H2. constructor; auto. } 
Qed. 

(*
Ltac invertEq :=
  match goal with
      |H:?x = ?y |- _ => solve[inv H]
  end. 
*)

(*if the beginning of a replay aborts, then so does the endpoint*)
Theorem abortReplay : forall S L H C L' e' e'' L'' e e0, 
                        replay H (Some(S,e0),L,e) (Some(S,e0),L',e') ->
                        validate S L H C (abort e'' L'') -> 
                        validate S L' H C (abort e'' L''). 
Proof.
  intros. dependent induction H0; auto.
  inv H0; eapply IHreplay; eauto; eapply validateAbortPropogate; eauto. 
Qed. 

(*partial abort can simulate full abort*)
Theorem fullImpliesPartial : forall C H T C' H' T' PT, 
                               f_step C H T C' H' T' -> poolAheadOf H T PT ->
                               poolRewind C H PT -> 
                               exists PT', p_multistep C H PT C' H' PT' /\
                                           poolAheadOf H' T' PT'.
Proof.
  intros. generalize dependent PT. induction H0; intros. 
  {inv H1. inv H4. 
   {inv H0; exfalso; apply H7; auto. }
   {inv H1. 
    {econstructor. split. eapply p_multi_step. eapply p_transStep. 
     eauto. constructor. constructor. inv H0; repeat constructor. }
    {econstructor. split. constructor. constructor. Hint Constructors AheadOf.
     inv H0; inv H3; decompSame; invertEq; repeat lookupSame; auto. omega. }
   }
  } 
  {eapply f_stampHeapMonotonic in H0. invertHyp. inv H1. eapply IHf_step in H6. 
   invertHyp. econstructor. split. eapply p_multi_L. eauto. constructor. auto.
   inv H2. eapply poolAheadOfExtension; eauto. inv H2. auto. }
  {eapply f_stampHeapMonotonic in H0. invertHyp. inv H1. eapply IHf_step in H8. 
   invertHyp. econstructor. split. eapply p_multi_R. eauto. constructor. inv H2. 
   eapply poolAheadOfExtension; eauto. auto. auto. inv H2. auto. 
  }
  {inv H1. inv H4. econstructor. split. eapply p_multi_step.
   eapply p_forkStep; eauto. constructor. repeat constructor. }
  {inv H5. inv H8. inv H12. 
   {econstructor. split. eapply p_multi_step. eapply p_eagerAbort; eauto.
    constructor. repeat constructor. inv H6. rewrite <- rewindIFFReplay.
    assert(rewind H (Some(S,e0),nil,e0) (Some(S,e0),(readItem l E v :: L'0), fill E v)). 
    econstructor. eauto. eapply r_readStepInvalid; eauto. omega. copy H2.
    eapply validateValidate in H2; eauto. invertHyp. 
    eapply rewindDiffStamp; eauto. eapply rewindValidPortion; eauto. }
   {inv H5; decompSame; try invertEq. 
    {invertEq. repeat lookupSame. omega. }
    {invertEq. repeat lookupSame.
     assert(validate S (readItem l E v0::L) H C (abort e' L')). inv H2. 
     eapply validateAbortPropogate; eauto. eapply validateAbortRead; eauto. 
     econstructor. split. eapply p_multi_step. eapply p_abortStep. 
     eapply abortReplay; eauto. rewrite plus_comm. constructor. repeat constructor. 
     inv H6. rewrite <- rewindIFFReplay. copy H7. 
     eapply validateValidate in H3. invertHyp. eapply rewindDiffStamp; eauto.
     eapply rewindValidPortion. eauto. eapply abortReplay in H7. eauto. 
     inv H2. eapply validateAbortPropogate; eauto. eapply validateAbortRead; eauto. }
    {invertEq. repeat lookupSame. }
   }
  }
  {inv H1. inv H4. eapply replayInvalid in H8; eauto. invertHyp. 
   econstructor. split. econstructor. eapply p_abortStep; eauto. constructor. 
   constructor. constructor. inv H2. eapply rewindValidPortion in H5; eauto.
   eapply validateValidate in H3. invertHyp. eapply rewindDiffStamp in H5; eauto. 
   rewrite <- rewindIFFReplay. auto. }
  {inv H2. inv H5. econstructor. split. econstructor.
   eapply p_allocStep; eauto. constructor. repeat constructor. }
  {inv H2. inv H5. inv H9. 
   {econstructor. split. econstructor. eapply p_commitStep; eauto. 
    constructor. repeat constructor. }
   {inv H2; try solve[decompSame; solveByInv]. }
  }
  {inv H1. inv H4. econstructor. split. econstructor. 
   eapply p_atomicStep; eauto. constructor. constructor. 
   eapply inTXAheadOf. constructor. }
  {inv H1. inv H4. econstructor. split. eapply p_multi_step. 
   eapply p_betaStep; eauto. constructor. repeat constructor. }
Qed. 

(*generalize step preserves rewind to thread pools*)
Theorem multistepPreservesRewind : forall C H T C' H' T',
                                poolRewind C H T -> p_multistep C H T C' H' T' ->
                                poolRewind C' H' T'. 
Proof.
  intros. induction H1. auto. apply IHp_multistep.
  eapply p_stepRewind; eauto. 
Qed. 

(*generalize full implies partial to thread pools*)
Theorem fullImpliesPartialMulti : forall C H T C' H' T' PT, 
                               f_multistep C H T C' H' T' -> poolAheadOf H T PT ->
                               poolRewind C H PT ->
                               exists PT', p_multistep C H PT C' H' PT' /\
                                           poolAheadOf H' T' PT'.
Proof.
  intros. generalize dependent PT. induction H0; intros. 
  {exists PT. split. constructor. auto. }
  {copy H0. eapply fullImpliesPartial in H0; eauto. invertHyp. 
   copy H0. apply multistepPreservesRewind in H5; auto. 
   eapply IHf_multistep in H6; eauto. invertHyp. exists x0. split. 
   eapply p_multi_trans; eauto. auto. }
Qed. 







