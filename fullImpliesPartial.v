Require Export stepPreservesRewind.  
  
(*
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
 *)

Inductive AheadOf (H : heap) : pool -> pool -> Prop :=
| aheadOfNoTX : forall tid e, AheadOf H (Single(noTXThread tid e)) (Single(noTXThread tid e))
| aheadOfTX : forall tid rv b b' e0 L L' e e' H',
    replay H (txThread b tid rv e0 L e) H' (txThread b' tid rv e0 L' e') ->
    AheadOf H (Single(txThread b tid rv e0 L e)) (Single(txThread b' tid rv e0 L' e'))
| replayPar : forall T1 T2 T1' T2',
    AheadOf H T1 T1' -> AheadOf H T2 T2' ->
    AheadOf H (Par T1 T2) (Par T1' T2'). 

Ltac sameStep :=
  match goal with
  |H : decompose ?t ?E ?e, H' : decompose ?t ?E' ?e' |- _ =>
   eapply decomposeDeterministic in H; eauto; invertHyp; repeat invertEq
  end. 

(*partial abort can simulate full abort*)
Theorem fullImpliesPartial : forall C H T C' H' T' PT, 
                               f_step C H T C' H' T' -> AheadOf H T PT ->
                               poolRewind C H PT -> 
                               exists PT', p_multistep C H PT C' H' PT' /\
                                           AheadOf H' T' PT'.
Proof.
  intros. generalize dependent PT. induction H0; intros. 
  {(*lifted step (full abort)*)
    inv H0. dependent destruction H1. admit. }
  {(*transactional step*)
    dependent destruction H0.
    {(*checkpoint read*)
      dependent destruction H3. dependent destruction H4.
      dependent destruction H3.
      {econstructor. split. eapply c_multi_step.
       eapply c_transStep. econstructor; eauto. constructor.
       econstructor. constructor. }
      {dependent destruction H4; sameStep. 
       {transEq. invertEq. econstructor. split. constructor.
        econstructor. eauto. }
       {transEq. invertEq. exfalso. eapply validInvalidStamp; eauto. }
      }
    }
    {(*non-checkpoint read*)
      dependent destruction H3. dependent destruction H4.
      dependent destruction H3.
      {econstructor. split. eapply c_multi_step.
       eapply c_transStep. econstructor; eauto. constructor.
       econstructor. constructor. }
      {dependent destruction H4; sameStep. 
       {transEq. invertEq. econstructor. split. constructor.
        econstructor. eauto. }
       {transEq. invertEq. exfalso. eapply validInvalidStamp; eauto. }
      }
    }
    {(*write*)
      dependent destruction H3. dependent destruction H4.
      dependent destruction H3.
      {econstructor. split. eapply c_multi_step.
       eapply c_transStep. econstructor; eauto. constructor.
       econstructor. constructor. }
      {dependent destruction H4; sameStep. econstructor. admit. }
    }
    {dependent destruction H1. dependent destruction H2.
     dependent destruction H1.
     {econstructor. split. eapply c_multi_step.
      eapply c_transStep. eapply t_atomicIdemStep; eauto.
      constructor. econstructor. constructor. }
     {dependent destruction H1; sameStep. econstructor.
      split. constructor. econstructor. eauto. }
    }
    {dependent destruction H1. dependent destruction H2.
     dependent destruction H1.
     {econstructor. split. eapply c_multi_step.
      eapply c_transStep. eapply t_betaStep; eauto.
      constructor. econstructor. constructor. }
     {dependent destruction H1; sameStep. econstructor.
      split. constructor. econstructor. eauto. }
    }
  }
  {inv H1. dependent destruction H2. eapply IHc_step in H5; eauto.
   invertHyp. econstructor. split. eapply multi_L. eauto.
   econstructor; eauto. admit. (*we need another noninterference lemma for replay*)
  }
  {inv H1. dependent destruction H2. eapply IHc_step in H7; eauto.
   invertHyp. econstructor. split. eapply multi_R. eauto.
   econstructor; eauto. admit. (*we need another noninterference lemma for replay*)
  }
  {inv H1. inv H2. econstructor. split. eapply c_multi_step.
   eapply c_forkStep; eauto. constructor. repeat constructor. }
  {inv H2. inv H3. econstructor. split. eapply c_multi_step.
   eapply c_allocStep; eauto. constructor. constructor. }
  {dependent destruction H2. dependent destruction H3.
   dependent destruction H2.
   {econstructor. split. eapply c_multi_step. eapply c_commitStep; eauto.
    constructor. constructor. }
   {dependent destruction H2; sameStep. }
  }
  {inv H1. inv H2. econstructor. split. eapply c_multi_step.
   eapply c_atomicStep; eauto. constructor. econstructor. 
   econstructor. }
  {inv H1. inv H2. econstructor. split. eapply c_multi_step.
   eapply c_betaStep; eauto. constructor. constructor. }
  {admit. }
Admitted. 

(*generalize step preserves rewind to thread pools*)
Theorem multistepPreservesRewind : forall C H T C' H' T',
                                poolRewind C H T -> p_multistep C H T C' H' T' ->
                                poolRewind C' H' T'. 
Proof.
  intros. induction H1. auto. apply IHmultistep.
  eapply p_stepRewind; eauto. 
Qed. 

(*generalize full implies partial to thread pools*)
Theorem fullImpliesPartialMulti : forall C H T C' H' T' PT, 
                               f_multistep C H T C' H' T' -> AheadOf H T PT ->
                               poolRewind C H PT ->
                               exists PT', p_multistep C H PT C' H' PT' /\
                                           AheadOf H' T' PT'.
Proof.
  intros. generalize dependent PT. induction H0; intros. 
  {exists PT. split. constructor. auto. }
  {copy H0. eapply fullImpliesPartial in H0; eauto. invertHyp. 
   copy H0. apply multistepPreservesRewind in H5; auto. 
   eapply IHmultistep in H6; eauto. invertHyp. exists x0. split. 
   eapply multi_trans; eauto. auto. }
Qed. 







