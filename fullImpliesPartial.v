Require Export partialImpliesFull.  


(*
 * If we can replay from one state to another and the first state is
 * invalid, then the second one must be too
 *)
Theorem replayInvalid : forall b1 b2 H H' rv wv tid e0 L e L' e' chkpnt HI, 
                          replay H (txThread b1 tid rv e0 L e) H' (txThread b2 tid rv e0 L' e') ->
                          validate tid rv wv e0 L H (abort chkpnt HI) ->
                          validate tid rv wv e0 L' H (abort chkpnt HI).
Proof.
  intros. genDeps{{chkpnt; HI}}. dependent induction H0; intros; auto.
  dependent destruction H0; eauto. 
  {eapply IHreplay; eauto. eapply readPropAbort; eauto.
   constructor. }
  {eapply IHreplay; eauto. eapply readPropAbort; eauto.
   constructor. }
  {eapply IHreplay; eauto. eapply readPropAbort; eauto.
   dependent destruction H4; constructor. }
Admitted. 

(*

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
| aheadOfTXRO : forall tid rv e0 L L' e e',
    replay H (txThread false tid rv e0 L e) H (txThread false tid rv e0 L' e') ->
    AheadOf H (Single(txThread false tid rv e0 L e)) (Single(txThread false tid rv e0 L' e'))
| aheadOfTXRW : forall tid rv b e0 L e,
    AheadOf H (Single(txThread b tid rv e0 L e)) (Single(txThread b tid rv e0 L e))
| replayPar : forall T1 T2 T1' T2',
    AheadOf H T1 T1' -> AheadOf H T2 T2' ->
    AheadOf H (Par T1 T2) (Par T1' T2'). 

Ltac sameStep :=
  match goal with
  |H : decompose ?t ?E ?e, H' : decompose ?t ?E' ?e' |- _ =>
   eapply decomposeDeterministic in H; eauto; invertHyp; repeat invertEq
  end. 

Theorem logMonotonic : forall H H' tid rv e0 L e L' e',
    replay H (txThread true tid rv e0 L e) H' (txThread false tid rv e0 L' e') -> False.
Proof.
  intros. dependent induction H0.
  {dependent destruction H0; eauto. }
Qed. 


Theorem AheadOfNI : forall C C' H H' T1 T1' T2 T2',
    f_step C H T1 C' H' T1' -> AheadOf H T2 T2' ->
    AheadOf H' T2 T2'.
Proof.
  intros. genDeps{{C; T1; C'; T1'}}. 
  induction H1; intros.
  {constructor. }
  {dependent destruction H1.
   {
Admitted. 
    
                        
(*partial abort can simulate full abort*)
Theorem fullImpliesPartial : forall C H T C' H' T' PT, 
                               f_step C H T C' H' T' -> AheadOf H T PT ->
                               poolRewind C H PT -> poolRewind C H T ->
                               exists PT', p_multistep C H PT C' H' PT' /\
                                           AheadOf H' T' PT'.
Proof.
  intros. generalize dependent PT. induction H0; intros. 
  {(*lifted step (full abort)*)
    inv H0. dependent destruction H3. dependent destruction H4. 
    {copy H0. eapply validateRewindHeapEq in H6; eauto. simpl in *.
     subst. eapply replayInvalid in H5; eauto.    
     assert(rewind H'0 (txThread false tid S e0 NilLog e0) H (txThread false tid S e0 L'0 e'0)).
     rewrite <- rewindIFFReplay in H4. eapply rewindTrans; eassumption.
     eapply abortRewind in H6; eauto; try omega. copy H5. 
     eapply validateValidate in H5. invertHyp. econstructor. split.
     eapply c_multi_step. eapply c_liftedStep. econstructor. eauto. 
     constructor. econstructor. rewrite <- rewindIFFReplay. assumption. }
    {copy H0. eapply validateRewindHeapEq in H4; eauto. simpl in *. subst. 
     econstructor. split. eapply c_multi_step. eapply c_liftedStep.
     econstructor; eauto. constructor. econstructor.
     eapply abortRewind in H5; eauto; try omega. rewrite <- rewindIFFReplay. 
     assumption. }
  }
  {(*transactional step*)
    dependent destruction H0.
    {(*checkpoint read*)
      dependent destruction H3. dependent destruction H6.
      {dependent destruction H6.
       {econstructor. split. eapply c_multi_step.
        eapply c_transStep. econstructor; eauto. constructor.
        econstructor. constructor. }
       {dependent destruction H7; sameStep. 
        {transEq. invertEq. econstructor. split. constructor.
         econstructor. eauto. }
        {transEq. invertEq. exfalso. eapply validInvalidStamp; eauto. }
       }
      }
      {econstructor. split. eapply c_multi_step.
        eapply c_transStep. econstructor; eauto. constructor.
        econstructor. constructor. }
    }
    {(*non-checkpoint read*)
      dependent destruction H3. dependent destruction H6.
      {econstructor. split. eapply c_multi_step.
       eapply c_transStep. econstructor; eauto. constructor.
       econstructor. }
    }
    {(*write*)
      dependent destruction H3. dependent destruction H6.
      {dependent destruction H6.
       {econstructor. split. eapply c_multi_step.
        eapply c_transStep. eapply t_writeLocked; eauto.
        constructor. econstructor. }
       {dependent destruction H7; sameStep. exfalso.
        eapply logMonotonic; eauto. }
      }
      {econstructor. split. eapply c_multi_step.
        eapply c_transStep. eapply t_writeLocked; eauto.
        constructor. econstructor. }
    }
    {dependent destruction H1. dependent destruction H2.
     dependent destruction H1.
     {econstructor. split. eapply c_multi_step.
      eapply c_transStep. eapply t_atomicIdemStep; eauto.
      constructor. econstructor. constructor. }
     {dependent destruction H1; sameStep. econstructor.
      split. constructor. econstructor. eauto. }
     {econstructor. split. eapply c_multi_step.
      eapply c_transStep. eapply t_atomicIdemStep; eauto.
      constructor. econstructor. }
    }
    {dependent destruction H1. dependent destruction H2.
     dependent destruction H1.
     {econstructor. split. eapply c_multi_step.
      eapply c_transStep. eapply t_betaStep; eauto.
      constructor. econstructor. constructor. }
     {dependent destruction H1; sameStep. econstructor.
      split. constructor. econstructor. eauto. }
     {econstructor. split. eapply c_multi_step.
      eapply c_transStep. eapply t_betaStep; eauto.
      constructor. econstructor. }
    }
  }
  {inv H1. dependent destruction H2. inv H3. eapply IHc_step in H6; eauto.
   invertHyp. econstructor. split. eapply multi_L. eauto.
   econstructor; eauto.

   eapply AheadOfNI; eauto. }
  {inv H1. inv H2. inv H3. eapply IHc_step in H8; eauto.
   invertHyp. econstructor. split. eapply multi_R. eauto.
   econstructor; eauto. eapply AheadOfNI; eauto. }
  {inv H1. inv H2. econstructor. split. eapply c_multi_step.
   eapply c_forkStep; eauto. constructor. repeat constructor. }
  {inv H2. inv H3. econstructor. split. eapply c_multi_step.
   eapply c_allocStep; eauto. constructor. constructor. }
  {dependent destruction H2. dependent destruction H3.
   dependent destruction H6. dependent destruction H5.
   {econstructor. split. eapply c_multi_step. eapply c_commitStep; eauto.
    constructor. constructor. }
   {dependent destruction H5; sameStep. }
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







