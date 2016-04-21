Require Export noninterference. 

Theorem validInvalidStamp : forall tid S lock,
                              validStamp tid S lock ->
                              invalidStamp tid S lock -> False. 
Proof.
  intros tid S lock H H0.
  inv H; inv H0; auto. omega.
Qed.
   
Theorem rewindNewerStamp : forall S C H1 H2 b1 b2 tid e0 L1 L2 t1 t2 HI HV chkpnt,
                             rewind H1 (txThread b1 tid S e0 L1 t1)
                                    H2 (txThread b2 tid S e0 L2 t2) ->
                             S < C -> @validate tid S C e0 b2 L2 H2 (commit chkpnt HI HV) ->
                             rewind H1 (txThread b1 tid C e0 L1 t1)
                                    H2 (txThread b2 tid C e0 L2 t2). 
Proof.
  intros. genDeps{{C; chkpnt; HI; HV}}. dependent induction H; intros.
  {constructor. }
  {dependent destruction H1.
   {(*r_readChkpnt*)
     inv H6. econstructor. eapply IHrewind; eauto. 
     eapply r_readChkpnt; eauto. rewrite H14 in H3. inv H3.
     inv H17; econstructor. omega. }
   {(*r_readNoChkpnt*)
     dependent destruction H6. econstructor; eauto. 
     eapply r_readNoChkpnt; eauto. transEq. invertEq.
     inv H7; econstructor; eauto. omega. }
   {(*r_readStepInvalid*)
     dependent destruction H7. transEq. invertEq. exfalso.
     eapply validInvalidStamp; eauto. }
   { (*r_writeLocked*) 
     copy H4. eapply validateAcquiredLock in H4; eauto. invertHyp.
     econstructor. eapply IHrewind; eauto. 
     eapply r_writeLocked; eauto. 
     dependent destruction H7; econstructor; eauto. omega. }
   {(*r_atomicIdemStep*)
     econstructor; eauto. eapply r_atomicIdemStep; auto. }
   {(*r_betaStep*)
     econstructor; eauto. eapply r_betaStep; eauto. }
  }
Qed. 

Theorem poolRewindNewerStamp : forall C C' H T,
    poolRewind C H T -> C' > C -> poolRewind C' H T. 
Proof.
  intros. induction H0.
  {constructor. }
  {econstructor; eauto. omega. }
  {econstructor; eauto. }
Qed. 
    
Theorem f_rewindNoninterference : forall C H C' H' T T' T2,
    f_step C H T C' H' T' -> poolRewind C H T2 ->
    poolRewind C' H' T2.
Proof.
  intros C H C' H' T T' T2 H0 H1. generalize dependent T2.
  induction H0; intros; eauto. 
  {(*if someone else aborts, then we can still rewind*)
    inv H0. eapply abortRewindNI; eauto. }
  {inv H0; auto.  
   {admit. }
  }
  {eapply rewindAlloc; auto. }
  {eapply commitRewindNI; eauto. }
  {eapply poolRewindNewerStamp; eauto. }
  {eapply poolRewindNewerStamp; eauto. }
Admitted. 

Theorem p_rewindNoninterference : forall C H C' H' T T' T2,
    p_step C H T C' H' T' -> poolRewind C H T2 ->
    poolRewind C' H' T2.
Proof.
  intros C H C' H' T T' T2 H0 H1. generalize dependent T2.
  induction H0; intros; eauto. 
  {inv H0. eapply abortRewindNI; eauto. }
  {inv H0; auto.  
   {admit. }
  }
  {eapply rewindAlloc; auto. }
  {eapply commitRewindNI; eauto. }
  {eapply poolRewindNewerStamp; eauto. }
  {eapply poolRewindNewerStamp; eauto. }
Admitted.     

(*f_step preserves rewind*)
Theorem f_stepRewind : forall C H T C' H' T', 
                       f_step C H T C' H' T' -> poolRewind C H T ->
                       poolRewind C' H' T'. 
Proof.  
  intros. induction H0; try solve[econstructor;econstructor; econstructor]. 
  {inv H0. econstructor; econstructor. }
  {inv H1. inv H0. dependent destruction H0.
   {(*t_readStep*)
     eapply rewindSingleInTX; eauto. econstructor. eauto.
     eapply r_readChkpnt; eauto. }
   {(*t_readStep*)
     eapply rewindSingleInTX; eauto. econstructor. eauto.
     eapply r_readNoChkpnt; eauto. }
   {(*t_writeLocked*)
     eapply rewindSingleInTX; eauto. econstructor. eauto.
     eapply r_writeLocked; eauto. }
   {(*t_atomicIdemStep*)
     eapply rewindSingleInTX; eauto. econstructor. eauto.
     econstructor. auto. }
   {(*t_betaStep*)
     eapply rewindSingleInTX; eauto. econstructor. eauto.
     eapply r_betaStep. auto. }
  }
  {inv H1. constructor. auto. eapply f_rewindNoninterference; eauto. }
  {inv H1. constructor; auto. eapply f_rewindNoninterference; eauto. }
  {(*timestamp extension*)
    dependent destruction H1. eapply rewindSingleInTX; eauto.
    eapply rewindNewerStamp; eauto. }
Qed. 

Theorem validateNoWrites : forall tid rv wv e0 L H chkpnt HI HV,
    @validate tid rv wv e0 false L H (commit chkpnt HI HV) ->
    H = HI. 
Proof.
  intros. dependent induction H0; auto.
Qed. 

Theorem commitRewind : forall H  H0 C tid e e' e0 b L L' S HV,
    @validate tid S C e0 b L H (commit (e', L') H0 HV) -> C > S ->
    rewind H0 (txThread false tid S e0 NilLog e0) H (txThread b tid S e0 L e) ->
    rewind H0 (txThread false tid C e0 NilLog e0) H0 (txThread false tid C e0 L' e'). 
Proof.
  intros H H0 C tid e e' e0 b L L' S HV H1 H2 H3.
  genDeps{{L'; e'; HV; C}}. dependent induction H3; intros. 
  {inv H1. constructor. }
  {dependent destruction H0. 
   {dependent destruction H6. 
    copy H8. eapply validateNoWrites in H8; eauto. subst.
    eapply rewindNewerStamp with (C := C); eauto. apply decomposeEq in H1.
    subst. assumption. }
   {dependent destruction H6. eapply IHrewind; eauto. }
   {dependent destruction H7. transEq. invertEq. exfalso.
    eapply validInvalidStamp; eauto. }
   {(*validWrite*)
     eapply validateAcquiredLock in H2; eauto. invertHyp. 
     eapply IHrewind; eauto. }
   {eauto. }
   {eauto. }
  }
Qed.

(** 
 * abortRewind
 * If the log at the end of a rewind derivation is invalid, then we can rewind
 * from the log returned from validate.
 * Maybe this would be easier if we didn't distinguish between H0 and H'?  
 * they should be the same.
 **)
Theorem abortRewind : forall H H0 C tid e e' e0 b L L' S,
    @validate tid S C e0 b L H (abort (e', L') H0) -> C > S ->
    rewind H0 (txThread false tid S e0 NilLog e0) H (txThread b tid S e0 L e) ->
    rewind H0 (txThread false tid C e0 NilLog e0) H0 (txThread false tid C e0 L' e'). 
Proof. 
  intros H H0 C tid e e' e0 b L L' S H1 H2 H3.
  dependent induction H3.
  {dependent destruction H1. inv H0. }
  {dependent destruction H0; eauto.
   {dependent destruction H5.  (*r_readChkpnt*)
    (*validChkpnt case is vacuous since it returns a commit *)
    
    (*invalidChkpnt: this read  is out of date, contradiction...*)
    {transEq. invertEq. exfalso. eapply validInvalidStamp; eauto. } 
    (*readPropAbort: this read is valid, but an earlier one is out of date, use IH*)
    {dependent destruction H6. eapply IHrewind; eauto. }
   } 
   {dependent destruction H5.  (*r_readNoChkpnt*)
    (*validRead case is vacuous since it returns a commit*)

    (*invalidRead: this read is out of date, contradiction...*)
    {transEq. invertEq. exfalso. eapply validInvalidStamp; eauto. }
    (*readPropAbort: this read is valid, but an earlier one is out of date, use IH*)
    {dependent destruction H6. eapply IHrewind; eauto. }
   }
   {dependent destruction H6.   (*r_readStepInvalid*)
    {(*invalidRead: this read is invalid, but we don't have a checkpoint*)
      transEq. invertEq. eapply commitRewind; eauto. }
    {dependent destruction H7. eauto. }
   }
   {eapply abortAcquiredLock in H5; eauto. }
  }
Qed.

Theorem validateRewindHeapEq : forall res b H H'' tid S  L'' e' e0 C,
    @validate tid S C e0 b L'' H res ->
    rewind H'' (txThread false tid S e0 NilLog e0) H (txThread b tid S e0 L'' e') ->
    invalidHeap res = H''.
Proof.
  intros res b H H' tid S L'' e' e0 C H0 H1.
  generalize dependent res. dependent induction H1; intros.
  {dependent destruction H0; auto. inv H1. }
  {dependent destruction H0.
   {dependent destruction H5.
    {eapply IHrewind in H7; eauto. }
    {eapply IHrewind in H7; eauto. }
    {dependent destruction H6. eapply IHrewind in H5; eauto. }
   }
   {dependent destruction H5.
    {eapply IHrewind in H7; eauto. }
    {eapply IHrewind in H7; eauto. }
    {dependent destruction H6. eapply IHrewind in H5; eauto. }
   }
   {dependent destruction H6.
    {transEq. invertEq. exfalso. eapply validInvalidStamp; eauto. }
    {transEq. invertEq. eapply IHrewind in H8; eauto. }
    {dependent destruction H7. eapply IHrewind in H6; eauto. }
   }
   {destruct res.
    {eapply validateAcquiredLock in H4; eauto. invertHyp.
     eapply IHrewind in H6; eauto. }
    {eapply abortAcquiredLock in H5; eauto. }
   }
   {eauto. }
   {eauto. }
  }
Qed. 

(*p_step preserves rewind*)
Theorem p_stepRewind : forall C H T C' H' T', 
                       p_step C H T C' H' T' -> poolRewind C H T ->
                       poolRewind C' H' T'. 
Proof. 
  intros. induction H0; try solve[econstructor;econstructor; econstructor]. 
  {(*p_abortStep*)
    inv H0. dependent destruction H1. econstructor; eauto.
    eapply abortRewind; eauto. eapply validateRewindHeapEq in H3; eauto.
    subst. eauto. }
  {inv H1. inv H0. dependent destruction H0.
   {(*t_readStep*)
     eapply rewindSingleInTX; eauto. econstructor. eauto.
     eapply r_readChkpnt; eauto. }
   {(*t_readStep*)
     eapply rewindSingleInTX; eauto. econstructor. eauto.
     eapply r_readNoChkpnt; eauto. }
   {(*t_writeLocked*)
     eapply rewindSingleInTX; eauto. econstructor. eauto.
     eapply r_writeLocked. eauto. eauto. assumption. }
   {(*t_atomicIdemStep*)
     eapply rewindSingleInTX; eauto. econstructor. eauto.
     econstructor. auto. }
   {(*t_betaStep*)
     eapply rewindSingleInTX; eauto. econstructor. eauto.
     eapply r_betaStep. auto. }
  }
  {inv H1. constructor. auto. eapply p_rewindNoninterference; eauto. }
  {inv H1. constructor. eapply p_rewindNoninterference; eauto. auto. }
  {(*timestamp extension*)
    dependent destruction H1. eapply rewindSingleInTX; eauto.
    eapply rewindNewerStamp; eauto. }
Qed. 
