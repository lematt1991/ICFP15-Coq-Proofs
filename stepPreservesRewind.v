Require Export stepPreservesUniqueness. 
   
Theorem rewindNewerStamp : forall S C H1 H2 b1 b2 tid e0 L1 L2 t1 t2 HI HV chkpnt,
                             rewind H1 (txThread b1 tid S e0 L1 t1)
                                    H2 (txThread b2 tid S e0 L2 t2) ->
                             C >= S -> @validate tid S C e0 b2 L2 H2 (commit chkpnt HI HV) ->
                             rewind H1 (txThread b1 tid C e0 L1 t1)
                                    H2 (txThread b2 tid C e0 L2 t2). 
Proof.
  intros. genDeps{{C; chkpnt; HI; HV}}. dependent induction H; intros.
  {constructor. }
  {dependent destruction H1.
   {(*r_readChkpnt*)
     invertHyp. econstructor. eapply IHrewind; eauto. 
     eapply r_readChkpnt; eauto. transEq. invertEq. 
     inv H8; constructor; omega. }
   {(*r_readNoChkpnt*)
     invertHyp. econstructor; eauto. 
     eapply r_readNoChkpnt; eauto. transEq. invertEq.
     inv H8; econstructor; eauto. omega. }
   {(*r_readStepInvalid*)
     dependent destruction H6.
     {invertHyp. transEq. invertEq.
      exfalso. eapply validInvalidStamp; eauto. }
     {invertHyp. transEq. invertEq.
      exfalso. eapply validInvalidStamp; eauto. }
   }
   {(*r_writeLocked*) 
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
    poolRewind C H T -> C' >= C -> poolRewind C' H T. 
Proof.
  intros. induction H0.
  {constructor. omega. }
  {econstructor; eauto. omega. omega. }
  {econstructor; eauto. }
Qed. 

Theorem f_rewindNoninterference : forall C H C' H' T T' T2,
    f_step C H T C' H' T' -> poolRewind C H T2 ->
    Disjoint nat (ids T) (ids T2) -> poolRewind C' H' T2.
Proof.
  intros. generalize dependent T2.
  induction H0; intros.
  {(*if someone else aborts, then we can still rewind*)
    inv H0. eapply abortRewindNI; eauto. }
  {inv H0; auto. simpl in *. eapply writeNI; eauto. }
  {simpl in *. eapply IHc_step. auto. constructor.
   intros. intro. inv H2. specialize (H4 x). apply H4.
   solveIn. }
  {simpl in *. eapply IHc_step. auto. constructor.
   intros. intro. inv H2. specialize (H4 x). apply H4.
   solveIn. }
  {eapply poolRewindNewerStamp; eauto. }
  {eapply rewindAlloc; auto. }
  {eapply commitRewindNI; eauto. }
  {eapply poolRewindNewerStamp; eauto. }
  {auto. }
  {eapply poolRewindNewerStamp; eauto. }
Qed. 

Theorem p_rewindNoninterference : forall C H C' H' T T' T2,
    p_step C H T C' H' T' -> poolRewind C H T2 ->
    Disjoint nat (ids T) (ids T2) -> poolRewind C' H' T2.
Proof.  
  intros. generalize dependent T2.
  induction H0; intros; eauto. 
  {inv H0. simpl in *. eapply abortRewindNI; eauto. }
  {inv H0; auto. eapply writeNI; eauto. }
  {simpl in *. eapply IHc_step. auto. constructor.
   intros. intro. inv H2. specialize (H4 x). apply H4.
   solveIn. }
  {simpl in *. eapply IHc_step. auto. constructor.
   intros. intro. inv H2. specialize (H4 x). apply H4.
   solveIn. }
  {eapply poolRewindNewerStamp; eauto. }
  {eapply rewindAlloc; auto. }
  {eapply commitRewindNI; eauto. }
  {eapply poolRewindNewerStamp; eauto. }
  {eapply poolRewindNewerStamp; eauto. }
Qed.

(*f_step preserves rewind*)
Theorem f_stepRewind : forall C H T C' H' T', 
                       f_step C H T C' H' T' -> poolRewind C H T ->
                       poolRewind C' H' T'. 
Proof.  
  intros. induction H0; try solve[econstructor;econstructor; econstructor]. 
  {inv H0. dependent destruction H1. econstructor. constructor.
   auto. auto. }
  {dependent destruction H0;
   match goal with
   |Hyp : poolRewind ?C ?H (Single ?T) |- _ => dependent destruction Hyp
   end; econstructor; eauto; econstructor; eauto; try solve[econstructor; eauto]. 
  }
  {inv H1. copy H0. eapply f_stepDisjoint in H0; eauto.
   econstructor; eauto. eapply f_rewindNoninterference; eauto. }
  {inv H1. copy H0. rewrite DisjointComm in H4. copy H4. eapply f_stepDisjoint in H4; eauto.
   econstructor; eauto. rewrite DisjointComm. auto.
   eapply f_rewindNoninterference; eauto. }
  {(*timestamp extension*)
    dependent destruction H1. econstructor. 
    econstructor. intros. intro. simpl in *. solveIn.
    omega. econstructor; eauto. econstructor; eauto. }
  {inv H1. econstructor. auto. }
  {dependent destruction H1. econstructor; eauto. }
  {dependent destruction H1. econstructor. econstructor.
   auto. auto. }
  {dependent destruction H1. econstructor; eauto. }
  {dependent destruction H1. econstructor.
   eapply rewindNewerStamp; eauto. omega. auto. auto. }
Qed. 

Theorem validateNoWrites : forall tid rv wv e0 L H chkpnt HI HV,
    @validate tid rv wv e0 false L H (commit chkpnt HI HV) ->
    H = HI. 
Proof.
  intros. dependent induction H0; auto.
Qed. 

Theorem commitRewind : forall H  H0 C tid e e' e0 b L L' S HV,
    @validate tid S C e0 b L H (commit (e', L') H0 HV) -> C >= S ->
    rewind H0 (txThread false tid S e0 NilLog e0) H (txThread b tid S e0 L e) ->
    rewind H0 (txThread false tid C e0 NilLog e0) H0 (txThread false tid C e0 L' e'). 
Proof.
  intros H H0 C tid e e' e0 b L L' S HV H1 H2 H3.
  genDeps{{L'; e'; HV; C}}. dependent induction H3; intros. 
  {inv H1. constructor. }
  {dependent destruction H0. 
   {invertHyp. copy H9. eapply validateNoWrites in H9; eauto. subst.
    eapply rewindNewerStamp with (C := C); eauto. apply decomposeEq in H1.
    subst. assumption. }
   {invertHyp. eapply IHrewind; eauto. }
   {dependent destruction H6; invertHyp.
    {transEq. invertEq. exfalso. eapply validInvalidStamp; eauto. }
    {transEq. invertEq. exfalso. eapply validInvalidStamp; eauto. }
   }
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
    @validate tid S C e0 b L H (abort (e', L') H0) -> C >= S ->
    rewind H0 (txThread false tid S e0 NilLog e0) H (txThread b tid S e0 L e) ->
    rewind H0 (txThread false tid C e0 NilLog e0) H0 (txThread false tid C e0 L' e'). 
Proof. 
  intros H H0 C tid e e' e0 b L L' S H1 H2 H3.
  dependent induction H3.
  {dependent destruction H1. inv H0. }
  {dependent destruction H0; eauto.
   {invertHyp. (*r_readChkpnt*)
    (*validChkpnt case is vacuous since it returns a commit *)
    (*invalidChkpnt: this read  is out of date, contradiction...*)
    {transEq. invertEq. exfalso. eapply validInvalidStamp; eauto. } 
    (*readPropAbort: this read is valid, but an earlier one is out of date, use IH*)
    eapply IHrewind; eauto. }
   {invertHyp; eauto. transEq. invertEq. exfalso.
    eapply validInvalidStamp; eauto. } 
   {dependent destruction H6; invertHyp; eauto.     (*r_readStepInvalid*)
    {transEq. invertEq. eapply commitRewind; eauto. }
    {transEq. invertEq. eapply commitRewind; eauto. }
   }
   {eapply abortAcquiredLock in H5; eauto. }
  }
Qed.

Theorem validateRewindHeapEq : forall res b H H'' tid S  L'' e' e0 C,
    @validate tid S C e0 b L'' H res ->
    rewind H'' (txThread false tid S e0 NilLog e0) H (txThread b tid S e0 L'' e') ->
    invalidHeap res = H''.
Proof.
  intros.
  generalize dependent res. dependent induction H1; intros.
  {dependent destruction H0; auto. inv H1. }
  {dependent destruction H0.
   {invertHyp; eauto. 
    {eapply IHrewind in H8; eauto. }
    {eapply IHrewind in H8; eauto. }
   }
   {invertHyp; eauto. 
    {eapply IHrewind in H8; eauto. }
   } 
   {dependent destruction H6; invertHyp; eauto; simpl in *. 
    {eapply IHrewind in H9; eauto. }
    {eapply IHrewind in H9; eauto. }
    {eapply IHrewind in H9; eauto. }
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
    inv H0. dependent destruction H1. copy H3.
    eapply validateRewindHeapEq in H3; eauto. simpl in *.
    subst. eapply abortRewind in H0; eauto. 
    econstructor; eauto. omega. }
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
     eapply r_atomicIdemStep; eauto. }
   {(*t_betaStep*)
     eapply rewindSingleInTX; eauto. econstructor. eauto.
     eapply r_betaStep. auto. }
  }
  {inv H1. copy H0. eapply p_stepDisjoint in H0; eauto.
   econstructor; eauto. eapply p_rewindNoninterference; eauto. }
  {inv H1. copy H0. rewrite DisjointComm in H4. copy H4. eapply p_stepDisjoint in H4; eauto.
   econstructor; eauto. rewrite DisjointComm. auto.
   eapply p_rewindNoninterference; eauto. }
  {(*timestamp extension*)
    dependent destruction H1. econstructor. 
    econstructor. intros. intro. simpl in *. solveIn. omega.
    econstructor; eauto. econstructor; eauto. }
  {inv H1. econstructor. auto. }
  {dependent destruction H1. econstructor; eauto. }
  {dependent destruction H1. econstructor. econstructor.
   auto. auto. }
  {dependent destruction H1. econstructor; eauto. }
  {dependent destruction H1. econstructor.
   eapply rewindNewerStamp; eauto. omega. auto. auto. }
Qed. 
