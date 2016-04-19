Require Export semantics. 
   
(*retrieve the stamp number from a heap location*)
Definition getStamp (x : location * term * lock) :=
  match x with
      |(_,_,s) => s
  end.   
 
Theorem validInvalidStamp : forall tid S lock,
                              validStamp tid S lock ->
                              invalidStamp tid S lock -> False. 
Proof.
  intros tid S lock H H0.
  inv H; inv H0; auto. omega.
Qed.

Inductive locked (tid : nat) : lock -> Prop :=
|acquired : forall oldV v, locked tid (Locked tid oldV v). 
 
Theorem validateNotIn : 
  forall tid l v b v'' lock''' rv wv e0 L H lock' chkpnt HI HV,
    Log.notIn l b L -> H l = Some(v'', lock''') -> validStamp tid rv lock''' -> 
    @validate tid rv wv e0 b L (update H l v lock') 
              (commit chkpnt HI HV) ->
    exists HV', @validate tid rv wv e0 b L H (commit chkpnt (update HI l v'' lock''') HV').
Proof.   
  intros tid l v b v'' lock''' rv wv e0 L H lock' chkpnt HI HV H0 H1 HV2 H3.
  remember (update H l v lock'). remember (commit chkpnt HI HV).
  genDeps{{chkpnt; HI; HV; H; l; v; lock'; lock'''}}.
  induction H3; intros; try solve[inv Heqv0].
  {inv Heqv0. subst. exists H1. rewrite updateUpdate.
   rewrite updateIdempotent. constructor. eassumption. }
  {inv Heqv0. dependent destruction H2. eapply IHvalidate in H2; eauto. 
   invertHyp. unfold lookup in H0. unfold update in H0. 
   destruct (Nat.eq_dec l0 l). 
   {subst. econstructor. econstructor; eauto. } 
   {econstructor. econstructor; eauto. }
  }
  {inv Heqv0. dependent destruction H2. eapply IHvalidate in H2; eauto. 
   invertHyp. unfold lookup in H0. unfold update in H0. 
   destruct (Nat.eq_dec l0 l). 
   {subst. econstructor. econstructor; eauto. } 
   {econstructor. econstructor; eauto. }
  }
  {inv Heqv0. dependent destruction H1. 
   eapply IHvalidate in H1; eauto. invertHyp. econstructor. 
   rewrite updatecomm; auto. econstructor; eauto. unfold lookup in H0. 
   unfold update in H0. destruct (Nat.eq_dec l0 l). contradiction. 
   eassumption. }
Qed. 

Theorem validateIn :  
  forall tid l v v'' rv wv e0 L H lock' chkpnt HI HV,
    Log.In l L -> H l = Some(v'', lock') -> 
    @validate tid rv wv e0 true L (update H l v lock') 
              (commit chkpnt HI HV) ->
    exists HV', @validate tid rv wv e0 true L H (commit chkpnt HI HV').
Proof.
  intros. dependent induction H2.
  {dependent destruction H0. eapply IHvalidate in H0; eauto. 
   invertHyp. unfold lookup in H4. unfold update in H4.
   destruct (Nat.eq_dec l l0).
   {subst. inv H4. econstructor. econstructor; eauto. }
   {econstructor. econstructor; eauto. }
  }
  {dependent destruction H0.
   {unfold lookup in H3. unfold update in H3.
    destruct (Nat.eq_dec l0 l0). Focus 2. exfalso; eauto.
    inv H3. eapply validateNotIn in H0; eauto. invertHyp.
    erewrite <- updateUpdate. econstructor. econstructor; eauto. constructor. }
   {eapply IHvalidate in H1; eauto. invertHyp. econstructor.
    econstructor; eauto. unfold lookup in H3. unfold update in H3.
    destruct (Nat.eq_dec l l0). contradiction. eassumption. }
  }
Qed. 

Theorem validateAcquiredLock : forall tid l v v' b rv wv e0 L L' H lock lock' chkpnt HI HV,
    lookup H l = Some(v', lock) ->
    acquireLock l v' tid rv L lock lock' L' -> 
    @validate tid rv wv e0 true L' (update H l v lock') (commit chkpnt HI HV) ->
    exists HV', @validate tid rv wv e0 b L H (commit chkpnt HI HV').
Proof.
  intros tid l v v' b rv wv e0 L L' H lock lock' chkpnt HI HV H0 H1 H2.
  dependent destruction H1. 
  {eapply validateIn in H1; eauto. }
  {dependent destruction H3. unfold update in H4. unfold lookup in H4. 
   destruct (Nat.eq_dec l l). inv H4. 
   eapply validateNotIn in H5; eauto. 
   constructor. omega. exfalso; auto. }
Qed. 

Theorem abortNotIn : 
  forall tid l v b v'' lock''' rv wv e0 L H lock' chkpnt HI,
    Log.notIn l b L -> H l = Some(v'', lock''') -> validStamp tid rv lock''' ->
    locked tid lock' ->
    @validate tid rv wv e0 b L (update H l v lock') (abort chkpnt HI) ->
    @validate tid rv wv e0 b L H (abort chkpnt (update HI l v'' lock''')).
Proof.
  intros. remember (update H l v lock'). remember (abort chkpnt HI).
  genDeps{{chkpnt; HI; H; l; v; lock'}}.
  induction H4; intros; try solve[inv Heqv0]. 
  {inv Heqv0. dependent destruction H5. eapply validateNotIn in H5; eauto. 
   invertHyp. unfold lookup in H0. unfold update in H0.
   destruct (Nat.eq_dec l0 l).
   {subst. inv H0. inv H3. inv H1. exfalso; auto. }
   {econstructor; eauto. }
  }
  {inv Heqv0. dependent destruction H5. eapply validateNotIn in H5; eauto. 
   invertHyp. unfold lookup in H0. unfold update in H0.
   destruct (Nat.eq_dec l0 l).
   {subst. inv H0. inv H3. inv H1. exfalso; auto. }
   {econstructor; eauto. }
  }
  {dependent destruction H0.
   {dependent destruction H1. eapply IHvalidate in H1; eauto.
    subst. inv Heqv0. eapply readPropAbort; eauto. constructor. }
   {inv Heqv0. dependent destruction H1. eapply IHvalidate in H1; eauto.
    eapply readPropAbort; eauto. constructor. }
  }
  {dependent destruction H1. inv Heqv0. eapply IHvalidate in H5; eauto.
   unfold lookup in H0. unfold update in H0. destruct (Nat.eq_dec l0 l).
   contradiction. rewrite updatecomm; auto. eapply writePropAbort. auto.
   eauto. }
Qed.

Theorem abortIn :  
  forall tid l v v'' rv wv e0 L H lock' chkpnt HI,
    Log.In l L -> H l = Some(v'', lock') -> 
    @validate tid rv wv e0 true L (update H l v lock') 
              (abort chkpnt HI) ->
    @validate tid rv wv e0 true L H (abort chkpnt HI).
Proof.
  intros. dependent induction H2.
  {dependent destruction H0. eapply validateIn in H0; eauto.
   invertHyp. unfold lookup in H4. unfold update in H4. destruct (Nat.eq_dec l l0).
   {subst. inv H4. econstructor; eauto. }
   {econstructor; eauto. }
  }
  {dependent destruction H3. dependent destruction H0. eapply IHvalidate in H0; eauto.
   eapply readPropAbort; eauto. constructor. }
  {dependent destruction H0.
   {unfold lookup in H3. unfold update in H3. destruct (Nat.eq_dec l0 l0).
    {inv H3. eapply abortNotIn in H0; eauto. erewrite <- updateUpdate.
     eapply writePropAbort; eauto. constructor. constructor. }
    {exfalso; auto. }
   }
   {eapply IHvalidate in H1; eauto. eapply writePropAbort; eauto.
    unfold lookup in H3. unfold update in H3. destruct (Nat.eq_dec l l0).
    contradiction. eauto. }
  }
Qed. 

Theorem abortAcquiredLock : forall tid l v v' b rv wv e0 L L' H lock lock' chkpnt HI,
    lookup H l = Some(v', lock) ->
    acquireLock l v' tid rv L lock lock' L' -> 
    @validate tid rv wv e0 true L' (update H l v lock') (abort chkpnt HI) ->
    @validate tid rv wv e0 b L H (abort chkpnt HI).
Proof.
  intros. dependent destruction H1. 
  {eapply abortIn in H2; eauto. }
  {dependent destruction H3. dependent destruction H5.
   unfold update in H5. unfold lookup in H5. 
   destruct (Nat.eq_dec l l). inv H5. 
   eapply abortNotIn in H2; eauto. constructor. auto. constructor. 
   exfalso; auto. }
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
     dependent destruction H6. transEq. invertEq. exfalso.
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

Theorem notInUpdate : forall H l v lock l',
    (update H l v lock) l' = None ->
    H l' = None. 
Proof.
  intros. unfold update in H0. destruct (Nat.eq_dec l l').
  {inv H0. }
  {assumption.  }
Qed.

(* `Nat.eq_dec l l'` == {l = l'} + {l <> l'}
 * is of type `sumbool`
 *)

Ltac heapUnfold := unfold lookup; unfold update.

Theorem rewindAllocSingle : forall tid H H' b1 b2 S e0 L l v L' e e',
    H' l = None ->
    rewind H (txThread b1 tid S e0 L e) H' (txThread b2 tid S e0 L' e') ->
    exists H'', rewind H'' (txThread b1 tid S e0 L e) (update H' l v (Unlocked 0)) (txThread b2 tid S e0 L' e').
Proof.
  intros tid H H' b1 b2 S e0 L l v L' e e' H0 H1. genDeps{{l; v}}. 
  induction H1; intros.
  {repeat econstructor. }
  {inv H0.
   {copy H2. eapply IHrewind in H2. invertHyp. exists x. econstructor; eauto.
    econstructor; eauto. destruct (eq_nat_dec l l0).
    {subst. unfold lookup in H5. transEq. invertEq. }
    {unfold lookup. unfold update. simplEq l l0. auto. }
   }
   {copy H2. eapply IHrewind in H0. invertHyp. exists x. econstructor. eauto.
    econstructor; eauto. heapUnfold. destruct (Nat.eq_dec l l0); auto. 
    subst. unfold lookup in *. transEq. invertEq. }
   {copy H2. eapply IHrewind in H2. invertHyp. exists x. econstructor.
    eauto. eapply r_readStepInvalid; eauto. destruct (Nat.eq_dec l l0); eauto. 
    {unfold lookup in H5. subst. transEq. invertEq. }
    {unfold lookup. unfold update. simplEq l l0. eauto. }
   }
   {copy H2. eapply notInUpdate in H2; eauto. eapply IHrewind in H2. invertHyp.
    exists x. econstructor; eauto. destruct (Nat.eq_dec l l0).
    {subst. unfold update in H0. destruct (Nat.eq_dec l0 l0). invertEq.
     exfalso. apply n. auto. }
    {rewrite <- updatecomm; auto. econstructor; eauto. heapUnfold. simplEq l l0.
     auto. }
   }
   {eapply IHrewind in H2. invertHyp. exists x. econstructor; eauto. eapply r_atomicIdemStep; eauto. }
   {eapply IHrewind in H2. invertHyp. exists x. econstructor; eauto. eapply r_betaStep; eauto. }
  }
Qed. 
  
Theorem rewindAlloc : forall C H T l v,
    H l = None -> 
    poolRewind C H T -> poolRewind C (update H l v (Unlocked 0)) T. 
Proof.
  intros C H T l v H0 H1. genDeps{{l; v}}. induction H1; intros.
  {constructor. }
  {eapply rewindAllocSingle in H0; eauto.  invertHyp. econstructor; eauto. }
  {econstructor; eauto. }
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
    inv H0.

    

   admit. }
  {inv H0; auto.  
   {admit. }
  }
  {eapply rewindAlloc; auto. }
  {admit. }
  {eapply poolRewindNewerStamp; eauto. }
  {eapply poolRewindNewerStamp; eauto. }
Admitted. 

Theorem p_rewindNoninterference : forall C H C' H' T T' T2,
    p_step C H T C' H' T' -> poolRewind C H T2 ->
    poolRewind C' H' T2.
Proof.
  intros C H C' H' T T' T2 H0 H1. generalize dependent T2.
  induction H0; intros; eauto. 
  {inv H0. admit. }
  {inv H0; auto.  
   {admit. }
  }
  {eapply rewindAlloc; auto. }
  {admit. }
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
   {dependent destruction H6. transEq. invertEq. exfalso.
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
   {dependent destruction H5.   (*r_readStepInvalid*)
    {(*invalidRead: this read is invalid, but we don't have a checkpoint*)
      transEq. invertEq. eapply commitRewind; eauto. }
    {dependent destruction H6. eauto. }
   }
   {eapply abortAcquiredLock in H5; eauto. }
  }
Qed.

Definition invalidHeap res :=
  match res with
  |commit _ H _ => H
  |abort _ H => H
  end. 

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
   {dependent destruction H5.
    {transEq. invertEq. exfalso. eapply validInvalidStamp; eauto. }
    {transEq. invertEq. eapply IHrewind in H7; eauto. }
    {dependent destruction H6. eapply IHrewind in H5; eauto. }
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
