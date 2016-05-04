Require Export semantics.

(**
* Theorems pertaining to validating a log before and after a write
*)

(**
If we update the heap with some location that does not exist
in the log, then it must still be in the result heaps.  This corresponds 
to the case where we are writing a location for the first time in a 
transaction, i.e. the lock was not previously been acquired
*)
Theorem validateNotIn : 
  forall tid l v b v'' lock''' rv wv e0 L H lock' chkpnt HI HV,
    Log.notIn l b L -> H l = Some(v'', lock''') -> validStamp tid rv lock''' -> 
    @validate tid rv wv e0 b L (update H l v lock') 
              (commit chkpnt HI HV) ->
    @validate tid rv wv e0 b L H (commit chkpnt (update HI l v'' lock''') (update HV l v'' lock''')).
Proof.   
  intros tid l v b v'' lock''' rv wv e0 L H lock' chkpnt HI HV H0 H1 HV2 H3.
  remember (update H l v lock'). remember (commit chkpnt HI HV).
  genDeps{{chkpnt; HI; HV; H; l; v; lock'; lock'''}}.
  induction H3; intros; try solve[inv Heqv0].
  {inv Heqv0. subst. rewrite updateUpdate.
   rewrite updateIdempotent. constructor. eassumption. }
  {inv Heqv0. invertHyp. heapUnfold. destruct (Nat.eq_dec l0 l).
   {subst. invertEq. econstructor; eauto. }
   {econstructor; eauto. }
  }
  {inv Heqv0. invertHyp. heapUnfold. destruct (Nat.eq_dec l0 l).
   {subst. invertEq. econstructor; eauto. }
   {econstructor; eauto. }
  }
  {inv Heqv0. invertHyp. rewrite updatecomm; auto. 
   rewrite updatecomm with (l := l) (l' := l0); auto. heapUnfold.
   econstructor; eauto. destruct (Nat.eq_dec l0 l). contradiction.
   assumption. }
Qed. 

(**
If we update the heap with some location that does exist
in the log, then the "invalid" heaps will be the same.  The 
valid heaps however, will differ by the value associated with `l`.
The non-updated heap will contain the previously written value, `v''`
and the result of validating with the updated heap will have the 
newly updated value `v`.
*)

Theorem validateIn :  
  forall tid l v v'' rv wv e0 L H lock' chkpnt HI HV,
    Log.In l L -> H l = Some(v'', lock') -> 
    @validate tid rv wv e0 true L (update H l v lock') 
              (commit chkpnt HI HV) ->
    @validate tid rv wv e0 true L H (commit chkpnt HI (update HV l v'' (Unlocked wv))).
Proof.
  intros. dependent induction H2.
  {invertHyp. eapply IHvalidate in H0; eauto. 
   heapUnfold. destruct (Nat.eq_dec l l0).
   {subst. invertEq. econstructor; eauto. }
   {econstructor; eauto. }
  }
  {invertHyp. 
   {heapUnfold. destruct (Nat.eq_dec l0 l0). Focus 2. exfalso; eauto.
    invertEq. eapply validateNotIn in H0; eauto.
    erewrite <- updateUpdate. erewrite <- updateUpdate with (H := (update HV0 l0 v0 (Unlocked wv))).
    econstructor; eauto. rewrite updateUpdate. eassumption. constructor. }
   {heapUnfold. destruct (Nat.eq_dec l l0). contradiction.
    erewrite updatecomm; auto. econstructor; auto. eauto. }
  }
Qed.

(**
When acquiring a lock via a write, we should get a "similar" result
when validating the log before and after the write.  The "invalid" heaps
will be exactly the same, however, the valid heaps may differ by the 
value associated with the location we are writing.
*)
Theorem validateAcquiredLock : forall tid l v v' b rv wv e0 L L' H lock lock' chkpnt HI HV,
    H l = Some(v', lock) ->
    acquireLock l v' tid rv L lock lock' L' -> 
    @validate tid rv wv e0 true L' (update H l v lock') (commit chkpnt HI HV) ->
    exists HV', @validate tid rv wv e0 b L H (commit chkpnt HI HV').
Proof.
  intros tid l v v' b rv wv e0 L L' H lock lock' chkpnt HI HV H0 H1 H2.
  dependent destruction H1. 
  {eapply validateIn in H1; eauto. }
  {invertHyp. heapUnfold. destruct (Nat.eq_dec l l).
   invertEq. eapply validateNotIn in H7; eauto. 
   constructor. omega. exfalso; auto. }
Qed.

(**
Analogous to validateNotIn but for aborts.  
*)
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
  {inv Heqv0. invertHyp. eapply validateNotIn in H5; eauto. 
   heapUnfold. destruct (Nat.eq_dec l0 l).
   {subst. invertEq. inv H1; exfalso; auto. }
   {econstructor; eauto. }
  }
  {inv Heqv0. invertHyp. eapply validateNotIn in H5; eauto. 
   heapUnfold. destruct (Nat.eq_dec l0 l).
   {subst. invertEq. inv H1; exfalso; auto. }
   {econstructor; eauto. }
  }
  {invertEq. dependent destruction H0.
   {invertHyp. eapply IHvalidate in H1; eauto.
    subst. eapply readPropAbort; eauto. constructor. constructor. }
   {invertHyp. eapply IHvalidate in H1; eauto.
    eapply readPropAbort; eauto. constructor. constructor. }
  } 
  {invertHyp. invertEq. eapply IHvalidate in H9; eauto.
   heapUnfold. destruct (Nat.eq_dec l0 l). contradiction.
   rewrite updatecomm; auto. eapply writePropAbort. auto.
   eauto. auto. auto. constructor. }
Qed.

(**
Analogous to `validateIn` for aborts
*)
Theorem abortIn :  
  forall tid l v v'' rv wv e0 L H lock' chkpnt HI,
    Log.In l L -> H l = Some(v'', lock') -> 
    @validate tid rv wv e0 true L (update H l v lock') 
              (abort chkpnt HI) ->
    @validate tid rv wv e0 true L H (abort chkpnt HI).
Proof.
  intros. dependent induction H2.
  {invertHyp. eapply validateIn in H0; eauto.
   heapUnfold. destruct (Nat.eq_dec l l0).
   {subst. invertEq. econstructor; eauto. }
   {econstructor; eauto. }
  }
  {dependent destruction H3. invertHyp. eapply IHvalidate in H0; eauto.
   eapply readPropAbort; eauto. constructor. }
  {invertHyp.
   {heapUnfold. destruct (Nat.eq_dec l0 l0).
    {invertEq. eapply abortNotIn in H0; eauto. erewrite <- updateUpdate.
     eapply writePropAbort; eauto. constructor. constructor. }
    {exfalso; auto. }
   }
   {eapply IHvalidate in H1; eauto. eapply writePropAbort; eauto.
    heapUnfold.  destruct (Nat.eq_dec l l0). contradiction. eauto. }
  }
Qed. 

(**
Analogous to `validateAcquiredlock`
*)
Theorem abortAcquiredLock : forall tid l v v' b rv wv e0 L L' H lock lock' chkpnt HI,
    H l = Some(v', lock) ->
    acquireLock l v' tid rv L lock lock' L' -> 
    @validate tid rv wv e0 true L' (update H l v lock') (abort chkpnt HI) ->
    @validate tid rv wv e0 b L H (abort chkpnt HI).
Proof.
  intros. dependent destruction H1. 
  {eapply abortIn in H2; eauto. }
  {invertHyp. dependent destruction H5.  
   heapUnfold. destruct (Nat.eq_dec l l). invertEq.
   eapply abortNotIn in H2; eauto. constructor. auto. constructor. 
   exfalso; auto. }
Qed. 

(**
Reverse direction of above 
*)

Theorem validateNotInRev : 
  forall tid l v b v'' lock''' rv wv e0 L H lock' chkpnt HI HV,
    Log.notIn l b L -> H l = Some(v'', lock''') -> 
    @validate tid rv wv e0 b L H (commit chkpnt HI HV) -> locked tid lock' ->
    @validate tid rv wv e0 b L (update H l v lock')
              (commit chkpnt (update HI l v lock') (update HV l v lock')). 
Proof.
  intros. remember (commit chkpnt HI HV).
  genDeps{{chkpnt; HI; HV; l; lock'''; v''; lock'}}. 
  induction H2; intros; inv Heqv0. 
  {constructor. }
  {invertHyp. destruct (Nat.eq_dec l l0).
   {subst. econstructor. heapUnfold. simplEq l0 l0. eauto.
    constructor. eapply IHvalidate; eauto. constructor. }
   {econstructor; eauto. heapUnfold. simplEq l0 l. eauto.
    eapply IHvalidate; eauto. constructor. }
  }
  {invertHyp. destruct (Nat.eq_dec l l0).
   {subst. econstructor. heapUnfold. simplEq l0 l0. eauto.
    constructor. eapply IHvalidate; eauto. constructor. }
   {econstructor; eauto. heapUnfold. simplEq l0 l. eauto.
    eapply IHvalidate; eauto. constructor. }
  }
  {invertHyp. rewrite updatecomm.
   rewrite updatecomm with (l := l) (l' := l0). econstructor; auto. 
   heapUnfold. simplEq l0 l. assumption. eapply IHvalidate; eauto.
   constructor. apply neqSymm; assumption. apply neqSymm. auto. }
Qed. 

Theorem validateInRev :  
  forall tid l v v'' rv wv e0 L H lock' chkpnt HI HV,
    Log.In l L -> H l = Some(v'', lock') -> 
    @validate tid rv wv e0 true L H (commit chkpnt HI HV) ->
    locked tid lock' ->
    @validate tid rv wv e0 true L (update H l v lock') 
              (commit chkpnt HI (update HV l v (Unlocked wv))).
Proof.
  intros. genDeps{{v''; lock'; v}}. dependent induction H2; intros.
  {invertHyp. destruct (Nat.eq_dec l l0).
   {econstructor. heapUnfold. subst. simplEq l0 l0. 
    eauto. constructor. eapply IHvalidate; eauto. constructor. }
   {econstructor; eauto. heapUnfold. simplEq l l0. eauto.
    eapply IHvalidate; eauto. constructor. }
  }
  {invertHyp. 
   {transEq. invertEq. erewrite <- updateUpdate with (H := HI0).
    erewrite <- updateUpdate with (H := (update HV0 l0 v'' (Unlocked wv))).
    rewrite updateUpdate with (H := HV0). econstructor; eauto.
    heapUnfold. simplEq l0 l0. auto. eapply validateNotInRev; eauto.
    constructor. }
   {rewrite updatecomm; auto. econstructor; auto. heapUnfold. simplEq l l0.
    assumption. eapply IHvalidate; eauto. constructor. }
  }
Qed. 

Theorem validateNotInLookup : forall b tid rv wv e0 L H res l,
    @validate tid rv wv e0 b L H res -> Log.notIn l b L ->
    H l = (invalidHeap res) l. 
Proof.
  intros. induction H0; try solve[simpl in *; dependent destruction H1; eauto]. 
  {simpl in *. dependent destruction H1. unfold update. simplEq l0 l. 
   auto. }
  {dependent destruction H2. invertHyp. eauto. 
   invertHyp. eauto. }
  {simpl in *. invertHyp. unfold update.
   simplEq l0 l. auto. }
Qed. 

Theorem validateAcquiredLockRev : forall tid l v v' b rv wv e0 L L' H lock lock' chkpnt HI HV,
    H l = Some(v', lock) ->
    acquireLock l v' tid rv L lock lock' L' ->
    @validate tid rv wv e0 b L H (commit chkpnt HI HV) ->
    exists HV', @validate tid rv wv e0 true L' (update H l v lock') (commit chkpnt HI HV'). 
Proof.
  intros. dependent destruction H1. 
  {eapply validateInRev in H2; eauto. constructor. }
  {copy H3. eapply validateNotInRev in H3; eauto. Focus 2. constructor. auto.
   replace HI with (update (update HI l v (Locked tid S' v')) l v' (Unlocked S')). econstructor.
   econstructor. heapUnfold. simplEq l l. reflexivity. eauto.
   auto. eauto. rewrite updateUpdate. eapply updateIdempotent.
   eapply validateNotInLookup in H4; eauto.
   simpl in *. rewrite <- H4. assumption. }
Qed.


Theorem abortNotInRev : 
  forall tid l v b v'' lock''' rv wv e0 L H lock' chkpnt HI,
    Log.notIn l b L -> H l = Some(v'', lock''') -> 
    @validate tid rv wv e0 b L H (abort chkpnt HI) -> locked tid lock' ->
    validStamp tid rv lock''' ->
    @validate tid rv wv e0 b L (update H l v lock') (abort chkpnt (update HI l v lock')). 
Proof.
  intros. remember (abort chkpnt HI).
  genDeps{{chkpnt; HI; l; v; v''; lock'''; lock'}}.
  induction H2; intros; inv Heqv0.  
  {invertHyp. destruct (Nat.eq_dec l l0).
   {subst. exfalso. eapply validInvalidStamp; eauto. 
    transEq. invertEq. assumption. }
   {eapply validateNotInRev in H2; eauto. econstructor; eauto.
    heapUnfold. simplEq l0 l. eauto. constructor. }
  }
  {dependent destruction H5. destruct (Nat.eq_dec l l0).
   {subst. exfalso. eapply validInvalidStamp; eauto. 
    transEq. invertEq. assumption. }
   {eapply validateNotInRev in H2; eauto. invertHyp.
    econstructor; eauto. heapUnfold. simplEq l0 l. eauto. }
  }
  {eapply readPropAbort. eapply IHvalidate; eauto. 
   dependent destruction H0; invertHyp; auto. auto. }
  {invertHyp. rewrite updatecomm; auto. eapply writePropAbort; eauto.
   eapply IHvalidate; eauto. constructor. heapUnfold.
   simplEq l0 l. eauto. }
Qed.    

Theorem abortInRev :  
  forall tid l v v'' rv wv e0 L H lock' chkpnt HI,
    Log.In l L -> H l = Some(v'', lock') -> 
    @validate tid rv wv e0 true L H (abort chkpnt HI) ->
    locked tid lock' ->
    @validate tid rv wv e0 true L (update H l v lock') 
              (abort chkpnt HI).
Proof.
  intros. genDeps{{v; v''; lock'; l}}. dependent induction H2; intros.
  {invertHyp. destruct (Nat.eq_dec l l0).
   {subst. transEq. invertEq. invertHyp. exfalso; auto. }
   {eapply validateInRev in H2; eauto. econstructor; eauto.
    heapUnfold. simplEq l0 l. eauto. constructor. }
  }
  {eapply readPropAbort; eauto. eapply IHvalidate; eauto.
   dependent destruction H0; invertHyp; auto. }
  {invertHyp.
   {transEq. invertEq.
    replace (update HI0 l v1 (Unlocked oldV0)) with
    (update (update HI0 l v0 (Locked tid oldV0 v1)) l v1 (Unlocked oldV0)).
    eapply writePropAbort. eapply abortNotInRev; eauto. constructor.
    constructor. heapUnfold. simplEq l l. auto. auto. auto.
    rewrite updateUpdate. auto. }
   {eapply writePropAbort. eapply IHvalidate; eauto. constructor.
    heapUnfold. simplEq l0 l. eauto. auto. auto. }
  }
Qed. 
    
Theorem abortAcquiredLockRev : forall tid l v v' b rv wv e0 L L' H lock lock' chkpnt HI,
    H l = Some(v', lock) ->
    acquireLock l v' tid rv L lock lock' L' ->
    @validate tid rv wv e0 b L H (abort chkpnt HI) ->
    @validate tid rv wv e0 true L' (update H l v lock') (abort chkpnt HI). 
Proof.
  intros. dependent destruction H1.
  {eapply abortInRev in H2; eauto. constructor. }
  {copy H3. eapply abortNotInRev in H3; eauto. 
   replace HI with (update(update HI l v (Locked tid S' v')) l v' (Unlocked S')).  
   Focus 2. rewrite updateUpdate. apply updateIdempotent.
   eapply  validateNotInLookup in H4; eauto. simpl in H4. 
   rewrite <- H4. assumption. eapply writePropAbort. eauto. heapUnfold.
   simplEq l l. eauto. auto. auto. constructor. constructor. auto. }
Qed. 