Require Export semantics.

Ltac heapUnfold :=
  match goal with
  |H : update ?h ?l ?v ?lock ?l' = ?x |- _ => unfold update in H; try heapUnfold
  | |- update ?H ?l ?v ?lock ?l' = ?x => unfold update
  end.

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
  {inv Heqv0. invertHyp. eapply IHvalidate in H2; eauto.
   invertHyp. exists x. heapUnfold.
   destruct(Nat.eq_dec l0 l); subst; econstructor; eauto. }
  {inv Heqv0. invertHyp. eapply IHvalidate in H2; eauto.
   invertHyp. exists x. heapUnfold.
   destruct(Nat.eq_dec l0 l); subst; econstructor; eauto. }
  {inv Heqv0. invertHyp. eapply IHvalidate in H4; eauto.
   invertHyp. econstructor. rewrite updatecomm; auto.
   econstructor; eauto. heapUnfold. destruct (Nat.eq_dec l0 l).
   contradiction. eassumption. }
Qed. 

Theorem validateIn :  
  forall tid l v v'' rv wv e0 L H lock' chkpnt HI HV,
    Log.In l L -> H l = Some(v'', lock') -> 
    @validate tid rv wv e0 true L (update H l v lock') 
              (commit chkpnt HI HV) ->
    exists HV', @validate tid rv wv e0 true L H (commit chkpnt HI HV').
Proof.
  intros. dependent induction H2.
  {invertHyp. eapply IHvalidate in H0; eauto. 
   invertHyp. heapUnfold. destruct (Nat.eq_dec l l0).
   {subst. invertEq. econstructor. econstructor; eauto. }
   {econstructor. econstructor; eauto. }
  }
  {invertHyp. 
   {heapUnfold. destruct (Nat.eq_dec l0 l0). Focus 2. exfalso; eauto.
    invertEq. eapply validateNotIn in H0; eauto. invertHyp.
    erewrite <- updateUpdate. econstructor. econstructor; eauto. constructor. }
   {eapply IHvalidate in H1; eauto. invertHyp. econstructor.
    econstructor; eauto. heapUnfold. destruct (Nat.eq_dec l l0).
    contradiction. eassumption. }
  }
Qed. 

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
   invertHyp. heapUnfold. destruct (Nat.eq_dec l0 l).
   {subst. invertEq. inv H1; exfalso; auto. }
   {econstructor; eauto. }
  }
  {inv Heqv0. invertHyp. eapply validateNotIn in H5; eauto. 
   invertHyp. heapUnfold. destruct (Nat.eq_dec l0 l).
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

Theorem abortIn :  
  forall tid l v v'' rv wv e0 L H lock' chkpnt HI,
    Log.In l L -> H l = Some(v'', lock') -> 
    @validate tid rv wv e0 true L (update H l v lock') 
              (abort chkpnt HI) ->
    @validate tid rv wv e0 true L H (abort chkpnt HI).
Proof.
  intros. dependent induction H2.
  {invertHyp. eapply validateIn in H0; eauto.
   invertHyp. heapUnfold. destruct (Nat.eq_dec l l0).
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

Theorem validateNotInRev : 
  forall tid l v b v'' lock''' rv wv e0 L H lock' chkpnt HI HV,
    Log.notIn l b L -> H l = Some(v'', lock''') -> 
    @validate tid rv wv e0 b L H (commit chkpnt HI HV) -> locked tid lock' ->
    exists HV', @validate tid rv wv e0 b L (update H l v lock') (commit chkpnt (update HI l v lock') HV'). 
Proof.
  intros. remember (commit chkpnt HI HV).
  genDeps{{chkpnt; HI; HV; l; lock'''; v''; lock'}}. 
  induction H2; intros; inv Heqv0. 
  {repeat econstructor. }
  {invertHyp. eapply IHvalidate in H4; eauto. invertHyp.
   destruct (Nat.eq_dec l l0). 
   {subst. econstructor. econstructor. heapUnfold. simplEq l0 l0.
    auto. Focus 2. eauto. inv H3. constructor. constructor. }
   {econstructor. econstructor. heapUnfold. simplEq l0 l. eauto.
    auto. eauto. } constructor. 
  }
  {invertHyp. eapply IHvalidate in H4; eauto. invertHyp.
   destruct (Nat.eq_dec l l0).
   {subst. econstructor. econstructor. heapUnfold. simplEq l0 l0.
    auto. Focus 2. eauto. inv H3. constructor. constructor. }
   {econstructor. econstructor. heapUnfold. simplEq l0 l. eauto.
    auto. eauto. } constructor. 
  }
  {invertHyp. eapply IHvalidate in H5; eauto. invertHyp.
   econstructor. rewrite updatecomm; auto. econstructor. heapUnfold.
   simplEq l0 l. eauto. auto. auto. eauto. constructor. }
Qed. 

Theorem validateInRev :  
  forall tid l v v'' rv wv e0 L H lock' chkpnt HI HV,
    Log.In l L -> H l = Some(v'', lock') -> 
    @validate tid rv wv e0 true L H (commit chkpnt HI HV) ->
    locked tid lock' ->
    exists HV', @validate tid rv wv e0 true L (update H l v lock') 
                     (commit chkpnt HI HV').
Proof.
  intros. genDeps{{v''; lock'; v}}. dependent induction H2; intros.
  {dependent destruction H0. eapply IHvalidate in H0; eauto.
   invertHyp. destruct (Nat.eq_dec l l0).
   {econstructor. econstructor. heapUnfold. subst. destruct (Nat.eq_dec l0 l0).
    auto. exfalso; auto. subst. transEq.
    invertEq. assumption. eauto. }
   {econstructor. econstructor; eauto. heapUnfold. simplEq l l0. eauto. }
  }
  {dependent destruction H0.
   {inv H4. transEq. invertEq. eapply validateNotInRev in H0.
    invertHyp. econstructor.
    replace (commit chkpnt (update HI0 l0 v1 (Unlocked oldV0)) ?HV') with
    (commit chkpnt (update (update HI0 l0 v0 (Locked tid oldV0 v1)) l0 v1 (Unlocked oldV0)) ?HV'). 
    Focus 2. rewrite updateUpdate. eauto. econstructor. heapUnfold. simplEq l0 l0.
    auto. eauto. eauto. eauto. eauto. eauto. constructor. }
   {eapply IHvalidate in H4; eauto. invertHyp. econstructor.
    econstructor; eauto. heapUnfold. simplEq l l0. eauto. }
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
  {copy H3. eapply validateNotInRev in H3; eauto. invertHyp. Focus 2. constructor. auto.
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
   {eapply validateNotInRev in H2; eauto. invertHyp.
    econstructor; eauto. heapUnfold. simplEq l0 l. eauto. constructor. }
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
   {eapply validateInRev in H2; eauto. invertHyp. econstructor; eauto.
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