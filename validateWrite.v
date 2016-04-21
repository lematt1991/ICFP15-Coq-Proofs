Require Export semantics.

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
