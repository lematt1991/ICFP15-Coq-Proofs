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
   {subst. invertEq. inv H3; inv H1; exfalso; auto. }
   {econstructor; eauto. }
  }
  {inv Heqv0. invertHyp. eapply validateNotIn in H5; eauto. 
   invertHyp. heapUnfold. destruct (Nat.eq_dec l0 l).
   {subst. invertEq. inv H3; inv H1; exfalso; auto. }
   {econstructor; eauto. }
  }
  {invertEq. dependent destruction H0.
   {invertHyp. eapply IHvalidate in H1; eauto.
    subst. eapply readPropAbort; eauto. constructor. }
   {invertHyp. eapply IHvalidate in H1; eauto.
    eapply readPropAbort; eauto. constructor. }
  } 
  {invertHyp. invertEq. eapply IHvalidate in H9; eauto.
   heapUnfold. destruct (Nat.eq_dec l0 l). contradiction.
   rewrite updatecomm; auto. eapply writePropAbort. auto.
   eauto. auto. auto. }
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
