Require Export validateWrite.

Theorem notInUpdate : forall H l v lock l',
    (update H l v lock) l' = None ->
    H l' = None. 
Proof.
  intros. heapUnfold. destruct (Nat.eq_dec l l').
  {invertEq. }
  {assumption.  }
Qed.
 
Theorem rewindAllocSingle : forall tid H H' b1 b2 S e0 L l v L' e e',
    H' l = None ->
    rewind H (txThread b1 tid S e0 L e) H' (txThread b2 tid S e0 L' e') ->
    exists H'', rewind H'' (txThread b1 tid S e0 L e) (update H' l v (Unlocked 0)) (txThread b2 tid S e0 L' e').
Proof.
  intros. genDeps{{l; v}}. induction H1; intros.
  {repeat econstructor. }
  {inv H0.  
   {copy H2. eapply IHrewind in H2. invertHyp. exists x. econstructor; eauto.
    econstructor; eauto. destruct (eq_nat_dec l l0).
    {subst. heapUnfold. transEq. invertEq. }
    {heapUnfold. simplEq l l0. auto. }
   }
   {copy H2. eapply IHrewind in H0; auto. invertHyp. exists x. econstructor. eauto.
    econstructor; eauto. heapUnfold. destruct (Nat.eq_dec l l0); auto. 
    subst. transEq. invertEq. }
   {copy H2. eapply IHrewind in H2. invertHyp. exists x. econstructor.
    eauto. eapply r_readStepInvalid; eauto. destruct (Nat.eq_dec l l0); eauto. 
    {heapUnfold. subst. transEq. invertEq. }
    {heapUnfold. simplEq l l0. eauto. }
   }
   {copy H2. eapply notInUpdate in H2; eauto. eapply IHrewind in H2. invertHyp.
    exists x. econstructor; eauto. destruct (Nat.eq_dec l l0).
    {subst. heapUnfold. destruct (Nat.eq_dec l0 l0). invertEq.
     exfalso. auto. }
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
  intros. genDeps{{l; v}}. induction H1; intros.
  {constructor. auto. }
  {eapply rewindAllocSingle in H0; eauto.  invertHyp. econstructor; eauto. }
  {econstructor; eauto. }
Qed.

Inductive releaseLocks (tid:nat) : forall b, heap -> log b -> heap -> Prop :=
| releaseNilLog : forall H, releaseLocks tid false H NilLog H
| releaseRead : forall L l v H H',
    releaseLocks tid true H L H' -> releaseLocks tid true H (Read l v L) H'
|releaseChkpnt : forall L l v E H H',
    releaseLocks tid false H L H' -> releaseLocks tid false H (Chkpnt l E v L) H'
|releaseWrite : forall b l L H H' v v' oldV,
    releaseLocks tid b H L H' -> Log.notIn l b L -> H l = Some(v, Locked tid oldV v') ->
    releaseLocks tid true H (Write b l L) (update H' l v' (Unlocked oldV)). 

Theorem abortReleaseLocks : forall e0 tid rv wv b L H res,
    @validate tid rv wv e0 b L H res ->
    releaseLocks tid b H L (invalidHeap res). 
Proof.
  intros. Hint Constructors releaseLocks.
  induction H0; simpl in *; eauto.
  {dependent destruction H1; eauto. }
Qed.

Theorem lookupReleaseUnowned : forall HI b tid L H l v lock,
    releaseLocks tid b H L HI -> ~locked tid lock ->
    H l = Some(v, lock) -> 
    HI l = Some(v, lock). 
Proof.
  intros. genDeps{{lock; v}}. induction H0; intros; simpl in *; eauto. 
  {heapUnfold. destruct (Nat.eq_dec l0 l).
   {subst. transEq. invertEq. exfalso. apply H3. constructor. }
   {eauto. }
  }
Qed. 

Theorem lookupReleaseMaybeOwned : forall b tid tid' L H l v oldV v' HI,
    releaseLocks tid b H L HI ->
    H l = Some(v, Locked tid' oldV v') ->
    (HI l = Some(v, Locked tid' oldV v') \/
     HI l = Some(v', Unlocked oldV)). 
Proof.
  intros. genDeps{{tid'; l; v; oldV; v'}}. induction H0; intros; simpl; auto. 
  {unfold update. destruct (Nat.eq_dec l l0).
   {subst. right. transEq. invertEq. auto. }
   {auto. }
  }
Qed. 

Theorem acquireReleaseNI : forall b b' tid' tid H l v v' lock lock' rv L L' L0 HI,
    @acquireLock l v' tid rv b L lock lock' L' -> H l = Some(v', lock) ->
    releaseLocks tid' b' (update H l v lock') L0 HI -> tid <> tid' ->
    releaseLocks tid' b' H L0 (update HI l v' lock).
Proof.
  intros. genDeps{{v'; L'; rv; b; tid; lock}}.
  dependent induction H2; intros; eauto. 
  {rewrite updateUpdate. rewrite updateIdempotent; auto. }
  {heapUnfold. destruct (Nat.eq_dec l l0).
   {subst. invertEq. dependent destruction H4; exfalso; auto. }
   {rewrite updatecomm; auto. econstructor; eauto. }
  }
Qed. 

Theorem abortRewindSingleNI : forall b' H H' HI b tid rv e0 L e L' tid',
    releaseLocks tid' b' H L' HI ->
    rewind H' (txThread false tid rv e0 NilLog e0) H (txThread b tid rv e0 L e) ->
    tid' <> tid -> 
    exists H'', rewind H'' (txThread false tid rv e0 NilLog e0) HI (txThread b tid rv e0 L e) .
Proof.
  intros. genDeps{{HI; L'; b'; tid'}}.
  dependent induction H1; intros.
  {repeat econstructor. }
  {dependent destruction H0.
   {copy H6. eapply IHrewind in H6; auto. invertHyp. exists x. econstructor; eauto. 
    econstructor; eauto. eapply lookupReleaseUnowned in H7; eauto. intro.
    inv H4. inv H6. exfalso; auto. inv H6. }
   {copy H6. eapply IHrewind in H6; auto. invertHyp. exists x. econstructor; eauto. 
    econstructor; eauto. eapply lookupReleaseUnowned in H7; eauto. intro.
    inv H4. inv H6. exfalso; auto. inv H6. }
   {copy H8. eapply IHrewind in H8; auto. invertHyp. exists x.
    econstructor; eauto. dependent destruction H5.
    {eapply lookupReleaseUnowned in H9; eauto.
     eapply r_readStepInvalid; eauto. constructor; auto.
     intro contra. inv contra. }
    {eapply lookupReleaseMaybeOwned in H9; eauto. inv H9.
     {eapply r_readStepInvalid; eauto. constructor; auto. }
     {dependent destruction H6.
      {inv H3.
       {eapply r_readChkpnt; eauto. constructor; auto. }
       {eapply r_readStepInvalid; eauto. constructor. constructor; auto.
        constructor. }
      }
      {inv H3.
       {eapply r_readNoChkpnt; eauto. constructor; auto. }
       {eapply r_readStepInvalid; eauto. constructor. constructor; auto.
        constructor. }
      }
     }
    }
   }
   {copy H6. eapply acquireReleaseNI in H6; eauto. copy H6. eapply IHrewind in H6; auto.
    invertHyp. econstructor. econstructor. eassumption.
    eapply lookupReleaseUnowned in H7. Focus 3. heapUnfold.
    simplEq l l. eauto. copy H7. eapply heapPullOut in H7. invertHyp.
    rewrite updateUpdate.
    replace (update x0 l v lock') with (update (update x0 l v' lock) l v lock').
    econstructor; eauto. heapUnfold. simplEq l l. auto. rewrite updateUpdate.
    auto. intro. dependent destruction H4. inv H6. exfalso; auto.
    inv H10. exfalso; auto. }
   {eapply IHrewind in H4; auto. invertHyp. exists x. econstructor; eauto.
    eapply r_atomicIdemStep; eauto. }
   {eapply IHrewind in H4; auto. invertHyp. exists x. econstructor; eauto.
    eapply r_betaStep; eauto. }
  }
Qed.

Ltac solveIn :=
  simpl;
   match goal with
   | H:In ?A (Intersection ?A ?S1 ?S2) ?x |- _ => inv H; try solveIn
   | H:In ?A (Singleton ?A ?x) ?y |- _ => inv H; try solveIn
   | |- In ?A (Intersection ?A ?S1 ?S2) ?x => constructor; solveIn
   | |- In ?A (Union ?A ?S1 ?S2) ?x => (apply Union_introl; solveIn) || (apply Union_intror; solveIn)
   | |- In ?A (Singleton ?A ?x) ?x => constructor
   | _ => assumption
   | H : In ?A (Empty_set ?A) ?x |- _ => inv H
   | H : In ?A (Union ?A ?S1 ?S2) ?x |- _ => inv H; solveIn
   end.

Theorem abortRewindNI : forall tid b rv wv e0 C L H T chkpnt HI,
    @validate tid rv wv e0 b L H (abort chkpnt HI) ->
    Disjoint nat (Singleton nat tid) (ids T) ->
    poolRewind C H T -> poolRewind (S C) HI T.
Proof.
  intros. genDeps{{tid; rv; wv; e0; L; b; HI}}. induction H2; intros.
  {constructor. auto. }
  {assert(tid0 <> tid). intro. subst. inv H4. specialize (H5 tid).
   apply H5. constructor; constructor. copy H3.
   eapply abortReleaseLocks in H3; eauto. simpl in *. 
   eapply abortRewindSingleNI in H3; eauto. invertHyp. econstructor.
   eauto. auto. auto. }
  {constructor. auto. eapply IHpoolRewind1; eauto. simpl in *.
   constructor. intros. intro. inv H2. specialize (H4 x). apply H4.
   solveIn. eapply IHpoolRewind2; eauto. constructor. intros.
   intro. solveIn. inv H2. specialize (H3 x). apply H3. solveIn. }
Qed. 

Theorem commitUnowned : forall b tid rv wv e0 L H chkpnt HI HV l v lock,
    @validate tid rv wv e0 b L H (commit chkpnt HI HV) ->
    H l = Some(v, lock) -> ~ locked tid lock ->
    HV l = Some(v, lock).
Proof.
  intros. remember (commit chkpnt HI HV). genDeps{{HI; HV; chkpnt; l; v; lock}}. 
  induction H0; intros; inv Heqv0; eauto. 
  {heapUnfold. destruct (Nat.eq_dec l l0).
   {subst. transEq. invertEq. 
    exfalso. apply H4. constructor. }
   {eauto. }
  }
Qed. 

Theorem commitMaybeOwned : forall chkpnt HI HV b tid rv tid' wv e0 L H l v oldV v',
    @validate tid rv wv e0 b L H (commit chkpnt HI HV) ->
    H l = Some(v, Locked tid' oldV v') ->
    (HV l = Some(v, Locked tid' oldV v') \/
     HV l = Some(v, Unlocked wv)). 
Proof.
  intros. remember(commit chkpnt HI HV).
  genDeps{{chkpnt; HI; HV; l; v; oldV; v'; tid'}}. 
  induction H0; intros; inv Heqv0; eauto. 
  {unfold update. destruct (Nat.eq_dec l l0).
   {subst. transEq. invertEq. auto. }
   {eauto. }
  }
Qed. 

Theorem commitWriteNI :
  forall b1 b2 tid' rv' wv' e0' L' l v v' tid rv L0 L lock lock' H chkpnt HI HV,
    @acquireLock l v' tid rv b1 L0 lock lock' L -> tid <> tid' ->
    H l = Some(v', lock) ->
    validate tid' rv' wv' e0' L' (update H l v lock') (commit chkpnt HI HV) ->
    exists HI' HV', @validate tid' rv' wv' e0' b2 L' H (commit chkpnt HI' HV') /\
    HV = (update HV' l v lock') /\ HV' l = Some(v', lock). 
Proof.
  intros. remember (update H l v lock'). remember (commit chkpnt HI HV).
  genDeps{{b1; tid; rv; v'; lock; L; H; l; v; lock'; chkpnt; HI; HV}}. 
  induction H3; intros; subst; inv Heqv0. 
  {repeat econstructor. auto. }
  {copy H6. eapply IHvalidate in H6; eauto. invertHyp. exists x. exists x0.
   split; auto. heapUnfold. destruct (Nat.eq_dec l0 l).
   {invertEq. dependent destruction H; dependent destruction H1. 
    exfalso; auto. exfalso; auto. }
   {econstructor; eauto. }
  }
  {copy H6. eapply IHvalidate in H6; eauto. invertHyp. exists x. exists x0.
   split; auto. heapUnfold. destruct (Nat.eq_dec l0 l).
   {invertEq. dependent destruction H; dependent destruction H1. 
    exfalso; auto. exfalso; auto. }
   {econstructor; eauto. }
  }
  {copy H5. eapply IHvalidate in H5; eauto. invertHyp. exists (update x l v' (Unlocked oldV)).
   exists (update x0 l v (Unlocked wv')). heapUnfold.
   destruct (Nat.eq_dec l0 l).
   {invertEq. dependent destruction H7; exfalso; auto. }
   {split. econstructor; eauto. split. rewrite updatecomm; eauto. heapUnfold.
    simplEq l l0. auto. }
  }
Qed. 

Theorem commitRewindSingleNI : forall b' H H' HI b tid chkpnt rv e0 L e L' e0' rv' C tid' HV,
    @validate tid' rv' C e0' b' L' H (commit chkpnt HI HV) -> rv < C ->
    rewind H' (txThread false tid rv e0 NilLog e0) H (txThread b tid rv e0 L e) ->
    tid <> tid' ->
    exists H'', rewind H'' (txThread false tid rv e0 NilLog e0) HV (txThread b tid rv e0 L e) .
Proof.
  intros. intros. genDeps{{tid'; rv'; C; e0'; L'; HI; HV}}.
  dependent induction H2; intros.
  {repeat econstructor. }
  {dependent destruction H0.
   {copy H6. eapply commitUnowned in H6; eauto. eapply IHrewind in H8.
    Focus 2. eauto. invertHyp. exists x. econstructor; eauto.
    econstructor; eauto. auto. auto. intro. dependent destruction H4.
    inv H9. exfalso; auto. inv H9. }
   {copy H6. eapply commitUnowned in H6; eauto. eapply IHrewind in H8.
    Focus 2. eauto. invertHyp. exists x. econstructor; eauto.
    econstructor; eauto. auto. auto. intro. dependent destruction H4.
    inv H9. exfalso; auto. inv H9. }
   {copy H8. eapply IHrewind in H8; auto. invertHyp.
    exists x. econstructor; eauto. dependent destruction H5.
    {eapply commitUnowned in H10; eauto. 
     inv H3. eapply r_readStepInvalid; eauto. constructor.
     constructor. auto. intro. inv H8. }
    {inv H3.
     {eapply commitMaybeOwned in H10; eauto. inv H10. 
      {eapply r_readStepInvalid; eauto. constructor. auto. constructor.
       auto. }
      {eapply r_readStepInvalid; eauto. constructor. constructor.
       auto. }
     }
     {eapply commitMaybeOwned in H10; eauto. inv H10.
      {econstructor; eauto. constructor. auto. constructor. auto. }
      {econstructor; eauto. constructor. auto. constructor. auto. }
     }
    }
   }
   {eapply commitWriteNI in H6; eauto. invertHyp. eapply IHrewind in H8; eauto.
    invertHyp. exists x1. econstructor; eauto. econstructor; eauto. }
   {eapply IHrewind in H4. invertHyp. exists x. econstructor. eauto.
    eapply r_atomicIdemStep; eauto. auto. auto. auto. }
   {eapply IHrewind in H4. invertHyp. exists x. econstructor. eauto.
    eapply r_betaStep; eauto. auto. auto. auto. }
  }   
Qed. 
          
Theorem commitRewindNI : forall tid b rv e0 C L H T chkpnt HI HV,
    @validate tid rv C e0 b L H (commit chkpnt HI HV) ->
    Disjoint nat (Singleton nat tid) (ids T) ->
    poolRewind C H T -> poolRewind (S C) HV T.
Proof. 
  intros. induction H2.
  {constructor. auto. }
  {assert(tid <> tid0). intro. subst. inv H1. specialize (H5 tid0).
   apply H5. solveIn. eapply commitRewindSingleNI in H2; eauto.
   invertHyp. econstructor; eauto. }
  {constructor; auto.
   {apply IHpoolRewind1. constructor. intros. intro. inv H3.
    inv H1. specialize (H3 x). apply H3. solveIn. }
   {apply IHpoolRewind2. constructor. intros. intro. inv H3.
    inv H1. specialize (H3 x). apply H3. solveIn. }
  }
Qed. 
  
Theorem writeSingleNI : forall b' b tid rv e0 L H H' e l v v' tid' rv' L' lock lock' L'',
    @acquireLock l v' tid' rv' b' L' lock lock' L'' ->
    rewind H' (txThread false tid rv e0 NilLog e0) H
           (txThread b tid rv e0 L e) ->
    H l = Some(v', lock) -> tid' <> tid ->
    exists H'', rewind H'' (txThread false tid rv e0 NilLog e0) (update H l v lock')
                  (txThread b tid rv e0 L e).
Proof. 
  intros. genDeps{{l; v'; tid'; rv'; L'; lock; lock'; L''; b'; v}}. 
  dependent induction H1; intros.
  {repeat econstructor. }
  {dependent destruction H0.
   {copy H6. eapply IHrewind with (v := v0) in H6; auto. invertHyp.
    exists x. destruct (Nat.eq_dec l l0).
    {subst. transEq. invertEq.
     dependent destruction H4; dependent destruction H8. 
     {exfalso; auto. }
     {econstructor; eauto. eapply r_readStepInvalid; eauto.
      Focus 2. heapUnfold. simplEq l0 l0. auto. constructor.
      auto. constructor; auto. constructor. }
    }
    {econstructor; eauto. eapply r_readChkpnt; eauto. heapUnfold. simplEq l0 l.
     eauto. }
   }
   {copy H6. eapply IHrewind with (v := v0) in H6; auto. invertHyp.
    exists x. destruct (Nat.eq_dec l l0).
    {subst. transEq. invertEq.
     dependent destruction H4; dependent destruction H8. 
     {exfalso; auto. }
     {econstructor; eauto. eapply r_readStepInvalid; eauto.
      Focus 2. heapUnfold. simplEq l0 l0. auto. constructor.
      auto. constructor; auto. constructor. }
    }
    {econstructor; eauto. eapply r_readNoChkpnt; eauto. heapUnfold. simplEq l0 l.
     eauto. }
   }
   {copy H8. eapply IHrewind with (v := v0) in H8; auto. invertHyp.
    exists x. destruct (Nat.eq_dec l l0).
    {subst. transEq. invertEq.
     dependent destruction H10; dependent destruction H5.
     {inv H3.
      {econstructor; eauto. eapply r_readStepInvalid; eauto.
       Focus 2. heapUnfold. simplEq l0 l0. auto. constructor.
       auto. constructor; auto. }
      {econstructor; eauto. eapply r_readStepInvalid; eauto.
       Focus 2. heapUnfold. simplEq l0 l0. eauto. constructor.
       auto. constructor. auto. }
     }
     {econstructor; eauto. eapply r_readStepInvalid. eauto. Focus 2.
      heapUnfold. simplEq l0 l0. auto. constructor. auto. constructor.
      auto. auto. }
    }
    {econstructor; eauto. eapply r_readStepInvalid. eauto. Focus 2.
     heapUnfold. simplEq l0 l. eauto. auto. auto. auto. }
   }
   {(*r_writelocked*)
     heapUnfold. destruct (Nat.eq_dec l l0).
     {invertEq. dependent destruction H4; dependent destruction H6; exfalso; auto. }
     {copy H6. eapply IHrewind in H6; eauto. invertHyp. exists x.
      econstructor; eauto. rewrite updatecomm; auto. econstructor; eauto.
      heapUnfold. simplEq l0 l. auto. }
   }
   {eapply IHrewind in H4; auto. invertHyp. exists x. econstructor; eauto.
    eapply r_atomicIdemStep; eauto. }
   {eapply IHrewind in H4; auto. invertHyp. exists x. econstructor; eauto.
    eapply r_betaStep; eauto. }
  }
Qed. 
  
Theorem writeNI : forall b lock lock' L' l v v' tid rv  C L H T,
    Disjoint nat (Singleton nat tid) (ids T) ->
    @acquireLock l v' tid rv b L lock lock' L' ->
    H l = Some(v', lock) ->
    poolRewind C H T -> poolRewind C (update H l v lock') T.
Proof.
  intros. induction H3.
  {repeat constructor. auto. }
  {assert(tid <> tid0). intro. subst. inv H0. specialize (H6 tid0).
   apply H6. solveIn. eapply writeSingleNI in H3; eauto. invertHyp.
   econstructor; eauto. }
  {constructor. auto.
   {apply IHpoolRewind1. constructor. intros. intro. inv H4.
    inv H0. specialize (H4 x). apply H4. solveIn. }
   {apply IHpoolRewind2. constructor. intros. intro. inv H4.
    inv H0. specialize (H4 x). apply H4. solveIn. }
  }
Qed.