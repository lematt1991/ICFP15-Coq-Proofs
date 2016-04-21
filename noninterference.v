Require Export validateWrite.

Ltac heapUnfold := unfold lookup; unfold update.

Theorem notInUpdate : forall H l v lock l',
    (update H l v lock) l' = None ->
    H l' = None. 
Proof.
  intros. unfold update in H0. destruct (Nat.eq_dec l l').
  {inv H0. }
  {assumption.  }
Qed.

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
    {unfold lookup in *. subst. transEq. invertEq. }
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

(*if tid doesn't own the lock, than it cannot be released after aborting*)
Theorem lookupValidAbort : forall res b tid rv wv e0 L H l v lock,
    @validate tid rv wv e0 b L H res -> ~locked tid lock ->
    lookup H l = Some(v, lock) -> 
    lookup (invalidHeap res) l = Some(v, lock). 
Proof.
  intros. genDeps{{lock; v}}. induction H0; intros; simpl in *; eauto. 
  {heapUnfold. destruct (Nat.eq_dec l0 l).
   {subst. transEq. invertEq. exfalso. apply H2. constructor. }
   {eauto. }
  }
  {heapUnfold. destruct (Nat.eq_dec l0 l).
   {subst. transEq. invertEq. exfalso. apply H2. constructor. }
   {eauto. }
  }
Qed. 

Theorem lookupAbortLocked : forall res b tid rv tid' wv e0 L H l v oldV v',
    @validate tid rv wv e0 b L H res ->
    H l = Some(v, Locked tid' oldV v') ->
    ((invalidHeap res) l = Some(v, Locked tid' oldV v') \/
     (invalidHeap res) l = Some(v', Unlocked oldV)). 
Proof.
  intros. genDeps{{tid'; l; v; oldV; v'}}. induction H0; intros; simpl; auto. 
  {copy H2. eapply IHvalidate in H2. heapUnfold. destruct (Nat.eq_dec l l0).
   {subst. simpl in *. unfold lookup in *. transEq. invertEq. right. auto. }
   {auto. }
  }
  {copy H2. eapply IHvalidate in H2. heapUnfold. destruct (Nat.eq_dec l l0).
   {subst. simpl in *. unfold lookup in *. transEq. invertEq. right. auto. }
   {eauto. }
  }
Qed. 
 
Theorem abortRewindSingleNI : forall b' H H' HI b tid chkpnt rv e0 L e L' e0' rv' wv' tid',
    @validate tid' rv' wv' e0' b' L' H (abort chkpnt HI) ->
    rewind H' (txThread false tid rv e0 NilLog e0) H (txThread b tid rv e0 L e) ->
    exists H'', rewind H'' (txThread false tid rv e0 NilLog e0) HI (txThread b tid rv e0 L e) .
Proof.
  intros. genDeps{{tid'; rv'; wv'; e0'; L'; HI}}.
  dependent induction H1; intros.
  {repeat econstructor. }
  {dependent destruction H0.
   {(*r_readChkpnt*)
     copy H5. eapply IHrewind in H5. Focus 2. eauto. invertHyp.
     exists x. econstructor. eauto. econstructor; eauto.
     eapply lookupValidAbort in H6. Focus 3. eauto. 
     simpl in *. assumption. intro. inv H5. dependent destruction H4.
     admit. (*we need tid <> tid'*)
   }
   {(*r_readNoChkpnt*)
     copy H5. eapply IHrewind in H5. Focus 2. eauto. invertHyp.
     exists x. econstructor. eauto. econstructor; eauto.
     eapply lookupValidAbort in H6. Focus 3. eauto. 
     simpl in *. assumption. intro. inv H5. dependent destruction H4.
     admit. (*we need tid <> tid'*)
   }
   {(*r_readStepInvalid*)
     copy H6. eapply IHrewind in H6. Focus 2. eauto. invertHyp. exists x.
     econstructor. eauto. dependent destruction H5.
     {eapply lookupValidAbort in H7; eauto. simpl in *.
      eapply r_readStepInvalid; eauto. constructor. auto. intro. inv H6. }
     {eapply lookupAbortLocked in H7. Focus 2. eauto. inv H7.
      {simpl in *. eapply r_readStepInvalid; eauto. constructor. auto. }
      {simpl in *. destruct (ge_dec rv s'). 
       {inv H3. econstructor; eauto. constructor. assumption. }
       {inv H3. eapply r_readStepInvalid; eauto. constructor. constructor.
        omega. }
      }
     }
   }
   {

     admit. }
   {eapply IHrewind in H3. Focus 2. eauto. invertHyp. exists x. econstructor.
    eauto. econstructor; eauto. }
   {eapply IHrewind in H3. Focus 2. eauto. invertHyp. exists x. econstructor.
    eauto. eapply r_betaStep; eauto. }
  }
Admitted. 

      
Theorem abortRewindNI : forall tid b rv wv e0 C L H T chkpnt HI,
    @validate tid rv wv e0 b L H (abort chkpnt HI) ->
    poolRewind C H T -> poolRewind (S C) HI T.
Proof.
  intros. genDeps{{tid; rv; wv; e0; L; b; HI}}.
  induction H1; intros.
  {constructor. }
  {eapply abortRewindSingleNI in H2; eauto. invertHyp. econstructor.
   eassumption. omega. }
  {constructor; eauto. }
Qed.

Theorem commitUnowned : forall b tid rv wv e0 L H chkpnt HI HV l v lock,
    @validate tid rv wv e0 b L H (commit chkpnt HI HV) ->
    H l = Some(v, lock) -> ~ locked tid lock ->
    HV l = Some(v, lock).
Proof.
  intros. remember (commit chkpnt HI HV). genDeps{{HI; HV; chkpnt; l; v; lock}}. 
  induction H0; intros; inv Heqv0; eauto. 
  {heapUnfold. destruct (Nat.eq_dec l l0).
   {subst. unfold lookup in *. transEq. invertEq. 
    exfalso. apply H2. constructor. }
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
  {heapUnfold. destruct (Nat.eq_dec l l0).
   {subst. unfold lookup in *. transEq. inv H0. auto. }
   {eauto. }
  }
Qed. 

Theorem commitRewindSingleNI : forall b' H H' HI b tid chkpnt rv e0 L e L' e0' rv' C tid' HV,
    @validate tid' rv' C e0' b' L' H (commit chkpnt HI HV) -> rv < C ->
    rewind H' (txThread false tid rv e0 NilLog e0) H (txThread b tid rv e0 L e) ->
    exists H'', rewind H'' (txThread false tid rv e0 NilLog e0) HV (txThread b tid rv e0 L e) .
Proof.
  intros. intros. genDeps{{tid'; rv'; C; e0'; L'; HI; HV}}.
  dependent induction H2; intros.
  {repeat econstructor. }
  {dependent destruction H0.
   {copy H6. eapply commitUnowned in H6; eauto. eapply IHrewind in H7.
    Focus 2. eauto. invertHyp. exists x. econstructor; eauto.
    econstructor; eauto. auto. intro. dependent destruction H4.
    {inv H8. (*we need tid <> tid'*) admit. }
    {inv H8. }
   }
   {copy H6. eapply commitUnowned in H6; eauto. eapply IHrewind in H7.
    Focus 2. eauto. invertHyp. exists x. econstructor; eauto.
    econstructor; eauto. auto. intro. dependent destruction H4.
    {inv H8. (*we need tid <> tid'*) admit. }
    {inv H8. }
   }
   {copy H7. eapply IHrewind in H7. Focus 2. eauto. invertHyp.
    exists x. econstructor; eauto. dependent destruction H5.
    {eapply commitUnowned in H8; eauto. 
     inv H3. eapply r_readStepInvalid; eauto. constructor.
     constructor. auto. intro. inv H7. }
    {inv H3. eapply commitMaybeOwned in H8; eauto. inv H8. 
     {eapply r_readStepInvalid; eauto. constructor. constructor.
      auto. }
     {eapply r_readStepInvalid; eauto. constructor. constructor.
      auto. }
    }
    auto. }
   {admit. }
   {eapply IHrewind in H4. invertHyp. exists x. econstructor. eauto.
    econstructor; eauto. auto. auto. }
   {eapply IHrewind in H4. invertHyp. exists x. econstructor. eauto.
    eapply r_betaStep; eauto. auto. auto. }
  }   
Admitted.

Theorem commitRewindNI : forall tid b rv e0 C L H T chkpnt HI HV,
    @validate tid rv C e0 b L H (commit chkpnt HI HV) ->
    poolRewind C H T -> poolRewind (S C) HV T.
Proof.
  intros. induction H1.
  {constructor. }
  {eapply commitRewindSingleNI in H1; eauto. invertHyp.
   econstructor; eauto. }
  {constructor; auto. }
Qed. 

   
