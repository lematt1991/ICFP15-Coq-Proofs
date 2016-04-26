Require Export stepPreservesRewind.  

Theorem validateNewerStamp : forall b tid rv rv' wv e0 L H chkpnt HI HV,
    validate tid rv wv e0 L H (commit chkpnt HI HV) -> rv' >= rv ->
    @validate tid rv' wv e0 b L H (commit chkpnt HI HV).   
Proof.
  intros b tid rv rv' wv e0 L H chkpnt HI HV H0 H1.
  remember (commit chkpnt HI HV). genDeps{{chkpnt; HI; HV; rv'}}.
  induction H0; intros; invertEq. (*not sure why dependent induction doesn't work here...*)
  {constructor. }
  {eapply validChkpnt; eauto. inv H1; constructor; auto. omega. }
  {eapply validRead; eauto. inv H1; econstructor; eauto. omega. }
  {eapply validWrite; eauto. omega. }
Qed. 
 
(*simulate a replay relation under full abort semantics as long as the endpoint
**log is valid*)
Theorem replayFMulti : forall b b' H C C' e0 L e L' e' H' chkpnt tid HI HV, 
                         rewind H (txThread b tid C e0 L e) H' (txThread b' tid C e0 L' e') ->
                         validate tid C C e0 L' H' (commit chkpnt HI HV) -> 
                         multistep_rev f_step C' H (Single(txThread b tid C e0 L e)) C' H' 
                                     (Single(txThread b' tid C e0 L' e')). 
Proof.
  intros b b' H C C' e0 L e L' e' H' chkpnt tid HI HV H0 H1.
  genDeps{{chkpnt; HI; HV; C'}}. dependent induction H0; intros.
  {constructor. }
  {dependent destruction H1.
   {invertHyp. econstructor. eauto. unfold f_step.
    eapply c_transStep. econstructor; eauto. }
   {invertHyp. econstructor. eauto. unfold f_step.
    eapply c_transStep. econstructor; eauto. }
   {dependent destruction H6; invertHyp.
    {econstructor; eauto. transEq. invertEq. exfalso.
     eapply validInvalidStamp; eauto. }
    {econstructor; eauto. transEq. invertEq. exfalso.
     eapply validInvalidStamp; eauto. }
   }
   {eapply validateAcquiredLock in H5; eauto. invertHyp. econstructor.
    eauto. eapply c_transStep. eapply t_writeLocked; eauto. }
   {econstructor. eauto. eapply c_transStep. eapply t_atomicIdemStep; eauto. }
   {econstructor. eauto. eapply c_transStep. eapply t_betaStep; eauto. }
  }
Qed. 

Theorem falseLogHeapsSame : forall tid rv wv e0 L H chkpnt HI HV,
    @validate tid rv wv e0 false L H (commit chkpnt HI HV) ->
    H = HI /\ H = HV.
Proof.
  intros. dependent induction H0; auto. 
Qed. 

Theorem validateValidatePropAbort :
  forall b l tid rv wv e0 HI v' lock H HV L chkpnt,
    validStamp tid rv lock -> Log.notIn l b L ->
    validate tid rv wv e0 L H (commit chkpnt HI HV) ->
    validate tid rv wv e0 L (update H l v' lock) (commit chkpnt (update HI l v' lock) (update HV l v' lock)). 
Proof.
  intros. remember (commit chkpnt HI HV).
  genDeps{{chkpnt; HI; HV; v'; lock; l}}.
  induction H2; intros; inv Heqv.
  {constructor. }
  {invertHyp. destruct (Nat.eq_dec l l0).
   {subst. destruct chkpnt. econstructor. heapUnfold. simplEq l0 l0. eauto. 
    inv H4. constructor. constructor; auto. eauto. }
   {destruct chkpnt. econstructor. heapUnfold. simplEq l0 l. eauto.
    auto. eauto. }
  }
  {invertHyp. destruct (Nat.eq_dec l l0).
   {subst. econstructor. heapUnfold. simplEq l0 l0. eauto. 
    inv H4. constructor. constructor; auto. eauto. }
   {econstructor. heapUnfold. simplEq l0 l. eauto.
    auto. eauto. }
  }
  {invertHyp. rewrite updatecomm.
   replace (update (update HV l v (Unlocked wv)) l0 v'0 lock) with
   (update (update HV l0 v'0 lock) l v (Unlocked wv)). 
   econstructor; eauto. heapUnfold. simplEq l0 l. eauto.
   apply updatecomm; auto. apply neqSymm. auto. }
Qed. 

Definition getChkpnt res :=
  match res with
  |abort (e', L) H => L
  |commit (e', L) HI HV => L
  end. 

Theorem notInChkpnt : forall b tid rv wv e0 L H res l,
    Log.notIn l b L -> validate tid rv wv e0 L H res ->
    Log.notIn l false (getChkpnt res). 
Proof.
  intros. induction H1; simpl; auto; dependent destruction H0; auto. 
  {destruct chkpnt. simpl in *. inv H2. }
  {destruct chkpnt. invertHyp. eauto. }
  {destruct chkpnt. invertHyp. eauto. }
  {invertHyp. }
Qed. 


Theorem validateNoWrites : forall tid rv wv e0 L H chkpnt HI HV,
    @validate tid rv wv e0 false L H (commit chkpnt HI HV) ->
    H = HI /\ H = HV.
Proof.
  intros. dependent induction H0; auto.
Qed. 
  
Theorem commitChkpnt : forall tid rv b wv e0 L H e' L' HI HV,
    @validate tid rv wv e0 b L H (commit (e', L') HI HV) ->
    exists chkpnt, validate tid rv wv e0 L' HI (commit chkpnt HI HI).
Proof. 
  intros. remember (commit (e', L') HI HV). 
  genDeps{{e'; L'; HI; HV}}. induction H0; intros; inv Heqv; eauto. 
  {repeat econstructor. }
  {(*valid checkpoint*)
    copy H2.  apply validateNoWrites in H2. invertHyp. subst. eauto. }
  {assert(commit (e', L') HI HV = commit (e', L') HI HV). auto.
   apply IHvalidate in H4. invertHyp. exists x. destruct x. 
   eapply validateValidatePropAbort. constructor. auto.
   eapply notInChkpnt in H2; eauto. simpl in H2. auto. auto. }
Qed. 

Theorem validateValidate : forall tid rv b wv e0 L H e' L' H',
    @validate tid rv wv e0 b L H (abort (e', L') H') ->
    exists chkpnt, validate tid rv wv e0 L' H' (commit chkpnt H' H').
Proof.
  intros. remember (abort (e',L') H'). genDeps{{e'; L'; H'}}.
  induction H0; intros.
  {inv Heqv. }
  {inv Heqv. }
  {inv Heqv. eapply commitChkpnt in H2; eauto. }
  {inv Heqv. }
  {inv Heqv. eapply commitChkpnt in H2; eauto. }
  {inv Heqv. }
  {inv Heqv. eauto. }
  {(*propogate abort*)
    invertEq. assert(abort (e', L') HI = abort (e', L') HI). auto.
    apply IHvalidate in H4. invertHyp. exists x.  
    eapply validateValidatePropAbort; eauto.
    constructor. auto. eapply notInChkpnt in H2; eauto. simpl in *. auto. }
Qed. 

(*full abort can simulate partial abort*)
Theorem partialImpliesFull : forall C H T C' H' T', 
                               p_step C H T C' H' T' -> poolRewind C H T ->
                               f_multistep C H T C' H' T'. 
Proof.
  intros. induction H0.
  {inv H0. dependent destruction H1. econstructor.
   eapply c_liftedStep. eapply f_abortStep; eauto. copy H0.
   eapply validateRewindHeapEq in H0; eauto. simpl in *.
   subst. copy H4. eapply abortRewind in H4; eauto; try omega.
   eapply validateValidate in H3. invertHyp.
   rewrite multistep_rev_eq. eapply validateNewerStamp in H5.
   eapply replayFMulti; eauto. omega. }
  {econstructor. eapply c_transStep; eauto. constructor. }
  {inv H1. eapply IHc_step in H5. eapply multi_L. eauto. } 
  {inv H1. eapply IHc_step in H6. eapply multi_R. eauto. }
  {econstructor. eapply c_forkStep; eauto. constructor. } 
  {econstructor. eapply c_allocStep; eauto. constructor. }
  {econstructor. eapply c_commitStep; eauto. constructor. }
  {econstructor. eapply c_atomicStep; eauto. constructor. }
  {econstructor. eapply c_betaStep; eauto. constructor. }
  {econstructor. eapply c_tsExtend; eauto. constructor. }
Qed. 

(*generalize to multistep*)
Theorem partialImpliesFullMulti : forall C H T C' H' T', 
                               p_multistep C H T C' H' T' -> poolRewind C H T ->
                               f_multistep C H T C' H' T'. 
Proof.
  intros. induction H0. 
  {constructor. }
  {copy H0. apply p_stepRewind in H0; auto. apply IHmultistep in H0.
   eapply partialImpliesFull in H3; eauto. eapply multi_trans; eauto. }
Qed. 



