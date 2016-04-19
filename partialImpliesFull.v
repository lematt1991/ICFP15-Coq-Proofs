Require Export stepPreservesRewind.  

Theorem validateNewerStamp : forall b tid rv rv' wv e0 L H chkpnt HI HV,
    validate tid rv wv e0 L H (commit chkpnt HI HV) -> rv' >= rv ->
    @validate tid rv' wv e0 b L H (commit chkpnt HI HV).   
Proof.
  intros b tid rv rv' wv e0 L H chkpnt HI HV H0 H1.
  remember (commit chkpnt HI HV). genDeps{{chkpnt; HI; HV; rv'}}.
  induction H0; intros; try solve[inv Heqv]. (*not sure why dependent induction doesn't work here...*)
  {constructor. }
  {inv Heqv. eapply validChkpnt; eauto. inv H1; constructor; eauto.
   omega. }
  {inv Heqv. eapply validRead; eauto. inv H1; econstructor; eauto. omega. }
  {inv Heqv. eapply validWrite; eauto. }
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
   {dependent destruction H5. econstructor. eauto. unfold f_step.
    eapply c_transStep. econstructor; eauto. }
   {dependent destruction H5. econstructor. eauto. unfold f_step.
    eapply c_transStep. econstructor; eauto. }
   {dependent destruction H5. transEq. invertEq. exfalso.
    eapply validInvalidStamp; eauto. }
   {eapply validateAcquiredLock in H5; eauto. invertHyp. econstructor.
    eauto. eapply c_transStep. eapply t_writeLocked; eauto. }
   {econstructor. eauto. eapply c_transStep. eapply t_atomicIdemStep; eauto. }
   {econstructor. eauto. eapply c_transStep. eapply t_betaStep; eauto. }
  }
Qed. 

Ltac invertEq :=
  match goal with
    | H1:?a = ?b, H2:?a = ?c |- _ => rewrite H1 in H2; inv H2
  end. 

Theorem falseLogHeapsSame : forall tid rv wv e0 L H chkpnt HI HV,
    @validate tid rv wv e0 false L H (commit chkpnt HI HV) ->
    H = HI /\ H = HV.
Proof.
  intros. dependent induction H0; auto. 
Qed. 
  
Theorem commitChkpnt : forall tid rv b wv e0 L H e' L' HI HV,
    @validate tid rv wv e0 b L H (commit (e', L') HI HV) ->
    validate tid rv wv e0 L' HI (commit (e', L') HI HI).
Proof.
  intros. remember (e', L'). remember (commit p HI HV).
  genDeps{{e'; L'; HI; HV; p}}. induction H0; intros.
  {subst. inv Heqv. constructor. }
Admitted.


Theorem validateValidate : forall tid rv b wv e0 L H e' L' H',
    @validate tid rv wv e0 b L H (abort (e', L') H') ->
    exists HV, validate tid rv wv e0 L' H' (commit (e', L') H' HV).
Proof.
  intros. remember (abort (e',L') H'). genDeps{{e'; L'; H'}}.
  induction H0; intros; try solve[inv Heqv]. 
  {(*invalidChkpnt*) inv Heqv. eapply commitChkpnt in H2; eauto. }
  {inv Heqv. eapply commitChkpnt in H2. econstructor. eauto. }
  {inv Heqv. eauto. }
  {inv Heqv. assert(abort (e', L') HI = abort (e', L') HI). auto.
   eapply IHvalidate in H2. invertHyp. Admitted. 



   
(*full abort can simulate partial abort*)
Theorem partialImpliesFull : forall C H T C' H' T', 
                               p_step C H T C' H' T' -> poolRewind C H T ->
                               f_multistep C H T C' H' T'. 
Proof.
  intros. induction H0.
  {inv H0. econstructor. unfold f_step. eapply c_liftedStep.
   eapply f_abortStep; eauto. dependent destruction H1.
   copy H3. eapply abortRewind in H2; eauto. 
   eapply validateRewindHeapEq in H2; eauto. subst. copy H3.
   eapply validateValidate in H3; eauto.
   invertHyp. eapply validateNewerStamp with (rv' := C) in H5; eauto.
   eapply replayFMulti in H5; eauto.
   rewrite multistep_rev_eq. eauto. omega. }
  {econstructor. eapply c_transStep; eauto. constructor. }
  {inv H1. eapply IHc_step in H4. eapply multi_L. eauto. } 
  {inv H1. eapply IHc_step in H5. eapply multi_R. eauto. }
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



