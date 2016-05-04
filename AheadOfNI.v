Require Export stepPreservesRewind. 

Inductive AheadOf (C : nat) (H : heap) : pool -> pool -> Prop :=
| aheadOfNoTX : forall tid e,
    tid < C -> AheadOf C H (Single(noTXThread tid e)) (Single(noTXThread tid e))
| aheadOfTXRO : forall tid rv e0 L L' e e',
    tid < C -> rv < C -> 
    replay H (txThread false tid rv e0 L e) H (txThread false tid rv e0 L' e') ->
    AheadOf C H (Single(txThread false tid rv e0 L e)) (Single(txThread false tid rv e0 L' e'))
| aheadOfTXRW : forall tid rv b e0 L e,
    tid < C -> rv < C ->
    AheadOf C H (Single(txThread b tid rv e0 L e)) (Single(txThread b tid rv e0 L e))
| replayPar : forall T1 T2 T1' T2',
    Disjoint nat (ids T1) (ids T2) ->
    AheadOf C H T1 T1' -> AheadOf C H T2 T2' ->
    AheadOf C H (Par T1 T2) (Par T1' T2'). 



  
Theorem abortAheadOfNI : forall C tid b rv wv e0 L H T chkpnt HI T',
    @validate tid rv wv e0 b L H (abort chkpnt HI) ->
    Disjoint nat (Singleton nat tid) (ids T) ->
    AheadOf C H T T' -> AheadOf (S C) HI T T'. 
Proof.
  intros. genDeps{{tid; rv; wv; e0; L; b; HI; chkpnt}}. induction H2; intros.
  {constructor. auto. }
  {assert(tid0 <> tid). intro. subst. inv H4. specialize (H5 tid).
   apply H5. constructor; constructor. copy H3.
   eapply abortReleaseLocks in H3; eauto. simpl in *. rewrite <- rewindIFFReplay in H2.  
   eapply abortRewindSingleNI in H3; eauto. invertHyp. econstructor; auto.
   rewrite <- rewindIFFReplay. copy H7. eapply rewindNoWrites in H7; eauto.
   subst. assumption. }
  {constructor; auto. }
  {constructor. simpl in *. auto. eapply IHAheadOf1; eauto. simpl in *.
   constructor. intros. intro. solveIn. inv H2. specialize (H3 x). apply H3.
   solveIn. eapply IHAheadOf2; eauto. constructor. intros.
   intro. solveIn. inv H2. specialize (H3 x). apply H3. solveIn. }
Qed. 
 
Theorem writeAheadOfNI : forall b lock lock' L' l v v' tid rv T' C L H T,
    Disjoint nat (Singleton nat tid) (ids T) ->
    @acquireLock l v' tid rv b L lock lock' L' ->
    H l = Some(v', lock) ->
    AheadOf C H T T' -> AheadOf C (update H l v lock') T T'. 
Proof.
  intros. induction H3.
  {repeat constructor. auto. }
  {assert(tid <> tid0). intro. subst. inv H0. specialize (H6 tid0).
   apply H6. solveIn. rewrite <- rewindIFFReplay in H5.
   eapply writeSingleNI with (v := v) in H5; eauto. invertHyp.
   econstructor; eauto. rewrite <- rewindIFFReplay. copy H7.
   eapply rewindNoWrites in H7; eauto. subst. assumption. }
  {constructor; auto. }
  {constructor. auto.
   {apply IHAheadOf1. constructor. intros. intro. inv H4.
    inv H0. specialize (H4 x). apply H4. solveIn. }
   {apply IHAheadOf2. constructor. intros. intro. inv H4.
    inv H0. specialize (H4 x). apply H4. solveIn. }
  }
Qed.


Theorem AheadOfNewerStamp : forall C C' H T T',
    AheadOf C H T T' -> C' >= C -> AheadOf C' H T T'. 
Proof.
  intros. induction H0; eauto; try solve[econstructor; eauto; omega]. 
Qed. 

Theorem AheadOfAlloc : forall C H T l v T',
    H l = None -> 
    AheadOf C H T T' ->
    AheadOf C (update H l v (Unlocked 0)) T T'.
Proof.
  intros. genDeps{{l; v}}. induction H1; intros.
  {constructor. auto. }
  {rewrite <- rewindIFFReplay in H2. eapply rewindAllocSingle with(v := v) in H2; eauto.
   invertHyp. econstructor; eauto. rewrite <- rewindIFFReplay. copy H4. 
   eapply rewindNoWrites in H4; eauto. subst. eauto. }
  {constructor; auto. }
  {econstructor; eauto. }
Qed.

Theorem commitAheadOfNI : forall tid b rv e0 C L H T chkpnt HI HV T',
    @validate tid rv C e0 b L H (commit chkpnt HI HV) ->
    Disjoint nat (Singleton nat tid) (ids T) ->
    AheadOf C H T T' -> AheadOf (S C) HV T T'.
Proof. 
  intros. induction H2.
  {constructor. auto. }
  {assert(tid <> tid0). intro. subst. inv H1. specialize (H5 tid0).
   apply H5. solveIn. rewrite <- rewindIFFReplay in H4.
   eapply commitRewindSingleNI in H0; eauto.  
   invertHyp. econstructor; eauto. rewrite <- rewindIFFReplay. copy H6.
   eapply rewindNoWrites in H6; eauto. subst. assumption. }
  {constructor; auto. }
  {constructor; auto.
   {apply IHAheadOf1. constructor. intros. intro. inv H3.
    inv H1. specialize (H3 x). apply H3. solveIn. }
   {apply IHAheadOf2. constructor. intros. intro. inv H3.
    inv H1. specialize (H3 x). apply H3. solveIn. }
  }
Qed. 

Theorem AheadOfNI : forall C C' H H' T1 T1' T2 T2',
    f_step C H T1 C' H' T1' -> AheadOf C H T2 T2' ->
    Disjoint nat (ids T1) (ids T2) -> AheadOf C' H' T2 T2'.
Proof.
  intros. genDeps{{T2; T2'}}. induction H0; intros; eauto. 
  {inv H0. eapply abortAheadOfNI in H4; eauto. }
  {dependent destruction H0; eauto. eapply writeAheadOfNI; eauto. }
  {simpl in *. eapply IHc_step; eauto. constructor. intros.
   intro. inv H2. specialize (H4 x). apply H4. constructor; solveIn. }
  {simpl in *. eapply IHc_step; eauto. constructor. intros.
   intro. inv H2. specialize (H4 x). apply H4. constructor; solveIn. }
  {simpl in *. eapply AheadOfNewerStamp; eauto. }
  {eapply AheadOfAlloc; eauto. }
  {simpl in *. eapply commitAheadOfNI; eauto. }
  {simpl in *. eapply AheadOfNewerStamp; eauto. }
  {simpl in *. eapply AheadOfNewerStamp; eauto. } 
Qed. 
