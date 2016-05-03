Require Export AheadOfNI.  
Require Export partialImpliesFull.

(*We can't go from a log with writes to one without.  This isn't a great name...*)
Theorem logMonotonic : forall H H' b tid rv e0 L e L' e',
    replay H (txThread true tid rv e0 L e) H' (txThread b tid rv e0 L' e') ->
    b = true. 
Proof.
  intros. dependent induction H0; auto.
  {dependent destruction H0; eauto. }
Qed. 

(*if a start state is invalid, then anywhere we can step to is also invalid*)
Theorem replayInvalid : forall H H' rv wv tid e0 L e L' e' chkpnt HI, 
                          replay H (txThread false tid rv e0 L e) H' (txThread false tid rv e0 L' e') ->
                          validate tid rv wv e0 L H (abort chkpnt HI) ->
                          validate tid rv wv e0 L' H (abort chkpnt HI).
Proof.
  intros. dependent induction H0; auto.
  dependent destruction H0; eauto. 
  {eapply IHreplay. eauto. eauto. eapply readPropAbort.
   eauto. constructor. }
  {eapply IHreplay. eauto. eauto. eapply readPropAbort.
   eauto. dependent destruction H4. constructor. }
  {eapply logMonotonic in H3. solveByInv. }
Qed. 

(* If we perform a timestamp extension in full abort, then we can either also
 * timestamp extened in partial abort, or we can partially abort.  Either
 * way we will still be ahead of full abort
 *)
Theorem AheadOfExtend : forall tid rv e0 L e''' L''' e H L' e' C,
    rewind H (txThread false tid rv e0 L e) H (txThread false tid rv e0 L' e') ->
    validate tid rv C e0 L H (commit (e''', L''') H H) -> C > rv ->
    exists e'' L'', 
    (validate tid rv C e0 L' H (commit (e'', L'') H H) /\
     rewind H (txThread false tid rv e0 L e) H (txThread false tid rv e0 L' e')) \/
    (validate tid rv C e0 L' H (abort (e'', L'') H) /\
     rewind H (txThread false tid C e0 L e) H (txThread false tid C e0 L'' e'')).
Proof.
  intros. genDeps{{e'''; L'''}}. 
  dependent induction H0; intros. 
  {econstructor. econstructor. left. split. eauto. constructor. }
  {dependent destruction H1. 
   {eapply IHrewind in H4; auto. invertHyp. inv H4; invertHyp.
    {econstructor. econstructor. left. split. econstructor; eauto.
     econstructor. eauto. econstructor; eauto. }
    {econstructor. econstructor. right. split. eapply readPropAbort; eauto.
     constructor. assumption. } eauto. 
   }
   {dependent destruction H5. copy H6. eapply IHrewind in H6; auto. invertHyp.
    inv H6; invertHyp.
    {econstructor. econstructor. right. split. econstructor; eauto.
     eapply rewindNewerStamp. eapply decomposeEq in H1. subst. eassumption.
     omega. eauto. }
    {econstructor. econstructor. right. split. eapply readPropAbort; eauto.
     constructor. assumption. } eauto. 
   }
   {eapply IHrewind in H2; auto. invertHyp. inv H2; invertHyp.
    {econstructor. econstructor. left. split; eauto. econstructor; eauto.
     eapply r_atomicIdemStep; eauto. }
    {econstructor. econstructor. right. split; eauto. } eauto. 
   }
   {eapply IHrewind in H2; auto. invertHyp. inv H2; invertHyp.
    {econstructor. econstructor. left. split; eauto. econstructor; eauto.
     eapply r_betaStep; eauto. }
    {econstructor. econstructor. right. split; eauto. } eauto. 
   }
  }
Qed. 

(*used for proving that two steps are the same*)
Ltac sameStep :=
  match goal with
  |H : decompose ?t ?E ?e, H' : decompose ?t ?E' ?e' |- _ =>
   eapply decomposeDeterministic in H; eauto; invertHyp; repeat invertEq
  end.

(*partial abort can simulate full abort*)
Theorem fullImpliesPartial : forall C H T C' H' T' PT, 
    f_step C H T C' H' T' -> AheadOf C H T PT ->
    poolRewind C H PT -> poolRewind C H T ->
    exists PT', p_multistep C H PT C' H' PT' /\
           AheadOf C' H' T' PT'.
Proof.
  intros. generalize dependent PT. induction H0; intros. 
  {(*lifted step (full abort)*)
    inv H0. dependent destruction H3. dependent destruction H4. 
    {copy H0. eapply validateRewindHeapEq in H8; eauto. simpl in *.
     subst. eapply replayInvalid in H5; eauto.    
     assert(rewind H'0 (txThread false tid S e0 NilLog e0) H (txThread false tid S e0 L'0 e'0)).
     rewrite <- rewindIFFReplay in H7. eapply rewindTrans; eassumption.
     eapply abortRewind in H8; eauto; try omega. copy H5. 
     eapply validateValidate in H5. invertHyp. econstructor. split.
     eapply c_multi_step. eapply c_liftedStep. econstructor. eauto. 
     constructor. econstructor; eauto. rewrite <- rewindIFFReplay. assumption. }
    {copy H0. eapply validateRewindHeapEq in H0; eauto. simpl in *. subst. 
     econstructor. split. eapply c_multi_step. eapply c_liftedStep.
     econstructor; eauto. constructor. econstructor; auto. 
     eapply abortRewind in H5; eauto. rewrite <- rewindIFFReplay. auto. 
     omega. }
  }
  {(*transactional step*)
    dependent destruction H0.
    {(*checkpoint read*)
      dependent destruction H3. dependent destruction H6.
      {dependent destruction H8.
       {econstructor. split. eapply c_multi_step.
        eapply c_transStep. econstructor; eauto. constructor.
        econstructor; auto. constructor. }
       {dependent destruction H9; sameStep. 
        {transEq. invertEq. econstructor. split. constructor.
         econstructor; eauto. }
        {transEq. invertEq. exfalso. eapply validInvalidStamp; eauto. }
       }
      }
      {econstructor. split. eapply c_multi_step.
        eapply c_transStep. econstructor; eauto. constructor.
        econstructor; eauto. constructor. }
    }
    {(*non-checkpoint read*)
      dependent destruction H3. dependent destruction H6.
      {econstructor. split. eapply c_multi_step.
       eapply c_transStep. econstructor; eauto. constructor.
       econstructor; auto. }
    }
    {(*write*)
      dependent destruction H3. dependent destruction H6.
      {dependent destruction H8.
       {econstructor. split. eapply c_multi_step.
        eapply c_transStep. eapply t_writeLocked; eauto.
        constructor. econstructor; auto. }
       {dependent destruction H9; sameStep. exfalso.
        eapply logMonotonic in H11. solveByInv. }
      }
      {econstructor. split. eapply c_multi_step.
       eapply c_transStep. eapply t_writeLocked; eauto.
       constructor. econstructor; auto. }
    }
    {dependent destruction H3. dependent destruction H4.
     dependent destruction H6.
     {econstructor. split. eapply c_multi_step.
      eapply c_transStep. eapply t_atomicIdemStep; eauto.
      constructor. econstructor; auto. constructor. }
     {dependent destruction H6; sameStep. econstructor.
      split. constructor. econstructor; eauto. }
     {econstructor. split. eapply c_multi_step.
      eapply c_transStep. eapply t_atomicIdemStep; eauto.
      constructor. econstructor; auto. }
    }
    {dependent destruction H3. dependent destruction H4.
     dependent destruction H6.
     {econstructor. split. eapply c_multi_step.
      eapply c_transStep. eapply t_betaStep; eauto.
      constructor. econstructor; auto. constructor. }
     {dependent destruction H6; sameStep. econstructor.
      split. constructor. econstructor; eauto. }
     {econstructor. split. eapply c_multi_step.
      eapply c_transStep. eapply t_betaStep; eauto.
      constructor. econstructor; auto. }
    }
  }
  {inv H1. dependent destruction H2. inv H3. eapply IHc_step in H7; eauto.
   invertHyp. econstructor. split. eapply multi_L. eauto.
   econstructor; eauto. Focus 2. eapply AheadOfNI; eauto.
   eapply f_stepDisjoint. Focus 3. eassumption. auto. auto.
   auto. }
  {inv H1. inv H2. inv H3. eapply IHc_step in H9; eauto.
   invertHyp. econstructor. split. eapply multi_R. eauto.
   econstructor; eauto. Focus 2. eapply AheadOfNI; eauto.
   rewrite DisjointComm. auto. rewrite DisjointComm.
   eapply f_stepDisjoint. Focus 3. eauto. auto. auto.
   rewrite DisjointComm. auto. }
  {inv H1. inv H2. econstructor. split. eapply c_multi_step.
   eapply c_forkStep; eauto. constructor. repeat constructor; eauto.
   intros. intro. simpl in *. solveIn. omega. }
  {inv H2. inv H3. econstructor. split. eapply c_multi_step.
   eapply c_allocStep; eauto. constructor. constructor. auto. }
  {dependent destruction H3. dependent destruction H5.
   {dependent destruction H8. dependent destruction H7.
    {econstructor. split. eapply c_multi_step. eapply c_commitStep; eauto. 
     constructor. econstructor. omega. }
    {dependent destruction H7; sameStep. }
   }
   {dependent destruction H7. econstructor. split.
    eapply c_multi_step. eapply c_commitStep; eauto. constructor.
    econstructor. omega. }
  }
  {inv H1. inv H2. econstructor. split. eapply c_multi_step.
   eapply c_atomicStep; eauto. constructor. econstructor; eauto.
   constructor. }
  {inv H1. inv H2. econstructor. split. eapply c_multi_step.
   eapply c_betaStep; eauto. constructor. constructor; auto. }
  {dependent destruction H3. dependent destruction H4.
   {dependent destruction H7. copy H1. eapply rewindNoWrites in H1; eauto.
    subst. copy H7. eapply rewindNoWrites in H7; eauto. subst.
    copy H0. eapply validateNoWrites in H0; eauto. invertHyp. subst.
    destruct chkpnt. eapply AheadOfExtend in H7; eauto. Focus 2.
    rewrite rewindIFFReplay. eassumption. invertHyp. inv H0; invertHyp.
    {econstructor. split. eapply c_multi_step. eapply c_tsExtend. eauto.
     constructor. econstructor; auto. rewrite <- rewindIFFReplay.
     eapply rewindNewerStamp; eauto. omega. }
    {econstructor. split. eapply c_multi_step. eapply c_liftedStep.
     econstructor. eauto. constructor. econstructor; eauto.
     rewrite <- rewindIFFReplay. assumption. }
   }
   {econstructor. split. eapply c_multi_step. eapply c_tsExtend.
    eauto. constructor. econstructor; auto. }
  }
Qed. 





    

           

     
     

(*generalize step preserves rewind to thread pools*)
Theorem multistepPreservesRewind : forall C H T C' H' T',
                                poolRewind C H T -> p_multistep C H T C' H' T' ->
                                poolRewind C' H' T'. 
Proof.
  intros. induction H1. auto. apply IHmultistep.
  eapply p_stepRewind; eauto. 
Qed. 

(*generalize full implies partial to thread pools*)
Theorem fullImpliesPartialMulti : forall C H T C' H' T' PT, 
                               f_multistep C H T C' H' T' -> AheadOf C H T PT ->
                               poolRewind C H PT -> poolRewind C H T ->
                               exists PT', p_multistep C H PT C' H' PT' /\
                                           AheadOf C' H' T' PT'.
Proof.
  intros. generalize dependent PT. induction H0; intros. 
  {exists PT. split. constructor. auto. }
  {copy H0. eapply fullImpliesPartial in H0; eauto. invertHyp. 
   copy H0. apply multistepPreservesRewind in H0; auto. 
   eapply IHmultistep in H0; eauto. invertHyp. exists x0. split. 
   eapply multi_trans; eauto. auto. eapply f_stepRewind; eauto. }
Qed. 






