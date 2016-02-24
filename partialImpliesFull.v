Require Export stepPreservesRewind.  

(*if the endpoint of a replay derivation can be validated, then the 
**start point can be validated too*)
Theorem replayCommit : forall S L H L' S' H' e0 e e', 
                         replay H (Some(S,e0),L,e) (Some(S,e0),L',e') ->
                         validate S L' H S' (commit H') -> 
                         exists H'', validate S L H S' (commit H'').
Proof.
  intros. dependent induction H0. 
  {eauto. }
  {inv H0; eauto. 
   {eapply IHreplay in H2;[idtac|eauto|eauto]. invertHyp. inv H0. eauto. }
   {eapply IHreplay in H2;[idtac|eauto|eauto]. invertHyp. inv H0. eauto. }
   {eapply IHreplay in H2;[idtac|eauto|eauto]. invertHyp. inv H0. eauto. }
  }
Qed. 

(*simulate a replay relation under full abort semantics as long as the endpoint
**log is valid*)
Theorem replayFMulti : forall H S C C' e0 L e L' S' e' H', 
                         replay H (Some(S,e0),L,e) (Some(S,e0),L',e') ->
                         validate S L' H S' (commit H') -> S < C ->
                         f_multistep C' H (Single(Some(C,e0),L,e)) C' H 
                                     (Single(Some(C,e0),L',e')). 
Proof. 
  intros. dependent induction H0. 
  {constructor. }
  {inv H0. 
   {econstructor. eapply f_transStep. eapply t_readStep; eauto. omega. eauto. }
   {eapply replayCommit in H1; eauto. invertHyp. inv H0. lookupSame. omega. }
   {econstructor. eapply f_transStep. eapply t_readInDomainStep; eauto. eauto. }
   {econstructor. eapply f_transStep. eapply t_writeStep; eauto. intros c. 
    inv c. eauto. }
   {econstructor. eapply f_transStep. eapply t_atomicIdemStep; eauto. intros c. 
    inv c. eauto. }
   {econstructor. eapply f_transStep. eapply t_betaStep; eauto. intros c. 
    inv c. eauto. }
  }
Qed. 

(*full abort can simulate partial abort*)
Theorem partialImpliesFull : forall C H T C' H' T', 
                               p_step C H T C' H' T' -> poolRewind C H T ->
                               f_multistep C H T C' H' T'. 
Proof.
  intros. induction H0.
  {econstructor. eapply f_transStep. eauto. constructor. }
  {inv H1. apply IHp_step in H4. apply f_multi_L. auto. }
  {inv H1. apply IHp_step in H5. apply f_multi_R. auto. }
  {inv H1. econstructor. eapply f_forkStep; eauto. constructor. }
  {inv H3. 
   {copy H12. inv H1. eapply abortRewind in H12; eauto. copy H3. 
    eapply validateValidate in H1. invertHyp. econstructor. 
    eapply f_eagerAbort; eauto. econstructor. eauto. 
    rewrite rewindIFFReplay in H12. eapply replayFMulti; eauto. }
   {inv H1. econstructor. eapply f_eagerAbort; eauto.
    eapply validateAbortRead; eauto. rewrite rewindIFFReplay in H7. 
    eapply decomposeEq in H4. subst. eapply replayFMulti; eauto. }
  }
  {inv H1. copy H0. eapply abortRewind in H1; eauto. copy H0. 
   eapply validateValidate in H2. invertHyp. econstructor. 
   eapply f_abortStep; eauto. rewrite rewindIFFReplay in H1. 
   eapply replayFMulti; eauto. }
  {econstructor. eapply f_allocStep; eauto. constructor. }
  {econstructor. eapply f_commitStep; eauto. constructor. }
  {econstructor. eapply f_atomicStep; eauto. constructor. }
  {econstructor. eapply f_betaStep; eauto. constructor. }
Qed. 

(*generalize to multistep*)
Theorem partialImpliesFullMulti : forall C H T C' H' T', 
                               p_multistep C H T C' H' T' -> poolRewind C H T ->
                               f_multistep C H T C' H' T'. 
Proof.
  intros. induction H0. 
  {constructor. }
  {copy H0. apply p_stepRewind in H0; auto. apply IHp_multistep in H0.
   eapply partialImpliesFull in H3; eauto. eapply f_multi_trans; eauto. }
Qed. 



