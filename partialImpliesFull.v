Require Export stepPreservesRewind.  

(*
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


 *)

(*simulate a replay relation under full abort semantics as long as the endpoint
**log is valid*)
Theorem replayFMulti : forall H C e0 L e L' e' H', 
                         replay H C (Some(C,e0),L,e) (Some(C,e0),L',e') ->
                         validate L' H (commit H') -> 
                         f_multistep C H (Single(Some(C,e0),L,e)) C H 
                                     (Single(Some(C,e0),L',e')). 
Proof.
  intros. dependent induction H0.  
  {constructor. }
  {inv H0.
   {econstructor. eapply c_transStep. econstructor; eauto.
    eapply IHreplay; eauto. }
   {omega. }
   {econstructor. eapply c_transStep. eapply t_readInDomainStep; eauto.
    eapply IHreplay; eauto. }
   {econstructor. eapply c_transStep. eapply t_writeStep; eauto.
    eapply IHreplay; eauto. }
   {econstructor. eapply c_transStep. eapply t_atomicIdemStep; eauto.
    eapply IHreplay; eauto. }
   {econstructor. eapply c_transStep. eapply t_betaStep; eauto.
    eapply IHreplay; eauto. }
  }
Qed. 
                              
(*full abort can simulate partial abort*)
Theorem partialImpliesFull : forall C H T C' H' T', 
                               p_step C H T C' H' T' -> poolRewind C H T ->
                               f_multistep C H T C' H' T'. 
Proof.
  intros. induction H0.
  {inv H0. econstructor. eapply c_liftedStep. econstructor.
   eauto. inv H1. eapply rewindAbort in H2; eauto.
   eapply validateValidate in H3. invertHyp.
   eapply rewindNewerStamp in H2; eauto. eapply replayFMulti.
   rewrite <- rewindIFFReplay. eauto. eauto. }
  {inv H0.
   {econstructor. eapply c_transStep. econstructor; eauto. constructor. }
   {econstructor. eapply c_transStep. econstructor; eauto. constructor. }
   {econstructor. eapply c_transStep. econstructor; eauto. constructor. }
   {econstructor. eapply c_transStep. eapply t_atomicIdemStep; eauto. constructor. }
   {econstructor. eapply c_transStep. eapply t_betaStep; eauto. constructor. }
  }
  {eapply c_multi_L. eapply IHc_step. inv H1. auto. }
  {inv H1. eapply c_multi_R. eapply IHc_step. auto. }
  {econstructor. eapply c_forkStep; eauto. constructor. }
  {econstructor. eapply c_allocStep; eauto. constructor. }
  {econstructor. eapply c_commitStep; eauto. constructor. }
  {econstructor. eapply c_atomicStep; eauto. econstructor. }
  {econstructor. eapply c_betaStep; eauto. econstructor. }
  {econstructor. eapply c_tsExtend; eauto. constructor. }
Qed. 

(*generalize to multistep*)
Theorem partialImpliesFullMulti : forall C H T C' H' T', 
                               p_multistep C H T C' H' T' -> poolRewind C H T ->
                               f_multistep C H T C' H' T'. 
Proof.
  intros. induction H0. 
  {constructor. }
  {copy H0. eapply p_stepRewind in H0; auto. 
   apply IHc_multistep in H0. eapply partialImpliesFull in H3; eauto.
   eapply c_multi_trans; eauto. }
Qed. 



