Require Export semantics. 
 
(*retrieve the stamp number from a heap location*)
Definition getStamp (x : location * term * lock) :=
  match x with
      |(_,_,s) => s
  end.  

(*if location l is present in heap H, then if we extend H with some number of
**locations, all of which have stamp C.  Then either we will get the same 
**result when looking up in the extended heap or we will get something that 
**has a timestamp of C*)
Theorem lookupExtension : forall H' l v S H C, 
                  lookup H l = Some(v, S) ->
                  Forall (fun x : TVar => getStamp x = Unlocked C) H' ->
                  lookup (H'++H) l = Some(v, S) \/
                  exists S' v', lookup (H'++H) l = Some(v', S') /\
                           S' = Unlocked C. 
Proof.
  induction H'; intros l v S H C HYP1 HYP2. 
  {simpl. auto. }
  {simpl in *. destruct a. destruct p. destruct (eq_nat_dec l l1). 
   {right. subst. repeat econstructor. inv HYP2. auto. }
   {inv HYP2. eapply IHH' in HYP1; eauto. }
  }
Qed. 

(*we can produce the same replay derivation under an extended heap, if everything
**in the extension has a timestamp greater than the thread being replayed and is unlocked*)
Theorem replayHeapExtension : forall H H' S e0 RS RS' WS WS' e e' C,
                      replay H (Some(S,e0),RS,WS,e) (Some(S,e0),RS',WS',e') -> S < C ->
                      Forall (fun x : TVar => getStamp x = Unlocked C) H' ->
                      replay (H'++H) (Some(S,e0),RS,WS,e) (Some(S,e0),RS',WS',e'). 
Proof.
  intros. dependent induction H0. 
  {constructor. }
  {inv H0. 
   {eapply lookupExtension with (H':=H') in H11; eauto. inv H11.
    {econstructor. eapply r_readStepValid; eauto. eauto. }
    {invertHyp. econstructor. eapply r_readStepInvalid; eauto. constructor.
     omega. eauto. }
   }
   {econstructor. eapply r_readStepValid; eauto. eauto. }
    {invertHyp. econstructor. eapply r_readStepInvalid; eauto. omega. eauto. }
   }
   {copy H8. eapply lookupExtension with (H':=H') in H0; eauto. inv H0. 
    {econstructor. eapply r_readStepInvalid; eauto. eauto. }
    {invertHyp. econstructor. eapply r_readStepInvalid; eauto. omega. eauto. }
   }
   {econstructor. eapply r_readInDomainStep; eauto. eauto. }
   {econstructor. eapply r_writeStep; eauto. eauto. }
   {econstructor. eapply r_atomicIdemStep; eauto. eauto. }
   {econstructor. eapply r_betaStep; eauto. eauto. }
  }
Qed. 

(*Generalizes the previous theorem to thread pools*)
Theorem poolRewindHeapExtension : forall H H' T C C', 
                                    C' >= C -> poolRewind C H T ->
                                    Forall (fun x : location * term * stamp => getStamp x = C) H' ->
                                    poolRewind C' (H'++H) T.
Proof.
  intros. induction H1. 
  {constructor. }
  {constructor. rewrite rewindIFFReplay. eapply replayHeapExtension; eauto. 
   rewrite <- rewindIFFReplay. auto. omega. }
  {constructor; auto. }
Qed. 


(*If the log at the end of a rewind derivation is invalid, then we can rewind
**from the log returned from validate*)
Theorem abortRewind : forall S L H S' e' L' e0 e,
                        validate S L H S' (abort e' L') ->
                        rewind H (Some (S, e0), [], e0) (Some (S, e0), L, e) ->
                        rewind H (Some (S, e0), [], e0) (Some (S, e0), L', e'). 
Proof.
  intros. dependent induction H1. 
  {inv H0. }
  {inv H2; eauto. 
   {inv H0; eauto. apply decomposeEq in H10. subst. auto. }
   {inv H0; eauto. eapply decomposeEq in H10. subst. auto. }
   {inv H0. eauto. }
  }
Qed. 

Ltac lookupSame :=
  match goal with
      |H:logLookup ?L ?l = ?v, H':logLookup ?L ?l = ?v' |- _ =>
       rewrite H in H'; inv H'
      |A:lookup ?H ?l = ?v, B:lookup ?H ?l = ?v' |- _ =>
       rewrite A in B; inv B
  end. 

(*the same rewind derivation can be produced with a newer stamp assuming the 
**log is valid*)
Theorem rewindDiffStamp : forall S C H e0 L e L' e' H' S', 
                        rewind H (Some(S,e0), L, e) (Some(S,e0), L', e') -> C > S ->
                        validate S L' H S' (commit H') ->
                        rewind H (Some(C,e0), L, e) (Some(C,e0), L', e').
Proof.
  intros. generalize dependent H'. dependent induction H0; intros. constructor. 
  inv H1.
  {econstructor. Focus 2. eapply r_readStepValid; eauto. omega.  
   eapply IHrewind; eauto. inv H3. eauto. }
  {inv H3. lookupSame. omega. }
  {econstructor. Focus 2. eapply r_readInDomainStep; eauto. eauto. }
  {inv H3. econstructor. Focus 2. eapply r_writeStep; eauto. intros c. inv c. 
   eapply IHrewind; eauto. }
  {econstructor. Focus 2. eapply r_atomicIdemStep; eauto. intros c. inv c. eauto. }
  {econstructor. Focus 2. eapply r_betaStep; eauto. intros c. inv c. eauto. }
Qed. 

(*rewind can always take place on a newer timestamp*)
Theorem poolRewindWeakening : forall C C' H T,
                                poolRewind C H T -> C' >= C ->
                                poolRewind C' H T. 
Proof.
  intros. induction H0.
  {constructor. }
  {constructor; auto. omega. }
  {constructor; auto. }
Qed. 

(*if a heap can be validated, then the resulting heap is an extension of the 
**input heap*)
Theorem validateHeapExtension : forall S H C H' L,
                                    validate S L H C (commit H')  ->
                                    exists H'', H' = H'' ++ H .
Proof.
  intros. dependent induction H0; eauto; try solve[exists nil; eauto].  
  {invertHyp. exists ((l,v,S')::x). simpl. reflexivity. }
Qed. 

(*when validating the heap, the extended portion must all have time stamp
**equal to the write version number*)
Theorem validateStampGE : forall H' S L H C,
                            validate S L H C (commit (H'++H)) ->
                            Forall (fun x => getStamp x = C) H'. 
Proof.
  intros. dependent induction H0; auto. 
  {destruct H'. constructor. apply lengthsEq in x. simpl in *. 
   rewrite app_length in x. omega. }
  {copy H0. eapply validateHeapExtension in H0. invertHyp. destruct H'. 
   simpl in x. apply lengthsEq in x. simpl in x. rewrite app_length in x. omega.
   constructor. inv x. auto. eapply IHvalidate; eauto. inversion x. auto. }
Qed. 

(*version clock and heap increase monotonically under the p_step relation*)
Theorem p_stampHeapMonotonic : forall C H T C' H' T',
             p_step C H T C' H' T' -> 
             C' >= C /\ (exists H'', H' = H'' ++ H /\ Forall (fun x => getStamp x = C) H''). 
Proof.
  intros. induction H0; try invertHyp; split; eauto; try solve[exists nil; auto]. omega.  
  {exists [(l,v,C)]. simpl. split; auto.  }
  {copy H0. apply validateHeapExtension in H0. invertHyp. exists x. split; auto. 
   eapply validateStampGE in H2. auto. }
Qed. 

(*p_step preserves rewind*)
Theorem p_stepRewind : forall C H T C' H' T', 
                       p_step C H T C' H' T' -> poolRewind C H T ->
                       poolRewind C' H' T'. 
Proof.
  intros. induction H0; try solve[repeat econstructor]. 
  {inv H1. inv H0; exfalso; apply H6; auto. inv H0. 
   {destruct(lt_dec S' S). 
    {constructor; auto. econstructor; eauto. eapply r_readStepValid; eauto. }
    {constructor; auto. econstructor; eauto. eapply r_readStepInvalid; eauto. omega. }
   }
   {constructor. econstructor; eauto. eapply r_readInDomainStep; eauto. auto. }
   {econstructor. econstructor; eauto. eapply r_writeStep; eauto. auto. }
   {econstructor. econstructor; eauto. eapply r_atomicIdemStep; eauto. auto. }
   {econstructor. econstructor; eauto. eapply r_betaStep; eauto. auto. }
  }
  {inv H1. constructor; auto. eapply p_stampHeapMonotonic in H0. invertHyp. 
   eapply poolRewindHeapExtension; eauto. }
  {inv H1. constructor; auto.  eapply p_stampHeapMonotonic in H0. invertHyp. 
   eapply poolRewindHeapExtension; eauto. }
  {inv H1. constructor; try omega. inv H3. 
   {copy H13. eapply abortRewind in H13; eauto. eapply validateValidate in H1. 
    invertHyp. eapply rewindDiffStamp; eauto. }
   {apply decomposeEq in H4. subst. eapply rewindDiffStamp; eauto. }
  }
  {inv H1. econstructor; try omega. copy H0. eapply abortRewind in H0; eauto.
   eapply validateValidate in H1; eauto. invertHyp. eapply rewindDiffStamp; eauto. }
Qed. 

(*version clock and heap increase monotonically under the f_step relation*)
Theorem f_stampHeapMonotonic : forall C H T C' H' T',
                               f_step C H T C' H' T' -> 
                               C' >= C /\ (exists H'', H' = H'' ++ H /\ Forall (fun x => getStamp x = C) H''). 
Proof.
  intros. induction H0; try invertHyp; split; eauto; try solve[exists nil; auto]. omega.  
  {exists [(l,v,C)]. simpl. split; auto.  }
  {copy H0. apply validateHeapExtension in H0. invertHyp. exists x. split; auto. 
   eapply validateStampGE in H2. auto. }
Qed. 

(*f_step preserves rewind*)
Theorem f_stepRewind : forall C H T C' H' T', 
                       f_step C H T C' H' T' -> poolRewind C H T ->
                       poolRewind C' H' T'. 
Proof.
  intros. induction H0; try solve[repeat econstructor]. 
  {inv H1. inv H0; exfalso; apply H6; auto. inv H0. 
   {destruct(lt_dec S' S). 
    {constructor; auto. econstructor; eauto. eapply r_readStepValid; eauto. }
    {constructor; auto. econstructor; eauto. eapply r_readStepInvalid; eauto. omega. }
   }
   {constructor. econstructor; eauto. eapply r_readInDomainStep; eauto. auto. }
   {econstructor. econstructor; eauto. eapply r_writeStep; eauto. auto. }
   {econstructor. econstructor; eauto. eapply r_atomicIdemStep; eauto. auto. }
   {econstructor. econstructor; eauto. eapply r_betaStep; eauto. auto. }
  }
  {inv H1. constructor; auto. eapply f_stampHeapMonotonic in H0. 
   invertHyp. eapply poolRewindHeapExtension; eauto. }
  {inv H1. constructor; auto. eapply f_stampHeapMonotonic in H0. 
   invertHyp. eapply poolRewindHeapExtension; eauto. }
  {constructor. constructor. omega. }
Qed. 