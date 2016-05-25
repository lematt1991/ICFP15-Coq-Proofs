Require Export stepPreservesRewind.  
  
(*AheadOf H t1 t2: t2 is in t1's future with respect to heap H*)
Inductive AheadOf H C : thread -> thread -> Prop :=
|noTXAheadOf : forall e, AheadOf H C (None, nil, e) (None, nil, e)
|inTXAheadOf : forall S e0 L L' e e', 
                 replay H C (Some(S,e0),L,e) (Some(S,e0),L',e') ->
                 AheadOf H C (Some(S,e0),L,e) (Some(S,e0),L',e').

(*Generalizes the previous relation to thread pools*)
Inductive poolAheadOf H C : pool -> pool -> Prop := 
|SingleAheadOf : forall t t', AheadOf H C t t' -> poolAheadOf H C (Single t) (Single t')
|ParAheadOf : forall T1 T2 T1' T2', 
           poolAheadOf H C T1 T1' -> poolAheadOf H C T2 T2' -> 
           poolAheadOf H C (Par T1 T2) (Par T1' T2'). 


(*
 * If we can replay from one state to another and the first state is
 * invalid, then the second one must be too
 *)
Theorem replayInvalid : forall H S e0 L C e L' e' eA LA, 
                          replay H C (Some(S,e0),L,e) (Some(S,e0),L',e') ->
                          validate L H (abort eA LA) ->
                          exists eA' LA', validate L' H (abort eA' LA').
Proof.
  intros. dependent induction H0; eauto. 
  {inv H0; eauto. 
   {assert(validate (readItem l E v::L) H (abort eA LA)).
    eapply validateAbortPropogate; eauto. eapply IHreplay in H0; eauto. }
   {assert(validate (readItem l E v::L) H (abort eA LA)).
    eapply validateAbortPropogate; eauto. eapply IHreplay in H0; eauto. }
   {assert(validate (writeItem l v::L) H (abort eA LA)).
    eapply validateAbortPropogate; eauto. eapply IHreplay in H0; eauto. }
  }
Qed. 

(*
 * If we can rewind/replay from one state to another and the final state 
 * is invalid, then it must also be possible to rewind/replay to the 
 * portion that is still valid as determined by validate 
 *)         
Theorem rewindValidPortion : forall S L H C e' L' e0 e, 
                               rewind H C (Some(S,e0),nil,e0) (Some(S,e0),L,e) ->
                               validate L H (abort e' L') ->
                               rewind H C (Some(S,e0),nil,e0) (Some(S,e0),L',e').
Proof.
  intros. dependent induction H0. 
  {inv H1. }
  {inv H1; eauto. 
   {inv H2. 
    {eapply IHrewind; eauto. }
    {transEq. invertEq. exfalso; auto. }
   }
   {inv H2. 
    {eapply IHrewind; eauto. }
    {eapply decomposeEq in H10. subst. auto. }
   }
   {inv H2. eauto. }
  }
Qed. 


(*if the beginning of a replay aborts, then so does the endpoint*)
Theorem abortReplay : forall S L H C L' e' e'' L'' e e0, 
                        replay H C (Some(S,e0),L,e) (Some(S,e0),L',e') ->
                        validate L H (abort e'' L'') -> 
                        validate L' H (abort e'' L''). 
Proof.
  intros. dependent induction H0; auto.
  inv H0; eapply IHreplay; eauto; eapply validateAbortPropogate; eauto. 
Qed. 

Theorem AheadOfAlloc : forall v C H T T' l,
    poolAheadOf H C T T' -> H l = None ->
    poolAheadOf (update H l v) C T T'. 
Proof.
  intros. induction H0.
  {inv H0.
   {repeat constructor. }
   {rewrite <- rewindIFFReplay in H2. eapply rewindAllocSingle in H2; eauto.
    constructor. constructor. rewrite <- rewindIFFReplay. eauto. }
  }
  {constructor; eauto. }
Qed. 

Theorem AheadOfCommitNI : forall T' C H T HV L,
    validate L H (commit HV) ->
    poolAheadOf H C T T' -> poolAheadOf HV (1+C) T T'. 
Proof.
  intros. induction H1.
  {constructor. inv H1.
   {constructor. }
   {constructor. erewrite <- rewindIFFReplay in *.
    eapply rewindCommitSingleNI; eauto. }
  }
  {econstructor; eauto. }
Qed. 

Theorem AheadOfNI : forall C H T C' H' T' T2 T2',
    poolAheadOf H C T2 T2' -> f_step C H T C' H' T' ->
    poolAheadOf H' C' T2 T2'.
Proof.
  intros. genDeps{{T2; T2'}}. induction H1; intros; auto. 
  {inv H0. auto. }
  {eapply AheadOfAlloc; eauto. }
  {eapply AheadOfCommitNI; eauto. }
Qed. 

Ltac invertHyp := 
  match goal with
    |H : poolAheadOf ?h ?c (Single (Some ?tx, ?L, ?e)) ?T |- _ => inv H; try invertHyp 
    |H : AheadOf ?h ?C (Some ?tx, ?L, ?e) ?T |- _ => inv H; try invertHyp
    |H : poolRewind ?C ?h (Single (Some ?tx, ?L, ?e)) |- _ => inv H; try invertHyp
    |H : poolAheadOf ?h ?C (Single(None, ?L,?e)) ?T |- _ => inv H; try invertHyp
    |H : AheadOf ?h ?C (None, ?L, ?e) ?T |- _ => inv H; try invertHyp
    |H : poolRewind ?C ?h (Single (None, ?L, ?t)) |- _ => inv H; try invertHyp
    | _ => tactics.invertHyp
  end. 

Theorem valueDecidable : forall (v1 v2 : term), v1 = v2 \/ v1 <> v2.
Proof.
  induction v1; intros; destruct v2; try solve[right; intro; solveByInv].
  {specialize (IHv1 v2); inv IHv1; auto; right; intro; invertEq; auto. }
  {destruct (Nat.eq_dec n n0). subst; auto. right. intro. invertEq. auto. }
  {left; auto. }
  {destruct (Nat.eq_dec n n0). subst; auto. right. intro. invertEq. auto. }
  {specialize (IHv1_1 v2_1). specialize (IHv1_2 v2_2). 
   inv IHv1_1; inv IHv1_2; auto; right; intro; invertEq; auto. }
  {specialize (IHv1 v2); inv IHv1; auto; right; intro; invertEq; auto. }
  {specialize (IHv1_1 v2_1). specialize (IHv1_2 v2_2). 
   inv IHv1_1; inv IHv1_2; auto; right; intro; invertEq; auto. }
  {specialize (IHv1 v2); inv IHv1; auto; right; intro; invertEq; auto. }
  {specialize (IHv1 v2); inv IHv1; auto; right; intro; invertEq; auto. }
  {specialize (IHv1 v2); inv IHv1; auto; right; intro; invertEq; auto. }
  {specialize (IHv1 v2); inv IHv1; auto; right; intro; invertEq; auto. }
Qed. 


Theorem replayAbort : forall H C S e0 L e L' e' L'' e'',
    replay H C (Some(S, e0), L, e) (Some(S, e0), L', e') ->
    validate L H (abort e'' L'') ->
    validate L' H (abort e'' L'').
Proof.
  intros. genDeps{{e''; L''}}. dependent induction H0; intros.
  {auto. }
  {inv H0; eauto.
   {eapply IHreplay. eauto. eauto. constructor; eauto. }
   {eapply IHreplay. eauto. eauto. constructor; eauto. }
   {eapply IHreplay. eauto. eauto. constructor; eauto. }
  }
Qed. 
    
Theorem replayValidate : forall H C S e0 L L' e e' HV,
    replay H C (Some(S, e0), L, e) (Some(S, e0), L', e') ->
    validate L H (commit HV) ->
    (exists HV', validate L' H (commit HV')) \/
    (exists L'' e'', validate L' H (abort e'' L'')). 
Proof.
  intros. generalize dependent HV. dependent induction H0; intros; eauto.  
  inv H0; eauto. 
  {assert((Some (S, e0), readItem l E v :: L, fill E v) ~= (Some (S, e0), readItem l E v :: L, fill E v)).
   auto. eapply IHreplay in H0; auto. inv H0; invertHyp; eauto.
   econstructor; eauto. }
  {destruct (valueDecidable v v'). 
   {assert((Some (S, e0), readItem l E v' :: L, fill E v') ~= (Some (S, e0), readItem l E v' :: L, fill E v')).
    auto. subst. eapply IHreplay in H3; eauto. constructor; eauto. }
   {right. exists L. exists (fill E (get (loc l))). eapply replayAbort; eauto.
    eapply validateAbortRead; eauto. }
  }
  {assert((Some (S, e0), writeItem l v :: L, fill E unit) ~= (Some (S, e0), writeItem l v :: L, fill E unit)).
   auto. eapply IHreplay in H0; eauto. econstructor; eauto. }
Qed. 

    
    
Theorem validateDeterministic : forall L H res res',
    validate L H res -> validate L H res' -> res = res'.
Proof.
  intros. generalize dependent res'. induction H0; intros.  
  {inv H1. auto. }
  {inv H2; eauto. transEq. invertEq. exfalso; auto. }
  {inv H1; eauto. eapply IHvalidate in H5. solveByInv.
   eapply IHvalidate in H7. solveByInv. }
  {inv H3; eauto. transEq. invertEq. exfalso; auto.
   eapply IHvalidate in H9. solveByInv. }
  {inv H1; eauto. eapply IHvalidate in H7; solveByInv.
   eapply IHvalidate in H8. invertEq. auto. }
Qed. 
   
Theorem tsExtendCatchUp : forall H C S L e e0 L' e' L'' e'' HV,
    validate L' H (abort e'' L'') -> validate L H (commit HV) -> 
    rewind H C (Some(S, e0), L, e) (Some(S, e0), L', e') ->
    rewind H C (Some(S, e0), L, e) (Some(S, e0), L'', e'').
Proof.
  intros. genDeps{{L''; e''}}. dependent induction H2; intros.
  {eapply validateDeterministic in H1; eauto. solveByInv. }
  {inv H3; eauto. 
   {inv H0; eauto. eapply decomposeEq in H10.
    subst. assumption. }
   {inv H0; eauto. eapply decomposeEq in H11. subst. eauto. }
   {inv H0. eauto. }
  }
Qed. 

(*partial abort can simulate full abort*)
Theorem fullImpliesPartial : forall C H T C' H' T' PT, 
    f_step C H T C' H' T' -> poolAheadOf H C T PT ->
    poolRewind C H PT -> 
    exists PT', p_multistep C H PT C' H' PT' /\
           poolAheadOf H' C' T' PT'.
Proof.
  intros. generalize dependent PT. induction H0; intros.
  {inv H0. invertHyp. copy H7. eapply replayInvalid in H7; eauto. invertHyp. 
   econstructor. split. eapply c_multi_step. eapply c_liftedStep. 
   econstructor. eauto. constructor. econstructor. econstructor. 
   copy H2. eapply rewindAbort in H2; eauto.
   eapply validateValidate in H0; eauto. invertHyp. 
   rewrite <- rewindIFFReplay. eapply rewindNewerStamp; eauto. }
  {inv H0; try invertHyp. 
   {inv H10. 
    {econstructor. split. eapply c_multi_step. eapply c_transStep. 
     econstructor; eauto. constructor. repeat econstructor. }
    {econstructor. split. constructor. constructor. constructor.  
     inv H0; try decompSame; invertEq. repeat transEq. invertEq.
     eauto. omega. transEq. invertEq. }
   }
   {inv H9.
    {econstructor. split. eapply c_multi_step. eapply c_transStep.
     econstructor; eauto. constructor. repeat econstructor. }
    {econstructor. split. repeat constructor. repeat constructor. 
     inv H0; try decompSame; invertEq. transEq. invertEq.
     repeat transEq. invertEq. transEq. invertEq. auto. }
   }
   {destruct S. Focus 2. exfalso; auto. invertHyp. inv H8.
    {econstructor. split. eapply c_multi_step. eapply c_transStep.
     eapply t_writeStep; eauto. constructor. repeat constructor. }
    {econstructor. split. repeat constructor. repeat constructor.
     inv H0; try decompSame; invertEq. assumption. }
   }
   {destruct S. Focus 2. exfalso; auto. invertHyp. inv H8.
    {econstructor. split. eapply c_multi_step. eapply c_transStep.
     eapply t_atomicIdemStep; eauto. constructor. repeat constructor. }
    {econstructor. split. repeat constructor. repeat constructor.
     inv H0; try decompSame; invertEq. assumption. }
   }
   {destruct S. Focus 2. exfalso; auto. invertHyp. inv H8.
    {econstructor. split. eapply c_multi_step. eapply c_transStep.
     eapply t_betaStep; eauto. constructor. repeat constructor. }
    {econstructor. split. repeat constructor. repeat constructor.
     inv H0; try decompSame; invertEq. assumption. }
   }
  }
  {inv H1. inv H2. eapply IHc_step in H5; auto. invertHyp. econstructor.
   split. eapply c_multi_L. eassumption. constructor. auto.
   eapply AheadOfNI; eauto. }
  {inv H1. inv H2. eapply IHc_step in H7; auto. invertHyp. econstructor.
   split. eapply c_multi_R. eassumption. constructor.
   eapply AheadOfNI; eauto. auto. }
  {invertHyp.  econstructor. split. eapply c_multi_step.
   eapply c_forkStep; eauto. constructor. repeat econstructor. }
  {invertHyp. econstructor. split. eapply c_multi_step.
   eapply c_allocStep; eauto. constructor. repeat econstructor. }
  {invertHyp. inv H9.
   {econstructor. split. eapply c_multi_step. eapply c_commitStep; eauto.
    constructor. repeat constructor. }
   {inv H2; decompSame; invertEq. }
  }
  {invertHyp. econstructor. split. eapply c_multi_step.
   eapply c_atomicStep; eauto. constructor. repeat econstructor. }
  {invertHyp. econstructor. split. eapply c_multi_step.
   eapply c_betaStep; eauto. constructor. repeat econstructor. }
  {invertHyp. copy H8. eapply replayValidate in H8; eauto. inv H8.
   {invertHyp. econstructor. split. eapply c_multi_step. eapply c_tsExtend.
    eauto. constructor. repeat constructor. rewrite <- rewindIFFReplay in *.
    eapply rewindNewerStamp; eauto. }
   {invertHyp. econstructor. split. eapply c_multi_step. eapply c_liftedStep.
    econstructor; eauto. constructor. repeat constructor.
    erewrite <- rewindIFFReplay in *. copy H2. eapply validateValidate in H2.
    invertHyp. eapply rewindNewerStamp; eauto.
    eapply tsExtendCatchUp; eauto. }
  }
Qed. 

   
(*generalize step preserves rewind to thread pools*)
Theorem multistepPreservesRewind : forall C H T C' H' T',
                                poolRewind C H T -> p_multistep C H T C' H' T' ->
                                poolRewind C' H' T'. 
Proof.
  intros. induction H1. auto. apply IHc_multistep.
  eapply p_stepRewind; eauto. 
Qed. 

(*generalize full implies partial to thread pools*)
Theorem fullImpliesPartialMulti : forall C H T C' H' T' PT, 
                               f_multistep C H T C' H' T' -> poolAheadOf H C T PT ->
                               poolRewind C H PT ->
                               exists PT', p_multistep C H PT C' H' PT' /\
                                           poolAheadOf H' C' T' PT'.
Proof.
  intros. generalize dependent PT. induction H0; intros. 
  {exists PT. split. constructor. auto. }
  {copy H0. eapply fullImpliesPartial in H0; eauto. invertHyp. 
   copy H0. apply multistepPreservesRewind in H5; auto. 
   eapply IHc_multistep in H6; eauto. invertHyp. exists x0. split. 
   eapply c_multi_trans; eauto. auto. }
Qed. 







