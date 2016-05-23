Require Export semantics. 

Theorem rewindAllocSingle : forall v C H S e0 L e L' e' l,
    rewind H C (Some(S, e0), L, e) (Some(S, e0), L', e') ->
    H l = None ->
    rewind (update H l v) C (Some(S, e0), L, e) (Some(S, e0), L', e'). 
Proof.
  intros. dependent induction H0.
  {econstructor. }
  {inv H1.
   {econstructor; eauto. econstructor; eauto.
    unfold update. destruct (Nat.eq_dec l l0).
    {subst. transEq. invertEq. }
    {assumption. }
   }
   {econstructor; eauto. econstructor; eauto.
    unfold update. destruct (Nat.eq_dec l l0).
    {subst. transEq. invertEq. }
    {eassumption. }
   }
   {econstructor; eauto. econstructor; eauto. }
   {econstructor; eauto. econstructor; eauto. }
   {econstructor; eauto. eapply r_atomicIdemStep; eauto. }
   {econstructor; eauto. eapply r_betaStep; eauto. }
  }
Qed.

Theorem rewindAlloc : forall v C H T l,
    poolRewind C H T -> H l = None ->
    poolRewind C (update H l v) T. 
Proof.
  intros. induction H0.
  {econstructor. }
  {econstructor; auto. eapply rewindAllocSingle; auto. }
  {econstructor; eauto. }
Qed. 

Theorem commitLookup : forall L H HV l v,
    H l = Some v -> validate L H (commit HV) ->
    exists v', HV l = Some v'.
Proof.
  intros. dependent induction H1; eauto. unfold update.
  destruct (Nat.eq_dec l0 l); eauto.
Qed. 

  
Theorem rewindCommitSingleNI : forall C H S e0 L e L' e' HV L'',
    validate L'' H (commit HV) -> S <= C ->
    rewind H C (Some(S, e0), L, e) (Some(S, e0), L', e') ->
    rewind HV (1+C) (Some(S, e0), L, e) (Some(S, e0), L', e'). 
Proof.
  intros. genDeps{{HV; L''}}. dependent induction H2; intros.
  {econstructor. }
  {inv H3.
   {econstructor. eapply IHrewind; eauto.
    eapply commitLookup in H0; eauto. invertHyp.
    eapply r_readStepInvalid; eauto. }
   {econstructor. eapply IHrewind; eauto. eapply commitLookup in H0; eauto.
    invertHyp. eapply r_readStepInvalid; eauto. }
   {econstructor. eapply IHrewind; eauto. econstructor; eauto. }
   {econstructor. eapply IHrewind; eauto. econstructor; eauto. }
   {econstructor. eapply IHrewind; eauto. eapply r_atomicIdemStep; eauto. }
   {econstructor. eapply IHrewind; eauto. eapply r_betaStep; eauto. }
  }
Qed. 
    
Theorem rewindCommitNI : forall C H T HV L,
    validate L H (commit HV) ->
    poolRewind C H T -> poolRewind (1+C) HV T. 
Proof.
  intros. induction H1.
  {repeat econstructor. }
  {econstructor; auto. eapply rewindCommitSingleNI; eauto. }
  {econstructor; eauto. }
Qed. 
  
Theorem f_stepNI : forall C H T1 C' H' T1' T2,
       f_step C H T1 C' H' T1' -> poolRewind C H T2 ->
       poolRewind C' H' T2. 
Proof.
  intros. induction H0; auto. 
  {inv H0. auto. }
  {eapply rewindAlloc; eauto. }
  {eapply rewindCommitNI; eauto. }
Qed.

Theorem rewindNewerStamp : forall H C S e0 e e' L L' HV,
    validate L' H (commit HV) ->
    rewind H C (Some(S, e0), L, e) (Some(S, e0), L', e') ->
    rewind H C (Some(C, e0), L, e) (Some(C, e0), L', e'). 
Proof.
  intros. generalize dependent HV. dependent induction H1; intros. 
  {constructor. }
  {inv H2.
   {econstructor. eassumption. econstructor; auto. }
   {inv H0. transEq. invertEq. econstructor. eapply IHrewind; eauto. 
    econstructor; eauto. }
   {econstructor. eapply IHrewind; eauto. econstructor; eauto. }
   {inv H0. econstructor. eapply IHrewind; eauto.
    econstructor; eauto. intro. solveByInv. }
   {econstructor. eapply IHrewind; eauto.
    eapply r_atomicIdemStep; eauto. intro. solveByInv. }
   {econstructor. eapply IHrewind; eauto.
    eapply r_betaStep; eauto. intro. solveByInv. }
  }
Qed. 

(*f_step preserves rewind*)
Theorem f_stepRewind : forall C H T C' H' T', 
                       f_step C H T C' H' T' -> poolRewind C H T ->
                       poolRewind C' H' T'. 
Proof.
  intros. induction H0. 
  {inv H0. econstructor; auto. econstructor. }
  {inv H0.
   {inv H1. econstructor; auto. econstructor. 
    eassumption. econstructor; eauto. }
   {inv H1. econstructor; auto. econstructor. eassumption.
    econstructor; eauto. }
   {inv H1. exfalso; auto. econstructor; eauto.
    econstructor. eassumption. econstructor; eauto. }
   {inv H1. exfalso; auto. econstructor; auto.
    econstructor. eassumption. eapply r_atomicIdemStep; eauto. }
   {inv H1. exfalso; auto. econstructor; auto.
    econstructor. eassumption. eapply r_betaStep; eauto. }
  }
  {inv H1. econstructor; eauto. eapply f_stepNI; eauto. }
  {inv H1. econstructor; eauto. eapply f_stepNI; eauto. }
  {repeat econstructor. }
  {repeat econstructor. }
  {econstructor. }
  {econstructor. econstructor. auto. }
  {econstructor. }
  {inv H1. econstructor; auto. eapply rewindNewerStamp; eauto. }
Qed. 

Theorem p_stepNI : forall C H T1 C' H' T1' T2,
       p_step C H T1 C' H' T1' -> poolRewind C H T2 ->
       poolRewind C' H' T2. 
Proof.
  intros. induction H0; auto. 
  {inv H0. auto. }
  {eapply rewindAlloc; eauto. }
  {eapply rewindCommitNI; eauto. }
Qed.

Theorem rewindAbort : forall H C S e0 L' e' L'' e'',
    validate L' H (abort e'' L'') ->
    rewind H C (Some(S, e0), nil, e0) (Some(S, e0), L', e') ->
    rewind H C (Some(S, e0), nil, e0) (Some(S, e0), L'', e'').
Proof.
  intros. genDeps{{L''; e''}}. dependent induction H1; intros.
  {inv H0. }
  {inv H2; eauto. 
   {inv H0; eauto. eapply decomposeEq in H9.
    subst. assumption. }
   {inv H0; eauto. eapply decomposeEq in H10. subst. eauto. }
   {inv H0. eauto. }
  }
Qed. 
  
(*p_step preserves rewind*)
Theorem p_stepRewind : forall C H T C' H' T', 
    p_step C H T C' H' T' -> poolRewind C H T ->
    poolRewind C' H' T'. 
Proof.
 intros. induction H0. 
 {inv H0. econstructor; auto. copy H3. eapply validateValidate in H3.
  invertHyp. inv H1. eapply rewindNewerStamp. eauto.
  eapply rewindAbort; eauto. }
  {inv H0.
   {inv H1. econstructor; auto. econstructor. 
    eassumption. econstructor; eauto. }
   {inv H1. econstructor; auto. econstructor. eassumption.
    econstructor; eauto. }
   {inv H1. exfalso; auto. econstructor; eauto.
    econstructor. eassumption. econstructor; eauto. }
   {inv H1. exfalso; auto. econstructor; auto.
    econstructor. eassumption. eapply r_atomicIdemStep; eauto. }
   {inv H1. exfalso; auto. econstructor; auto.
    econstructor. eassumption. eapply r_betaStep; eauto. }
  }
  {inv H1. econstructor; eauto. eapply p_stepNI; eauto. }
  {inv H1. econstructor; eauto. eapply p_stepNI; eauto. }
  {repeat econstructor. }
  {repeat econstructor. }
  {econstructor. }
  {econstructor. econstructor. auto. }
  {econstructor. }
  {inv H1. econstructor; auto. eapply rewindNewerStamp; eauto. }
Qed. 