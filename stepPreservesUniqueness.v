Require Export noninterference. 
Require Import Coq.Sets.Powerset_facts. 


(**
* Uniqueness of thread pools
*)

(** States that *)
Inductive extension (C : nat) (T T' : pool) : Prop :=
  extension_ : forall extra, ids T' = Union nat (ids T) extra ->
                        (forall id, In nat extra id -> id >= C) ->
                        extension C T T'. 


Theorem unionEmpty : forall A S, Union A S (Empty_set A) = S.
Proof.
  intros. apply Extensionality_Ensembles. constructor.
  intro. intros. solveIn. constructor. auto.
Qed. 
  
Theorem f_stepExtension : forall C H T C' H' T',
    f_step C H T C' H' T' -> extension C T T'.
Proof.
  intros. induction H0; try solve[(econstructor; simpl; [erewrite unionEmpty; eauto|
                                                    intros id H999; inv H999])].
  {inv H0. econstructor. simpl. erewrite unionEmpty. auto.
   intros. solveIn. }
  {dependent destruction H0; (econstructor; simpl; [erewrite unionEmpty; eauto|
                                                    intros id H999; inv H999]). }
  {inv IHc_step. eapply extension_ with (extra := extra); auto. simpl. 
   rewrite H1. rewrite Union_associative. rewrite Union_commutative with (A := extra).
   rewrite <- Union_associative. auto. }
  {inv IHc_step. eapply extension_ with (extra := extra); auto. simpl. 
   rewrite H1. rewrite Union_associative. rewrite Union_commutative with (B := extra).
   rewrite <- Union_associative. auto. }
  {econstructor. simpl. auto. intros. solveIn. auto. }
Qed. 

Theorem p_stepExtension : forall C H T C' H' T',
    p_step C H T C' H' T' -> extension C T T'.
Proof.
  intros. induction H0; try solve[(econstructor; simpl; [erewrite unionEmpty; eauto|
                                                    intros id H999; inv H999])].
  {inv H0. econstructor. simpl. erewrite unionEmpty. auto.
   intros. solveIn. }
  {dependent destruction H0; (econstructor; simpl; [erewrite unionEmpty; eauto|
                                                    intros id H999; inv H999]). }
  {inv IHc_step. eapply extension_ with (extra := extra); auto. simpl. 
   rewrite H1. rewrite Union_associative. rewrite Union_commutative with (A := extra).
   rewrite <- Union_associative. auto. }
  {inv IHc_step. eapply extension_ with (extra := extra); auto. simpl. 
   rewrite H1. rewrite Union_associative. rewrite Union_commutative with (B := extra).
   rewrite <- Union_associative. auto. }
  {econstructor. simpl. auto. intros. solveIn. auto. }
Qed. 

Theorem poolRewindLt : forall C H T,
    poolRewind C H T -> (forall id, In nat (ids T) id -> id < C).
Proof.
  induction T; intros; simpl in *; auto. 
  {inv H0; inv H1;  auto. }
  {inv H0; inv H1; auto. }
Qed. 

Theorem DisjointComm : forall A T1 T2, Disjoint A T1 T2 <-> Disjoint A T2 T1.
Proof.
  intros. split; intros. 
  {constructor. intros. intro. inv H. specialize (H1 x).
   apply H1. solveIn. }
  {constructor. intros. intro. inv H. specialize (H1 x).
   apply H1. solveIn. }
Qed. 
    
Theorem f_stepDisjoint : forall C H T C' H' T' T2,
    poolRewind C H T -> poolRewind C H T2 ->
    f_step C H T C' H' T' -> Disjoint nat (ids T) (ids T2) ->
    Disjoint nat (ids T') (ids T2). 
Proof.
  intros. generalize dependent T2. induction H2; intros; simpl in *; eauto. 
  {inv H1. auto. }
  {dependent destruction H1; simpl in *; eauto. }
  {inv H0. apply IHc_step in H8; auto. apply f_stepExtension in H2.
   inv H2. rewrite H0. constructor. intros. intro. solveIn. inv H5.
   {inv H2.
    {inv H3. specialize (H2 x). apply H2. solveIn. }
    {apply H4 in H5. eapply poolRewindLt in H1; eauto. omega. }
   }
   {inv H3. specialize (H5 x). apply H5. solveIn. }
  }
  {inv H0. apply IHc_step in H7; auto. apply f_stepExtension in H2.
   inv H2. rewrite H0. constructor. intros. intro. inv H2. inv H5.
   {inv H3. specialize (H5 x). apply H5. solveIn. }
   {inv H2. 
    {inv H3. specialize (H2 x). apply H2. solveIn. }
    {apply H4 in H5. eapply poolRewindLt in H1; eauto. omega. }
   } apply DisjointComm. auto. }
  {inv H3. inv H0. constructor. intros. intro. inv H0.
   {inv H3.
    {inv H0. specialize (H4 x). apply H4. solveIn. }
    {inv H0. eapply poolRewindLt in H2; eauto. omega. }
   }
  }
Qed. 

Theorem p_stepDisjoint : forall C H T C' H' T' T2,
    poolRewind C H T -> poolRewind C H T2 ->
    p_step C H T C' H' T' -> Disjoint nat (ids T) (ids T2) ->
    Disjoint nat (ids T') (ids T2). 
Proof.
  intros. generalize dependent T2. induction H2; intros; simpl in *; eauto. 
  {inv H1. auto. }
  {dependent destruction H1; simpl in *; eauto. }
  {inv H0. apply IHc_step in H8; auto. apply p_stepExtension in H2.
   inv H2. rewrite H0. constructor. intros. intro. inv H2. inv H5.
   {inv H2.
    {inv H3. specialize (H2 x). apply H2. solveIn. }
    {apply H4 in H5. eapply poolRewindLt in H1; eauto. omega. }
   }
   {inv H3. specialize (H5 x). apply H5. solveIn. }
  }
  {inv H0. apply IHc_step in H7; auto. apply p_stepExtension in H2.
   inv H2. rewrite H0. constructor. intros. intro. inv H2. inv H5.
   {inv H3. specialize (H5 x). apply H5. solveIn. }
   {inv H2. 
    {inv H3. specialize (H2 x). apply H2. solveIn. }
    {apply H4 in H5. eapply poolRewindLt in H1; eauto. omega. }
   } apply DisjointComm. auto. }
  {inv H3. inv H0. constructor. intros. intro. inv H0.
   {inv H3.
    {inv H0. specialize (H4 x). apply H4. solveIn. }
    {inv H0. eapply poolRewindLt in H2; eauto. omega. }
   }
  }
Qed. 
   
