Require Export ast.  
Require Export Coq.Logic.FunctionalExtensionality.

(*maps locations to terms and time stamps*)

Definition heap := location -> option term. 

Definition emptyHeap : heap := fun _ => None. 

Definition update H l v : heap :=
  fun l' => if eq_nat_dec l l'
         then Some v
         else H l'. 

Theorem heapExt : forall (H1 H2 : heap), (forall l, H1 l = H2 l) <-> H1 = H2.
Proof.
  intros. split.
  {intros. eapply functional_extensionality; auto. }
  {intros. subst. reflexivity. }
Qed.  

Theorem lookupUpdate : forall H l v v',
                         H l = Some(v') -> 
                         (update H l v) l = Some(v). 
Proof.
  intros. unfold update. destruct (PeanoNat.Nat.eq_dec l l); auto.
  exfalso. apply n. auto.
Qed. 


Theorem updateUpdate : forall H l v v',
                         update (update H l v) l v' = update H l v'.
Proof.
  intros. apply heapExt. intros. unfold update. destruct (PeanoNat.Nat.eq_dec l l0); auto.
Qed. 

Theorem updateIdempotent : forall H l v,
                             H l  = Some v ->
                             update H l v = H.
Proof.
  intros H l v H0. apply heapExt. intros. unfold update.
  destruct (PeanoNat.Nat.eq_dec l l0).
  {subst. rewrite H0. reflexivity. }
  {auto. }
Qed. 
  
Theorem updatecomm : forall H l l' v v',
    l <> l' ->
    update (update H l v) l' v' =
    update (update H l' v') l v.
Proof.
  intros. apply heapExt. intros. unfold update.
  destruct (PeanoNat.Nat.eq_dec l' l0); destruct (PeanoNat.Nat.eq_dec l l0); auto.
  subst. exfalso; auto.
Qed. 

Theorem heapPullOut : forall H l v,
    H l = Some v  ->
    exists H', H = update H' l v. 
Proof.
  intros. exists (fun l' => if PeanoNat.Nat.eq_dec l l' then Some v else H l'). 
  apply heapExt. intros. unfold update. destruct (PeanoNat.Nat.eq_dec l l0).
  {subst. auto. }
  {auto. }
Qed.

Ltac heapUnfold :=
  match goal with
  |H : update ?h ?l ?v ?lock ?l' = ?x |- _ => unfold update in H; try heapUnfold
  | |- update ?H ?l ?v ?lock ?l' = ?x => unfold update
  end.