Require Export ast.  
Require Export Coq.Logic.FunctionalExtensionality.

(*maps locations to terms and time stamps*)

Definition heap := location -> option (term*lock). 

Definition emptyHeap : heap := fun _ => None. 

Definition lookup (H:heap) l := H l. 

Definition update H l v stamp : heap :=
  fun l' => if eq_nat_dec l l'
         then Some (v, stamp)
         else H l'. 

Theorem heapExt : forall (H1 H2 : heap), (forall l, H1 l = H2 l) <-> H1 = H2.
Proof.
  intros. split.
  {intros. eapply functional_extensionality; auto. }
  {intros. subst. reflexivity. }
Qed. 

Theorem lookupUpdate : forall H l v lock v' lock',
                         lookup H l = Some(v', lock') -> 
                         lookup (update H l v lock) l = Some(v, lock). 
Proof.
  intros. unfold update. unfold lookup. destruct (PeanoNat.Nat.eq_dec l l); auto.
  exfalso. apply n. auto.
Qed. 


Theorem updateUpdate : forall H l v v' lock lock',
                         update (update H l v lock) l v' lock' = update H l v' lock'.
Proof.
  intros. apply heapExt. intros. unfold update. destruct (PeanoNat.Nat.eq_dec l l0); auto.
Qed. 

Theorem updateIdempotent : forall H l v lock,
                             lookup H l  = Some(v, lock) ->
                             update H l v lock = H.
Proof.
  intros H l v lock H0. apply heapExt. intros. unfold update.
  destruct (PeanoNat.Nat.eq_dec l l0).
  {subst. unfold lookup in H0. rewrite H0. reflexivity. }
  {auto. }
Qed. 
  
Theorem updatecomm : forall H l l' v v' lock lock',
    l <> l' ->
    update (update H l v lock) l' v' lock' =
    update (update H l' v' lock') l v lock.
Proof.
  intros. apply heapExt. intros. unfold update.
  destruct (PeanoNat.Nat.eq_dec l' l0); destruct (PeanoNat.Nat.eq_dec l l0); auto.
  subst. exfalso; auto.
Qed. 
  