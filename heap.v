Require Export ast.  
Require Export Coq.Arith.Peano_dec. 

(*maps locations to terms and time stamps*)
Definition heap := list TVar. 

(*lookup an address in the heap*)
Fixpoint lookup (H:heap) (l:location) :=
  match H with
      |(l', v, stamp)::H' => if eq_nat_dec l l'
                            then Some (v, stamp)
                            else lookup H' l
      |nil => None
  end. 

Fixpoint update H l (v : term) (stamp : lock) :=
  match H with
    | (l', v', s')::H' =>
      if eq_nat_dec l l'
      then (l', v, stamp) :: H'
      else (l', v', s') :: update H' l v stamp
    | nil => nil
  end. 
(*
 * If we can lookup a location in heap H, then we must 
 * still be able to find it if we extend the heap.
 *)
Theorem lookupExtension : forall Hnew H l v S, 
                            lookup H l  = Some(v, S) ->
                            exists v' S', lookup (Hnew++H) l = Some(v', S'). 
Proof.
  induction Hnew; intros. 
  {simpl. exists v. exists S. assumption. }
  {simpl. destruct a. destruct p. destruct (eq_nat_dec l l1). 
   {subst. eauto. }
   {eapply IHHnew in H0. invertHyp. eauto. }
  }
Qed.

Theorem lookupUpdate : forall H l v lock v' lock',
                         lookup H l = Some(v', lock') -> 
                         lookup (update H l v lock) l = Some(v, lock). 
Proof.
  induction H; intros.
  {simpl in *. inv H. }
  {simpl in *. destruct a. destruct p. destruct (eq_nat_dec l l1).
   {inv H0. simpl. destruct (eq_nat_dec l1 l1); auto. exfalso.
    apply n. auto. }
   {simpl in *. destruct (eq_nat_dec l l1).
    {subst. exfalso. apply n; auto. }
    {eapply IHlist. eauto. }
   }
  }
Qed.

Theorem updateUpdate : forall H l v v' lock lock',
                         update (update H l v lock) l v' lock' = update H l v' lock'.
Proof.
  induction H; intros; auto.
  simpl in *. destruct a. destruct p. destruct (eq_nat_dec l n).
  {simpl. subst. destruct (eq_nat_dec n n); auto. exfalso. apply n0; auto. }
  {simpl. destruct (eq_nat_dec l n).
   {contradiction. }
   {rewrite IHlist. auto. }
  }
Qed.

Theorem updateIdempotent : forall H l v lock,
                             lookup H l  = Some(v, lock) ->
                             update H l v lock = H.
Proof.
  induction H; intros; auto.
  simpl in *. destruct a. destruct p. destruct (eq_nat_dec l l1).
  {subst. inv H0. auto. }
  {rewrite IHlist. auto. assumption. }
Qed. 




  