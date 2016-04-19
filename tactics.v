Require Export Coq.Logic.ProofIrrelevance. 
Require Export Coq.Init.Datatypes.
Require Export Coq.Arith.Peano_dec.

(*General Purpose tactics*)
Ltac inv H := inversion H; subst; clear H. 
Ltac copy H :=
  match type of H with
      |?x => assert(x) by auto
  end. 
Ltac invertHyp :=
  match goal with
      |H:exists x, ?P |- _ => inv H; try invertHyp
      |H: ?P /\ ?Q |- _ => inv H; try invertHyp
  end. 

Ltac solveByInv :=
  match goal with
      |H:_ |- _ => solve[inv H]
  end. 

(*proof irrelevance*)
Ltac proofsEq :=
  match goal with
    |H:?x, H':?x |- _ => (assert(H = H') by eapply proof_irrelevance); subst
  end. 

(*If inversion produces the same hypothesis, skip it, otherwise invert all equalities*)
Ltac invertEq :=
  match goal with
  |H:?a = ?b |- _ => let n := fresh
                   in inversion H as n; match type of n with
                                          |?a = ?b => fail
                                        end
  |H:?a = ?b |- _ => inv H
  end.

Ltac transEq :=
  match goal with
  |H:?a = ?b,H':?a = ?c |- _ => rewrite H in H'
  |H:?a = ?b,H':?c = ?a |- _ => rewrite H in H'
  |H:?a = ?b,H':?b = ?c |- _ => rewrite H in H'
  |H:?a = ?b,H':?c = ?b |- _ => rewrite H in H'
  end. 

Theorem rewriteEq : forall l l' (p : l = l'), PeanoNat.Nat.eq_dec l l' = left p. 
Proof.
  intros. subst. destruct (PeanoNat.Nat.eq_dec l' l'); auto. replace eq_refl with e.
  auto. apply proof_irrelevance. exfalso. auto.
Qed. 

Theorem rewriteNeq : forall l l' (p : l <> l'), PeanoNat.Nat.eq_dec l l' = right p. 
Proof.
  intros. subst. destruct (PeanoNat.Nat.eq_dec l l'). contradiction.
  replace p with n. auto. apply proof_irrelevance.
Qed. 

Theorem neqSymm : forall A (l l' : A), l <> l' <-> l' <> l.
Proof.
  intros. split.
  {intro. intro. subst. auto. }
  {intro. intro. subst. auto. }
Qed. 

Ltac simplEq l l' :=
  match goal with
  |H : l = l |- _ =>
   replace (PeanoNat.Nat.eq_dec l l) with ((left H) : {l = l} + {l <> l});
   [idtac|symmetry; apply rewriteEq]
  |H : l <> l' |- _ =>
   replace (PeanoNat.Nat.eq_dec l l') with ((right H) : {l = l'} + {l <> l'});
   [idtac|symmetry; apply rewriteNeq]
  |H : l' <> l |- _ =>
   rewrite neqSymm in H; 
   replace (PeanoNat.Nat.eq_dec l l') with ((right H) : {l = l'} + {l <> l'});
   [idtac|symmetry; apply rewriteNeq]
  end.