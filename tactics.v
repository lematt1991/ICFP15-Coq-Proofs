Require Export Coq.Logic.ProofIrrelevance. 

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