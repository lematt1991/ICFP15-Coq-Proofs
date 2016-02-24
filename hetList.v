(*Library for heterogeneous lists*)
Inductive Het : Type :=
|HetConstr : forall A, A -> Het. 

Inductive hlist : Type :=
| HNil : hlist
| HCons : forall {A},  A -> hlist -> hlist. 

Notation "{{ x ; .. ; y }}" := (HCons x .. (HCons y HNil) ..) : hetlist_scope.
Open Scope hetlist_scope. 

(*Hack for generalize dependent of multiple parameters*)
Ltac genDeps xs :=
  match xs with
    |HCons ?x ?xs => generalize dependent x; genDeps xs
    |HNil => idtac
  end. 







