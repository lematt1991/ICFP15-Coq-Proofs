Require Export List. 
Export ListNotations. 
Require Export tactics.
Open Scope type_scope. 

Inductive term : Type :=
|lambda : term -> term
|loc : nat -> term
|unit : term
|var : nat -> term
|app : term -> term -> term
|get : term -> term
|put : term -> term -> term
|alloc : term -> term
|fork : term -> term
|atomic : term -> term
|inatomic : term -> term. 

Inductive value : term -> Prop :=
|v_lam : forall e, value (lambda e)
|v_loc : forall n, value (loc n)
|v_unit : value unit. 

(*Evaluation context*)
Inductive ctxt : Type :=
|hole : ctxt
|appCtxt : term -> ctxt -> ctxt
|appValCtxt (t:term) : value t -> ctxt -> ctxt
|getCtxt : ctxt -> ctxt
|putCtxt : term -> ctxt -> ctxt 
|putValCtxt (t:term) : value t -> ctxt -> ctxt
|allocCtxt : ctxt -> ctxt
|inatomicCtxt : ctxt -> ctxt. 

(*location (address)*)
Definition location := nat.

(*timestamp used by the STM*)
Definition stamp := nat. 

Inductive log : bool -> Type :=
|Read : forall b, location -> term -> log b -> log b
|Chkpnt : location -> ctxt -> term -> log false -> log false
|Write : forall b, location -> log b -> log true
|NilLog : log false.

Module Log.

  Inductive notIn (l : location) : forall b, log b -> Prop :=
  |notInNil : notIn l false NilLog
  |notInRead : forall l' v' b L, notIn l b L -> notIn l b (Read b l' v' L)
  |notInChkpnt : forall l' v E L, notIn l false L -> notIn l false (Chkpnt l' v E L)
  |notInWrite : forall l' b L, l <> l' -> notIn l b L -> notIn l true (Write b l' L). 
  
  Inductive In (l : location) : log true -> Prop :=
  |InRead : forall l' v L, In l L -> In l (Read true l' v L)
  |InWrite : forall b L, notIn l b L -> In l (Write b l L)
  |InWriteNext : forall L l',
                   l <> l' ->
                   In l L -> In l (Write true l' L). 
End Log. 

Inductive lock : Type :=
|Locked : nat -> nat -> term -> lock     (*ID of thread who owns lock, previous stamp and previous val*)
|Unlocked : nat -> lock   (*version number*)
. 
(*"Address" * contents * stamp*)
Definition TVar := location * term * lock. 

(*thread ID, start TX info, read set, write set, term*)
Inductive thread : Type :=
|noTXThread : nat -> term -> thread
|txThread : forall b, nat -> nat -> term -> log b -> term -> thread
.
                   
Inductive pool : Type := 
|Single : thread -> pool
|Par : pool -> pool -> pool. 

Definition chkpnt := term * log false.

 