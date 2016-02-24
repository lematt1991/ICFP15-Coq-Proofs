Require Export Coq.Init.Datatypes. 
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

(*log entry for STM metadata*)
Inductive logItem : Type := 
|readItem : location -> ctxt -> term -> logItem
|writeItem : location -> term -> logItem
. 

Definition log := list logItem. 
 
Definition thread := option (nat * term) * log * term. 

Inductive pool : Type := 
|Single : thread -> pool
|Par : pool -> pool -> pool. 





 