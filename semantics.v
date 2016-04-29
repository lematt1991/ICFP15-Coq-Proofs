Set Implicit Arguments.
Require Export heap.           
Require Export Omega.   
Require Export hetList. 
Require Export Coq.Program.Equality. 

(*evaluation context decomposition*)
Inductive decompose : term -> ctxt -> term -> Prop :=
|decompApp : forall e1 e2 E e, decompose e1 E e ->
                               decompose (app e1 e2) (appCtxt e2 E) e
|decompAppVal : forall v e2 E e (prf:value v), 
                  decompose e2 E e -> decompose (app v e2) (appValCtxt v prf E) e
|appHole : forall e v, value v -> decompose (app (lambda e) v) hole (app (lambda e) v)
|decompGet : forall e E e', decompose e E e' -> 
                            decompose (get e) (getCtxt E) e'
|decompGetHole : forall l, decompose (get (loc l)) hole (get (loc l))
|decompPut : forall e1 e2 E e, decompose e1 E e -> 
                               decompose (put e1 e2) (putCtxt e2 E) e
|decompPutVal : forall v e2 E e (prf:value v), 
                  decompose e2 E e -> 
                  decompose (put v e2) (putValCtxt v prf E) e
|decompPutHole : forall n v, value v -> decompose (put (loc n) v) hole (put (loc n) v)
|decompAlloc : forall e E e', decompose e E e' ->
                         decompose (alloc e) (allocCtxt E) e'
|decompAllocHole : forall v, value v -> decompose (alloc v) hole (alloc v)
|decompAtomicHole : forall e, decompose (atomic e) hole (atomic e)
|decompFork : forall e, decompose (fork e) hole (fork e)
|decompInAtomic : forall e e' E, decompose e E e' ->
                            decompose (inatomic e) (inatomicCtxt E) e'
|decompInAtomicHole : forall v, value v -> decompose (inatomic v) hole (inatomic v). 

(*values cannot be decomposed*)
Theorem decomposeValFalse : forall t E e, value t -> decompose t E e -> False. 
Proof.
  intros t E e v d. inv d; try solve[inv v]. 
Qed. 
 
(*proves that values cannot be decomposed*)
Ltac decompVal :=
  match goal with
      |H:value ?t, H':decompose ?t ?E ?e |- _ => 
       apply decomposeValFalse in H'; auto; inv H'
      |H:decompose (lambda ?e) ?E ?e' |- _ => inv H
      |H:decompose (loc ?l) ?E ?e |- _ => inv H
  end. 

(*inverts a decomposition nested inside another*)
Ltac invertDecomp := 
  match goal with
      |H:decompose (app ?e1 ?e2) ?E ?e |- _ => inv H
      |H:decompose (get ?e) ?E ?e' |- _ => inv H
      |H:decompose (put ?e1 ?e2) ?E ?e |- _ => inv H
      |H:decompose (alloc ?e) ?E ?e' |- _ => inv H
      |H:decompose (fork ?e) ?E ?e' |- _ => inv H
      |H:decompose (inatomic ?e) ?E ?E' |- _ => inv H
  end. 

(*evaluation context decomposition is deterministic*)
Theorem decomposeDeterministic : forall t E E' e e', 
                                   decompose t E e -> decompose t E' e' ->
                                   E = E' /\ e = e'. 
Proof.
  intros t E E' e e' HD1 HD2. genDeps {{ E'; e'}}. 
  induction HD1; intros; try(invertDecomp; try decompVal); try solve[auto |
  match goal with
    |H:forall e'0 E', decompose ?e E' e'0 -> ?E = E' /\ ?e' = e'0, 
     H':decompose ?e ?E'' ?e'' |- _ =>  apply H in H'; invertHyp; eauto; try (proofsEq; eauto)
  end]. 
  inv HD2. eauto. 
Qed. 
 
(*proves that the results of the same decomposition are the same*)
Ltac decompSame :=
  match goal with
      |H:decompose ?t ?E ?e,H':decompose ?t ?E' ?e' |- _ =>
       eapply decomposeDeterministic in H; eauto; invertHyp
  end.  

(*fill an evaluation context*)
Fixpoint fill (E:ctxt) (e:term) := 
  match E with
      |appCtxt e' E => app (fill E e) e'
      |appValCtxt v _ E => app v (fill E e)
      |getCtxt E => get (fill E e)
      |putCtxt e' E => put (fill E e) e'
      |putValCtxt v _ E => put v (fill E e)
      |allocCtxt E => alloc (fill E e)
      |inatomicCtxt E => inatomic (fill E e)
      |hole => e 
  end.

(*
commit H1 H2:
  -indicates the log is valid 
  -HI has writes undone in case we later find a violation (invalid heap)
  -HV keeps values in place but releases locks (valid heap)
abort e L ==> log was invalid, resume execution at term e with log L
*)
Inductive validateRes : Type := 
|commit : chkpnt -> heap -> heap -> validateRes 
|abort : chkpnt -> heap -> validateRes. 

Definition invalidHeap res :=
  match res with
  |commit _ H _ => H
  |abort _ H => H
  end. 

Inductive invalidStamp (tid : nat) (rv : nat) : lock -> Prop :=
| StampStale : forall s, rv < s -> invalidStamp tid rv (Unlocked s)
| StampLocked : forall s v s', s <> tid -> invalidStamp tid rv (Locked s s' v). 

Inductive validStamp (tid : nat) (rv : nat) : lock -> Prop :=
| LockOwned : forall s' v, validStamp tid rv (Locked tid s' v)
| StampFresh : forall s, rv >= s -> validStamp tid rv (Unlocked s).

Theorem validInvalidStamp : forall tid S lock,
                              validStamp tid S lock ->
                              invalidStamp tid S lock -> False. 
Proof.
  intros tid S lock H H0.
  inv H; inv H0; auto. omega.
Qed.

(* Transactional log validation
 * Validate RV L H WV Res
 * RV - read version
 * RS - read set
 * H - heap
 * WV - write version
 * Res - result of validation, either:
 *    + commit - validation succeeded
 *    + abort e L - abort, picking up with term `e` and log `L`
 *)

Inductive readTail : forall b, log b -> log b -> Prop :=
|cTail : forall l v E L, readTail (Chkpnt l E v L) L
|rTail : forall l v L, readTail (Read l v L) L.  

Inductive validate (tid : nat) (rv wv : nat) (e0 : term) : forall b, log b -> heap -> validateRes -> Prop :=
|validNil : forall H, validate tid rv wv e0 NilLog H (commit (e0, NilLog) H H)
|validChkpnt : forall lock l v v' E H HI HV L chkpnt,
                    H l = Some(v', lock) -> validStamp tid rv lock ->
                    validate tid rv wv e0 L H (commit chkpnt HV HI) ->
                    validate tid rv wv e0 (Chkpnt l E v L) H (commit (fill E (get (loc l)), L) HV HI)
|invalidChkpnt : forall lock l v v' E H HI HV L chkpnt,
                   H l = Some(v', lock) -> invalidStamp tid rv lock ->
                   validate tid rv wv e0 L H (commit chkpnt HI HV) ->
                   validate tid rv wv e0 (Chkpnt l E v L) H (abort chkpnt(*(fill E (get (loc l)), L)*) HI)
|validRead : forall lock l v v' H HI HV L chkpnt,
               H l = Some(v', lock) -> validStamp tid rv lock ->
               validate tid rv wv e0 L H (commit chkpnt HI HV) ->
               validate tid rv wv e0 (Read l v L) H (commit chkpnt HI HV)
|invalidRead : forall lock l v v' H HI HV L chkpnt,
                 H l = Some(v', lock) -> invalidStamp tid rv lock ->
                 validate tid rv wv e0 L H (commit chkpnt HI HV) ->
                 validate tid rv wv e0 (Read l v L) H (abort chkpnt HI)
|validWrite : forall l v v' H HI HV b (L : log b) chkpnt oldV,
                H l = Some(v, Locked tid oldV v') -> rv >= oldV -> Log.notIn l b L ->
                validate tid rv wv e0 L H (commit chkpnt HI HV) -> 
                validate tid rv wv e0 (Write b l L) H
                         (commit chkpnt (update HI l v' (Unlocked oldV))
                                 (update HV l v (Unlocked wv)))
|readPropAbort : forall b H chkpnt HI L L',
                   validate tid rv wv e0 L' H (abort chkpnt HI) ->
                   readTail L L' ->
                   @validate tid rv wv e0 b L H (abort chkpnt HI)
|writePropAbort : forall H chkpnt HI b l v v' oldV L,
                    validate tid rv wv e0 L H (abort chkpnt HI) ->
                    H l = Some(v, Locked tid oldV v') -> Log.notIn l b L -> rv >= oldV ->  
                    validate tid rv wv e0 (Write b l L) H
                             (abort chkpnt (update HI l v' (Unlocked oldV))). 

Ltac invertHyp :=
  match goal with
  |H : readTail (Chkpnt ?l ?E ?v ?L) ?L' |- _ => dependent destruction H; try invertHyp
  |H : readTail (Read ?l ?v ?L) ?L' |- _ => dependent destruction H; try invertHyp
  |H : readTail (Write ?b ?l ?L) ?L' |- _ => dependent destruction H
  |H : readTail NilLog ?L' |- _ => dependent destruction H
  |H : validate ?tid ?S ?C ?e0 (Read ?l ?v ?L) ?H0 ?res |- _ => dependent destruction H; try invertHyp
  |H : validate ?tid ?S ?C ?e0 (Chkpnt ?l ?E ?v ?L) ?H0 ?res |- _ => dependent destruction H; try invertHyp
  |H : validate ?tid ?S ?C ?e0 (Write ?b ?l ?L) ?H0 ?res |- _ => dependent destruction H; try invertHyp
  |H : validate ?tid ?S ?C ?e0 NilLog ?H0 ?res |- _ => dependent destruction H; try invertHyp
  |H : Log.notIn ?l ?b (Chkpnt ?l' ?E ?v ?L) |- _ => dependent destruction H; try invertHyp
  |H : Log.notIn ?l ?b (Read ?l' ?v ?L) |- _ => dependent destruction H; try invertHyp
  |H : Log.notIn ?l ?b (Write ?b' ?l' ?L) |- _ => dependent destruction H; try invertHyp
  |H : Log.In ?l (Chkpnt ?l' ?E ?v ?L) |- _ => dependent destruction H; try invertHyp
  |H : Log.In ?l (Read ?l' ?v ?L) |- _ => dependent destruction H; try invertHyp
  |H : Log.In ?l (Write ?b' ?l' ?L) |- _ => dependent destruction H; try invertHyp
  |H : locked ?tid ?lock |- _ => inv H; try invertHyp
  |H : invalidStamp ?tid ?rv (Locked ?tid' ?oldV ?v) |- _ => inv H; try invertHyp
  |H : invalidStamp ?tid ?rv (Unlocked ?v) |- _ => inv H; try invertHyp
  | _ => tactics.invertHyp
  end.

Fixpoint open (e:term) (k:nat) (e':term) :=
  match e with
      |lambda e => lambda (open e (S k) e')
      |loc l => loc l
      |unit => unit
      |var k' => if eq_nat_dec k k'
                then e'
                else var k'
      |app e1 e2 => app (open e1 k e') (open e2 k e')
      |get e => get (open e k e')
      |put e1 e2 => put (open e1 k e') (open e2 k e')
      |alloc e => alloc (open e k e')
      |fork e => fork (open e k e')
      |atomic e => atomic (open e k e')
      |inatomic e => inatomic (open e k e')
  end. 


Inductive acquireLock (l : location) (v : term) (tid rv : nat) : forall b, log b -> lock -> lock -> log true -> Prop :=
| acquireLocked : forall L oldV,
    Log.In l L -> (*already locked it*)
    acquireLock l v tid rv L (Locked tid oldV v) (Locked tid oldV v) L    
| acquireUnlocked : forall b L S',
    rv >= S' -> Log.notIn l b L -> (*newly acquired*)
    acquireLock l v tid rv L (Unlocked S') (Locked tid S' v) (Write b l L).   

Inductive trans_step : heap -> thread -> heap -> thread -> Prop :=
(*read after write*)
|t_readChkpnt : forall S (L : log false) E l t tid v e0 lock H, 
                  decompose t E (get (loc l)) -> 
                  H l = Some(v, lock) -> validStamp tid S lock ->
                  trans_step H (txThread false tid S e0 L t) H
                             (txThread false tid S e0 (Chkpnt l E v L) (fill E v))
|t_readNoChkpnt : forall S L E l t tid v e0 lock H, 
                  decompose t E (get (loc l)) -> 
                  H l = Some(v, lock) -> validStamp tid S lock ->
                  trans_step H (txThread true tid S e0 L t) H
                             (txThread true tid S e0 (Read l v L) (fill E v))
|t_writeLocked : forall b S L tid E l L' t v v' e0 H lock lock',
                   decompose t E (put (loc l) v) ->
                   H l = Some(v', lock) -> acquireLock l v' tid S L lock lock' L' ->
                   trans_step H (txThread b tid S e0 L t) (update H l v lock')
                              (txThread true tid S e0 L' (fill E unit))
|t_atomicIdemStep : forall b E e t tid L H S e0,
                     decompose t E (atomic e) -> 
                     trans_step H (txThread b tid S e0 L t) H (txThread b tid S e0 L (fill E e))
|t_betaStep : forall b L E e t v tid S e0 H, 
              decompose t E (app (lambda e) v) -> 
              trans_step H (txThread b tid S e0 L t) H (txThread b tid S e0 L (fill E (open e 0 v)))
.

(*if lock is acquired, then read backed up value, otherwise pull a value out of thin air*)
Inductive mkVal (rv : nat) : lock -> term -> Prop :=
| mkLockedValid : forall tid oldV v, rv >= oldV -> mkVal rv (Locked tid oldV v) v
| mkLockedInvalid : forall tid oldV v v', rv < oldV -> mkVal rv (Locked tid oldV v) v'
| mkUnlocked : forall stamp v, mkVal rv (Unlocked stamp) v. 

Inductive readOrChkpnt l v E : forall b, log b -> log b -> Prop :=
|chkpnt : forall tail, @readOrChkpnt l v E false tail (Chkpnt l E v tail)
|nochkpnt : forall tail, @readOrChkpnt l v E true tail (Read l v tail). 

Inductive replay_step : heap -> thread -> heap -> thread -> Prop :=
(*read after write*)
|r_readChkpnt : forall S (L : log false) E l t tid v e0 lock H, 
                decompose t E (get (loc l)) -> 
                H l = Some(v, lock) -> validStamp tid S lock ->
                replay_step H (txThread false tid S e0 L t) H
                            (txThread false tid S e0 (Chkpnt l E v L) (fill E v))
|r_readNoChkpnt : forall S L E l t tid v e0 lock H, 
                  decompose t E (get (loc l)) -> 
                  H l = Some(v, lock) -> validStamp tid S lock ->
                  replay_step H (txThread true tid S e0 L t) H
                             (txThread true tid S e0 (Read l v L) (fill E v))
|r_readStepInvalid : forall b S L tid E H l t v e0 lock v' L', 
                       decompose t E (get (loc l)) -> mkVal S lock v' ->
                       H l = Some(v, lock) -> invalidStamp tid S lock ->
                       readOrChkpnt l v' E L L' -> 
                       replay_step H (txThread b tid S e0 L t) H
                                   (txThread b tid S e0 L' (fill E v'))
|r_writeLocked : forall b S L tid E l t v v' e0 H lock lock' L',
                   decompose t E (put (loc l) v) ->
                   H l = Some(v', lock) -> acquireLock l v' tid S L lock lock' L' ->
                   replay_step H (txThread b tid S e0 L t) (update H l v lock')
                               (txThread true tid S e0 L' (fill E unit))
|r_atomicIdemStep : forall b E e t tid L H S e0,
                     decompose t E (atomic e) -> 
                     replay_step H (txThread b tid S e0 L t) H (txThread b tid S e0 L (fill E e))
|r_betaStep : forall b L E e t v tid S e0 H, 
              decompose t E (app (lambda e) v) -> 
              replay_step H (txThread b tid S e0 L t) H (txThread b tid S e0 L (fill E (open e 0 v)))
. 

(*reflexive transitive closure of replay_step*)
Inductive replay : heap -> thread -> heap -> thread -> Prop :=
|replayRefl : forall H t, replay H t H t
|replayStep : forall t t' t'' H H' H'', 
                replay_step H t H' t' -> replay H' t' H'' t'' -> 
                replay H t H'' t''. 

(*left recursive version of replay*)
Inductive rewind : heap -> thread -> heap -> thread -> Prop :=
|rewindRefl : forall t H, rewind H t H t
|rewindStep : forall t t' t'' H H' H'', 
                rewind H t H' t' -> replay_step H' t' H'' t'' -> 
                rewind H t H'' t''. 

Definition step_sig := nat -> heap -> pool -> nat -> heap -> pool -> Prop. 

(*common steps (single step)*)
Inductive c_step (st : step_sig) : step_sig :=
|c_liftedStep : forall C H P C' H' P',
                  st C H P C' H' P' ->
                  c_step st C H P C' H' P'
|c_transStep : forall C H H' t t', trans_step H t H' t' -> 
                           c_step st C H (Single t) C H' (Single t')
|c_parLStep : forall C H T1 T2 C' H' T1', 
          c_step st C H T1 C' H' T1' -> c_step st C H (Par T1 T2) C' H' (Par T1' T2)
|c_parRStep : forall C H T1 T2 C' H' T2', 
          c_step st C H T2 C' H' T2' -> c_step st C H (Par T1 T2) C' H' (Par T1 T2')
|c_forkStep : forall C H E e tid t, 
              decompose t E (fork e) ->
              c_step st C H (Single(noTXThread tid t)) (S C) H 
                   (Par (Single(noTXThread tid (fill E unit))) (Single(noTXThread C e)))
|c_allocStep : forall C H v E t l tid, 
               H l = None -> decompose t E (alloc v) ->
               c_step st C H (Single(noTXThread tid t)) C (update H l v (Unlocked 0))
                    (Single(noTXThread tid (fill E (loc l))))
|c_commitStep : forall b C H HI HV chkpnt S L v t tid E e0, 
                  validate tid S C e0 L H (commit chkpnt HI HV) -> decompose t E (inatomic v) ->
                  c_step st C H (Single(txThread b tid S e0 L t)) (plus 1 C)
                         HV (Single(noTXThread tid (fill E v)))
|c_atomicStep : forall C H E e t tid, 
                decompose t E (atomic e) ->
                c_step st C H (Single(noTXThread tid t)) (S C) H 
                       (Single(txThread false tid C (fill E(inatomic e)) NilLog (fill E (inatomic e))))
|c_betaStep : forall C H E e t v tid, 
              decompose t E (app (lambda e) v) -> 
              c_step st C H (Single(noTXThread tid t)) C H
                     (Single(noTXThread tid (fill E (open e 0 v))))
|c_tsExtend : forall b C H t S L e0 tid HI HV chkpnt,
                validate tid S C e0 L H (commit chkpnt HI HV) ->
                c_step st C H (Single(txThread b tid S e0 L t)) (plus 1 C) H
                       (Single(txThread b tid C e0 L t))
.

Inductive p_step_ : nat -> heap -> pool -> nat -> heap -> pool -> Prop :=
|p_abortStep : forall b L L' S H H' tid C e e0 e', 
                 validate tid S C e0 L H (abort (e', L') H') ->
                 p_step_ C H (Single(txThread b tid S e0 L e))
                        (plus 1 C) H' (Single(txThread false tid C e0 L' e'))
.

(*full abort STM semantics (single step)*)
Inductive f_step_ : nat -> heap -> pool -> nat -> heap -> pool -> Prop :=
|f_abortStep : forall b L L' S H H' tid C e e0 e', 
                 validate tid S C e0 L H (abort (e', L') H') ->
                 f_step_ C H (Single(txThread b tid S e0 L e))
                        (plus 1 C) H' (Single(txThread false tid C e0 NilLog e0))
. 

Definition p_step := c_step p_step_.
Definition f_step := c_step f_step_. 

(*reflexive transitive closure of partial multistep*)
Inductive multistep (st : step_sig) : step_sig :=
|c_multi_refl : forall C H T, multistep st C H T C H T
|c_multi_step : forall C H T C' H' T' C'' H'' T'', 
                  st C H T C' H' T' -> multistep st C' H' T' C'' H'' T'' ->
                  multistep st C H T C'' H'' T''. 

Inductive multistep_rev (st : step_sig) : step_sig :=
|c_multi_rev_refl : forall C H T, multistep_rev st C H T C H T
|c_multi_rev_step : forall C H T C' H' T' C'' H'' T'', 
    multistep_rev st C H T C' H' T' -> st C' H' T' C'' H'' T'' -> 
    multistep_rev st C H T C'' H'' T''.

Definition f_multistep := multistep f_step.
Definition p_multistep := multistep p_step.

(*reflexivit transitive closure of trans_step*)
Inductive trans_multistep : heap -> thread -> heap -> thread -> Prop :=
|trans_refl : forall t H, trans_multistep H t H t
|trans_multi_step : forall t t' t'' H H' H'', 
                      trans_step H t H' t' -> trans_multistep H' t' H'' t'' ->
                      trans_multistep H t H'' t''. 

(*indicates that L1 is a postfix of L2*)
Definition postfix {A:Type} (L1 L2 : list A) := exists diff, L2 = diff ++ L1. 

Require Export Coq.Sets.Ensembles. 

Fixpoint ids P :=
  match P with
  | Par P1 P2 => Union nat (ids P1) (ids P2)
  | Single (noTXThread id _) => Singleton nat id
  | Single (txThread _ id _ _ _ _) => Singleton nat id
  end. 

(*all threads can rewind to their initial term of a transaction and have
**a stamp number less than the global clock.  The stamp number 
**constraint probably doesn't belong here, but its handy to have*)
Inductive poolRewind (C : nat) (H : heap) : pool -> Prop :=
|rewindSingleNoTX : forall tid e, tid < C -> poolRewind C H (Single(noTXThread tid e))
|rewindSingleInTX : forall b tid S e0 L e H',
                      rewind H' (txThread false tid S e0 NilLog e0) H (txThread b tid S e0 L e) ->
                      tid < C -> S < C -> poolRewind C H (Single(txThread b tid S e0 L e)) 
|rewindPar : forall T1 T2,
    Disjoint nat (ids T1) (ids T2) ->
    poolRewind C H T1 -> poolRewind C H T2 -> poolRewind C H (Par T1 T2). 

Inductive unique (C : nat) : pool -> Prop :=
|SingletonNoTX : forall id e, id < C -> unique C (Single (noTXThread id e))
|SingletonTX : forall b id rv e0 L e, id < C -> unique C (Single (txThread b id rv e0 L e))
|ParUnique : forall T1 T2,
    Disjoint nat (ids T1) (ids T2) -> unique C T1 -> unique C T2 ->
    unique C (Par T1 T2). 

(*inject every step in a multistep derivation into a Par*)
Theorem multi_L : forall st C H T1 T2 T1' C' H', 
                      multistep (c_step st) C H T1 C' H' T1' ->
                      multistep (c_step st) C H (Par T1 T2) C' H' (Par T1' T2). 
Proof.
  intros st C H T1 T2 T1' C' H' HYP. induction HYP.
  {constructor. }
  {econstructor. eapply c_parLStep. eassumption. auto. }
Qed. 
  
(*inject every step in a multistep derivation into a Par*)
Theorem multi_R : forall st C H T1 T2 T2' C' H', 
                      multistep (c_step st) C H T2 C' H' T2' ->
                      multistep (c_step st) C H (Par T1 T2) C' H' (Par T1 T2'). 
Proof.
  intros st C H T1 T2 T2' C' H' HYP. induction HYP.
  {constructor. }
  {econstructor. eapply c_parRStep. eassumption. eassumption. }
Qed. 

(*filling an evaluation context with the result of a decomposition
**yields the initial term that was decomposed *)
Theorem decomposeEq : forall E t e, decompose t E e -> t = fill E e. 
Proof.
  induction E; intros; try solve[inv H; simpl;erewrite <- IHE; eauto]. 
  {inv H; auto. }
Qed. 

Theorem lengthsEq : forall (A:Type) (x y : list A), x = y -> length x = length y. 
Proof.
  induction x; intros. 
  {destruct y. auto. inv H. }
  {destruct y. inv H. inv H. simpl. apply f_equal. auto. }
Qed. 


(*replay relation is transitive*)
Theorem trans_replay: forall H H' H'' t t' t'', 
                         replay H' t' H'' t'' -> replay H t H' t' ->
                         replay H t H'' t''. 
Proof.
  intros H H' H'' t t' t'' HYP1 HYP2. induction HYP2.
  auto. econstructor. eauto. auto. 
Qed. 

(*rewind relation is transitive*)
Theorem rewindTrans : forall H H' H'' t t' t'', 
                        rewind H t H' t' -> rewind H' t' H'' t'' ->
                        rewind H t H'' t''. 
Proof.
  intros H H' H'' t t' t'' HYP1 HYP2. genDeps{{H; t}}.
  induction HYP2; intros; auto.
  econstructor. eapply IHHYP2. assumption. assumption. 
Qed. 

(*replay and rewind are equivalent*)
Theorem rewindIFFReplay : forall H H' t t', 
                            rewind H t H' t' <-> replay H t H' t'. 
Proof.
  intros H H' t t'. split; intros HYP. 
  {induction HYP. constructor. eapply trans_replay; eauto.
   econstructor. eauto. constructor. }
  {induction HYP. constructor. eapply rewindTrans; eauto.
   econstructor; eauto. constructor. }
Qed. 


(*partial multistep relation is transitive*)
Theorem multi_trans : forall st C H T C' H' T' C'' H'' T'',
                          multistep st C H T C' H' T' ->
                          multistep st C' H' T' C'' H'' T'' ->
                          multistep st C H T C'' H'' T''.
Proof.
  intros st C H T C' H' T' C'' H'' T'' HYP1 HYP2. 
  induction HYP1; auto. econstructor; eauto.
Qed. 

Theorem multi_rev_trans : forall st C H T C' H' T' C'' H'' T'',
    multistep_rev st C H T C' H' T' ->
    multistep_rev st C' H' T' C'' H'' T'' ->
    multistep_rev st C H T C'' H'' T''.
Proof.
  intros st C H T C' H' T' C'' H'' T'' HYP1 HYP2. 
  induction HYP2; auto.
  econstructor; auto.
Qed. 

Theorem multistep_rev_forward : forall st C H T C' H' T',
    multistep st C H T C' H' T' -> multistep_rev st C H T C' H' T'.
Proof.
  intros. induction H0.
  {constructor. }
  {eapply multi_rev_trans. eapply c_multi_rev_step. constructor.
   eauto. eauto. }
Qed. 

Theorem multistep_rev_backward : forall st C H T C' H' T',
    multistep_rev st C H T C' H' T' -> multistep st C H T C' H' T'. 
  intros. induction H0.
  {constructor. }
  {eapply multi_trans. eauto. eapply c_multi_step. eauto. constructor. }
Qed. 

Theorem multistep_rev_eq : forall st C H T C' H' T',
    multistep st C H T C' H' T' <-> multistep_rev st C H T C' H' T'. 
Proof.
  intros. split. apply multistep_rev_forward.
  apply multistep_rev_backward.
Qed. 