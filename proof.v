
Require Import Coq.ZArith.BinInt.
Require Import Coq.Numbers.BinNums.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.Zbool.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Omega.
Require Import Coq.Bool.Sumbool.


(* An index into memory *)
Definition Ix := Z.

(* values in memory *)
Definition MemValue := Z.

(* factor used in building expressions *)
(*Inductive Factor : Set := Raw : MemValue -> Factor. *)

(* A statement in our grammar *)
Inductive Stmt : Type := Write : Z -> MemValue -> Stmt.

(* A program is a list of statements *)
Inductive Program : Type :=
  Program2Stmts : Stmt -> Stmt -> Program.

(* Memory is a function from an index to a value *)
Definition Memory :=  Ix -> MemValue.

(* initial state of memory *)
Definition initMemory : Memory := fun ix => Z0.

Theorem initMemoryAlwaysZero : forall (wix: Ix), (initMemory wix) = Z0.
Proof.
  auto.
Qed.


Definition writeToMemory (wix: Ix) (wval: MemValue) (mold: Memory) : Memory :=
  fun ix => if Zeq_bool ix wix then wval else mold ix.

Theorem readFromWriteIdentical : forall (wix: Ix) (wval: MemValue) (mem: Memory),
    (writeToMemory wix wval mem) wix = wval.
Proof.
  intros wix wval mem.
  unfold writeToMemory.
  assert ((wix = wix)).
  reflexivity.
  rewrite  Zeq_is_eq_bool in H.
  rewrite H.
  reflexivity.
Qed.

Theorem readFromWriteDifferent : forall (wix: Ix) (rix: Ix) (wval : MemValue) (mem: Memory),
    rix <> wix -> (writeToMemory wix wval mem) rix = mem rix.
Proof.
  intros wix rix wval mem.
  intros rix_neq_wix.
  unfold writeToMemory.
  rewrite Zeq_is_eq_bool in rix_neq_wix.
Admitted.



  

(* Model the effect of memory writes on memory. *)
Definition modelStmtMemorySideEffect (s: Stmt) (mold: Memory) : Memory :=
  match s with
  | Write wix wval => (writeToMemory wix wval mold)
  end.

Definition modelProgramMemorySideEffect (p: Program) : Memory :=
  match p with
  | Program2Stmts s1 s2 => let s1mem := (modelStmtMemorySideEffect s1 initMemory) in
                           (modelStmtMemorySideEffect s2 s1mem)
  end.


(* Two programs are equivalent if their final states of memory is the same *)
Definition programsEquivalent (p:Program) (q: Program) : Prop :=
  modelProgramMemorySideEffect p  = modelProgramMemorySideEffect q.


(* State theorem I wish to prove. *)
(* If array indeces are not equal, it is safe to flip them*)
Definition AllowFlipIfWritesDontAlias : Prop :=
  forall (i1 i2: Ix), forall (v1 v2: MemValue),
      i1 <> i2 ->
  programsEquivalent
    (Program2Stmts (Write i1 v1) (Write i2 v2))
    (Program2Stmts (Write i2 v2) (Write i1 v1)).

(* Theorem about integer equalities I need to separate writes into disjoint sets *)
Theorem trichotomy: forall (i1 i2 scrutinee: Ix), i1 <> i2 -> (scrutinee = i1) \/ (scrutinee = i2) \/ (scrutinee <> i1 /\ scrutinee <> i2).
Proof.
  intros i1 i2 scrutinee.
  omega.
Qed.

Theorem allowFlipIfWritesDontAlias:
  forall (i1 i2: Ix), forall (v1 v2: MemValue),
      i1 <> i2 ->
  programsEquivalent
    (Program2Stmts (Write i1 v1) (Write i2 v2))
    (Program2Stmts (Write i2 v2) (Write i1 v1)).
Proof.
  intros i1 i2.
  intros v1 v2.
  intros i1_neq_i2.
  unfold programsEquivalent.
  unfold modelProgramMemorySideEffect.
  unfold modelStmtMemorySideEffect.
  extensionality curix.
  assert (curix = i1) \/ (curix = i2) \/ (curix <> i1 /\ curix <> i2).

Qed.


(**** Schedule stuff for later, I know nothing on how to prove this stuff ****)
(* A timepoint for a schedule *)
Definition Timepoint := nat. 

(* A schedule maps statements to time points *)
Definition ScheduleMap := Stmt -> Timepoint.

