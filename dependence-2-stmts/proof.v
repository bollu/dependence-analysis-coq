Require Import Coq.ZArith.BinInt.
Require Import Coq.ZArith.BinIntDef.
Require Import Coq.Numbers.BinNums.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.Zbool.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Omega.
Require Import Coq.Bool.Sumbool.
Require Import Coq.ZArith.Zhints.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Structures.Equalities.

Open Scope Z_scope.


(** An index into memory *)
Notation Ix := Z.

(** values in memory *)
Definition MemValue := Z.


(** A statement in our grammar *)
Inductive Stmt : Type := Write : Z -> MemValue -> Stmt.

(** A program is a list of statements *)
Inductive Program : Type :=
  Program2Stmts : Stmt -> Stmt -> Program.

(** Memory is a function from an index to a value *)
Definition Memory :=  Ix -> MemValue.

(** initial state of memory *)
Definition initMemory : Memory := fun ix => Z0.

(** Lemma that describes the initial state of memory as being zeroed out *)
Theorem initMemoryAlwaysZero : forall (wix: Ix), (initMemory wix) = Z0.
Proof.
  auto.
Qed.


(** Implement writing to memory *)
Definition writeToMemory (wix: Ix) (wval: MemValue) (mold: Memory) : Memory :=
  fun ix => if (ix =? wix)%Z then wval else mold ix.

(* Show that reading from a memory location that has been written to returns
the written value *)
Theorem readFromWriteIdentical : forall (wix: Ix) (wval: MemValue) (mem: Memory),
    (writeToMemory wix wval mem) wix = wval.
Proof.
  intros wix wval mem.
  unfold writeToMemory.
  rewrite Z.eqb_refl.
  reflexivity.
Qed.


(** Reading from a memory location that was written to, when the read does not
alias the write queries the previous state of memory *)
Theorem readFromWriteDifferent : forall (wix: Ix) (rix: Ix) (wval : MemValue) (mem: Memory),
    rix <> wix -> (writeToMemory wix wval mem) rix = mem rix.
Proof.
  intros wix rix wval mem.
  intros rix_neq_wix.
  unfold writeToMemory.
  assert((rix =? wix)%Z = false).
  apply Z.eqb_neq in rix_neq_wix.
  auto.
  rewrite H.
  reflexivity.
Qed.


(** Model the effect of memory writes on memory. *)
Definition modelStmtMemorySideEffect (s: Stmt) (mold: Memory) : Memory :=
  match s with
  | Write wix wval => (writeToMemory wix wval mold)
  end.

(** A program's effect on memory is to sequentially execute its statements *)
Definition modelProgramMemorySideEffect (p: Program) : Memory :=
  match p with
  | Program2Stmts s1 s2 => let s1mem := (modelStmtMemorySideEffect s1 initMemory) in
                           (modelStmtMemorySideEffect s2 s1mem)
  end.


(** Two programs are equivalent if their final states of memory is the same *)
Definition programsEquivalent (p:Program) (q: Program) : Prop :=
  modelProgramMemorySideEffect p  = modelProgramMemorySideEffect q.


(* Theorem about integer equalities I need to separate writes into disjoint sets *)
Theorem trichotomy: forall (i1 i2 scrutinee: Ix), i1 <> i2 -> (scrutinee = i1) \/ (scrutinee = i2) \/ (scrutinee <> i1 /\ scrutinee <> i2)%Z.
Proof.
  intros.
  omega.
Qed.

(** Theorem to be proven: If array indeces are not equal, it is safe to flip writes *)
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
  destruct (trichotomy i1 i2 curix).
  auto.
  rewrite readFromWriteDifferent.
  rewrite H.
  rewrite readFromWriteIdentical.
  rewrite readFromWriteIdentical.
  reflexivity.
  omega.
  destruct H.
  rewrite H.
  rewrite readFromWriteIdentical.
  rewrite readFromWriteDifferent.
  rewrite readFromWriteIdentical.
  auto.
  auto.
  rewrite readFromWriteDifferent.
  rewrite readFromWriteDifferent.
  rewrite readFromWriteDifferent.
  rewrite readFromWriteDifferent.
  auto.
  omega.
  omega.
  omega.
  omega.
Qed.

