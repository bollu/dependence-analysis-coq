Require Import Coq.Lists.List.
Require Import FunInd.
Require Import Coq.Lists.ListSet.
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
Require Import Coq.FSets.FMapInterface.
Require Import FMapAVL.
Require Import FMapFacts.
Require Import Coq.Logic.FinFun.
Require Import Nat.
Require Import VectorDef.
Require Import MSetWeakList.

(* thank you kind stranger for showing me functorial modules syntax *)
(* http://newartisans.com/2016/10/using-fmap-in-coq/ *)

Require Import
  Coq.FSets.FMapList
  Coq.Structures.OrderedTypeEx.

Module Import M := FMapList.Make(Z_as_OT).
Module Import MFacts := WFacts(M).



Require Import
  Coq.FSets.FMapFacts.

(*Module P := WProperties_fun N_as_OT M.
*)



(* An index into memory *)
Definition MemIx := Z.

(* values in memory *)
Definition MemValue := Z.

(* factor used in building expressions *)
(*Inductive Factor : Set := Raw : MemValue -> Factor. *)

(* A statement in our grammar *)
Inductive Stmt :  Type :=
  Write : MemIx -> MemValue -> Stmt.

(* Memory is a function from an index to a value *)
Definition Memory :=  MemIx -> MemValue.

(* initial state of memory *)
Definition initMemory : Memory := fun ix => Z0.

Theorem initMemoryAlwaysZero : forall (wix: MemIx), (initMemory wix) = Z0.
Proof.
  auto.
Qed.


Definition writeToMemory (wix: MemIx) (wval: MemValue) (mold: Memory) : Memory :=
  fun ix => if (ix =? wix)%Z then wval else mold ix.

Theorem readFromWriteIdentical : forall (wix: MemIx) (wval: MemValue) (mem: Memory),
    (writeToMemory wix wval mem) wix = wval.
Proof.
  intros wix wval mem.
  unfold writeToMemory.
  rewrite Z.eqb_refl.
  reflexivity.
Qed.


(* I do not know who Zneq_to_neq fails. TODO: debug this *)
Theorem readFromWriteDifferent : forall (wix: MemIx) (rix: MemIx) (wval : MemValue) (mem: Memory),
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


  

(* Model the effect of memory writes on memory. *)
Definition modelStmtMemorySideEffect (mold: Memory) (s: Stmt) : Memory :=
  match s with
  | Write wix wval => (writeToMemory wix wval mold)
  end.



(**** Schedule stuff for later, I know nothing on how to prove this stuff ****)
(* A timepoint for a schedule *)

(* We shouldn't think of this as an actual list, we should think of the list indeces
as indeces for the schedule to operate on *)
Definition Stmts := list Stmt.

Definition timepoint := nat.

Definition ScheduleFn :=  nat -> nat.

Definition Schedule (stmts: Stmts) (f: ScheduleFn) := Bijective f.

Function scheduleSideEffect (stmts: Stmts) (f: ScheduleFn) (schedule: Schedule stmts f)  (mold: Memory) : Memory :=
  List.fold_left modelStmtMemorySideEffect stmts initMemory.

           
Definition Dependence : Type := nat * nat.
Definition DependenceSet := ListSet.set (Dependence).


Definition CompleteDependenceSet (depset: DependenceSet) (stmts: Stmts) (f: ScheduleFn) (schedule: Schedule stmts f) : Prop :=
  forall (t0 t1 : timepoint)
         (wix: MemIx)
         (val0 val1 : MemValue)
         (t0validwidness: t0 < length stmts)
         (t1validwitness: t1 < length stmts),
    (List.nth_error stmts t0 = Some (Write wix val0) /\
    List.nth_error stmts t1 = Some (Write wix val1)) <->
    List.In ((t0, t1)) depset.


Definition validNewSchedule (depset: DependenceSet) (stmts: Stmts)
        (f f': ScheduleFn)
        (schedule : Schedule stmts f)
        (schedule' : Schedule stmts f') : Prop :=
  CompleteDependenceSet depset stmts f schedule ->
  forall (t0 t1 : timepoint),
    ListSet.set_In (t0, t1) depset -> (f' t0) < (f' t1).


Definition schedulesHaveSameSideEffect (stmts: Stmts) (f f': ScheduleFn) (schedule: Schedule  stmts f) (schedule': Schedule stmts f') :=
  forall (mold: Memory),
    scheduleSideEffect stmts f schedule mold = scheduleSideEffect  stmts f' schedule' mold.


Theorem schedulesHaveSameSideEffectIsRefl: forall (stmts: Stmts) (f: ScheduleFn) (schedule: Schedule stmts f), schedulesHaveSameSideEffect stmts f f schedule schedule.
Proof.
  intros.
  unfold schedulesHaveSameSideEffect.
  intros. reflexivity.
Qed.

Theorem validNewScheduleHasSameSideEffect: forall (depset: DependenceSet) (stmts: Stmts) (f f': ScheduleFn) (schedule: Schedule stmts f) (schedule': Schedule stmts f'), CompleteDependenceSet depset stmts f schedule -> validNewSchedule depset stmts f f' schedule schedule' -> schedulesHaveSameSideEffect stmts f f' schedule schedule'.
Proof.
  intros.

  (* no statements *)
  induction stmts.
  + unfold schedulesHaveSameSideEffect.
    intros.
    unfold scheduleSideEffect.
    simpl. reflexivity.

  + intros.
    unfold Schedule in schedule.
    unfold Schedule in schedule'.
    unfold Schedule in IHstmts.
    specialize (IHstmts schedule schedule').
    unfold schedulesHaveSameSideEffect.
    intros.
    unfold scheduleSideEffect.
    auto.
    (* WAIT WHAT? HOW IN THE FUCK? IS MY THEOREM TOO STRONG? o_O *)
Qed.

