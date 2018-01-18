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
Import EqNotations.

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
Definition Stmts (n: nat) := Vector.t Stmt n.

Definition timepoint (n: nat) := Fin.t n.

Definition ScheduleFn (n: nat) :=  timepoint n -> timepoint n.

Inductive Schedule (n: nat) (stmts: Stmts n) (f: ScheduleFn n) :=
| mkSchedule: Bijective f -> Schedule n stmts f.

Definition stmtAtTimepoint (n: nat) (stmts: Stmts n) (time: timepoint n) (f: ScheduleFn n) (schedule: Schedule n stmts f) : Stmt :=
  Vector.nth stmts (f time).


Definition Program (n: nat) := Vector.t Stmt n.

Function oneElemVector (A: Set) (a: A) : Vector.t A 1 :=
  Vector.cons A a 0 (Vector.nil A).

Function scheduleIndex (n: nat) (ix: nat) (witness: ix < n) (stmts: Stmts n) (f: ScheduleFn n) (schedule: Schedule n stmts f) : Stmt :=
  Vector.nth stmts (f (Fin.of_nat_lt witness)).
  

                               
Definition Vector1N (n: nat) : Vector.t nat n.
Proof.
  assert(length (seq 1 n) = n).
  rewrite List.seq_length.
  reflexivity.
  exact (rew H in  of_list (seq 1 n)).
Defined.


Function Vector1N' (n: nat) : Vector.t nat n :=
  let v := (seq 1 n) in
  rew List.seq_length _ _ in of_list v.


(* Interesting place where we need dependent pattern match *)
Function scheduleStmtsGo (n: nat) (ix: nat) (witness: ix < n) (stmts: Stmts n) (f: ScheduleFn n) (schedule: Schedule n stmts f): Program ix :=
  match ix as curix return ((curix < ix) -> Program (S curix)) with
  | O => fun _ => let a' := Vector.nth stmts (f (Fin.of_nat_lt witness)) in
    oneElemVector _ a'
  | S ix' => fun ix_new_lt_ix =>
               let a' := Vector.nth stmts (f (Fin.of_nat_lt witness)) in
               let witness' := lt_trans _ _ _ (Nat.lt_succ_diag_r _ ) (lt_trans _ _ _ ix_new_lt_ix witness) in
               let recur := scheduleStmtsGo n ix' witness' stmts f schedule in
                   Vector.append (oneElemVector _ a') recur
  end.
           
  
Function scheduleSideEffect (n: nat) (stmts: Stmts n) (f: ScheduleFn n) (schedule: Schedule n stmts f)  (mold: Memory) : Memory :=
  Vector.fold_left modelStmtMemorySideEffect initMemory stmts.

           
Inductive Dependence (n: nat) :=
| mkDependence : Fin.t n -> Fin.t n -> Dependence n.


Definition DependenceSet (n: nat) := ListSet.set (Dependence n).

Definition timepointToNat (n: nat) (t: timepoint n)  : nat :=
  proj1_sig (Fin.to_nat t).

Definition CompleteDependenceSet (n: nat) (depset: DependenceSet n) (stmts: Stmts n) (f: ScheduleFn n) (schedule: Schedule n stmts f) : Prop :=
  forall (t0 t1 : timepoint n)
         (wix: MemIx)
         (val0 val1 : MemValue),
    timepointToNat n t0 < timepointToNat n t1 ->
    stmtAtTimepoint n stmts t0 f schedule = (Write wix val0) ->
    stmtAtTimepoint n stmts t1 f schedule = (Write wix val1) ->
    ListSet.set_In (mkDependence n t0 t1) depset.


Definition validNewSchedule (n: nat) (depset: DependenceSet n) (stmts: Stmts n)
        (f f': ScheduleFn n)
        (schedule : Schedule n stmts f)
        (schedule' : Schedule n stmts f') : Prop :=
  CompleteDependenceSet n depset stmts f schedule ->
  forall (t0 t1 : timepoint n),
    ListSet.set_In (mkDependence n t0 t1) depset -> timepointToNat n (f' t0) < timepointToNat n (f' t1).


Definition schedulesHaveSameSideEffect (n: nat) (stmts: Stmts n) (f f': ScheduleFn n) (schedule: Schedule n stmts f) (schedule': Schedule n stmts f') :=
  forall (mold: Memory),
    scheduleSideEffect n stmts f schedule mold = scheduleSideEffect n stmts f' schedule' mold.




Theorem cons_and_append_equivalence:
  forall (n: nat) (A: Set) (a: A) (xx: Vector.t A n),
    Vector.cons A a n xx = Vector.append (Vector.cons A a _ (Vector.nil _)) xx.
  intros.
  simpl.
  reflexivity.
Qed.

Theorem validNewSchedulesHasSameSideEffect: forall (n: nat) (stmts: Stmts n) (f f': ScheduleFn n) (schedule: Schedule n stmts f) (schedule': Schedule n stmts f')(depset: DependenceSet n),
    CompleteDependenceSet n depset stmts f schedule ->
    validNewSchedule n depset stmts f f' schedule schedule' ->
    schedulesHaveSameSideEffect n stmts f f' schedule schedule'.
  intros.
  generalize dependent depset. 
  generalize dependent schedule'. 
  generalize dependent f'.
  induction (rev stmts).
  - (* 0 *)
    intros.
    unfold schedulesHaveSameSideEffect.
    intros.
    unfold scheduleSideEffect. simpl. reflexivity.

  - (* Induction *)
    intros.
    rename h into newStmt.
    unfold schedulesHaveSameSideEffect.
    intros.
    destruct newStmt.
    unfold scheduleSideEffect.
