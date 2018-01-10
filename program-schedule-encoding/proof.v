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
Definition modelStmtMemorySideEffect (s: Stmt) (mold: Memory) : Memory :=
  match s with
  | Write wix wval => (writeToMemory wix wval mold)
  end.



(**** Schedule stuff for later, I know nothing on how to prove this stuff ****)
(* A timepoint for a schedule *)

(* We shouldn't think of this as an actual list, we should think of the list indeces
as indeces for the schedule to operate on *)
Definition Stmts (n: nat) := Vector.t Stmt n.

Definition timepoint  (k: nat) (n: nat) := (k < n).


Definition ScheduleFn (n: nat) : Type := forall (k1 k2: nat), timepoint k1 n -> timepoint k2 n.

Inductive Schedule (n: nat) (f: ScheduleFn n): Type :=
 |  mkSchedule: Bijective f -> Schedule n f.

Definition Program (n: nat) (f: ScheduleFn n) := prod (Stmts n) (Schedule n f).

Definition programStmts (n: nat) (f: ScheduleFn n) (p: Program n f) : Stmts n := fst p.


(* get ith instruction from a program *)
Definition programIthInstr  (n: nat) (f: ScheduleFn n) (p: Program n f) (i: timepoint n) : Stmt :=
   nth (fst p) i.


Inductive dependence :=
| mkDependence: nat -> nat -> dependence.

(* If there is a write to wix at this timepoint t, return [t], else return [] *)
Definition getWriteAtTimepoint (n: nat) (f: ScheduleFn n) (p: Program n f) (wix_needle: MemIx) (tp: timepoint n) : list (timepoint n) :=
  match programIthInstr n f p tp with
  | Write wix _ => if (wix =? wix_needle)%Z
                   then tp::List.nil
                   else List.nil
  end.


Theorem n_minus_1_lt_n (n: nat)  : n > 1 -> n - 1 < n.
  intros.
  induction n.
  inversion H.
  simpl. omega.
Qed.

(* need to match with witness for why n = 1 or n > 1
Definition decTimepoint (n: nat) (t: timepoint n) : timepoint n :=
  match t with
  | Fin.F1 => Fin.F1
  | Fin.FS prev => Fin.of_nat_lt (n_minus_1_lt_n n)
  end.
*)
                

Definition decTimepoint (n: nat) (t: timepoint n) : timepoint n := t.

Function getWritesTillTimepointGo (n: nat)
           (f: ScheduleFn n)
           (p: Program n f)
           (wix_needle: MemIx)
           (tcur: timepoint n) : list (timepoint n) :=
  match tcur with
  | Fin.F1 => getWriteAtTimepoint n f p wix_needle tcur
  | Fin.FS _ =>  let writeAtPrevTimepoints := getWritesTillTimepointGo n f p wix_needle (decTimepoint _ tcur) in writeAtPrevTimepointss

  end.



Definition makeDependences (n: nat) (f: ScheduleFn n) (p: Program n f) : list dependence :=
  match programStmts n f p with
  | Vector.nil _ => List.nil
  | cons _ s _ rest =>  match s with
                        | Write wix _ => List.nil
                        end
  end.


