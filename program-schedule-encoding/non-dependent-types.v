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
  Default: Stmt

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
Definition program := list Stmt.

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
  unfold schedulesHaveSameSideEffect.
  intros.
  unfold scheduleSideEffect.
  simpl. reflexivity.

  intros.
  unfold Schedule in schedule.
  unfold Schedule in schedule'.
  unfold Schedule in IHstmts.
  specialize (IHstmts schedule schedule').
  unfold schedulesHaveSameSideEffect.
  intros.
  unfold scheduleSideEffect.
  auto.
  (* WAIT WHAT? HOW IN THE FUCK? IS MY THEOREM TOO STRONG? o_O*)
Qed.


Definition flip2 : ScheduleFn :=
  fun x => match x with
           | 0 => 1
           | 1 => 0
           | x => x
           end.

(* this has got to have a cleaner proof o_O *)
Theorem flip2Bijective: Bijective (flip2).
Proof.
  unfold Bijective.
  exists flip2.
  split.
  intros.
  assert(x = 0 \/ x = 1 \/ (x > 1)). omega.
  destruct H. rewrite H. simpl. reflexivity.
  destruct H. rewrite H. simpl. reflexivity.
  destruct H. reflexivity.
  assert(flip2 (S m) = S m).
  unfold flip2. destruct H. reflexivity. reflexivity.
  rewrite H0. rewrite H0. reflexivity.

  intros.
  assert(y = 0 \/ y = 1 \/ (y > 1)). omega.
  destruct H. subst. auto.
  destruct H. subst. auto.
  destruct H. auto.
  assert(flip2 (S m) = S m).
  unfold flip2. destruct m. inversion H. auto.
  repeat((rewrite H0)). auto.
Qed.
  
Definition flip2General (n: nat) (m: nat) (witness: n < m) : ScheduleFn :=
  fun x => if x =? n
           then m
           else if x =? m
                then n
                else x.

(* Build flip2General so that we can easily create schedules to test *)
Theorem flip2GeneralInvolutive: forall (n m: nat) (witness: n < m) (x: nat), flip2General n m witness (flip2General n m witness x) = x.
  intros.
  assert(x = n \/ x = m \/ (x <> n /\ x <> m)). omega.
  destruct H.  rewrite H. unfold flip2General. rewrite <- beq_nat_refl. assert(m <> n). omega.  rewrite <- Nat.eqb_neq in H0. rewrite H0. rewrite <- beq_nat_refl. reflexivity.

  destruct H. rewrite H. unfold flip2General. assert(m <> n). omega.
  rewrite <- Nat.eqb_neq in H0. rewrite H0. simpl.
  assert(m =? m = true). rewrite Nat.eqb_eq. reflexivity.
  rewrite H1. simpl.
  assert( n =? n = true). rewrite Nat.eqb_eq. reflexivity.
  rewrite H2. auto.
  destruct H.

  unfold flip2General.
  rewrite <- Nat.eqb_neq in H.
  rewrite <- Nat.eqb_neq in H0.
  rewrite H. simpl.
  rewrite H0. simpl.
  rewrite H. rewrite H0. auto.
Qed.

Theorem flip2GeneralBijective: forall (n m: nat) (witness: n < m),
    Bijective(flip2General n m witness).
Proof.
  intros.
  unfold Bijective.
  exists (flip2General n m witness).
  split.
  intros.
  apply flip2GeneralInvolutive.
  apply flip2GeneralInvolutive.
Qed.

(* Now we can create any schedule by composing flips with idSchedule *)
Definition idScheduleFn : ScheduleFn := fun x => x.
Theorem idScheduleBijective: Bijective(idScheduleFn).
Proof.
  unfold Bijective.
  exists idScheduleFn.
  unfold idScheduleFn. auto.
Qed.

Definition program2Schedule (p: program) : Schedule p id :=
  idScheduleBijective.

Theorem balancedSubtractionAddition : forall (n m t : nat), n + m = t -> n > 0 -> ((n - 1) + (m + 1)) = t.
Proof.
  intros. omega.
Qed.


Definition schedule2Program (stmts: Stmts) (f: ScheduleFn) (sched: Schedule stmts f) (fuel: nat) (ix: nat) (fuel_gt_zero: fuel > 0) (ix_plus_fuel_eq_length: ix + fuel = length stmts): program :=
  match fuel with
  | O => List.nil
  | S(fuel') => List.cons (List.at m,  )
  end.
       

Definition twoWritesNonAliasingProgram : Stmts := List.cons (Write 0%Z 0%Z) (List.cons (Write 1%Z 0%Z) List.nil).
