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
  fun ix => if (ix =? wix)%Z then wval else mold ix.

Theorem readFromWriteIdentical : forall (wix: Ix) (wval: MemValue) (mem: Memory),
    (writeToMemory wix wval mem) wix = wval.
Proof.
  intros wix wval mem.
  unfold writeToMemory.
  rewrite Z.eqb_refl.
  reflexivity.
Qed.


(* I do not know who Zneq_to_neq fails. TODO: debug this *)
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
  intros i1_neq_i2.
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


(**** Schedule stuff for later, I know nothing on how to prove this stuff ****)
(* A timepoint for a schedule *)
Definition Timepoint := nat. 

(* A schedule maps statements to time points *)
Definition PList := list Stmt.
Definition Schedule := Timepoint -> Timepoint.

(* Identity schedule *)
Definition idSchedule : Schedule := fun x => x.

(* Cannot do this, since I cannot store [dep]
Inductive Dependence : Prop -> Type :=
  mkDependence (t1: Timepoint)  (t2: Timepoint) : Dependence (t1 < t2).
*)
Inductive Dependence : Type :=
  mkDependence:  Timepoint -> Timepoint -> Dependence.

Definition emptyWrites : M.t Timepoint := M.empty Timepoint.

Definition ListNth (T: Type) (n: nat)  (v: T)  (l: list T) : Prop := nth_error l n = Some v.
                                              
Definition ValidDependence (d: Dependence) (p: PList): Prop :=
  match d with
    mkDependence i j => i < j /\ j < (length p) /\
                        exists (wix: Ix) (v0 v1 : MemValue),
                          ListNth _ i (Write wix v0) p /\
                          ListNth _ j (Write wix v1) p
  end.


Function extractDependencesGo
         (stmtindex: nat)
         (prog: PList)
         (writes: M.t Timepoint)
         { struct prog }
  : list Dependence :=
  match prog with
  | nil => nil
  | cons stmt prog' =>
    match stmt with
    | Write wix _ => let
        newwrites := add wix stmtindex writes in
      let nextDependences := extractDependencesGo (stmtindex + 1) prog' newwrites in
      match find wix writes with
      | Some oldt => (mkDependence oldt stmtindex)::nextDependences
      | None => nextDependences
      end
    end
  end.

Theorem extractDependencesGoProducesValidDependences :
  forall (stmtindex: Timepoint)
         (prog : PList)
         (writes: M.t Timepoint)
         (d: Dependence),
  exists (origprog: PList),
         skipn stmtindex origprog = prog -> 
    (forall (wix: Ix) (tp: Timepoint), M.MapsTo wix tp writes -> tp < stmtindex) ->
    List.In d (extractDependencesGo stmtindex prog writes)  ->
    ValidDependence d prog.
  intros stmtsleft prog writes d.
  functional induction (extractDependencesGo stmtsleft prog writes).
  - intros. contradiction.
  - intros. destruct d. unfold ValidDependence. destruct H1. inversion H1. rewrite <- H3.
    apply find_mapsto_iff in e2.
    specialize (IHl )
    split.
    + 
  

Theorem extractDependencesProducesValidDependences:
  forall (prog : PList) (d: Dependence),
    List.In d (extractDependences prog) -> ValidDependence d.
  intros prog d.
  unfold extractDependences.
  apply extractDependencesGoProducesValidDependences.
  intros wix tp mapsto.
  inversion mapsto.
Qed.

Theorem DependenceToAlias: forall  (prog: PList) (d: Dependence) (t0 t1: Timepoint), 
    d = mkDependence t0 t1 ->
    List.In d (extractDependences prog) ->
    exists (wix: Ix) (w0: Stmt) (w1: Stmt) (val0 val1: MemValue), List.In w0 prog /\ w0 = (Write wix val0) /\ List.In w1 prog /\ w1 = (Write wix val1) /\ Some w0 = nth_error prog t0.
  intros prog. induction prog.
  intros.
  inversion H0.
  intros.
  assert(ValidDependence d).
  apply extractDependencesProducesValidDependences in H0.
  exact H0.
  unfold ValidDependence in H1.
  destruct d in H1.
  assert(t3 = length prog - 1 \/ t3 < length prog - 1).



Theorem DependenceRepresentsAliasing:
  forall (stmtindex: Timepoint)
         (prog : PList)
         (writes: M.t Timepoint)
         (d: Dependence),
    (forall (wix: Ix) (tp: Timepoint), M.MapsTo wix tp writes -> tp < stmtindex) ->
    List.In d (extractDependencesGo stmtindex prog writes)  ->
    ValidDependence d.


Definition ValidSchedule (s: Schedule) : Prop :=
  Bijective s.

Definition ScheduleSatisfiesDependence (s: Schedule) (d: Dependence) : Prop :=
  match d with
  | mkDependence t0 t1 => s t0 < s t1
  end.



(* The identity schedule produces valid dependences *)
Theorem IdentityScheduleSatisfiesDependenceFromProgram: forall (prog: PList),
    forall (d: Dependence), List.In d (extractDependences prog) -> ScheduleSatisfiesDependence idSchedule d.
  apply extractDependencesProducesValidDependences.
Qed.


Definition ScheduleSatisfiesProgramDependences
           (sched: Schedule) (prog: PList) : Prop :=
  ValidSchedule sched -> 
  forall (d: Dependence), List.In d (extractDependences prog) -> ScheduleSatisfiesDependence sched d.
Proof.
  intros sched prog. generalize dependent sched.
  induction prog.
  intros.
  - simpl in H0.
    contradiction.
  - intros.


Function applyScheduleToProgram (sched: Schedule) (prog: PList) : PList :=
  (* TODO *)

  Theorem scheduleSemanticsMapping forall (prog: Plist) (sched: Schedule), ScheduleSatisfiesProgramDependences sched prog -> programsEquivalent prog (applyScheduleToProgram sched prog).
Proof.
