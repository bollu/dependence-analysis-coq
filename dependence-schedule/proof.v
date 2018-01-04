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
Inductive Dependence : Type := mkDependence:  Timepoint -> Timepoint -> Dependence.

Function extractDependencesGo
         (stmtindex: Timepoint)
         (prog: PList)
         (writes: M.t Timepoint)
  : list  Dependence :=
  match prog with
  | nil => nil
  | (Write wix _)::ps =>
    let newwrites := add wix stmtindex writes in
    let laterdeps := extractDependencesGo (stmtindex + 1) ps newwrites in
    match find wix writes with
    | Some prevstmtix => (mkDependence prevstmtix stmtindex):: laterdeps
    | None => laterdeps
    end
  end.

Definition emptyWrites : M.t Timepoint := M.empty Timepoint.

Definition extractDependences (prog: PList) : list Dependence :=
  extractDependencesGo 0 prog emptyWrites.
                                              
Definition ValidDependence (d: Dependence) : Prop :=
  match d with
    mkDependence i j => i < j
  end.



Theorem extractDependencesGoProducesValidDependences :
  forall (stmtindex: Timepoint)
         (prog : PList)
         (writes: M.t Timepoint)
         (d: Dependence),
    (forall (wix: Ix) (tp: Timepoint), M.MapsTo wix tp writes -> tp < stmtindex) ->
    List.In d (extractDependencesGo stmtindex prog writes)  ->
    ValidDependence d.
  intros stmtindex prog writes d H.
  functional induction extractDependencesGo stmtindex prog writes.
  simpl. tauto.
  MFacts.map_iff.
  intros HNew.
  apply in_inv in HNew.
  (* seems legit till here *)
  destruct HNew.
  assert (prevstmtix < stmtindex).
  rewrite <- find_mapsto_iff in e0.
  specialize (H wix prevstmtix).
  specialize (H e0).
  auto.
  unfold ValidDependence.
  destruct d.
  inversion H0.
  rewrite <- H3.
  rewrite <- H4.
  exact H1.
  assert(forall (wix0 : Ix) (tp : Timepoint),
            MapsTo wix0 tp (add wix stmtindex writes) -> tp < stmtindex + 1).
  intros.
  specialize (H wix0 tp).
  rewrite add_mapsto_iff in H1.
  destruct H1.
  destruct H1.
  rewrite H2.
  intuition.
  destruct H1.
  rewrite (H H2).
  intuition.
  specialize (IHl H1 H0).
  exact IHl.
  intros INew.


  assert((forall (wix0 : Ix) (tp : Timepoint),
             MapsTo wix0 tp (add wix stmtindex writes) -> tp < stmtindex + 1)).
  intros wix0 tp.
  intuition.
  specialize (H wix0 tp).
  rewrite add_mapsto_iff in H0.
  destruct H0.
  destruct H0.
  rewrite H1.
  intuition.
  destruct H0.
  specialize (H H1).
  rewrite H.
  intuition.

  specialize (IHl H0).
  specialize (IHl INew).
  exact IHl.
  Qed.

Theorem extractDependencesProducesValidDependences:
  forall (prog : PList) (d: Dependence),
    List.In d (extractDependences prog) -> ValidDependence d.
  intros prog d.
  unfold extractDependences.
  apply extractDependencesGoProducesValidDependences.
  intros wix tp mapsto.
  inversion mapsto.
Qed.

Definition ValidSchedule (s: Schedule) : Prop :=
  Bijective s.
