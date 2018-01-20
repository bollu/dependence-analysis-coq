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
Require Import FSetInterface.
Require Import FSetList.
Require Import Coq.Program.Equality.
Import EqNotations.

(* Require Import CoLoR.Util.FSet.FSetUtil. *)
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
Definition memix := nat.

(* values in memory *)
Definition memvalue := Z.

Inductive write : Type :=
  Write: memix -> memvalue -> write.


Definition memory :=  memix -> memvalue.

Notation "ix '::=' val" := (memory ix val) (at level 60).

(* initial state of memory *)
Definition initMemory : memory := fun ix => Z0.

Theorem initMemoryAlwaysZero : forall (wix: memix), (initMemory wix) = Z0.
Proof.
  auto.
Qed.


Definition writeToMemory (wix: memix) (wval: memvalue) (mold: memory) : memory :=
  fun ix => if (ix =? wix) then wval else mold ix.

Theorem readFromWriteIdentical : forall (wix: memix) (wval: memvalue) (mem: memory),
    (writeToMemory wix wval mem) wix = wval.
Proof.
  intros wix wval mem.
  unfold writeToMemory.
  rewrite Nat.eqb_refl.
  reflexivity.
Qed.


(* I do not know who Zneq_to_neq fails. TODO: debug this *)
Theorem readFromWriteDifferent : forall (wix: memix) (rix: memix) (wval : memvalue) (mem: memory),
    rix <> wix -> (writeToMemory wix wval mem) rix = mem rix.
Proof.
  intros wix rix wval mem.
  intros rix_neq_wix.
  unfold writeToMemory.
  assert((rix =? wix) = false).
  apply Nat.eqb_neq in rix_neq_wix.
  auto.
  rewrite H.
  reflexivity.
Qed.


(* Model the effect of memory writes on memory. *)
Definition modelWriteSideEffect (mold: memory) (w: write) : memory :=
  match w with
  | Write wix wval => (writeToMemory wix wval mold)
  end.


Inductive com: nat ->  Type :=
| CSeq: forall (n: nat), com n -> write -> com (n + 1)
| CBegin: com 0.


Theorem n_minus_1_plus_1_eq_n_when_n_gt_0: forall (n: nat), n > 0 -> n - 1 + 1 = n.
Proof. intros. omega. Qed.



Example c_example' : com 2 := (CSeq _ (CSeq _ CBegin (Write 1 100%Z)) (Write 1 100%Z)).


Definition timepoint: Type := nat.
Definition writeset: Type := memix -> list timepoint.

Definition emptyWriteSet : writeset := fun ix => List.nil.
Definition addToWriteSet (ws: writeset) (ix: memix) (tp: timepoint) : writeset :=
  fun ix' => if ix' =? ix
             then List.cons tp (ws ix')
             else ws ix'.
Definition singletonWriteSet (ix: memix) (tp: timepoint) : writeset :=
  addToWriteSet emptyWriteSet ix tp.
Definition mergeWriteSets (ws ws': writeset) : writeset :=
  fun ix => ws ix ++ ws' ix.
               

Definition writeToWriteset (w: write) (tp: timepoint) : writeset :=
  match w with
  | Write ix value => singletonWriteSet ix tp
  end.



Definition dependence: Type := nat * nat.
Definition dependenceset: Type := list dependence.
Definition emptyDependenceSet : dependenceset := List.nil.


Definition dependenceLexPositive (d: dependence) : Prop :=
  fst d < snd d.

Definition commandIxInRange (n: nat) (c: com n) (i: nat) : Prop :=
  i <= n /\ i >= 1.

Definition dependenceInRange (d: dependence) (n: nat) (c: com n) : Prop :=
  commandIxInRange n c (fst d) /\ commandIxInRange n c (snd d).

Definition writeIx (w: write) : memix :=
  match w with
  | Write ix _ => ix
  end.


Program Fixpoint getWriteAt (n: nat) (c: com n) (i: nat) (witness: i <= n /\ i >= 1) :=
  match c with
  | CBegin => _
  | CSeq _ c' w => if i == n then w else getWriteAt _ c' i _
  end.
Next Obligation.
  omega.
Defined.
Next Obligation.
  split.
  apply le_lt_or_eq in H0.
  destruct H0.
  omega.
  contradiction.
  assumption.
Defined.

   
Program Definition dependenceAliases (d: dependence) (n: nat) (c: com n) (witness: dependenceInRange d n c) : Prop :=
  let ix1 := fst d in
  let ix2 := snd d in
  let w1 := getWriteAt n c ix1 _ in
  let w2 := getWriteAt n c ix2 _ in
  writeIx w1 = writeIx w2.
Next Obligation.
  unfold dependenceInRange in witness.
  destruct witness.
  auto.
Defined.
Next Obligation.
  unfold dependenceInRange in witness.
  destruct witness.
  auto.
Defined.
        
  

  
Fixpoint computeWriteSet (n: nat) (c: com n) : writeset :=
  match c with
  | CSeq n' cs w => mergeWriteSets (computeWriteSet n' cs) (writeToWriteset w n)
  | CBegin => emptyWriteSet
  end.
  

Definition dependencesFromWriteSetAndWrite (t: timepoint) (ws: writeset) (w: write) : dependenceset :=
  match w with
  | Write ix _ => let prev_write_timepoints_at_ix := ws ix in
                  List.map (fun pwt => (pwt, t))  prev_write_timepoints_at_ix
  end.
    

Fixpoint computeDependences (n: nat) (c: com n) : dependenceset :=
  match c with
  | CBegin => emptyDependenceSet
  | CSeq n' c' w =>
    let prevdeps := computeDependences n' c' in
    let prevwriteset := computeWriteSet n' c' in
    (dependencesFromWriteSetAndWrite n prevwriteset w) ++ prevdeps
  end.

(* computeDependences on "com 0" always returns an empty dependence set *)
Theorem computeDependence0IsEmpty: forall (n: nat) (c: com n), n = 0 -> computeDependences n c = List.nil.
Proof.
  intros.
  unfold computeDependences.
  remember c as c'.
  destruct c.
  omega.
  rewrite Heqc'.
  unfold emptyDependenceSet.
  reflexivity.
Qed.

    
(* ComputeDependences always returns dependences that are lex positive *)
Theorem computeDependencesLexPositive': forall (n: nat) (c: com n),
    let deps := computeDependences n c in
    forall (d: dependence), List.In d deps -> dependenceLexPositive d.
Proof.
  (* How to open let? *)
Abort.

(* computeWriteSet n c will have all writes <= n*)
Theorem computeWriteSetInBounds: forall (n: nat) (c: com n) (ix: memix) (t: timepoint), List.In t ((computeWriteSet n c) ix) -> t <= n.
Proof.
  intros.
  generalize dependent ix.
  generalize dependent t0.
  dependent induction c.
  intros.
  simpl in H.
  unfold mergeWriteSets in H.
  rewrite List.in_app_iff in H.
  destruct H.
  specialize (IHc t0 ix H).
  omega.
  unfold writeToWriteset in H.
  unfold singletonWriteSet in H.
  unfold emptyWriteSet in H.
  unfold addToWriteSet in H.
  destruct w.
  assert(ix = m \/ ~(ix = m)). omega.
  destruct H0.
  subst.
  rewrite Nat.eqb_refl in H.
  simpl in H.
  destruct H.
  omega.
  contradiction.
  rewrite <- Nat.eqb_neq in H0.
  rewrite H0 in H.
  contradiction.
  intros.
  unfold computeWriteSet in H.
  unfold emptyWriteSet in H.
  simpl in H.
  contradiction.
Qed.


  

Theorem computeDependencesLexPositive: forall (n: nat) (c: com n),
    forall (d: dependence), List.In d (computeDependences n c) -> dependenceLexPositive d.
Proof.
  intros.
  generalize dependent d.
  dependent induction c.
  intros.
  unfold computeDependences in H.
  fold computeDependences in H.
  rewrite List.in_app_iff in H.
  destruct H.

Abort.