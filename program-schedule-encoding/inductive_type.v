Require Import Coq.Lists.List.
Require Import FunInd.
Require Import Coq.Lists.ListSet.
Require Import Coq.ZArith.BinInt.
Require Import Coq.ZArith.BinIntDef.
Require Import Coq.Numbers.BinNums.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.Zbool.
Require Import Coq.ZArith.Int.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ExtensionalityFacts.
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
Require Import CoLoR.Util.FSet.FSetUtil.
Import EqNotations.
Import EqdepFacts.

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
Notation memix := nat.

(* values in memory *)
Notation memvalue := Z.

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

Definition writeToMemory' (w: write) (mold: memory) : memory :=
  match w with
  | Write ix val => writeToMemory ix val mold
  end.

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


Inductive com: Type :=
| CSeq: com -> write -> com
| CBegin: com.

Fixpoint comlen (c: com) : nat :=
  match c with
  | CBegin => 0
  | CSeq c' _ => 1 + comlen c'
  end.

Theorem n_minus_1_plus_1_eq_n_when_n_gt_0: forall (n: nat), n > 0 -> n - 1 + 1 = n.
Proof. intros. omega. Qed.



Example c_example' : com := (CSeq (CSeq CBegin (Write 1 100%Z)) (Write 1 100%Z)).


Notation timepoint  := nat.
Definition writeset: Type := memix -> list timepoint.

Definition emptyWriteSet : writeset := fun ix => List.nil.
Definition addToWriteSet (ws: writeset) (ix: memix) (tp: timepoint) : writeset :=
  fun ix' => if ix' =? ix
             then List.cons tp (ws ix')
             else ws ix'.
Definition singletonWriteSet (ix: memix) (tp: timepoint) : writeset :=
  addToWriteSet emptyWriteSet ix tp.

(* Reason about what it means to be in a singleton write set *)
Lemma destructInSingletonWriteSet:
  forall (ix curix: memix) (curtp tp: timepoint),
    List.In curtp ((singletonWriteSet ix tp) curix) -> curtp = tp /\ ix = curix.
  intros.
  unfold singletonWriteSet in H.
  unfold addToWriteSet in H.
  assert (curix = ix \/ curix <> ix).
  omega.

  destruct H0.
  (* curix = ix *)
  rewrite <- Nat.eqb_eq in H0.
  rewrite H0 in H.
  inversion H.
  split; auto.
  rewrite Nat.eqb_eq in H0. auto.
  inversion H1.
  (* curix <> ix *)
  rewrite <- Nat.eqb_neq in H0.
  rewrite H0 in H.
  inversion H.
Qed.

Definition mergeWriteSets (ws ws': writeset) : writeset :=
  fun ix => ws ix ++ ws' ix.

               

Definition writeToWriteset (w: write) (tp: timepoint) : writeset :=
  match w with
  | Write ix value => singletonWriteSet ix tp
  end.

Lemma destructInWriteToWriteSet':
  forall (n: nat) (curtp : timepoint) (ix curix: memix) (val: memvalue),
    List.In curtp (writeToWriteset (Write ix val) n curix) -> curtp = n /\ curix = ix.
Proof.
  intros.
  unfold writeToWriteset in H.
  apply destructInSingletonWriteSet in H.
  omega.
Qed.


Definition dependence: Type := nat * nat.
Definition dependenceset: Type := list dependence.
Definition emptyDependenceSet : dependenceset := List.nil.


Definition dependenceLexPositive (d: dependence) : Prop :=
  fst d < snd d.

Definition commandIxInRange  (c: com) (i: nat) : Prop :=
  i <= comlen c /\ i >= 1.

Lemma commandIxInRangeDestructOnCSeq: forall (c: com) (w: write) (i: nat), commandIxInRange (CSeq c w) i  -> i <> comlen c + 1  -> commandIxInRange c i.
Proof.
  intros.
  unfold commandIxInRange in H.
  unfold commandIxInRange. simpl in H.
  omega.
Qed.

Lemma commandIxInRangeInclusive: forall (c: com) (w: write) (i: nat), commandIxInRange c i -> commandIxInRange (CSeq c w) i.
  unfold commandIxInRange. unfold comlen. fold comlen.
  intros.
  omega.
Qed.
 

Definition dependenceInRange (d: dependence) (c: com) : Prop :=
  commandIxInRange c (fst d) /\ commandIxInRange c (snd d).

Lemma dependenceInRangeSymmetric: forall (tbegin tend: timepoint) (c: com),
    dependenceInRange (tbegin, tend) c <-> dependenceInRange (tend, tbegin) c.
Proof.
  intros.
  assert (forall (tbegin tend: timepoint),
             dependenceInRange (tbegin, tend) c ->
             dependenceInRange (tend, tbegin) c).
  unfold dependenceInRange.
  unfold  commandIxInRange.
  simpl.
  intros.
  omega.
  split.
  apply H.
  apply H.
Qed.

Definition writeIx (w: write) : memix :=
  match w with
  | Write ix _ => ix
  end.


(* Non dependent typed versions *)
Program Fixpoint getWriteAt' (c: com) (i: nat) : option write :=
  match c with
  | CBegin => None
  | CSeq c' w => if i =? (comlen c) then Some w else getWriteAt' c' i
  end.


Program Definition dependenceAliases' (d: dependence) (c: com) : Prop :=
  let ix1 := fst d in
  let ix2 := snd d in
  let w1 := getWriteAt' c ix1 in
  let w2 := getWriteAt' c ix2 in
  option_map writeIx w1 = option_map writeIx w2.

Lemma dependenceAliases'Symmetric: forall (tbegin tend: timepoint) (c: com),
    dependenceAliases' (tbegin, tend) c <-> dependenceAliases' (tend, tbegin) c.
  intros.
  assert (forall (x y: timepoint), dependenceAliases' (x, y) c -> dependenceAliases' (y, x) c).
  unfold dependenceAliases'. simpl.
  intros. auto.
  split.
  apply H.
  apply H.
Qed.
  
Fixpoint computeWriteSet (c: com) : writeset :=
  match c with
  | CSeq  cs w => mergeWriteSets (computeWriteSet cs) (writeToWriteset w (comlen c))
  | CBegin => emptyWriteSet
  end.
  

Definition dependencesFromWriteSetAndWrite (t: timepoint) (ws: writeset) (w: write) : dependenceset :=
  match w with
  | Write ix _ => let prev_write_timepoints_at_ix := ws ix in
                  List.map (fun pwt => (pwt, t))  prev_write_timepoints_at_ix
  end.
    

Fixpoint computeDependences (c: com) : dependenceset :=
  match c with
  | CBegin => emptyDependenceSet
  | CSeq c' w =>
    let prevdeps := computeDependences  c' in
    let prevwriteset := computeWriteSet c' in
    (dependencesFromWriteSetAndWrite (comlen c) prevwriteset w) ++ prevdeps
  end.

(* computeDependences on "com 0" always returns an empty dependence set *)
Theorem computeDependence0IsEmpty: forall (c: com), comlen c = 0 -> computeDependences c = List.nil.
Proof.
  intros.
  destruct c.
  simpl in H. inversion H.
  simpl.
  reflexivity.
Qed.

    

Theorem computeWriteSetInBounds: forall (c: com) (ix: memix) (t: timepoint), List.In t ((computeWriteSet  c) ix) -> t <= (comlen c) /\ t >= 1.
Proof.
  intros c.
  induction c.
  intros.
  unfold computeWriteSet in H. fold computeWriteSet in H.
  unfold mergeWriteSets in H.
  rewrite List.in_app_iff in H.
  destruct H.
  specialize (IHc  _ _ H).
  unfold comlen. fold comlen. omega.
  unfold comlen. fold comlen.
  unfold writeToWriteset in H. simpl in H. destruct w.
  apply destructInSingletonWriteSet in H.
  omega.
  intros.
  inversion H.
Qed.


  

Theorem computeDependencesLexPositive: forall (c: com),
    forall (d: dependence), List.In d (computeDependences c) -> dependenceLexPositive d.
Proof.
  intros.
  generalize dependent d.
  induction c.
  intros.
  unfold computeDependences in H.
  simpl in H.
  fold computeDependences in H.
  destruct w. rewrite List.in_app_iff in H.
  destruct H.
  (* till here, shit makes sense *)
  unfold dependencesFromWriteSetAndWrite in H.
  apply in_map_iff in H.
  destruct H.
  destruct H.
  apply computeWriteSetInBounds in H0.
  unfold dependenceLexPositive.
  subst.
  simpl.
  omega.
  specialize (IHc d H).
  assumption.
  intros.
  unfold computeDependences in H.
  simpl in H.
  contradiction.
Qed.



Theorem computeDependencesInRange: forall (c: com),
    forall (d: dependence), List.In d (computeDependences c) -> dependenceInRange d c.
  intros.
  generalize dependent d.
  induction c.
  intros.
  unfold computeDependences in H.
  fold computeDependences in H.
  rewrite List.in_app_iff in H.
  destruct H.
  unfold dependencesFromWriteSetAndWrite in H.
  destruct w.
  unfold dependenceInRange.
  destruct d.
  unfold commandIxInRange.
  simpl.
  apply in_map_iff in H.
  destruct H.
  destruct H.
  inversion H.
  subst.
  apply computeWriteSetInBounds in H0.
  omega.
  specialize (IHc d H).
  unfold dependenceInRange.
  unfold dependenceInRange in IHc.
  destruct d.
  simpl in IHc.
  simpl.
  unfold commandIxInRange.
  unfold commandIxInRange in IHc.
  unfold comlen. fold comlen.
  omega.

  intros.
  simpl in H.
  contradiction.
Qed.



Lemma getWriteAt'RangeConsistent: forall (c: com) (i: nat) (w: write), getWriteAt' c i  = Some w -> i >= 1 /\ i <= comlen c.
Proof.
  intros c.
  induction c.
  intros.
  unfold getWriteAt' in H.
  fold getWriteAt' in H.
  assert(forall (x y : nat), x < y \/ x = y \/ x > y) as trichotomy. intros. omega.
  unfold comlen in H. fold comlen in H.
  specialize( trichotomy i ((comlen c) + 1)).
  destruct trichotomy.
  (* i < n + 1 *)
    assert (i <> 1 + (comlen c)). omega.
    fold getWriteAt' in H.
    rewrite <- Nat.eqb_neq in H1.
    rewrite H1 in H.
    specialize (IHc _ _ H).
    destruct IHc.
    split; try assumption. unfold comlen. fold comlen. omega.

  intros.
     destruct H0.
     (* i = n + 1 *)
     unfold comlen. fold comlen.
     omega.

     (* i > n + 1 *)
      assert (i <> 1 + (comlen c)). omega.
        rewrite <- Nat.eqb_neq in H1.
        rewrite H1 in H.
        specialize (IHc _ _ H).
        omega.
        (* contradiction *)
  (*CBegin case - contradiction *)
    intros.
    unfold getWriteAt' in H.
    inversion H.
Qed.

Lemma getWriteAt'RangeComplete: forall (c: com) (i: nat), i >= 1 /\ i <= (comlen c) -> exists (w: write), getWriteAt' c i = Some w.
Proof.
  intros c.
  induction c.
  intros.
  unfold getWriteAt'. fold getWriteAt'.
  remember (comlen c) as n.
  assert(i = 1 + n\/ i < 1 + n \/ i > 1 + n) as trichotomy. omega.
  (* i = n  + 1 *)
  destruct trichotomy as [tri | tri'].
  rewrite <- Nat.eqb_eq in tri.
  unfold comlen. fold comlen.
  rewrite <- Heqn.
  exists w.
  rewrite tri.
  reflexivity.

  destruct tri' as [tri' | tri''].
  (* i < n + 1 *)
  assert(i >= 1 /\ i <= n). omega.
  specialize (IHc _ H0).
  destruct IHc.
  assert (i <> 1 + n). omega.
  rewrite <- Nat.eqb_neq in H2.
  unfold comlen. fold comlen. rewrite <- Heqn.
  rewrite H2.
  exists x.
  assumption.
  assert (i >= 1 /\ i <= n). unfold comlen in H. fold comlen in H. omega.
  specialize (IHc i H0).
  assert (i > 1 + n /\ i <= n).
  omega.
  inversion H1.
  assert (i <> 1 + comlen c). omega.
  rewrite <- Nat.eqb_neq in H4.
  unfold comlen. fold comlen.
  rewrite H4.
  destruct IHc.
  exists x.
  assumption.
  (* i > n + 1 *)
  intros.
  unfold comlen in H.
  inversion H.
  omega.
Qed.


Lemma getWriteAt'OnCSeq: forall (c: com) (w: write), getWriteAt' (CSeq c w) (comlen c + 1) = Some w.
  intros c.
  dependent induction c.
  intros.
  simpl.
  assert (comlen c + 1  =? S (comlen c) = true).
  rewrite Nat.eqb_eq. omega.
  unfold comlen. fold comlen.
  rewrite H.
  reflexivity.
  intros.
  simpl.
  reflexivity.
Qed.

Lemma getWriteAt'DestructOnCSeq: forall (c: com ) (i: nat) (w: write),
    i <= comlen c /\ i >= 1 -> getWriteAt' (CSeq c w) i = getWriteAt' c i.
Proof.
  intros c.
  dependent induction c.
  intros.
  assert (i = comlen c + 1 \/ i < comlen  c + 1).
  unfold comlen in H. fold comlen in H. omega.
  destruct H0.
  rewrite H0.
  rewrite getWriteAt'OnCSeq.
  simpl.
  assert (comlen c + 1 =? S (S (comlen c)) = false).
  rewrite Nat.eqb_neq. omega.
  rewrite H1.
  assert (comlen c +1 =? S(comlen c) = true). rewrite Nat.eqb_eq. omega.
  rewrite H2.
  reflexivity.
  simpl.
  assert (i =?  (S (S (comlen c))) = false). rewrite Nat.eqb_neq. omega.
  assert (i =? S (comlen c) = false). rewrite Nat.eqb_neq. omega.
  rewrite H1. rewrite H2.
  reflexivity.
  intros.
  simpl.
  unfold comlen in H. fold comlen in H.
  omega.
Qed.

Lemma computeWriteSetRange: forall (c: com) (wix: memix) (i: nat), List.In i (((computeWriteSet  c)) wix) -> i >= 1 /\ i <= comlen c.
  intros c.
  induction c.
  intros.
  unfold computeWriteSet in H.
  fold computeWriteSet in H.
  unfold mergeWriteSets in H.
  rewrite List.in_app_iff in H.
  destruct H.
  (* induction case - List.In i (computeWriteSet n c wix) *)
  specialize (IHc _ _ H).
  unfold comlen. fold comlen.
  omega.
  unfold writeToWriteset in H.
  destruct w.
  (* new case - List.In i (singletonWriteSet m (n + 1) wix ) *)
  unfold singletonWriteSet in H.
  unfold addToWriteSet in H.
  assert (wix = n \/ wix <> n).
  omega.
  destruct H0.
  (* wix = m *)
  rewrite <- Nat.eqb_eq in H0.
  rewrite H0 in H.
  destruct H.
  unfold comlen. fold comlen.
  unfold comlen in H. fold comlen in H.
  omega.
  destruct H.
  (* wix <> m *)
  rewrite <- Nat.eqb_neq in H0.
  rewrite H0 in H.
  inversion H.
  (* CBegin case *)
  intros.
  inversion H.
Qed.


(* All writes are present in write set *)
Lemma computeWriteSetCharacterBwd :  forall (c: com) (wix: memix) (wval: memvalue) (i: nat),
    getWriteAt' c i  = Some (Write wix wval) -> List.In i ((computeWriteSet c) wix).
Proof.
  intros.
  generalize dependent i.
  generalize dependent wix.
  generalize dependent wval.
  dependent induction c.
  intros.
  unfold computeWriteSet.
  fold computeWriteSet.
  unfold mergeWriteSets.
  rewrite List.in_app_iff.
  remember H as getWriteAt'Invoke.
  clear HeqgetWriteAt'Invoke.
  apply getWriteAt'RangeConsistent in H.
  unfold comlen in H. fold comlen in H.
  assert (i = comlen c + 1 \/ i < comlen c + 1) as icase.
  omega.
  destruct icase as [i_eq_sn | i_lt_sn].
  - (* i = n + 1*)
  right.
  unfold writeToWriteset.
  destruct w.
  unfold singletonWriteSet.
  unfold addToWriteSet.
  inversion getWriteAt'Invoke.
  assert (i =? S(comlen c)= true). rewrite Nat.eqb_eq. omega.
  rewrite H0 in H1. simpl in H1.
  inversion H1.
  assert (wix =? wix = true). exact (Nat.eqb_refl wix).
  rewrite H2.
  rewrite Nat.eqb_eq in H0.
  rewrite H0.
  simpl.
  auto.
  (* i < n + 1 *)
  -  left.
     assert (i >= 1 /\ i <= comlen c) as witness. omega.
     assert(exists (w: write), getWriteAt'  c i = Some w) as writeExists.
     apply (getWriteAt'RangeComplete _ _ witness).
     inversion getWriteAt'Invoke.
     destruct writeExists.
     destruct x.
     specialize (IHc _ _ _ H0).
     assert (i <> S (comlen c)). omega.
     rewrite <- Nat.eqb_neq in H2.
     rewrite H2 in H1.
     rewrite H0 in H1.
     inversion H1.
     rewrite H4 in IHc.
     assumption.
     (* i > n + 1 *)
  - intros.
    inversion H.
Qed.

Lemma destructInWriteToWriteSet:
  forall (w: write) (n: nat) (curtp : timepoint) (curix: memix),
    List.In curtp (writeToWriteset w n curix) -> curtp = n.
Proof.
  intros.
  unfold writeToWriteset in H.
  destruct w.
  apply destructInSingletonWriteSet in H.
  destruct H.
  assumption.
Qed.






(* All writes in write set exist in code *)
Theorem computeWriteSetCharacterFwd :  forall (c: com) (wix: memix) (i: nat), List.In i ((computeWriteSet  c) wix) -> exists (wval: memvalue), getWriteAt'  c i = Some (Write wix wval).
Proof.
  intros  c.
  intros H.
  dependent induction c.


  intros.
  assert (i >= 1 /\ i <= S (comlen c)).
  apply computeWriteSetInBounds in H0.
  unfold comlen in H0. fold comlen in H0.
  omega.
  unfold computeWriteSet in H0. fold computeWriteSet in H0. unfold mergeWriteSets in H0.

  rewrite List.in_app_iff in H0.
  destruct H0.
  - (* in write set till n*)
    assert (i <= comlen c).
    apply computeWriteSetInBounds in H0. omega.
    destruct w.
    specialize (IHc _ _ H0).
    destruct IHc.
    exists x.
    rewrite getWriteAt'DestructOnCSeq.
    assumption.
    omega.
  - (* in new write set *)
    intros.
    assert (i = comlen c+ 1). apply destructInWriteToWriteSet in H0.
    unfold comlen in H1. fold comlen in H1.
    unfold comlen in H0. fold comlen in H0.
    omega.
    destruct w.
    exists z.
    apply destructInWriteToWriteSet' in H0.
    destruct H0.
    rewrite H3.
    rewrite H2.
    apply getWriteAt'OnCSeq.

    (* CBegin case *)
  - intros.
    inversion H0.
Qed.

(* Destruction principle for dependenceAlises over CSeq *)
(* either the dependence end is pointing to the final instruction, in which case
   the dependence begin must alias with this. *)
(* Otherwise, the alasing is happening inside *)
Theorem destructDependenceAliasesInCSeq: forall (c: com) (tbegin tend: timepoint)  (wix: memix) (wval: memvalue),
    dependenceLexPositive (tbegin, tend) ->
    dependenceInRange (tbegin, tend) (CSeq  c (Write wix wval)) ->
    dependenceAliases' (tbegin, tend) (CSeq  c (Write wix wval)) <->
    (tend = comlen c + 1 /\ exists (wval_begin: memvalue), (getWriteAt'  c tbegin) = Some (Write wix wval_begin)) \/
    (tend <> comlen c + 1 /\ dependenceAliases' (tbegin, tend)  c).
  intros c.
  split.
  (* -> *)
  intros.
  assert ((tend = comlen c + 1) \/ (tend < comlen c + 1 /\ tend >= 1)).
  unfold dependenceInRange in H0.
  unfold commandIxInRange in H0.
  simpl in H0.
  omega.
  destruct H2.
  (* tend = n + 1 *)
  left.
  unfold dependenceAliases' in H1.
  simpl in H1.
  subst.
  assert (comlen c + 1 =? S (comlen c) = true). rewrite Nat.eqb_eq. omega.
  rewrite H2 in H1. simpl.
  assert (tbegin =? S (comlen c) = false).
  unfold dependenceLexPositive in H.
  simpl in H.
  rewrite Nat.eqb_neq. omega.
  rewrite H3 in H1.
  simpl in H1.
  split.
  auto.
  remember (getWriteAt' c tbegin) as write_at_begin.
  assert (exists (w: write), getWriteAt' c tbegin = Some w).
  apply getWriteAt'RangeComplete.
  unfold dependenceInRange in H0. unfold commandIxInRange in H0. simpl in H0.
  unfold dependenceLexPositive in H. simpl in H. omega.
  destruct H4.
  subst.
  destruct x eqn:xSave.
  rewrite H4.
  exists z.
  unfold writeIx in H1.
  rewrite H4 in H1.
  simpl in H1.
  subst.
  assert (n = wix). inversion H1. reflexivity.
  rewrite H5. reflexivity.

  (* tend <>  n + 1 *)
  right.
  unfold dependenceAliases' in H1.
  simpl fst in H1.
  simpl snd in H1.
  assert (tbegin < comlen c + 1 /\ tbegin >= 1).
  unfold dependenceLexPositive in H. simpl in H.
  unfold dependenceInRange in H0.
  unfold commandIxInRange in H0. simpl in H0.
  omega.
  rewrite getWriteAt'DestructOnCSeq in H1.
  rewrite getWriteAt'DestructOnCSeq in H1.
  unfold dependenceAliases'.
  simpl.
  assert (tend <> comlen c + 1). omega.
  auto.
  omega.
  omega.
  (* <- *)
  intros.
  destruct H1.
  (* tend = n + 1 *)
  destruct H1.
  unfold dependenceAliases'.
  simpl fst. simpl snd.
  rewrite H1. rewrite getWriteAt'OnCSeq.
  assert (tbegin < comlen c + 1 /\ tbegin >= 1).
  unfold dependenceLexPositive in H. unfold dependenceInRange in H0. unfold commandIxInRange in H0. simpl in H. simpl in H0.
  omega.
  assert (getWriteAt'  (CSeq c (Write wix wval)) tbegin = getWriteAt' c tbegin).
  apply getWriteAt'DestructOnCSeq.
  omega.
  rewrite H4.
  destruct H2.
  rewrite H2.
  simpl.
  reflexivity.
  (* tend <> n + 1 *)
  (* Note that in A \/ B, when you are in B case, you are not given ~A. That is very interesting, thanks to LEM. So, I need to explicitly state that t <> n + 1
   *)
  destruct H1.
  unfold dependenceAliases'.
  rewrite getWriteAt'DestructOnCSeq.
  rewrite getWriteAt'DestructOnCSeq.
  unfold dependenceAliases' in H2.
  exact H2.
  simpl.
  unfold dependenceInRange in H0. unfold commandIxInRange in H0. simpl in H0.
  omega.
  simpl.
  unfold dependenceInRange in H0. unfold commandIxInRange in H0. simpl in H0.
  unfold dependenceLexPositive in H. simpl in H.
  omega.
Qed.

Lemma dependenceInRangeInclusive: forall (d: dependence) (c: com) (w: write),  dependenceInRange d c -> dependenceInRange d  (CSeq c w).
  unfold dependenceInRange. unfold commandIxInRange. destruct d. simpl.
  intros.
  omega.
Qed.
  

Theorem computeDependencesAlias'Fwd: forall (c: com ), forall (d: dependence), List.In d (computeDependences c) ->  dependenceAliases' d  c.
Proof.
  intros  c.
  induction c.
  intros.
  unfold computeDependences in H.
  fold computeDependences in H.
  unfold dependencesFromWriteSetAndWrite in H.
  destruct w eqn:Wsave.
  rewrite List.in_app_iff in H.
  destruct H.
  apply List.in_map_iff in H.
  unfold comlen in H. fold comlen in H.
  destruct H.
  destruct H.
  destruct d eqn:Dsave.
  inversion H.
  simpl.
  subst.
  unfold dependenceAliases'. simpl.
  assert (n0 >= 1 /\ n0 <= comlen c).
  apply computeWriteSetInBounds in H0.
  omega.
  assert (n0 =? S (comlen c) = false).
  rewrite Nat.eqb_neq.
  omega.
  assert (comlen c =? comlen c = true).
  rewrite Nat.eqb_eq. omega.
  rewrite H2. rewrite H3.
  simpl.
  apply computeWriteSetCharacterFwd in H0.
  destruct H0.
  rewrite H0.
  simpl.
  reflexivity.
  -
    (* inductive case? *)
    destruct d eqn:Dsave.
    apply  destructDependenceAliasesInCSeq.
    apply computeDependencesLexPositive in H. exact H.
    apply computeDependencesInRange in H.
    apply dependenceInRangeInclusive. exact H.
    assert (n1 = comlen c + 1 \/ n1 <> comlen c+ 1).
    omega.
    destruct H0.
    + (* n1 = n + 1 *)
      apply computeDependencesInRange in H.
      unfold dependenceInRange in H.
      unfold commandIxInRange in H.
      simpl in H. omega.
    + (* n1 <> n + 1 *)
      intros.
      right.
      specialize (IHc _ H).
      split.
      assumption. assumption.
  - intros.
    inversion H.
Qed.


(* Show under what conditions we can shorten the range of a dependence *)
Theorem dependenceInRangeDestructOnCSeq: forall (d: dependence) (c: com) (w: write), dependenceInRange d (CSeq c w) -> snd d <> comlen c + 1 ->
dependenceLexPositive d ->
dependenceInRange d c.
Proof.
  unfold dependenceInRange.
  unfold commandIxInRange.
  unfold dependenceLexPositive.
  destruct d. simpl.
  intros.
  omega.
Qed.


Theorem computeDependenceAlias'Bwd:   forall (c: com), forall (d: dependence), dependenceAliases' d c -> dependenceInRange d c -> dependenceLexPositive d  -> List.In d (computeDependences c).
Proof.
  intros c.
  induction c.
  intros.
  destruct d eqn:dsave.
  destruct w eqn:wsave.
  remember H as depAliases. clear HeqdepAliases.
  apply (destructDependenceAliasesInCSeq c n n0 _ _ H1 H0) in H.
  destruct H.
  - (* n0 = comlen c + 1 *)
    destruct H. destruct H2.
    unfold computeDependences. fold computeDependences.
    unfold dependencesFromWriteSetAndWrite.
    rewrite List.in_app_iff.
    left. (* Dependence will be part of new write set *)
    rewrite List.in_map_iff.
    exists n.
    split.
    unfold comlen. fold comlen.
    rewrite H. rewrite Nat.add_comm. reflexivity.
    eapply computeWriteSetCharacterBwd.
    apply H2.

  - (* n0 <> comlen c + 1 => n0 <= comlen c *)
    intros.
    unfold computeDependences.
    fold computeDependences.
    unfold dependencesFromWriteSetAndWrite.
    rewrite List.in_app_iff.
    right. (* This depenednece will be in the older set of deps *)
    assert (dependenceInRange (n, n0) c).
    apply dependenceInRangeDestructOnCSeq with (w := w).
    exact H0. simpl. destruct H. exact H. exact H1.
    destruct H.
    apply IHc.
    exact H3.
    exact H2. exact H1.

  - (* CBegin *)
    intros.
    simpl.
    unfold dependenceInRange in H0.
    unfold commandIxInRange in H0.
    simpl in H0.
    omega.
Qed.






Fixpoint runProgram  (p: com) (initmemory: memory) : memory :=
  match p with
  | CBegin => initmemory
  | CSeq p' w => writeToMemory' w  (runProgram p' initmemory)
  end.


(* definition of program equality *)
Definition ceq (c c' : com) : Prop :=
  forall (initmemory : memory), (runProgram c initmemory) = (runProgram c' initmemory).

Notation "x '===' y" := (ceq x y) (at level 70).

Theorem ceq_refl: forall (c: com), c === c.
Proof.
  intros.
  unfold ceq.
  intros. reflexivity.
Qed.

Theorem ceq_symmetric: forall(c c': com), c === c' <-> c' === c.
Proof.
  intros.
  unfold ceq.
  split.
  intros.
  auto.
  intros. auto.
Qed.

Fixpoint com_append (c c': com) : com :=
  match c' with
  | CBegin => c
  | CSeq c' w => CSeq  (com_append  c c') w
  end.


Notation "x '+++' y"  := (com_append  x y) (at level 60).
Theorem ceq_add_cseq: forall (cn cn' : com) (w: write), cn === cn' -> (CSeq cn w) ===  (CSeq cn' w).
Proof.
  intros.
  unfold ceq.
  unfold runProgram.
  fold runProgram.
  intros.
  unfold ceq in H.
  specialize (H initmemory).
  rewrite H.
  reflexivity.
Qed.

Theorem runprogram_distribute_append: forall (cn cn': com), forall (initmem: memory), runProgram (cn +++ cn') initmem = runProgram cn' (runProgram cn initmem).
  intros cn cn'. generalize dependent cn. induction cn'.
  intros.
  unfold com_append. fold com_append.
  unfold runProgram. fold runProgram. rewrite IHcn'.
  reflexivity.
  intros. unfold com_append.
  unfold runProgram. fold runProgram. reflexivity.
Qed.




(* Should be handy: https://coq.inria.fr/library/Coq.Logic.EqdepFacts.html *)

(* As usual, dependent typed hell *)
Theorem ceq_append_weak: forall (c cl cr : com), cl === cr ->cl +++ c === cr +++ c.
Proof.
  intro c.
  induction c.
  intros.
  unfold com_append. fold com_append.
  apply ceq_add_cseq.
  apply IHc. exact H.
  intros.
  unfold com_append. exact H.
Qed.

Theorem ceq_append_strong: forall (cl cl' cr cr': com), cl === cr -> cl' === cr' -> cl +++ cl' === cr +++ cr'.
  intros.
  unfold ceq in H.
  unfold ceq in H0.
  unfold ceq.
  intros.
  rewrite runprogram_distribute_append.
  rewrite runprogram_distribute_append.
  rewrite H.
  rewrite H0.
  reflexivity.
Qed.

Theorem ceq_switch_no_alias: forall (wix1 wix2: memix) (wval1 wval2: memvalue),
    wix1 <> wix2 ->
    CSeq (CSeq CBegin (Write wix1 wval1)) (Write wix2 wval2) ===
         CSeq (CSeq CBegin (Write wix2 wval2)) (Write wix1 wval1).
  intros.
  unfold ceq.
  intros.
  unfold runProgram.
  unfold writeToMemory'.
  apply functional_extensionality.
  intros.
  assert (x = wix2 \/ x <> wix2). omega.
  destruct H0.
  rewrite H0.
  unfold writeToMemory.
  assert (wix2 =? wix2 = true). rewrite Nat.eqb_eq. omega.
  assert (wix2 =? wix1 = false). rewrite Nat.eqb_neq. omega.
  rewrite H1. rewrite H2. reflexivity.

  unfold writeToMemory.
  subst.
  assert (x =? wix2 = false). rewrite Nat.eqb_neq. omega.
  rewrite H1. reflexivity.
Qed.


(* 
Fixpoint mapProgramWithScheduleGo (s: nat -> nat) (witness: Bijective s) (c: com) (newc: com) (n: nat): com :=
  let sinv := inverse s
                      curw = getWriteAt' c 
  newc' := 
  in
  if loc == n
  then newc
  else let 
                                              
 *)

(* A proposition that witnesses that c' is the output of schedule s applied to c,
   and that s and sinv are inverses.
   Equivalently, it witnesses that c is the output of schedule sinv applied to c'
*)
Definition scheduleMappingWitness (s sinv: nat -> nat) (c c': com) : Prop :=
  comlen c = comlen c' /\
  is_inverse s sinv /\
  forall (i: nat), i >= 1 /\ i <= comlen c ->
                   s i >= 1 /\ s i <= comlen c /\
                   sinv i >= 1 /\ sinv i <= comlen c' /\
                   getWriteAt' c i = getWriteAt' c' (s i) /\
                   getWriteAt' c (sinv i) = getWriteAt' c' i.


Lemma scheduleMappingWitnessSymmetric: forall (s sinv: nat -> nat) (c c': com),
    scheduleMappingWitness s sinv c c' -> scheduleMappingWitness sinv s c' c.
Proof.
  unfold scheduleMappingWitness.
  intros.
  destruct H. destruct H0. 
  split; try auto.
  split.
  unfold is_inverse. unfold is_inverse in H0. destruct H0. split; auto.
  intros.
  specialize (H1 i).
  rewrite H. rewrite H in H1.
  specialize (H1 H2). destruct H1. destruct H3. destruct H4. destruct H5.
  destruct H6.
  split. auto. split. auto. split. auto. auto.
Qed.


Definition applyScheduleToDependence (s: nat -> nat) (d: dependence) : dependence :=
  match d with
  | (x0, x1) => (s x0, s x1)
  end.

Definition scheduleRespectsDependence (s: nat -> nat) (d: dependence) : Prop :=
  dependenceLexPositive (applyScheduleToDependence s d).

Definition scheduleRespectsDependenceSet (s: nat -> nat) (ds: dependenceset) : Prop := forall (d: dependence), List.In d ds -> scheduleRespectsDependence s d.

(* A dependence set is complete if it contains all the dependence we expect
it to contain. TODO: Rewrite the definition of the completeness of
our computeDepenedence function using this notion *)
(* NOTE: this is not enough, is it? We need a definition that this thing allows us to
flip assert that if we have a depenendece, then it's present in the list *)
Definition validDependence (c: com) (d: dependence) : Prop :=
  dependenceAliases' d c /\ dependenceInRange d c /\ dependenceLexPositive d.
Hint Unfold validDependence.

Definition completeDependenceSet (c: com) (ds: dependenceset) : Prop :=
  forall (d: dependence),
    (validDependence c d -> List.In d ds) /\
    (List.In d ds -> validDependence c d).


(* If we have an empty dependence set, then it is impossible for instructions to alias. *)
Theorem emptyDependenceSetImpliesNoAliasing: forall (i j : nat) (c: com), completeDependenceSet c Datatypes.nil -> dependenceLexPositive (i, j) -> dependenceInRange (i, j) c ->  exists (w w': write), getWriteAt' c i = Some w /\ getWriteAt' c j = Some w' /\ writeIx w <> writeIx w'.
Proof.
  intros.
  assert (exists (wi: write), getWriteAt' c i = Some wi).
  unfold dependenceInRange in H1. destruct H1. simpl in H1.
  unfold commandIxInRange in H1.
  apply getWriteAt'RangeComplete.
  omega.
  assert (exists (wj: write), getWriteAt' c j = Some wj).
  unfold dependenceInRange in H1.  simpl in H1. destruct H1.
  apply getWriteAt'RangeComplete.
  unfold commandIxInRange in H3.
  omega.
  destruct H2. destruct H3.
  exists x. exists x0.
  split.
  assumption.
  split.
  assumption.
  assert (writeIx x = writeIx x0 \/ writeIx x <> writeIx x0) as aliasing_cases. omega.
  destruct aliasing_cases.
  (* have alias *)
  -  unfold completeDependenceSet in H.
     specialize (H (i, j)).
     destruct H as [intoList outOfList].
     assert (False) as contra.
     apply intoList.
     unfold validDependence.
     split.
     unfold dependenceAliases'. simpl. rewrite H2. rewrite H3. simpl. rewrite H4.
     reflexivity.
     split. assumption. assumption.
     inversion contra.
    (* no alias *)
    -  exact H4.
Qed.


(* Slightly better way of stating theorem *)
Theorem emptyDependenceSetImpliesNoAliasing': forall (i j : nat) (c: com), completeDependenceSet c Datatypes.nil -> i <> j ->  commandIxInRange c i -> commandIxInRange c j -> exists (w w': write), getWriteAt' c i = Some w /\ getWriteAt' c j = Some w' /\ writeIx w <> writeIx w'.
  intros.
  assert (i < j \/ i > j) as ij_order. omega.
  destruct ij_order as [i_lt_j | i_gt_j].
  - (* i < j *)
    apply emptyDependenceSetImpliesNoAliasing.
    exact H.
    unfold dependenceLexPositive. simpl. assumption.
    unfold dependenceInRange. auto.
  - (* i > j *)
    intros.
    assert (exists (w w': write), getWriteAt' c j = Some w /\ getWriteAt' c i = Some w' /\ writeIx w <> writeIx w').

    apply (emptyDependenceSetImpliesNoAliasing j i c).
    exact H.
    auto.
    unfold dependenceInRange. auto.
    destruct H3.
    destruct H3.
    exists x0.
    exists x.
    split.
    destruct H3. destruct H4. assumption.
    split.
    destruct H3.  assumption.
    destruct H3. destruct H4. omega.
Qed.


Theorem scheduleMappingWitnessDestructOnCSeqEqual:
  forall (c c' : com) (s sinv: nat -> nat) (w: write) (ds: dependenceset),
    completeDependenceSet c ds ->
    scheduleMappingWitness s sinv (CSeq c w) (CSeq c' w) ->
    scheduleRespectsDependenceSet s ds ->
    scheduleMappingWitness s sinv c c'.
Proof.
  intros.
  unfold scheduleMappingWitness.
  unfold scheduleMappingWitness in H0.
  destruct H0.
  split.
  - (* lengths equal *)
    unfold comlen in H0. fold comlen in H0. omega.
  - split.
    + (* bijective *)
      destruct H2.
      exact H2.
    + (* range *)
      intros.
      destruct H2. specialize (H4 i). destruct H4.
      unfold comlen. fold comlen. omega.
      unfold comlen in H5. fold comlen in H5.
      split. omega. split.
      unfold comlen in H0. fold comlen in H0.
      assert (comlen c = comlen c'). omega.
      unfold scheduleRespectsDependenceSet in H1.
Abort.

  

(* TODO, QUESTION: Why is this not trivial for coq? *)
Theorem writesEqualDecidable: forall (w w': write), w = w' \/ w <> w'.
  intros.
  destruct w.
  destruct w'.
  assert( n = n0 \/ n <> n0). omega.
  assert (z = z0 \/ z <> z0). omega.
  destruct H.
  destruct H0.
  left.
  congruence.
  right.
  congruence.
  right. congruence.
Qed.

(* Notion of a subprogram aliasing with a single write *)
Definition NoAliasingBetweenSubprogramAndWrite (c: com) (wix: memix) : Prop :=
  forall (i: nat), commandIxInRange c i ->
                   option_map writeIx (getWriteAt' c i) <> Some wix.

                                                                  


Lemma NoAliasingBetweenSubprogramAndWriteDestructOnCSeq:
  forall (c: com) (wix wixalias: memix) (wval: memvalue),
    NoAliasingBetweenSubprogramAndWrite (CSeq c (Write wix wval)) wixalias ->
    NoAliasingBetweenSubprogramAndWrite c wixalias /\ wix <> wixalias.
Proof.
  intros.
  split.
  - (* No aliasing between c and wixalias *)
    unfold NoAliasingBetweenSubprogramAndWrite.
    unfold NoAliasingBetweenSubprogramAndWrite in H.
    intros.
    specialize (H i).
    simpl in H.
    assert (i =? S (comlen c ) = false).
    rewrite Nat.eqb_neq. unfold commandIxInRange in H0. omega.
    rewrite H1 in H.
    apply H.
    apply commandIxInRangeInclusive.
    assumption.
  - (* wix <> wixalias *)
    intros.
    unfold NoAliasingBetweenSubprogramAndWrite in H.
    specialize (H (comlen c + 1)).
    simpl in H.
    assert (comlen c + 1 =? S (comlen c) = true). rewrite Nat.eqb_eq. omega.
    rewrite H0 in H.
    simpl in H.
    assert (Some wix <> Some wixalias -> wix <> wixalias). auto.
    apply H1. apply H.
    unfold commandIxInRange.
    unfold comlen. fold comlen. omega.
Qed.

(* If two subprograms do not alias, we can reorder them freely *)
Definition NoAliasingBetweenSubprograms (c1 c2: com) : Prop :=
    forall (i j: nat),
    commandIxInRange c1 i->
    commandIxInRange c2 j ->
    option_map writeIx (getWriteAt' c1 i) <> option_map writeIx (getWriteAt' c2 j).

Lemma NoAliasingBetweenSubprogramsDestructOnCSeq: forall (c1 c2: com) (wix: memix) (wval: memvalue),
    NoAliasingBetweenSubprograms (CSeq c1 (Write wix wval)) c2 ->
    NoAliasingBetweenSubprograms c1 c2 /\
    NoAliasingBetweenSubprogramAndWrite c2 wix.
    
Proof.
  intros.
  split.
  (* No aliasing between subprograms *)
  unfold NoAliasingBetweenSubprograms.
  intros.
  unfold NoAliasingBetweenSubprograms in H.
  specialize (H i j).
  assert (commandIxInRange (CSeq c1 (Write wix wval)) i).
  apply commandIxInRangeInclusive. auto.
  specialize (H H2 H1).
  rewrite getWriteAt'DestructOnCSeq in H.
  exact H.
  unfold commandIxInRange in H0. omega.
  (* No aliasing with write *)
  unfold NoAliasingBetweenSubprogramAndWrite.
  unfold NoAliasingBetweenSubprograms in H.
  specialize (H (comlen c1 + 1)).
  assert (commandIxInRange (CSeq c1 (Write wix wval)) (comlen c1 + 1)).
  unfold commandIxInRange. unfold comlen. fold comlen. omega.
  intros.
  specialize (H i H0 H1).
  simpl in H.
  assert (comlen c1 + 1 =? S(comlen c1) = true).
  rewrite Nat.eqb_eq. omega.
  rewrite H2 in H.
  simpl in H. auto.
Qed.

(* If a subprogram does not touch a memory location, then we can use the original
state of memory at this location *)
Lemma NoAliasingBetweenSubprogramAndWriteAllowsPunchthrough:
  forall (c: com) (wix: memix) (mem: memory),
    NoAliasingBetweenSubprogramAndWrite c wix ->
    (runProgram c mem) wix = mem wix.
Proof.
  intros.
  induction c.
  unfold runProgram. fold runProgram.
  unfold writeToMemory'. destruct w eqn:wsave.
  unfold writeToMemory.
  assert (wix = n \/ wix <> n) as wixcases. omega.
  destruct wixcases.
  - (* wix = m, but this cannot be possible since the program does not alias *)
    unfold NoAliasingBetweenSubprogramAndWrite in H.
    assert (wix <> n).
    (* pick last instruction *)
    specialize (H (comlen c + 1)).
    unfold commandIxInRange in H. unfold comlen in H. fold comlen in H.
    assert (comlen c + 1 <= 1 + comlen c). omega.
    assert (comlen c + 1 >= 1). omega.
    simpl in H.
    (* TODO: why do I need to prove this?! PROOF AUTOMATION. *)
    assert (comlen c + 1 =? S (comlen c) = true).  rewrite Nat.eqb_eq. omega.
    rewrite H3 in H. simpl in H.
    assert (Some n <> Some wix -> wix <> n). auto.
    apply H4. apply H; auto.
    contradiction.

  - (* wix <> m. We automatically use the written value *)
    intros.
    assert (wix =? n = false). rewrite Nat.eqb_neq. omega.
    apply NoAliasingBetweenSubprogramAndWriteDestructOnCSeq in H.
    destruct H.
    specialize (IHc H).
    rewrite H1.
    auto.

  - (* runprogram of cbegin *)
    intros.
    unfold runProgram. fold runProgram. auto.
Qed.




Theorem NoAliasingBetweenSubprogramAndWriteAllowsReordering:
  forall (c: com) (wix: memix)  (wval: memvalue) (mem: memory),
    NoAliasingBetweenSubprogramAndWrite c wix ->
    runProgram c (writeToMemory' (Write wix wval) mem) =
    writeToMemory' (Write wix wval) (runProgram c mem).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  assert (x = wix \/ x <> wix) as xcases. omega.

  destruct xcases.
  (* x = wix. *)
  unfold writeToMemory'.
  unfold writeToMemory.
  assert (x =? wix = true). rewrite Nat.eqb_eq. omega.
  rewrite H1. fold writeToMemory.
  remember (fun ix : memix => if ix =? wix then wval else mem0 ix) as oldmem.
  assert (runProgram c oldmem x = oldmem x).
  apply NoAliasingBetweenSubprogramAndWriteAllowsPunchthrough.
  rewrite <- H0 in H. assumption.
  rewrite H2.
  rewrite Heqoldmem. rewrite H1. reflexivity.
  assert (x =? wix = false). rewrite Nat.eqb_neq. omega.
  (* x <> wix *)
  generalize dependent wix.
  generalize dependent wval.
  generalize dependent x.
  generalize dependent mem0.
  induction c.
  intros.
  unfold writeToMemory'.
  rewrite readFromWriteDifferent.
  unfold runProgram. fold runProgram.
  specialize (IHc mem0 x wval wix).
  destruct w eqn:wsave.
  assert (NoAliasingBetweenSubprogramAndWrite c wix /\ n <> wix).
  apply NoAliasingBetweenSubprogramAndWriteDestructOnCSeq in H.
  assumption.
  destruct H2.
  specialize (IHc H2 H0 H1).
  unfold writeToMemory' in IHc.
  unfold writeToMemory'.
  assert (n = x \/ n <> x) as mcases.
  omega.
  destruct mcases.
  - (* m = x *)
    unfold writeToMemory.
    assert (x =? n = true). rewrite Nat.eqb_eq. omega.
    rewrite H5.
    reflexivity.
  - (* m <> x *)
    intros.
    assert (writeToMemory n z (runProgram c mem0) x = runProgram c mem0 x).
    unfold writeToMemory. assert (x =? n = false). rewrite Nat.eqb_neq. omega.
    rewrite H5.
    reflexivity.
    rewrite H5.
    assert (writeToMemory n z (runProgram c (writeToMemory wix wval mem0)) x = runProgram c mem0 x).
    setoid_rewrite readFromWriteDifferent.
    rewrite IHc.
    setoid_rewrite readFromWriteDifferent.
    reflexivity. omega. omega.
    rewrite H6.
    reflexivity.
    (* CBegin case *)
  - intros.
    assumption.
  - intros.
    unfold runProgram. fold runProgram.
    reflexivity.
Qed.



Theorem NoAliasingBetweenSubprogramsAllowsReordering: forall (c1 c2: com),
    NoAliasingBetweenSubprograms c1 c2 -> c1 +++ c2 === c2 +++ c1.
  Proof.
  intros.
  unfold ceq.
  intros.
  rewrite runprogram_distribute_append.
  rewrite runprogram_distribute_append.
  generalize dependent H. generalize dependent initmemory.
  generalize dependent c2.
  induction c1.

  (* Induction over c1 *)
  - (* c1 = seq *)
    intros.
    unfold runProgram. fold runProgram.
    remember H as H'. clear HeqH'.
    destruct w eqn:wsave.
    apply NoAliasingBetweenSubprogramsDestructOnCSeq in H.
    destruct H.
    specialize (IHc1 c2 initmemory H).
    rewrite <- IHc1.
    remember (runProgram c1 initmemory) as c1finalstate.
    apply NoAliasingBetweenSubprogramAndWriteAllowsReordering.
    assumption.
  - (* CBegin *)
    intros.
    unfold runProgram. fold runProgram.
    reflexivity.
Qed.


Definition aliasingWriteTimepointsSet (c: com) (ix: memix) (l: list timepoint) : Prop :=
  List.NoDup l /\
  forall (t: timepoint),
    List.In t l -> commandIxInRange c t /\ (exists (wval: memvalue), getWriteAt' c t = Some (Write ix wval)).


(* getAliasingWriteTimepoints actually does what it says it does *)
(* NOTE: I need to change this a little to exhibit NoDup.

Theorem getAliasingWriteTimepointsForProgramGivesAliasingWrites:
  forall (c: com) (ix: memix),
    aliasingWriteTimepointsSet c
                     ix
                     (getAliasingWriteTimepointsForProgram c ix).
Proof.
  intros.
  unfold aliasingWriteTimepointsSet.
  intros.
  induction c.
  (* CSeq *)
  unfold getAliasingWriteTimepointsForProgram in H.
  fold getAliasingWriteTimepointsForProgram in H.

  assert (writeIx w = ix \/ writeIx w <> ix) as ix_destruct. omega.
  destruct ix_destruct.
  - (* writeIx = w *)
  assert (writeIx w =? ix = true). rewrite Nat.eqb_eq. omega.
  rewrite H1 in H.
  apply List.in_inv in H.
  destruct H.
  + (* comlen (CSeq c w) = t0 *)
    unfold commandIxInRange.
    split. unfold comlen. fold comlen. unfold comlen in H. fold comlen in H. omega.
    destruct w eqn:wsave. (* need acess to wval *)
    exists m0. unfold getWriteAt'.
    assert (t0 =? comlen (CSeq c (Write m m0)) = true). rewrite Nat.eqb_eq. omega.
    rewrite H2. auto. unfold writeIx in H0. rewrite H0. reflexivity.
  +  (*  List.In t0 (getAliasingWriteTimepointsForProgram c ix - induction! *)
    intros.
    specialize (IHc H).
    destruct IHc.
    split.
    (* commandIxInRange (CSeq c w) t0 *)
    *  apply commandIxInRangeInclusive. assumption.
    *  destruct H3. exists x.
       assert (getWriteAt' (CSeq c w) t0 = getWriteAt' c t0).
       unfold commandIxInRange in H2.
       rewrite (getWriteAt'DestructOnCSeq c t0 w H2). reflexivity.
       rewrite H4. auto.
  -  (* writeIx w <> ix *)
    assert (writeIx w =? ix = false). rewrite Nat.eqb_neq. assumption.
    rewrite H1 in H. specialize (IHc H). destruct IHc.
    split.
    + (* commandIxInRange (Cseq c w) t0 *)
      apply commandIxInRangeInclusive. assumption.
    + (* exists ... *)
      destruct H3.
      exists x.
       assert (getWriteAt' (CSeq c w) t0 = getWriteAt' c t0).
       unfold commandIxInRange in H2.
       rewrite (getWriteAt'DestructOnCSeq c t0 w H2). reflexivity.
       rewrite H4. auto.
  - (* CBegin *)
    intros.
    inversion H.
Qed.
*)


(* TODO: has no one really defined these combinators? *)
Lemma list_length_1_implies_singleton: forall (a: Type) (l: list a), length l = 1 -> exists (x: a), l = List.cons x List.nil.
  intros a l.
  destruct l.
  intros. inversion H.
  intros.
  inversion H.
  rewrite List.length_zero_iff_nil in H1.
  exists a0.
  rewrite H1.
  reflexivity.
Qed.

(* TODO: has no one really defined these combinators? *)
Lemma list_length_2_implies_2_elems: forall (a: Type) (l: list a),
    length l = 2 -> exists (x x': a), l = List.cons x (List.cons x' List.nil).
  intros a l.
  destruct l.
  intros. inversion H.
  intros.
  inversion H.
  apply list_length_1_implies_singleton in H1.
  destruct H1.
  exists a0. exists x.
  rewrite H0.
  reflexivity.
Qed.

Lemma list_length_gt_2_implies_at_least_2_elems: forall (a: Type) (l: list a),
    length l >= 2 -> exists (x x' : a) (l': list a), l = List.cons x (List.cons x' l').
Proof.
  intros.
  destruct l.
  inversion H.
  destruct l.
  inversion H.
  inversion H1.
  exists a0. exists a1. exists l.
  reflexivity.
Qed.

Fixpoint getLatestAliasingWriteTimepointForProgram (c: com) (ix: memix) : option timepoint :=
  match c with
  | CBegin => None
  | CSeq c' w => if writeIx w =? ix
                 then Some (comlen c) 
                 else  getLatestAliasingWriteTimepointForProgram c' ix
  end.

Definition latestAliasingWriteTimepointSpec (c: com) (ix: memix) (latest: option timepoint): Prop :=
  (exists (n: timepoint),
      (latest = Some n) /\
      commandIxInRange c n /\
      (exists (wval: memvalue), getWriteAt' c n = Some (Write ix wval)) /\
      forall (t: timepoint), t > n -> commandIxInRange c t ->
     exists (w: write), getWriteAt' c t = Some w /\ writeIx w <> ix) \/
  (latest = None /\
   forall (t: timepoint),
     commandIxInRange c t ->
     exists (w: write), getWriteAt' c t = Some w /\ writeIx w <> ix).



                   
Theorem emptyDependenceSetWillHaveSingleAliasingWrite:
  forall (c: com) (ix: memix) (lt: list timepoint),
    completeDependenceSet c List.nil ->
    aliasingWriteTimepointsSet c ix lt ->
    (exists (t: timepoint),
        lt = List.cons t List.nil) \/ lt = List.nil.
  intros.
  unfold aliasingWriteTimepointsSet in H0.
  assert (length lt <= 1 \/ length lt >= 2) as lt_destruct. omega.
  destruct lt_destruct.
  - (* length lt <= 1 *)
    assert (length lt = 0 \/ length lt = 1) as lt_0_or_1. omega.
    destruct lt_0_or_1.
    + (* length lt = 0 *)
      assert (lt = List.nil).
      rewrite <- length_zero_iff_nil. assumption.
      right. assumption.
    + (* length lt = 1 *)
      intros.
      apply list_length_1_implies_singleton in H2.
      destruct H2.
      left.
      exists x.
      assumption.
  - (* length >= 2 *)
    intros.
    apply list_length_gt_2_implies_at_least_2_elems in H1.
    destruct H1.
    destruct H1.
    destruct H1.
    assert (List.In x lt) as x_in_lt.
    rewrite H1. apply in_eq.
    assert (List.In x0 lt) as x0_in_lt.
    rewrite H1.
    unfold List.In.
    right. left. reflexivity.
    assert (x = x0 \/ x <> x0).
    omega.
    destruct H2.
    + (* x = x0, will lead to contradiction because set is nodup *)
      destruct H0.
      rewrite H2 in H1.
      rewrite H1 in H0.
      rewrite List.NoDup_cons_iff in H0.
      destruct H0.
      assert (List.In x0 (x0 :: x1)). unfold List.In. left. auto.
      contradiction.
    + (* x <> x0, will let me show that I have two aliasing writes. Also contadiction *)
      intros.
      destruct H0.
      assert (commandIxInRange c x /\
              exists (wval: memvalue), getWriteAt' c x = Some (Write ix wval)).
      apply (H3 x x_in_lt).
      assert (commandIxInRange c x0 /\
              exists (wval: memvalue), getWriteAt' c x0 = Some (Write ix wval)).
      apply (H3 x0 x0_in_lt).
      destruct H4.
      destruct H5.
      destruct H6.
      destruct H7.
      assert (exists (w w': write),
                 getWriteAt' c x = Some w /\
                 getWriteAt' c x0 = Some w' /\
                 writeIx w <> writeIx w').
      apply (emptyDependenceSetImpliesNoAliasing' _ _ _ H H2 H4 H5).
      destruct H8.
      destruct H8.
      destruct H8.
      destruct H9.
      subst.
      rewrite H6 in H8.
      rewrite H7 in H9.
      inversion H8.
      inversion H9.
      rewrite <- H11 in H10.
      rewrite <- H12 in H10.
      simpl in H10.
      (* finally, we get a contadiction! ix <> ix *)
      (* we exhibited an aliasing *)
      contradiction.
Qed.

  
Definition applyScheduleToDependenceSet (s: nat -> nat) (ds: dependenceset) : dependenceset :=
  List.map (applyScheduleToDependence s) ds.

(* TODO: super ugly proof, this is too much of low level algebra. NEED PROOF AUTOMATION! *)
Theorem dependenceAliasesTransportAcrossValidSchedule:
  forall (c c': com) (s sinv: nat -> nat) (d: dependence),
    scheduleMappingWitness s sinv c c' ->
    dependenceAliases' d c ->
    dependenceInRange d c -> 
    dependenceAliases' (applyScheduleToDependence s d) c'.
Proof.
  unfold dependenceAliases'.
  intros.
  destruct d eqn:dsave.
  simpl. simpl in H0.
  unfold scheduleMappingWitness in H.
  remember (getWriteAt' c n) as w_c_at_n.
  remember (getWriteAt' c n0) as w_c_at_n0.
  destruct H. destruct H2.
  remember (getWriteAt' c' (s n)) as w_c'_at_sn.
  remember (getWriteAt' c' (s n0)) as w_c'_at_sn0.

  assert (getWriteAt' c' (s n) = getWriteAt' c n).
  specialize (H3 n).
  assert (n >= 1 /\ n <= comlen c) as n_inbounds. unfold dependenceInRange in H1. unfold commandIxInRange in H1. simpl in H1. omega.
  specialize (H3 n_inbounds).
  destruct H3. destruct H4. destruct H5. intuition. 

  assert (getWriteAt' c' (s n0) = getWriteAt' c n0). specialize (H3 n0). assert (n0 >= 1 /\ n0 <= comlen c). unfold dependenceInRange in H1. unfold commandIxInRange in H1. simpl in H1. omega.
  specialize (H3 H5). intuition.
  subst.
  rewrite H4. rewrite H5. rewrite H0. reflexivity.
Qed.

Theorem dependenceInRangeTransportAcrossValidSchedule:
  forall (c c': com) (s sinv: nat -> nat) (d: dependence),
    scheduleMappingWitness s sinv c c' ->
    dependenceInRange d c -> 
    dependenceInRange (applyScheduleToDependence s d) c'.
Proof.
  unfold dependenceInRange.
  unfold scheduleMappingWitness.
  unfold applyScheduleToDependence.
  unfold commandIxInRange.
  destruct d eqn:dsave.
  simpl.
  intuition.
  simpl. specialize (H4 n). cut (n >=1 /\ n <= comlen c). intros.
  specialize (H4 H3). omega. omega.
  specialize (H4 n). omega. specialize (H4 n0). omega. specialize (H4 n0). omega.
Qed.


Theorem dependenceLexPositiveTransportAcrossValidSchedule:
  forall (c: com) (s: nat -> nat) (d: dependence) (ds: dependenceset),
    completeDependenceSet c ds ->
    scheduleRespectsDependenceSet s ds ->
    dependenceLexPositive d ->
    dependenceAliases' d c ->
    dependenceInRange d c -> 
    dependenceLexPositive (applyScheduleToDependence s d).
Proof.
  intros.
  destruct d.
  specialize (H0 (n, n0)).
  unfold completeDependenceSet in H.
  assert(List.In (n, n0) ds).
  apply H; intuition.
  unfold scheduleRespectsDependence in H0.
  apply H0. assumption.
Qed.



Theorem dependenceLexPositiveTransportAcrossValidSchedule'':
  forall (c c': com) (s sinv: nat -> nat) (d: dependence) (ds: dependenceset),
    completeDependenceSet c ds -> 
    scheduleMappingWitness s sinv c c' ->
    scheduleRespectsDependenceSet s ds ->
    dependenceAliases' d c ->
    dependenceInRange d c ->
    dependenceLexPositive d ->
    dependenceLexPositive (applyScheduleToDependence s d).
Proof.
  intros c c' s sinv d ds dscomplete mapwitness respectdeps aliases inrange lexpos.
  induction c.
  destruct d as [tbegin tend] eqn:dsave.
  destruct w as [wix wval] eqn:wsavee.


  assert (s tbegin < s tend \/ s tbegin = s tend \/ s tbegin > s tend) as tbegin_tend_cases. omega.


  destruct tbegin_tend_cases as [tbegin_tend_lt | tbegin_tend_eq_or_gt].
  - (* s tbegin < s tend *)
    auto.

  - (* s tbegin = s tend.
        => tbegin = tend.
    Will be contradiction, because there is a dependence (tbegin, tend)
   *) 
  destruct tbegin_tend_eq_or_gt as [tbegin_tend_eq | tbegin_tend_gt].
  assert (tbegin = tend) as tbegin_eq_tend_by_s_bij.
  cut (sinv (s tbegin) = sinv (s tend)).
  unfold scheduleMappingWitness in mapwitness.
  destruct mapwitness as [_ [isinv _]].
  unfold is_inverse in isinv. destruct isinv.
  rewrite (H tbegin), (H tend). auto.
  rewrite tbegin_tend_eq. auto.
  unfold dependenceLexPositive in lexpos. simpl in lexpos.
  assert (tbegin = tend /\ tbegin < tend). auto.
  omega.


   (* tbegin > tend.
    *)
  (* Since we have (tbegin, tend) as a dependence, transport it *)
  (* This will give us (s tbegin, s tend) as a dependence *)
  (* this contradicts s tbegin > s tend since all dependences transported by "s"
     are lex-positive *)
  unfold scheduleRespectsDependenceSet in respectdeps.
  assert (scheduleRespectsDependence s (tbegin, tend)) as tbegin_tend_respected_by_s.
  apply respectdeps.
  destruct (dscomplete (tbegin, tend)) as [intoList _].
  unfold completeDependenceSet in intoList.
  apply intoList.
  unfold validDependence.
  intuition.

  unfold scheduleRespectsDependence in tbegin_tend_respected_by_s.
  unfold dependenceLexPositive in tbegin_tend_respected_by_s.
  unfold applyScheduleToDependence in tbegin_tend_respected_by_s.
  simpl in tbegin_tend_respected_by_s.
  assert (s tbegin > s tend /\ s tbegin < s tend) as contra.
  omega.
  omega.

  - (* CBegin cannot have a dependence *)
    destruct d  as [tbegin tend].
    unfold scheduleRespectsDependenceSet in respectdeps.
     unfold dependenceInRange in inrange.
     unfold commandIxInRange in inrange.
     simpl in inrange.
     omega.
Qed.

Theorem is_inverse_injective: forall (A B:Set) (f: A -> B) (g: B -> A) (a b: A), is_inverse f g -> f a = f b -> a = b.
Proof.
  intros.
  assert (g (f a) = g (f b)) as gcall.
  rewrite H0. reflexivity.
  unfold is_inverse in H. destruct H.
  cut (a = g (f a)).
  cut (b = g (f b)).
  intros.
  rewrite H2. rewrite H3. auto.
  intuition. intuition.
Qed.

Theorem is_inverse_symmetric: forall (A B:Set) (f: A -> B) (g: B -> A), is_inverse f g -> is_inverse g f.
Proof.
  intros.
  unfold is_inverse in *.
  intuition.
Qed.
(* If D is a complete dependence set for c, and c --s--> c', Then s(D) is a valid dependence set for c' *)
(* This is kind of fucked because I need that hypotheiss about lex transport. *)
(* I need to think about this more carefully *)
Theorem dependenceSetTransportAcrossValidSchedule:
  forall (c c': com) (s sinv: nat -> nat) (ds: dependenceset),
    completeDependenceSet c ds ->
    scheduleMappingWitness s sinv c c' ->
    scheduleRespectsDependenceSet s ds ->
    completeDependenceSet c' (applyScheduleToDependenceSet s ds).
Proof.

  intros.

  assert (scheduleMappingWitness sinv s c' c) as witness_inv. apply scheduleMappingWitnessSymmetric. intuition.

  unfold completeDependenceSet.
  intros d'.

  split.
  intros valid_dep_d'.
  unfold validDependence in valid_dep_d'.
  destruct valid_dep_d' as [aliases_d' [inrange_d' lexpos_d']].

  unfold applyScheduleToDependenceSet. unfold applyScheduleToDependence.
  rewrite List.in_map_iff.
  exists (applyScheduleToDependence sinv d').

  split.
  destruct d'.
  unfold applyScheduleToDependence.
  assert (forall (n: nat), s (sinv n) = n). unfold scheduleMappingWitness in H0. intuition. unfold is_inverse in H0. intuition.
  intuition.
  apply H.

  unfold validDependence.
  split.

  eapply dependenceAliasesTransportAcrossValidSchedule.
  exact witness_inv.
  assumption.
  assumption.

  split.
  eapply dependenceInRangeTransportAcrossValidSchedule.
  exact witness_inv.
  assumption.

  assert (dependenceAliases' (applyScheduleToDependence sinv d') c).
  eapply dependenceAliasesTransportAcrossValidSchedule.
  exact witness_inv.
  assumption.
  assumption.


  destruct d' as [tbegin tend] eqn:dsave.
  assert (sinv tbegin < sinv tend \/ sinv tbegin = sinv tend \/ sinv tbegin > sinv tend) as cases. omega.
  destruct cases as [lt | eq_or_gt].
  (* lt *)
  unfold dependenceLexPositive, applyScheduleToDependence.
  simpl. auto.
  destruct eq_or_gt as [eq | gt].
  (* eq *)
  assert (tbegin = tend).
  eapply is_inverse_injective.
  unfold scheduleMappingWitness in witness_inv.
  destruct witness_inv as [_ [inv _]].
  exact inv. assumption.
  unfold dependenceLexPositive in lexpos_d'.
  assert (tbegin < tend /\ tbegin = tend) as contradict.
  intuition.
  omega.
  (* gt *)
  assert (List.In (applyScheduleToDependence sinv (tend, tbegin)) ds) as wrong_dep.
  unfold completeDependenceSet in H.
  apply H.
  + (* show that we get aliases *)
   unfold validDependence. split.
  eapply dependenceAliasesTransportAcrossValidSchedule.
  exact witness_inv.
  rewrite dependenceAliases'Symmetric.
  auto.
  rewrite dependenceInRangeSymmetric. auto.
  split.
  eapply dependenceInRangeTransportAcrossValidSchedule.
    exact witness_inv. rewrite dependenceInRangeSymmetric. auto.
   unfold dependenceLexPositive. simpl. auto.

  + (* Now that we have wrong_dep, show that it will be preserved lex. This will violate our assumption that sinv (tbegin, tend) is a dependence *)
    assert (tend < tbegin).
    unfold scheduleRespectsDependenceSet in H1.
    specialize (H1 _ wrong_dep).
    unfold scheduleRespectsDependence in H1.
    simpl in H1.
    unfold dependenceLexPositive in H1.
    simpl in H1.
    unfold scheduleMappingWitness in witness_inv.
    destruct witness_inv as [_ [inv _]].
    unfold is_inverse in inv.
    destruct inv as [inv_s inv_sinv].
    cut (s (sinv tend) = tend).
    cut (s (sinv tbegin) = tbegin).
    intros tend_inv tbegin_inv.
    rewrite <- tend_inv. rewrite <- tbegin_inv. omega.
    apply inv_s.
    apply inv_s.
    assert (tend < tbegin /\ tbegin < tend) as contra.
    unfold dependenceLexPositive in lexpos_d'. simpl in lexpos_d'.
    omega.
    (* blow this up *)
    omega.

  + intros d'_in_transport_ds.
    (* other direction: we know that we hve a dependence d', we need to show it's fine *)
    unfold validDependence.
    unfold applyScheduleToDependenceSet  in d'_in_transport_ds.
    rewrite List.in_map_iff in d'_in_transport_ds.
    destruct d'_in_transport_ds as [d [d'_from_d d_in_ds]].

    remember H as completedepset. clear Heqcompletedepset.
    unfold completeDependenceSet in H.
    specialize (H d).
    destruct H as [_ memberProps].
    specialize (memberProps d_in_ds).
    unfold validDependence in memberProps.
    rewrite <- d'_from_d.

    split.
    eapply dependenceAliasesTransportAcrossValidSchedule; try intuition.
    apply H0.
    intuition.
    intuition.
    intuition.


    eapply dependenceInRangeTransportAcrossValidSchedule.
    apply H0. intuition.

    eapply dependenceLexPositiveTransportAcrossValidSchedule.
    exact completedepset.
    auto. auto. auto. auto.
Qed.



Lemma completeDependenceSetConsDestructOnCSeq:
  forall (c: com) (wix: memix) (wval: memvalue)
         (tbegin tend: timepoint) (ds: dependenceset),
    completeDependenceSet (CSeq c (Write wix wval)) ((tbegin, tend) :: ds) ->
    (tend = comlen c + 1 /\
     (exists (wval': memvalue), getWriteAt' c tbegin = Some (Write wix wval'))) \/
    (tend <> comlen c + 1).
Proof.
  intros c wix wval tbegin tend ds completedepset.
  assert (tend = comlen c + 1 \/ tend <= comlen c \/ tend > comlen c + 1) as tend_cases.
  omega.
  destruct tend_cases as [tend_at_end| tend_not_at_end].

  - (* tend = comlen c + 1 *)
    left.
    split; try auto.
    unfold completeDependenceSet in completedepset.
    specialize (completedepset (tbegin, tend)).
    destruct completedepset as [_ inListValid].
    assert (validDependence (CSeq c (Write wix wval)) (tbegin, tend)) as d_is_valid.
    apply inListValid.
    unfold List.In. left. reflexivity.
    unfold validDependence in d_is_valid.
    destruct d_is_valid as [d_aliases [d_in_range d_lexpos]].
    assert (exists (w:write), getWriteAt' c tbegin = Some w) as exists_w_tbegin.
    apply getWriteAt'RangeComplete.
    unfold dependenceInRange,commandIxInRange, comlen in d_in_range.
    fold comlen in d_in_range.
    simpl in d_in_range.
    destruct d_in_range as [tbegin_range tend_range].
    unfold dependenceLexPositive in d_lexpos. simpl in d_lexpos.
    omega.


    destruct exists_w_tbegin as [w_tbegin w_tbegin_witness].
    destruct w_tbegin as [w_tbegin_ix w_tbegin_val].
    exists w_tbegin_val.
    unfold dependenceAliases' in d_aliases.
    simpl in d_aliases.
    cut (tbegin =? S(comlen c) = false).
    cut (tend =? S(comlen c) = true).
    intros if1 if2. rewrite if1, if2 in d_aliases.
    inversion d_aliases as [wix_eq_witness].
    rewrite w_tbegin_witness in wix_eq_witness.
    simpl in wix_eq_witness. inversion wix_eq_witness.
    rewrite w_tbegin_witness.
    rewrite H0. reflexivity.
    rewrite Nat.eqb_eq. unfold dependenceInRange, commandIxInRange, dependenceLexPositive in d_in_range, d_lexpos. simpl in d_in_range,d_lexpos.
    omega.
    rewrite Nat.eqb_neq. unfold dependenceInRange, commandIxInRange, dependenceLexPositive in d_in_range, d_lexpos. simpl in d_in_range,d_lexpos. omega.

  -  intros. right. omega.
Qed.

Lemma latestAliasingWriteTimepointSpecDestructOnCSeq:
  forall (c: com) (latestw: write) (readix: memix) (latest_aliasingt: timepoint),
    latestAliasingWriteTimepointSpec (CSeq c latestw) readix (Some latest_aliasingt) ->
    latest_aliasingt <> comlen c + 1 ->
    latestAliasingWriteTimepointSpec c readix (Some latest_aliasingt).
Proof.
  intros.
  unfold latestAliasingWriteTimepointSpec.
  unfold latestAliasingWriteTimepointSpec in H.
  destruct H.
  destruct H. destruct H. destruct H1.
  destruct H2.
  left.
  exists latest_aliasingt.
  inversion H.

  split; try auto.
  split.

  - (* commandIxInRange c x *)
    unfold commandIxInRange in *.
    unfold comlen in *. fold comlen in *. omega.

  - intros. split.
    destruct H2 as [wval].
    exists wval.
    cut (getWriteAt' (CSeq c latestw) x = getWriteAt' c x).
    intros write_at_destruct.
    rewrite <- write_at_destruct. rewrite H2. reflexivity.
    rewrite getWriteAt'DestructOnCSeq. auto.
    rewrite <- H5. unfold commandIxInRange in H1. unfold comlen in H1. fold comlen in H1. omega.

    intros.
    specialize (H3 t0 H4).
    cut (commandIxInRange (CSeq c latestw) t0).
    intros t0_in_range_cseq.
    specialize (H3 t0_in_range_cseq).
    destruct H3 as [write_at_t0 write_at_t0_witness].
    exists write_at_t0.
    destruct write_at_t0_witness.
    assert (getWriteAt' (CSeq c latestw) t0 = getWriteAt' c t0).
    apply getWriteAt'DestructOnCSeq.
    unfold commandIxInRange in H6. omega.
    rewrite <- H8.
    split. exact H3.
    exact H7.
    apply commandIxInRangeInclusive. exact H6.

  - intros.
    destruct H.
    inversion H.
Qed.


Theorem noLatestAliasingWriteDestructOnCSeq:
  forall (c: com) (w: write) (readix: memix),
    latestAliasingWriteTimepointSpec (CSeq c w) readix None ->
    latestAliasingWriteTimepointSpec c readix None.
Proof.
  intros c w readix witness_on_cseq.
  unfold latestAliasingWriteTimepointSpec.
  right.
  split.
  auto.
  intros t_check.
  intros t_check_in_c.
  assert (commandIxInRange (CSeq c w) t_check) as t_check_in_cseq.
  apply commandIxInRangeInclusive. exact t_check_in_c.

  assert (getWriteAt' c t_check = getWriteAt' (CSeq c w) t_check) as write_inclusive.
  symmetry.
  apply getWriteAt'DestructOnCSeq. unfold commandIxInRange in t_check_in_c.
  omega.

  assert (exists (w_t : write), getWriteAt' (CSeq c w) t_check = Some w_t) as w_at_tcheck_in_cseq.
  apply (getWriteAt'RangeComplete (CSeq c w) t_check).
  (* TODO: an "auto" should suffice after this *)
  unfold commandIxInRange in t_check_in_c.
  unfold comlen. fold comlen. omega.

  destruct w_at_tcheck_in_cseq as [w_at_tcheck  w_at_tcheck_witness].
  exists w_at_tcheck.
  split.
  rewrite write_inclusive.
  rewrite w_at_tcheck_witness.
  reflexivity.

  unfold latestAliasingWriteTimepointSpec in witness_on_cseq.
  destruct witness_on_cseq as [contra | usefulcase].
  destruct contra.
  destruct H.
  inversion H.

  destruct usefulcase.
  assert (writeIx w_at_tcheck <> readix) as goal.
  specialize (H0 t_check).
  specialize (H0 t_check_in_cseq).
  destruct H0.
  destruct H0.

  assert (w_at_tcheck = x).
  rewrite H0 in w_at_tcheck_witness.
  inversion w_at_tcheck_witness.
  auto.
  rewrite H2.
  exact H1.
  exact goal.
Qed.


Theorem noLatestAliasingWriteAllowsPunchthrough: forall (c: com) (readix: memix)  (initmem: memory),
    latestAliasingWriteTimepointSpec c readix None ->
    runProgram c initmem readix = (initmem readix).
Proof.
  intros c. induction c.
  intros readix initmem no_aliasing_tp.
  assert (latestAliasingWriteTimepointSpec c readix None) as destruct_H.
  eapply noLatestAliasingWriteDestructOnCSeq.
  exact no_aliasing_tp.
  destruct w as [wix wval].
  assert (wix = readix \/ wix <> readix) as wix_cases.
  omega.
  destruct wix_cases as [wix_eq_readix | wix_neq_readix].
  (* wix = readix *)
  (* I can create a contradiction because now the write aliases *)
  assert (wix <> readix).
  unfold latestAliasingWriteTimepointSpec in no_aliasing_tp.
  destruct no_aliasing_tp as [contra | useful].
  + destruct contra. destruct H. inversion H.
  + destruct useful. specialize (H0 (comlen c + 1)).
    assert (commandIxInRange (CSeq c (Write wix wval)) (comlen c + 1)) as inrange.
    unfold commandIxInRange, comlen. fold comlen. omega.
    specialize (H0 inrange).
    destruct H0.
    destruct H0.
    inversion H0.
    assert (comlen c + 1 =? S(comlen c) = true) as eq_dumb.
    rewrite Nat.eqb_eq. omega.
    rewrite eq_dumb in H3.
    clear eq_dumb.
    destruct x as [xix xval].
    inversion H3.
    simpl in H1. exact H1.
  +  assert (wix = readix /\ wix <> readix) as absurd. auto.
     omega.
  + (* wix = readix *)
    intros.
    unfold runProgram.
    fold runProgram.
    unfold writeToMemory'.
    rewrite readFromWriteDifferent.
    apply IHc.
    exact destruct_H.
    omega.
  + (* CBegin case *)
    intros.
    unfold runProgram. auto.
Qed.
                        


Theorem latestAliasingWriteWillBeValue: forall (c: com) (readix: memix) (aliasingt: timepoint) (wval: memvalue) (initmem: memory),
    latestAliasingWriteTimepointSpec c readix (Some aliasingt) ->
    (getWriteAt' c  aliasingt = Some (Write readix wval)) ->
    runProgram c initmem readix = wval.
Proof.
  intros c readix aliasingt wval initmem.
  intros tpspec.
  intros aliasingtwrite.
  induction c.
  - (* CSeq *)
    assert (aliasingt = S(comlen c) \/ aliasingt < S (comlen c)).
    apply getWriteAt'RangeConsistent in aliasingtwrite.
    unfold comlen in aliasingtwrite. fold comlen in aliasingtwrite.
    omega.
    destruct H as [aliasingt_at_end | aliasingt_before_end].
    (* aliasingt = S (comlen C) *)
    + rewrite aliasingt_at_end in *. clear aliasingt_at_end.
    assert (w = Write readix wval).
    unfold getWriteAt' in aliasingtwrite.
    unfold comlen in aliasingtwrite. fold comlen in aliasingtwrite.
    assert (S (comlen c) =? 1 + comlen c = true) as comlen_c_p_1_equiv.
    rewrite Nat.eqb_eq. omega.
    rewrite comlen_c_p_1_equiv in aliasingtwrite.
    inversion aliasingtwrite.
    reflexivity.
    rewrite H.
    unfold runProgram. fold runProgram.
    unfold writeToMemory'.
    apply readFromWriteIdentical.

  (* aliasingt < S (comlen C) *)
    + intros.
      destruct w as [finalwix finalwval].
      assert (finalwix <> readix).
      * assert (finalwix <> readix \/ finalwix = readix).
        omega.
        destruct H.
        assumption.
      (* derive contradition from finalwix = readix *)
        unfold latestAliasingWriteTimepointSpec in tpspec.
        destruct tpspec.
        (* Some tp exists *)
        destruct H0.
        destruct H0.
        inversion H0. rewrite <- H3 in *. clear H3. clear H0. clear x.
        destruct H1.
        destruct H1.
        specialize (H2 (S (comlen c))).
        assert (S (comlen c) > aliasingt). omega.
        specialize (H2 H3). clear H3.
        assert (commandIxInRange (CSeq c (Write finalwix finalwval)) (S (comlen c))).
        unfold commandIxInRange. unfold comlen. fold comlen. omega.
        specialize (H2 H3). clear H3.
        destruct H2.
        unfold getWriteAt' in H2.
        assert (S (comlen c) =? comlen (CSeq c (Write finalwix finalwval)) = true).
        unfold comlen. fold comlen. rewrite Nat.eqb_eq. omega.
        rewrite H3 in H2. clear H3.
        destruct H2.
        inversion H2.
        rewrite <- H5 in *.
        clear H5. clear H2.
        simpl in H3.
        (* contradiction, baby *)
        assert (finalwix <> readix /\ finalwix = readix).
        omega.
        omega.
        (* Some tp = None *)
        destruct H0. inversion H0.

        (* aliasingt < S (comlen C) \/ finalwix <> read ix *)
      * intros.


        assert (getWriteAt' c aliasingt = Some (Write readix wval)).
        rewrite <- aliasingtwrite.
        symmetry.
        eapply getWriteAt'DestructOnCSeq.
        apply getWriteAt'RangeConsistent in aliasingtwrite.
        omega.

        unfold runProgram. fold runProgram.
        unfold writeToMemory'.
        rewrite readFromWriteDifferent.
        apply IHc.

        (* we need to show that latestAliasingWriteTimepointSpec
can be destructed *)
        eapply latestAliasingWriteTimepointSpecDestructOnCSeq.
        exact tpspec.
        omega.
        exact H0.
        omega.

  - (* CBegin *)
    intros.
    unfold getWriteAt' in aliasingtwrite.
    inversion aliasingtwrite.
Qed.



Theorem noLatestAliasingWriteTimepointTransportAcrossValidSchedule:
  forall (s sinv: nat -> nat) (c c': com) (readix: memix),
    scheduleMappingWitness s sinv c c' ->
    latestAliasingWriteTimepointSpec c readix None -> 
    latestAliasingWriteTimepointSpec c' readix None.
Proof.
  intros s sinv c c' readix schedwitness tpwitness.
  unfold latestAliasingWriteTimepointSpec in *.
  destruct tpwitness.
  - (* useless case, Some n = None *)
    destruct H.
    destruct H.
    inversion H.
  - (* useful case *)
    intros.
    destruct H.
    right.
    split. auto.
    intros t0.
    intros t0_in_range.
    specialize (H0 (sinv t0)).
    assert (commandIxInRange c (sinv t0)).
    unfold commandIxInRange in *.
    unfold scheduleMappingWitness in schedwitness.
    destruct schedwitness.
    destruct H2.
    specialize (H3 t0).
    rewrite H1 in H3.
    cut (t0 >= 1 /\ t0 <= comlen c'). intros t0_in_range_c.
    specialize (H3 t0_in_range_c).
    omega.
    omega.
    specialize (H0 H1).
    destruct H0 as [w_at_sinv_t0 witness_w_at_sinv_t0].
    exists w_at_sinv_t0.
    assert (getWriteAt' c' t0 = getWriteAt' c (sinv t0)).
    unfold scheduleMappingWitness in schedwitness.
    destruct schedwitness.
    destruct H2.
    specialize (H3 t0).
    assert (t0 >= 1 /\ t0 <= comlen c) as t0_range. unfold commandIxInRange in t0_in_range. rewrite H0 in *. omega.
    specialize (H3 t0_range).
    intuition.
    rewrite H0.
    auto.
Qed.


Theorem commandIxInRangeTransportAlongValidSchedule:
  forall (s sinv: nat -> nat) (c c': com) (tp: timepoint),
    scheduleMappingWitness s sinv c c' ->
    (commandIxInRange c tp <->
    commandIxInRange c' (s tp)).
Proof.
  intros s sinv c c' tp witness.
  split.
  (* -> *)
  intros tp_inrange.
  unfold commandIxInRange in *.
  unfold scheduleMappingWitness in witness.
  destruct witness.
  destruct H0. specialize (H1 tp).
  cut (tp >= 1 /\ tp <= comlen c).
  intros tp_inrange'.
  specialize (H1 tp_inrange').
  destruct H1. destruct H2.
  rewrite <- H. omega.
  omega.

  intros stp_inrange.
  unfold commandIxInRange in *.
  unfold scheduleMappingWitness in witness.
  destruct witness.
  destruct H0.
  specialize (H1 (s tp)).
  assert (sinv (s tp) = tp).
  unfold is_inverse in H0.
  destruct H0.
  apply H0.
  rewrite H2 in H1.
  omega.
Qed.


Theorem getWriteAt'TransportAlongValidSchedule:
  forall (s sinv: nat -> nat) (c c': com) (tp: timepoint) (w: write),
    scheduleMappingWitness s sinv c c' ->
    (getWriteAt' c tp = Some w <->
    getWriteAt' c' (s tp) = Some w).
Proof.

  intros.
  split.
  intros.
  unfold scheduleMappingWitness in H.
  destruct H.
  destruct H.
  destruct H1. specialize (H1 tp).
  assert (tp >= 1 /\ tp <= comlen c).
  eapply getWriteAt'RangeConsistent.
  exact H0.
  specialize (H1 H2).
  destruct H1.
  destruct H3.
  destruct H4.
  destruct H5.
  destruct H6.
  rewrite <- H6.
  auto.
  (* <- *)
  intros.
  unfold scheduleMappingWitness in H.
  destruct H.
  destruct H1.
  rewrite H in H2.
  specialize (H2 (s tp)).
  assert (s tp >= 1 /\ s tp <= comlen c').
  eapply getWriteAt'RangeConsistent.
  exact H0.
  specialize (H2 H3).
  destruct H2.
  destruct H4.
  destruct H5.
  destruct H6.
  destruct H7.
  destruct H8.
  cut (getWriteAt' c tp = getWriteAt' c (sinv (s tp))).
  intros.
  rewrite H8.
  rewrite H0.
  reflexivity.
  unfold is_inverse in H1.
  destruct H1.
  specialize (H1 tp).
  rewrite H1.
  reflexivity.
Qed.

Theorem is_inverse_cancellation: forall (A: Set) (s s': A -> A) (a: A),
    is_inverse s s' -> ((s (s' a)) = a).
Proof.
  intros.
  unfold is_inverse in H.
  destruct H.
  apply H0.
Qed.


(* TODO, this proof feels "suspect to me". Please check *)
Theorem latestAliasingWriteTimepointSpecTransportAcrossValidSchedule:
  forall (ds: dependenceset)  (s sinv: nat -> nat) (c c': com) (latest_tp: timepoint) (readix: memix),
    completeDependenceSet c ds -> 
    scheduleMappingWitness s sinv c c' ->
    scheduleRespectsDependenceSet s ds ->
    latestAliasingWriteTimepointSpec c readix (Some latest_tp) ->
    latestAliasingWriteTimepointSpec c' readix (Some (s latest_tp)).
Proof.
  intros ds s sinv c c' latest_tp readix.
  intros.
  remember H2 as H2'. clear HeqH2'.
  unfold latestAliasingWriteTimepointSpec in H2.
  destruct H2.
  - (* Some case *)
    intros.
    unfold latestAliasingWriteTimepointSpec.
    left. (* Some timepoint exists in goal *)
    destruct H2.
    destruct H2.
    inversion H2.
    rewrite <- H5 in *. clear H5. clear H2.
    destruct H3.
    destruct H3.

    assert (scheduleMappingWitness sinv s c' c).
    apply scheduleMappingWitnessSymmetric. assumption.
   
    assert (is_inverse sinv s) as inv_sinv_s.
    unfold scheduleMappingWitness in H0.
    destruct H0. destruct H6. apply is_inverse_symmetric. assumption.

    (* -- cleanup up hypotheis, proceed with goal --*)
    exists (s latest_tp).
    split.
    + reflexivity.
    + split.
      * eapply commandIxInRangeTransportAlongValidSchedule.
        exact H5.
        erewrite is_inverse_cancellation. assumption.
        exact inv_sinv_s.
      * split.
        ** destruct H3 as [wval c_latest_tp].
           exists wval.
           eapply getWriteAt'TransportAlongValidSchedule.
           exact H5.
           rewrite is_inverse_cancellation.
           exact c_latest_tp.
           exact inv_sinv_s.
        **  intros t'.
            intros t'_gt_s_latest_tp.
            intros t'_in_range.
            assert (exists (w: write), getWriteAt' c' t' = Some w) as existence_of_write_at_t'.
            apply getWriteAt'RangeComplete.
            unfold commandIxInRange in t'_in_range. omega.
            destruct existence_of_write_at_t' as [w_at_t' witness_w_at_t'].
            exists w_at_t'.
            split.
            ***  rewrite witness_w_at_t'. reflexivity.
            *** intros.
                assert (writeIx w_at_t' = readix \/ writeIx w_at_t' <> readix) as
                    writeIx_w_at_t'_cases.
                omega.
                destruct writeIx_w_at_t'_cases as [writeIx_eq | writeIx_neq].
                **** (* writeIX w_at_t' = readix. Derive contradiction since this will give us a dependence that is not supposed to exist *)
                  (* TODO, NOTE: Note that I don't actually derive a contradiction, sow what's going on? *)
                  assert (dependenceLexPositive (s latest_tp, t')) as lexpos.
                  unfold dependenceLexPositive. simpl. omega.


                  assert (dependenceAliases' (s latest_tp, t') c') as aliases.
                  unfold dependenceAliases'.
                  simpl.
                  rewrite witness_w_at_t'.
                  unfold option_map.
                  rewrite writeIx_eq.
                  destruct H3 as [w_latest_tp w_latest_tp_witness].
                  assert (getWriteAt' c' (s latest_tp) = Some (Write readix w_latest_tp)).
                  eapply getWriteAt'TransportAlongValidSchedule.
                  exact H5.
                  rewrite is_inverse_cancellation.
                  exact w_latest_tp_witness.
                  exact inv_sinv_s.
                  rewrite H3.
                  simpl. reflexivity.


                  assert (dependenceInRange (s latest_tp, t') c').
                  unfold dependenceInRange.
                  simpl.
                  split.
                  eapply commandIxInRangeTransportAlongValidSchedule.
                  exact H5.
                  rewrite is_inverse_cancellation.
                  exact H2.
                  exact inv_sinv_s.
                  apply getWriteAt'RangeConsistent in witness_w_at_t'.
                  unfold commandIxInRange. omega.


                  assert (completeDependenceSet c' (applyScheduleToDependenceSet s ds)) as ds'_complete.
                  eapply  dependenceSetTransportAcrossValidSchedule.
                  exact H.
                  exact H0.
                  exact H1.


                  (* use the fact that ds' is complete to show that this dependence is fucked *)
                  assert (List.In (s latest_tp, t') (applyScheduleToDependenceSet s ds)) as legit_dep.
                  unfold completeDependenceSet in ds'_complete.
                  destruct (ds'_complete (s latest_tp, t')).
                  apply H7.
                  unfold validDependence.
                  intuition.

                  unfold applyScheduleToDependenceSet in legit_dep.
                  rewrite List.in_map_iff in legit_dep.
                  destruct legit_dep as [legit_dep_in_c legit_dep_in_c_witness].

  (* cool, we have a dependence in c. exploit this to derive contradicction *)
                  destruct legit_dep_in_c_witness.

                  destruct legit_dep_in_c as [c_dep_begin c_dep_end].
                  inversion H7. clear H7.
                  specialize (H4 (sinv t')).
                  cut (sinv t' > latest_tp).
                  intros. specialize (H4 H7).
                  cut (commandIxInRange c (sinv t')).
                  intros.
                  specialize (H4 H9).
                  destruct H4 as [write_at_sinv_t' write_at_sinv_t'_witness].
                  destruct write_at_sinv_t'_witness.


                  assert (Some write_at_sinv_t' = Some w_at_t').
                  rewrite <- H4.
                  eapply getWriteAt'TransportAlongValidSchedule.
                  exact H0.
                  rewrite is_inverse_cancellation.
                  assumption.
                  apply is_inverse_symmetric. assumption.
                  inversion H13.
                  rewrite <- H15.
                  exact H12.
                  eapply commandIxInRangeTransportAlongValidSchedule.
                  exact H0.
                  rewrite is_inverse_cancellation.
                  assumption.
                  apply is_inverse_symmetric. assumption.
                  assert (sinv t' > latest_tp).
                  assert (c_dep_begin = latest_tp).
                  eapply is_inverse_injective.
                  assert (is_inverse s sinv) as inv_s_sinv.
                  apply is_inverse_symmetric. assumption.
                  apply inv_s_sinv.
                  apply H10.
                  rewrite <- H7.
                  assert (c_dep_end = sinv t').
                  rewrite <- H11.
                  erewrite is_inverse_cancellation.
                  reflexivity.
                  exact inv_sinv_s.
                  rewrite <- H9.
                  assert (dependenceLexPositive (c_dep_begin, c_dep_end)).
                  unfold completeDependenceSet in H.
                  specialize (H (c_dep_begin, c_dep_end)).
                  destruct H.
                  specialize (H12 H8).
                  destruct H12.
                  intuition.
                  unfold dependenceLexPositive in H12.
                  simpl in H12. assumption.
                  assumption.
                ****  assumption.
  -  intros.
     destruct H2.
     inversion H2.
Qed.







(* Prove this here so we can use all the machinery we have about the abstract spec on this particular instantiation *)
Theorem getLatestAliasingWriteTimepointForProgramCorrect: forall (c: com) (aliasix: memix),
    latestAliasingWriteTimepointSpec c aliasix (getLatestAliasingWriteTimepointForProgram c aliasix).
  intros.
  induction c.
  unfold latestAliasingWriteTimepointSpec in IHc.
  destruct IHc.

  unfold latestAliasingWriteTimepointSpec.
  destruct w as [wix wval].
  assert (wix = aliasix \/ wix <> aliasix). omega.
  destruct H0 as [wix_eq_aliasix | wix_neq_aliasix].
  (* wix = aliasix *)
  - left.
    exists (comlen c + 1).
    unfold getLatestAliasingWriteTimepointForProgram.
    fold getLatestAliasingWriteTimepointForProgram.
    simpl.


    assert (wix =? aliasix = true) as wix_eq_aliasix'.
    rewrite Nat.eqb_eq. omega.
    rewrite wix_eq_aliasix'. clear wix_eq_aliasix'.
    split.
    + assert (S (comlen c) = comlen c + 1).
      omega.
      rewrite H0. clear H0.
      reflexivity.
    + split.
      * unfold commandIxInRange. unfold comlen. fold comlen.
        omega.
      * split.
        ** assert (comlen c + 1 =? S (comlen c) = true).
           rewrite Nat.eqb_eq. omega.
           rewrite H0. clear H0.
           exists wval.
           rewrite wix_eq_aliasix.
           reflexivity.
        **  intros.
            unfold commandIxInRange in H1.
            unfold comlen in H1.
            fold comlen in H1.
            omega.

  (* wix <> aliasix *)
  - intros.
    left.
    assert (wix =? aliasix = false). rewrite Nat.eqb_neq. omega.
    unfold getLatestAliasingWriteTimepointForProgram.
    simpl.
    rewrite H0.
    fold getLatestAliasingWriteTimepointForProgram.
    + 


  (* wix <> aliasix *)
Admitted.

Theorem getWriteAt'TransportAlongValidSchedule':
  forall (s sinv: nat -> nat) (c c': com) (tp: timepoint) (w: write),
    scheduleMappingWitness s sinv c c' -> 
    getWriteAt' c tp = getWriteAt' c' (s tp).
  intros.
  assert ((tp >= 1 /\ tp <= comlen c) \/ tp = 0 \/ tp > comlen c) as tp_cases. omega.
  destruct tp_cases as [tp_in_range | tp_out_of_range].
Abort.


(* Main theorem of the day. If a *schedule s* respects a *complete dependence set ds*, then the semantics of the original program is the same as that of the rescheduled program *)
Theorem reschedulePreservesSemantics: forall (c c': com) (ds: dependenceset) (s sinv: nat -> nat),
    completeDependenceSet c ds -> scheduleMappingWitness s sinv c c' ->
    scheduleRespectsDependenceSet s ds -> c === c'.
Proof.
  intros c.
  intros c' ds.
  intros s sinv dscomplete witness respectsdeps.
  unfold ceq.
  intros initmemory.
  apply functional_extensionality.
  intros readix.
  set (lastaliasingtp := getLatestAliasingWriteTimepointForProgram c readix).
  assert (latestAliasingWriteTimepointSpec c readix (getLatestAliasingWriteTimepointForProgram c readix)) as latesttpspec.
  apply getLatestAliasingWriteTimepointForProgramCorrect.
  remember latesttpspec as latesttpspec'.
  clear Heqlatesttpspec'.
  unfold latestAliasingWriteTimepointSpec in latesttpspec.
  destruct latesttpspec as [ havelatesttp | nolatesttp].
  destruct havelatesttp as [tp_of_latest spec_of_tp_latest].
  destruct spec_of_tp_latest as
      [tp_latest_witness
         [tp_latest_in_range
            [tp_latest_has_write no_t_after_tp]]].
  destruct tp_latest_has_write as [tp_latest_wval tp_latest_wval_witness].
  assert (runProgram c initmemory readix = tp_latest_wval).
  eapply latestAliasingWriteWillBeValue.
  rewrite tp_latest_witness in latesttpspec'.
  apply latesttpspec'.
  apply tp_latest_wval_witness.
  rewrite H.

  assert (runProgram c' initmemory readix = tp_latest_wval).
  assert (latestAliasingWriteTimepointSpec c' readix (Some (s tp_of_latest))) as latestt'_spec.
  eapply latestAliasingWriteTimepointSpecTransportAcrossValidSchedule.
  apply dscomplete.
  apply witness.
  apply respectsdeps.
  rewrite tp_latest_witness in latesttpspec'.
  apply latesttpspec'.


  eapply latestAliasingWriteWillBeValue.
  apply latestt'_spec.
  assert (getWriteAt' c' (s tp_of_latest) = Some(Write readix tp_latest_wval)).
  eapply getWriteAt'TransportAlongValidSchedule.
  exact witness.
  exact tp_latest_wval_witness.
  exact H0.
  rewrite H0.
  reflexivity.

  assert (runProgram c initmemory readix = (initmemory readix)) as c_val.
  apply noLatestAliasingWriteAllowsPunchthrough.
  destruct nolatesttp.
  rewrite H in latesttpspec'.
  exact latesttpspec'.


  assert (runProgram c' initmemory readix = (initmemory readix)) as c'_val.
  apply noLatestAliasingWriteAllowsPunchthrough.
  destruct nolatesttp.
  rewrite H in latesttpspec'.
  assert (latestAliasingWriteTimepointSpec c' readix None) as transport_latest_tp_spec.
  eapply noLatestAliasingWriteTimepointTransportAcrossValidSchedule.
  exact witness.
  exact latesttpspec'.
  exact transport_latest_tp_spec.
  rewrite c_val. rewrite c'_val. reflexivity.
Qed.