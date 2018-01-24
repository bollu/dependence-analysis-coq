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


Definition timepoint: Type := nat.
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
  assert (curix = ix \/ curix <> ix). omega.
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
  assert (wix = m \/ wix <> m).
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
    exists m0.
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
  exists m0.
  unfold writeIx in H1.
  rewrite H4 in H1.
  simpl in H1.
  subst.
  assert (m = wix). inversion H1. reflexivity.
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
  assert (n >= 1 /\ n <= comlen c).
  apply computeWriteSetInBounds in H0. omega.
  assert (n =? S (comlen c) = false).
  rewrite Nat.eqb_neq. omega.
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
    assert (n0 = comlen c + 1 \/ n0 <> comlen c+ 1).
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
      split. assumption. assumption.
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
  apply (destructDependenceAliasesInCSeq c n n0 m m0 H1 H0) in H.
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

Definition scheduleRespectsDependence (s: nat -> nat) (d: dependence) : Prop := dependenceLexPositive (applyScheduleToDependence s d).

Definition scheduleRespectsDependenceSet (s: nat -> nat) (ds: dependenceset) : Prop := forall (d: dependence), List.In d ds -> scheduleRespectsDependence s d.

(* A dependence set is complete if it contains all the dependence we expect
it to contain. TODO: Rewrite the definition of the completeness of
our computeDepenedence function using this notion *)
Definition completeDependenceSet (c: com) (ds: dependenceset) : Prop :=
  forall (d: dependence),
    dependenceAliases' d c ->
    dependenceInRange d c ->
    dependenceLexPositive d  -> List.In d ds.

(* Show that a complete dependence set on (CSeq c w) is a complete
dependence set on c *)
Lemma completeDependenceSetDestructOnCSeq: forall (c: com) (w: write) (ds: dependenceset), completeDependenceSet (CSeq c w) ds -> completeDependenceSet c ds.
  intros.
  unfold completeDependenceSet.
  unfold completeDependenceSet in H.
  intros.
  destruct d.
  apply (H (n, n0)).
  unfold dependenceAliases'.
  rewrite getWriteAt'DestructOnCSeq.
  rewrite getWriteAt'DestructOnCSeq.
  simpl.
  unfold dependenceAliases' in H0. simpl in H0. exact H0.
  simpl.
  unfold dependenceInRange in H1.
  unfold commandIxInRange in H1. simpl in H1.
  omega.
  simpl.
  unfold dependenceInRange in H1.
  unfold commandIxInRange in H1. simpl in H1. omega.
  apply dependenceInRangeInclusive.
  exact H1.
  exact H2.
Qed.



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
  - unfold completeDependenceSet in H.
    simpl in H.
    assert (False) as contra.
    apply H with (d := (i, j)).
    unfold dependenceAliases'. simpl. rewrite H2. rewrite H3. simpl. rewrite H4.
    reflexivity.
    assumption. assumption.
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
  assert( m = m1 \/ m <> m1). omega.
  assert (m0 = m2 \/ m0 <> m2). omega.
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
  assert (wix = m \/ wix <> m) as wixcases. omega.
  destruct wixcases.
  - (* wix = m, but this cannot be possible since the program does not alias *)
    unfold NoAliasingBetweenSubprogramAndWrite in H.
    assert (wix <> m).
    (* pick last instruction *)
    specialize (H (comlen c + 1)).
    unfold commandIxInRange in H. unfold comlen in H. fold comlen in H.
    assert (comlen c + 1 <= 1 + comlen c). omega.
    assert (comlen c + 1 >= 1). omega.
    simpl in H.
    (* TODO: why do I need to prove this?! PROOF AUTOMATION. *)
    assert (comlen c + 1 =? S (comlen c) = true).  rewrite Nat.eqb_eq. omega.
    rewrite H3 in H. simpl in H.
    assert (Some m <> Some wix -> wix <> m). auto.
    apply H4. apply H; auto.
    contradiction.

  - (* wix <> m. We automatically use the written value *)
    intros.
    assert (wix =? m = false). rewrite Nat.eqb_neq. omega.
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
  assert (NoAliasingBetweenSubprogramAndWrite c wix /\ m <> wix).
  apply NoAliasingBetweenSubprogramAndWriteDestructOnCSeq in H.
  assumption.
  destruct H2.
  specialize (IHc H2 H0 H1).
  unfold writeToMemory' in IHc.
  unfold writeToMemory'.
  assert (m = x \/ m <> x) as mcases.
  omega.
  destruct mcases.
  - (* m = x *)
    unfold writeToMemory.
    assert (x =? m = true). rewrite Nat.eqb_eq. omega.
    rewrite H5.
    reflexivity.
  - (* m <> x *)
    intros.
    assert (writeToMemory m m0 (runProgram c mem0) x = runProgram c mem0 x).
    unfold writeToMemory. assert (x =?m = false). rewrite Nat.eqb_neq. omega.
    rewrite H5.
    reflexivity.
    rewrite H5.
    assert (writeToMemory m m0 (runProgram c (writeToMemory wix wval mem0)) x = runProgram c mem0 x).
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


  (* Get the time points of all instructions that alias the given memory index *)
Fixpoint getAliasingWriteTimepointsForProgram (c: com) (ix: memix) : list timepoint :=
  match c with
  | CBegin => List.nil
  | CSeq c' w => let rest :=  (getAliasingWriteTimepointsForProgram c' ix) in
                if writeIx w =? ix then List.cons (comlen c) rest else rest
  end.

Definition aliasingWriteTimepointsSet (c: com) (ix: memix) (l: list timepoint) : Prop :=
  List.NoDup l /\
  forall (t: timepoint),
    List.In t l -> commandIxInRange c t /\ (exists (wval: memvalue), getWriteAt' c t = Some (Write ix wval)).

Theorem getAliasingWriteTimepointsForProgramCorrect:
  forall (c: com) (ix: memix),
    aliasingWriteTimepointsSet c
                     ix
                     (getAliasingWriteTimepointsForProgram c ix).
Proof.
Admitted.

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

(* If D is a complete dependence set for c, and c --s--> c', Then s(D) is a valid dependence set for c' *)
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
  intros.

  unfold applyScheduleToDependenceSet.
  rewrite List.in_map_iff.
  exists (applyScheduleToDependence sinv d').

  split.
  destruct d'.
  unfold applyScheduleToDependence.
  assert (forall (n: nat), s (sinv n) = n). unfold scheduleMappingWitness in H0. intuition. unfold is_inverse in H0. intuition.
  intuition.
  apply H.
  eapply dependenceAliasesTransportAcrossValidSchedule.
  exact witness_inv.
  assumption.
  assumption.

  eapply dependenceInRangeTransportAcrossValidSchedule.
  exact witness_inv. assumption.

  eapply dependenceLexPositiveTransportAcrossValidSchedule


                                                                               
   

                                  
Theorem emptyDependenceSetAllowsAllReschedules: forall (c c': com) (s sinv: nat -> nat),
    completeDependenceSet c List.nil -> scheduleMappingWitness s sinv c c' -> c === c'.
    unfold ceq.
    intros.
    apply functional_extensionality.
    intros.
    (* TODO: is remember the correct way to add a hypothesis to context? *)
    remember (getAliasingWriteTimepointsForProgram c x) as aliasingwritetps.
    assert ((exists (t: timepoint),
                aliasingwritetps = List.cons t List.nil) \/ aliasingwritetps = List.nil).
    eapply emptyDependenceSetWillHaveSingleAliasingWrite.
    exact H.
    rewrite Heqaliasingwritetps.
    apply getAliasingWriteTimepointsForProgramCorrect.

    destruct H1.
    + (* have one aliasing write *)
      destruct H1.
      induction c.
      unfold runProgram. fold runProgram. unfold writeToMemory'.
      destruct w.
      unfold writeToMemory.
      assert (x = m \/ x <> m). omega.
      (* x can't be equal to m, if it is, then this write also aliases which is nonsense *)
      destruct H2.

      * (* x = m. *)
        remember Heqaliasingwritetps as Heqaliasingwritetps'.
        clear HeqHeqaliasingwritetps'.
        rewrite H2 in Heqaliasingwritetps.
        unfold getAliasingWriteTimepointsForProgram in Heqaliasingwritetps.
        fold getAliasingWriteTimepointsForProgram in Heqaliasingwritetps.
        simpl in Heqaliasingwritetps. assert (m =? m = true). rewrite Nat.eqb_eq. reflexivity.
        rewrite H3 in Heqaliasingwritetps. rewrite H1 in Heqaliasingwritetps.
        inversion Heqaliasingwritetps.
        assert (x =? m = true). rewrite Nat.eqb_eq. omega.
        rewrite H4. clear H4. clear H3.

        (* now, look for same instruction in c' *)
        


(* Main theorem of the day. If a *schedule s* respects a *complete dependence set ds*, then the semantics of the original program is the same as that of the rescheduled program *)
Theorem reschedulePreservesSemantics: forall (c c': com) (ds: dependenceset) (s sinv: nat -> nat),
    completeDependenceSet c ds -> scheduleMappingWitness s sinv c c' ->
    scheduleRespectsDependenceSet s ds -> c === c'.
Proof.
  intros c c' ds.
  induction ds.
  - (* ds is empty *)
    intros.




                              
