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


(* Should be handy: https://coq.inria.fr/library/Coq.Logic.EqdepFacts.html *)

(* As usual, dependent typed hell *)
Theorem ceq_append: forall (cl cl' cr cr' : com), cl === cr -> cl' === cr' -> cl +++ cl' === cr +++ cr'.
Proof.
  intros.
  induction cl'.
  induction cr'.
  unfold com_append. fold com_append.
  remember (cl +++ cl') as ll.
  remember (cr +++ cr') as rr.
  unfold ceq.
  intros.
Abort.
