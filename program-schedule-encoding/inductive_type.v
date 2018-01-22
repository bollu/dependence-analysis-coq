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


(* Non dependent typed versions *)
Program Fixpoint getWriteAt' (n: nat) (c: com n) (i: nat) : option write :=
  match c with
  | CBegin => None
  | CSeq _ c' w => if i =? n then Some w else getWriteAt' _ c' i
  end.


Program Definition dependenceAliases' (d: dependence) (n: nat) (c: com n) : Prop :=
  let ix1 := fst d in
  let ix2 := snd d in
  let w1 := getWriteAt' n c ix1 in
  let w2 := getWriteAt' n c ix2 in
  option_map writeIx w1 = option_map writeIx w2.

  
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

Theorem computeWriteSetInBounds: forall (n: nat) (c: com n) (ix: memix) (t: timepoint), List.In t ((computeWriteSet n c) ix) -> t <= n /\ t >= 1.
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



Theorem computeDependencesInRange: forall (n: nat) (c: com n),
    forall (d: dependence), List.In d (computeDependences n c) -> dependenceInRange d n c.
  intros.
  generalize dependent d.
  dependent induction c.
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
  omega.

  intros.
  simpl in H.
  contradiction.
Qed.


(* Stuck in dependent type hell. Going to try non dependent typed version. *)
Theorem computeDependencesAlias: forall (n: nat) (c: com n), forall (d: dependence) (witness: List.In d (computeDependences n c)), dependenceAliases d n c (computeDependencesInRange _ _  d witness).
Proof.
  intros.
  generalize dependent d.
  dependent induction c.
  intros.
  unfold computeDependences in witness.
  fold computeDependences in witness.
  unfold dependenceAliases.
  unfold getWriteAt.
Abort.



Lemma getWriteAt'RangeConsistent: forall (n: nat) (c: com n) (i: nat) (w: write), getWriteAt' n c i  = Some w -> i >= 1 /\ i <= n.
Proof.
  intros n c.
  dependent induction c.
  intros.
  unfold getWriteAt' in H.
  fold getWriteAt' in H.
  assert(forall (x y : nat), x < y \/ x = y \/ x > y) as trichotomy. intros. omega.
  specialize( trichotomy i (n + 1)).
  destruct trichotomy.
  (* i < n + 1 *)
    assert (i <> n + 1). omega.
    fold getWriteAt' in H.
    rewrite <- Nat.eqb_neq in H1.
    rewrite H1 in H.
    specialize (IHc _ _ H).
    destruct IHc.
    split; try assumption. omega.

  intros.
     destruct H0.
     (* i = n + 1 *)
     omega.

     (* i > n + 1 *)
      assert (i <> n + 1). omega.
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

Lemma getWriteAt'RangeComplete: forall (n: nat) (c: com n) (i: nat), i >= 1 /\ i <= n -> exists (w: write), getWriteAt' n c i = Some w.
Proof.
  intros n c.
  dependent induction c.
  intros.
  unfold getWriteAt'. fold getWriteAt'.
  assert(i = n + 1 \/ i < n + 1 \/ i > n + 1) as trichotomy. omega.
  (* i = n  + 1 *)
  destruct trichotomy as [tri | tri'].
  rewrite <- Nat.eqb_eq in tri.
  rewrite tri.
  exists w. reflexivity.

  destruct tri' as [tri' | tri''].
  (* i < n + 1 *)
  assert(i >= 1 /\ i <= n). omega.
  specialize (IHc _ H0).
  destruct IHc.
  assert (i <> n + 1). omega.
  rewrite <- Nat.eqb_neq in H2.
  rewrite H2.
  exists x.
  assumption.

  (* i > n + 1 *)
  omega. (* contradiction *)
  intros.
  omega.
Qed.

Lemma getWriteAt'OnCSeq: forall (n: nat) (c: com n) (w: write), getWriteAt' _ (CSeq _ c w) (n + 1) = Some w.
  intros n c.
  dependent induction c.
  intros.
  simpl.
  assert (n + 1 + 1 =? n + 1 + 1 = true).
  rewrite Nat.eqb_eq. auto.
  rewrite H.
  reflexivity.
  intros.
  simpl.
  reflexivity.
Qed.

Lemma getWriteAt'DestructOnCSeq: forall (n: nat) (c: com n) (i: nat) (w: write),
    i <= n /\ i >= 1 -> getWriteAt' (n + 1) (CSeq n c w) i = getWriteAt' n c i.
Proof.
  intros n c.
  dependent induction c.
  intros.
  assert (i = n + 1 \/ i < n + 1). omega.
  destruct H0.
  rewrite H0.
  rewrite getWriteAt'OnCSeq.
  simpl.
  assert ((n + 1 =? n + 1 + 1) = false).
  rewrite Nat.eqb_neq. omega.
  rewrite H1.
  assert (n +1 =? n + 1 = true). rewrite Nat.eqb_eq. reflexivity.
  rewrite H2.
  reflexivity.
  simpl.
  assert (i =? n + 1 + 1 = false). rewrite Nat.eqb_neq. omega.
  assert (i =? n + 1 = false). rewrite Nat.eqb_neq. omega.
  rewrite H1. rewrite H2.
  reflexivity.
  intros.
  simpl.
  omega.
Qed.

Lemma computeWriteSetRange: forall (n: nat) (c: com n) (wix: memix) (i: nat), List.In i (((computeWriteSet n c)) wix) -> i >= 1 /\ i <= n.
  intros n c.
  dependent induction c.
  intros.
  unfold computeWriteSet in H.
  fold computeWriteSet in H.
  unfold mergeWriteSets in H.
  rewrite List.in_app_iff in H.
  destruct H.
  (* induction case - List.In i (computeWriteSet n c wix) *)
  specialize (IHc _ _ H).
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
Lemma computeWriteSetCharacterBwd :  forall (n: nat) (c: com n) (wix: memix) (wval: memvalue) (i: nat),
    getWriteAt' n c i  = Some (Write wix wval) -> List.In i ((computeWriteSet n c) wix).
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
  assert (i = n + 1 \/ i < n + 1) as icase. omega.
  destruct icase as [i_eq_sn | i_lt_sn].
  - (* i = n + 1*)
  right.
  unfold writeToWriteset.
  destruct w.
  unfold singletonWriteSet.
  unfold addToWriteSet.
  inversion getWriteAt'Invoke.
  assert (i =? n + 1 = true). rewrite Nat.eqb_eq. assumption.
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
     assert (i >= 1 /\ i <= n) as witness. omega.
     assert(exists (w: write), getWriteAt' n c i = Some w) as writeExists.
     apply (getWriteAt'RangeComplete _ _ _ witness).
     inversion getWriteAt'Invoke.
     destruct writeExists.
     destruct x.
     specialize (IHc _ _ _ H0).
     assert (i <> n + 1). omega.
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


Lemma destructInWriteToWriteSet':
  forall (n: nat) (curtp : timepoint) (ix curix: memix) (val: memvalue),
    List.In curtp (writeToWriteset (Write ix val) n curix) -> curtp = n /\ curix = ix.
Proof.
  intros.
  unfold writeToWriteset in H.
  apply destructInSingletonWriteSet in H.
  omega.
Qed.




(* All writes in write set exist in code *)
Theorem computeWriteSetCharacterFwd :  forall (n: nat) (c: com n) (wix: memix) (i: nat), List.In i ((computeWriteSet n c) wix) -> exists (wval: memvalue), getWriteAt' n c i = Some (Write wix wval).
Proof.
  intros n c.
  intros H.
  dependent induction c.


  intros.
  assert (i >= 1 /\ i <= n + 1).
  apply computeWriteSetInBounds in H0.
  omega.
  unfold computeWriteSet in H0. fold computeWriteSet in H0. unfold mergeWriteSets in H0.

  rewrite List.in_app_iff in H0.
  destruct H0.
  - (* in write set till n*)
    assert (i <= n).
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
    assert (i = n + 1). apply destructInWriteToWriteSet in H0. assumption.
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



Theorem computeDependencesAlias': forall (n: nat) (c: com n), forall (d: dependence), List.In d (computeDependences n c) ->  dependenceAliases' d n c.
Proof.
  intros.
  generalize dependent d.
  dependent induction c.
  intros.
  unfold computeDependences in H.
  fold computeDependences in H.
  rewrite List.in_app_iff in H.
  destruct H.
  unfold dependencesFromWriteSetAndWrite in H.
  destruct w.
  apply in_map_iff in H.
  destruct H.
  destruct H.
  unfold computeWriteSet in H0.
  destruct c.
  fold computeWriteSet in H0.
Abort.



