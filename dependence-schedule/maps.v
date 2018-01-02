
(* Me proving statements about maps to understand how to use maps in Coq *)

Require Import FunInd.
Require Import Coq.Lists.List.
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
Require Import Coq.Logic.FinFun.

(* thank you kind stranger for showing me functorial modules syntax *)
(* http://newartisans.com/2016/10/using-fmap-in-coq/ *)

Require Import
  Coq.FSets.FMapList
  Coq.Structures.OrderedTypeEx.

Module Import MNat := FMapList.Make(Nat_as_OT).


Require Import
        Coq.FSets.FMapFacts.

Definition Time := nat.
Definition IxToTime := MNat.t Time.
Definition IxToIx := MNat.t Z.
Definition NatToNat := MNat.t nat.

Definition IxToTimeMempty : IxToTime := MNat.empty Time.

Example correct :(add 1 1 IxToTimeMempty = add 1 1 IxToTimeMempty).
Proof.
  reflexivity.
Qed.

Definition keys (mm: IxToTime) : list nat :=
  List.map  fst (elements mm).


(* Check if you can prove anything about key/value pairs *)
Definition Map1 := add (10) 1 IxToTimeMempty.

Example keys_nonegative:  forall (k: nat), List.In k (keys Map1) ->  (k <= 20).
Proof.
  intros k.
  intros belong.
  (* Interesting, simpl seems to be quite good at this type of reasoning *)
  simpl in belong.
  destruct belong.
  omega.
  tauto.
Qed.

Definition NatToNatEmpty : NatToNat := MNat.empty nat.

(* We wish to show that map will have only positive values *)
Function idMapsGo (mm: NatToNat)  (n: nat) {struct n}: NatToNat :=
  match n with
  | O => mm
  | S (next) => idMapsGo (MNat.add n n mm) next
  end.

Example keys_nonnegative: forall (n: nat), forall (k: nat), List.In k (keys (idMapsGo NatToNatEmpty n)) -> k >= 0.
Proof.
  intros n k.
  functional induction (idMapsGo NatToNatEmpty n).