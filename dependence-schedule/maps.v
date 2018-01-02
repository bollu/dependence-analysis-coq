
(* Me proving statements about maps to understand how to use maps in Coq *)

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

Module Import M := FMapList.Make(Z_as_OT).


Require Import
        Coq.FSets.FMapFacts.

Definition Time := nat.
Definition IxToTime := M.t Time.
Definition IxToIx := M.t Z.

Definition IxToTimeMempty := M.empty Time.

Example correct :(add 1%Z 1 IxToTimeMempty = add 1%Z 1 IxToTimeMempty).
Proof.
  reflexivity.
Qed.

Definition keys (mm: IxToTime) : list Z :=
  List.map  fst (elements mm).


(* Check if you can prove anything about key/value pairs *)
Definition Map1 := add (10)%Z 1 IxToTimeMempty.

Example keys_nonegative:  forall (k: Z), List.In k (keys Map1) ->  (k >= 0)%Z.
Proof.
  intros k.
  intros belong.
  (* Interesting, simpl seems to be quite good at this type of reasoning *)
  simpl in belong.
  destruct belong.
  omega.

Fixpoint idMapsGo (mm: IxToIx)
  tauto.
Qed.