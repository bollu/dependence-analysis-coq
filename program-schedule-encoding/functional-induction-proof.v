

(* Me proving statements about maps to understand how to use maps in Coq *)

Require Import FunInd.
Require Import Coq.Lists.List.
Require Import Coq.FSets.FMapInterface.
Require Import FMapFacts.
Require Import FunInd FMapInterface.


Require Import
        Coq.FSets.FMapList
        Coq.Structures.OrderedTypeEx.

Module Import MNat := FMapList.Make(Nat_as_OT).
Module Import MNatFacts := WFacts(MNat).



Module Import OTF_Nat := OrderedTypeFacts Nat_as_OT.
Module Import KOT_Nat := KeyOrderedType Nat_as_OT.
(* Consider using https://coq.inria.fr/library/Coq.FSets.FMapFacts.html *)
(* Consider using https://coq.inria.fr/library/Coq.FSets.FMapFacts.html *)
(* Consider using https://coq.inria.fr/library/Coq.FSets.FMapFacts.html *)

Definition NatToNat := MNat.t nat.
Definition NatToNatEmpty : NatToNat := MNat.empty nat.

(* We wish to show that map will have only positive values *)
Function insertNats (n: nat)  (mm: NatToNat)  {struct n}: NatToNat :=
  match n with
  | O => mm
  | S (next) => insertNats  next (MNat.add n n mm)
  end.

Theorem insertNatsDoesNotDeleteKeys:
  forall (n: nat) (k: nat) (mm: NatToNat),
    MNat.In k mm -> MNat.In k (insertNats n mm).
  intros n.
  intros k mm.
  intros kinmm.
  functional induction insertNats n mm.
  exact kinmm.
  rewrite add_in_iff in IHn0.
  assert(S next = k \/ MNat.In k mm).
  auto.
  apply IHn0.
  exact H.
Qed.
