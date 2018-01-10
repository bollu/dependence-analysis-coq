
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

Theorem insertNatsDoesNotDelete: forall (n: nat) (k: nat) (mm: NatToNat), MNat.In k mm -> MNat.In k (insertNats n mm).
  intros n. induction n.
  intros k mm.
  intros kinmm.
  simpl.
  exact kinmm.
  intros k mm.
  intros k_in_mm.



Example keys_nonnegative: forall (n: nat) (mm: NatToNat), 
    forall (k: nat),
      (MNat.In k mm -> k >= 0) -> 
      (MNat.In k (insertNats n mm)) -> k >= 0.
Proof.
  intros n.
  induction n.
  intros mm k kinmm.
  intros in_oldk.
  simpl in in_oldk.
  apply kinmm in in_oldk.
  intuition.
  intros mm k kinmm.
  intros in_insertnats_mm.
  rewrite elements_in_iff in in_insertnats_mm.
  destruct in_insertnats_mm.
  rewrite <- elements_mapsto_iff in H.
  simpl in H.

  assert (k = S n /\ MNat.In k mm).
  rewrite -> add_mapsto_iff in H.

  (* Now what?? *)

  (* Either k = (Sn) or K \in mm. If k = Sn then k > 0.
     if k \in mm, then use kinmm. But, how do I split these two cases? *)

  Admitted.
