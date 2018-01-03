
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



Definition keys (mm: NatToNat) : list nat :=
  List.map  fst (elements mm).



(* forall n mm, (forall k, List.In k (keys mm) -> k >= 0) -> (forall k, List.In k (keys (insertNats n mm)) -> k >= 0) *)
Theorem key_add_presence: forall (k: nat) (v: nat) (mm : NatToNat) (curk : nat), MNat.In curk ((add k v mm)) -> curk = k \/ MNat.In curk mm.
  intros k v mm curk.
  map_iff.
  intros x.
  intuition.
Qed.

Theorem Key_to_relation_keys_projection:  
  forall (k: nat)  (mm : NatToNat) , MNat.In k mm  <-> List.In k (keys mm).
Proof.
  intros k mm.
  (* how to prove double implication *)
  split.
  (* forward *)

Example keys_nonnegative: forall (n: nat) (mm: NatToNat), 
    forall (k: nat),
      (MNat.In k mm -> k >= 0) -> 
      (MNat.In k (insertNats n mm)) -> k >= 0.
Proof.
  intros n.
  induction n.
  intros mm k kinmm.
  intros in_oldk.
  (* Now what?? *)

  (* Either k = (Sn) or K \in mm. If k = Sn then k > 0.
     if k \in mm, then use kinmm. But, how do I split these two cases? *)

  Admitted.
