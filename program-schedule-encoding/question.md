I'm trying to learn to use the `ListMap` module in Coq. I'm really not sure about proving properties about the keys or values in a `ListMap`, when the `ListMap` is created by a recursive function. I feel like I do not know what tactics to use.


    (* Me proving statements about maps to understand how to use maps in Coq *)
    
    Require Import FunInd.
    Require Import Coq.Lists.List.
    Require Import Coq.FSets.FMapInterface.
    
    
    Require Import
      Coq.FSets.FMapList
      Coq.Structures.OrderedTypeEx.
    
    Module Import MNat := FMapList.Make(Nat_as_OT).
    Require Import
            Coq.FSets.FMapFacts.
    
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
    
    (* vvvvv How do I prove this? Intuitively it is true *)
    Example keys_nonnegative: forall (n: nat),
        forall (k: nat),
          List.In k (keys (insertNats n NatToNatEmpty)) -> k >= 0.
    Proof.
      intros n k in_proof.
      induction n.
      simpl in in_proof. tauto.
      (* ??? NOW WHAT *)
    Admitted.

Informally, the argument I would use for the below program is that because `n >= 0` because it is a `nat`, the keys inserted into the map by `idMapsGo` will also always be non-negative.

I need to induct on `n` for `keys_nonnegative`. On the `nth` step, we add a key `n`, which will be non-negative (due to being a `nat`). The base case is trivial. 

However, I am unable to convert this intuition into a Coq proof :)
