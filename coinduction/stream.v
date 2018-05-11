Require Import List.

CoInductive Stream (A: Set) : Set :=
| SCons : A -> Stream A -> Stream A.


CoInductive LList (A: Set) : Set :=
| LNil : LList A
| LCons : A -> LList A -> LList A.

Implicit Arguments LNil [A].
Implicit Arguments LCons [A].


CoInductive LTree (A: Set) : Set :=
| LLeaf : LTree A
| LBin: A -> LTree A -> LTree A -> LTree A.

Implicit Arguments LLeaf [A].


(* ex 13.1, create an injection from list to llist *)
Fixpoint list_to_llist {a: Set} (l: list a): LList a :=
  match l with
  | nil => LNil
  | cons x xs => LCons x (list_to_llist xs)
  end.

Lemma list_to_llist_inj: forall (a: Set) (x y: list a),
    list_to_llist x = list_to_llist y ->
    x = y.
Proof.
  intros until x.
  induction x.
  - intros.
    destruct y; try auto; try discriminate.
  - intros.
    assert (forall (Ty : Set) (v: Ty) (l : list Ty),
               list_to_llist (v :: l) = LCons v (list_to_llist l)) as
        LIST_TO_LLIST_UNFOLD.
    auto.

    rewrite LIST_TO_LLIST_UNFOLD in H.
    destruct y.
    -- simpl in H. discriminate.
    -- rewrite LIST_TO_LLIST_UNFOLD in H.
       inversion H.
       subst.
       assert (x = y) as X_EQ_Y.
       apply IHx; auto.
       subst.
       auto.
Qed.

CoFixpoint from (n: nat) : LList nat := LCons  n (from (S n)). 