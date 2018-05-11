(* Exercise from the CoqArt book, chapter 13: Infinite objects and proofs *)
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

(* create stream [n, n+1, n+2, ...] *)
CoFixpoint from (n: nat) : LList nat := LCons  n (from (S n)).
Definition Nats : LList nat := from 0.

CoFixpoint general_omega {A: Set} (u v: LList A): LList A :=
  match v with
  | LNil => u
  | LCons b v' =>
    match u with
      | LNil => LCons b (general_omega v' v)
      | LCons a u' => LCons a (general_omega u' v)
    end
  end.

Definition lomega {A: Set} (u: LList A): LList A := general_omega u u.

CoFixpoint LAppend {A: Set} (u v: LList A): LList A :=
  match u with
  | LNil => v
  | LCons a u' => LCons a (LAppend u' v)
  end.

Definition LList_decompose {A: Set} (l: LList A): LList A :=
  match l with
  | LNil => LNil
  | LCons a l' => LCons a l'
  end.

Lemma LList_decompose_lemma:
  forall {A: Set} (l: LList A), l = LList_decompose l.
Proof.
  intros.
  case l;  unfold LList_decompose; reflexivity.
Qed.

Eval simpl in (LAppend (LCons 1 (LCons 2 LNil))
                       (LCons 1 (LCons 2 LNil))).

(* LList_decompose forces it *)
(* TODO: ponder why this is the case? *)
Eval simpl in (LList_decompose (LAppend (LCons 1 (LCons 2 LNil))
                       (LCons 1 (LCons 2 LNil)))).


Check (trans_equal).

Ltac LList_unfold term :=
  apply trans_equal with (1 := LList_decompose_lemma term).

Theorem LAppend_LNil: forall (A: Set) (l: LList A),
    LAppend LNil l = l.
Proof.
  intros.

  LList_unfold (LAppend LNil l).


  case l.
  - simpl. auto.
  - simpl. auto.
Qed.

  


Theorem LAppend_LCons:
  forall (A: Set) (a: A) (u v: LList A),
    LAppend (LCons a u) v = LCons a (LAppend u v).
Proof.
  intros; simpl.

  LList_unfold (LAppend (LCons a u) v).
  simpl. auto.
Qed.

Hint Rewrite LAppend_LNil LAppend_LCons : llists.

CoInductive Infinite (A: Set) : LList A -> Prop :=
| Infinite_LCons:
    forall (a: A) (l: LList A), Infinite A l -> Infinite A (LCons a l).
Hint Resolve Infinite_LCons : llists.

Lemma from_unfold: forall n:nat, from n = LCons n (from (S n)).
Proof.
  intros.
  LList_unfold (from n).
  simpl.
  reflexivity.
Qed.

Definition F_from:
  (forall n: nat, Infinite nat (from n)) ->
  (forall n: nat, Infinite nat (from n)).
Proof.
  intros H n.
  rewrite (from_unfold n).
  constructor.
  trivial.
Qed.

Theorem from_Infinite_V0: forall (n: nat), Infinite nat (from n).
Proof.
  cofix H.
  intro n.
  rewrite (from_unfold n).
  constructor.
  auto.
  Guarded.
Qed.

CoFixpoint Lrepeat {A: Set} (a: A): (LList A) := LCons a (Lrepeat a).

Lemma Lrepeat_unfold: forall {A: Set} (a: A), Lrepeat a = LCons a (Lrepeat a).
Proof.
  intros.
  LList_unfold (Lrepeat a).
  simpl.
  reflexivity.
Qed.

Lemma repeat_infinite: forall (A: Set) (a: A), Infinite A (Lrepeat a).
Proof.
  intros.
  cofix.
  rewrite Lrepeat_unfold.
  constructor.
  assumption.
  Guarded.
Qed.
  
Lemma general_omega_infinite: forall (A: Set) (a: A) (l l': LList A),
    Infinite A (general_omega l  (LCons a l')).
Proof.
  intros A.
  cofix.
  intros until l'.
  case l.
      
  - assert (UNFOLD_GENERAL_OMEGA: general_omega LNil (LCons a l') =
          LCons a (general_omega l'  (LCons a l') )).
    LList_unfold (general_omega LNil (LCons a l')).
    auto.
    rewrite UNFOLD_GENERAL_OMEGA.
    constructor.
    apply general_omega_infinite.
    Guarded.

  - intros.
    assert (UNFOLD_GENERAL_OMEGA: general_omega (LCons a0 l0) (LCons a l') =
            LCons a0 (general_omega l0 (LCons a l'))).
    LList_unfold (general_omega (LCons a0 l0) (LCons a l')).
    simpl; trivial.

    rewrite UNFOLD_GENERAL_OMEGA.
    constructor.
    apply general_omega_infinite.
    Guarded.
Qed.

Theorem omega_infinite: forall (A: Set) (a: A) (l: LList A),
    Infinite A (lomega (LCons a l)).
Proof.
  intros.
  unfold lomega.
  apply general_omega_infinite.
Qed.

Inductive BugInfinite (A: Set) : LList A -> Prop :=
  | BugInfinite_intro: forall (a: A) (l: LList A),
    BugInfinite A l -> BugInfinite A (LCons a l).

(* Is this correct? This seems to simple to be true *)
Lemma BugInfinite_contra: forall (A: Set) (l: LList A),
    BugInfinite A l -> False.
Proof.
  intros.
  induction H.
  auto.
Qed.

Theorem LNil_not_Infinite: forall (A: Set), ~Infinite A LNil.
Proof.
  intros a H.
  inversion H.
Qed.

Theorem Infinite_of_LCons:
  forall (A: Set) (a: A) (u: LList A),
    Infinite A (LCons a u) -> Infinite A u.
Proof.
  intros.
  inversion H.
  subst.
  auto.
Qed.

Theorem LAppend_of_infinite:
  forall (A: Set) (u: LList A),
    Infinite A u -> forall (v: LList A), Infinite A (LAppend u v).
Proof.
  intros until A.
  cofix.

  intros until u.
  intros U_INF.
  destruct u.
  - inversion U_INF.
  - intros.
    assert (APPEND_TO_CONS: LAppend (LCons a u) v = LCons a (LAppend u v)).
    LList_unfold (LAppend (LCons a u) v).
    simpl.
    auto.
    rewrite APPEND_TO_CONS.
    constructor.
    apply LAppend_of_infinite; auto.
    eapply Infinite_of_LCons; exact U_INF.
Qed.

Inductive Finite (A: Set) : LList A -> Prop :=
| Finite_LNil : Finite A LNil
| Finite_LCons: forall (a: A) (l: LList A), Finite A l ->
                                       Finite A (LCons a l).
  
  
    

             