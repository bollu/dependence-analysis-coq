(* Exercise from the CoqArt book, chapter 13: Infinite objects and proofs *)
Require Import List.
Require Import Relations.

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


Hint Resolve Finite_LNil Finite_LCons : llists.

Theorem Finite_of_LCons: forall (A: Set) (a: A) (l: LList A),
    Finite A (LCons a l) -> Finite A l.
Proof.
  intros. inversion H. auto.
Qed.

Theorem LAppend_of_finite: forall (A: Set) (l l': LList A),
    Finite A l ->
    Finite A l' ->
    Finite A (LAppend l l').
Proof.
  intros until l'.
  intros LFIN L'FIN.
  induction LFIN; subst.
  - rewrite LAppend_LNil.
    auto.
  - rewrite LAppend_LCons.
    constructor.
    auto.
Qed.


Lemma Finite_not_Infinite: forall (A: Set) (l: LList A),
    Finite A l -> ~ Infinite A l.
Proof.
  intros A l FIN INF.
  induction FIN.
  - inversion INF.
  - inversion INF. subst.
    apply (IHFIN H0).
Qed.


Lemma Infinite_not_Finite: forall (A: Set) (l: LList A),
    Infinite A l -> ~ Finite A l.
Proof.
  intros A l INF FIN.
  induction FIN.
  - inversion INF.
  - inversion INF. subst.
    apply (IHFIN H0).
Qed.

      

(* TODO: This is bugging me, how can I not prove this?! *)
(* We will know, we must know ;) *)
Lemma Not_Finite_Infinite: forall (A: Set) (l: LList A),
    ~ Finite A l -> Infinite A l.
Proof.
  cofix.
  intros A l L_NOT_FINITE.
  destruct l.
  Guarded.
  -- contradiction (L_NOT_FINITE (Finite_LNil A)).
  Guarded.
  -- constructor.
     apply Not_Finite_Infinite.
     Guarded.

     assert (L_NOT_FIN: ~Finite A l).
     intros AFIN.
     assert (CONTRA: Finite A (LCons a l)).
     constructor. auto.
     apply (L_NOT_FINITE CONTRA).
     auto.
     Guarded.
Qed.

Theorem LAppend_RNil_finite: forall (A: Set) (l: LList A),
    Finite A l ->
    LAppend l LNil = l.
Proof.
  intros.
  induction H.
  - apply LAppend_LNil.
  - rewrite LAppend_LCons.
    rewrite IHFinite.
    auto.
Qed.

  
Theorem general_omega_of_finite:
  forall (A: Set) (u v: LList A),
    Finite A u ->
    Finite A v ->
    general_omega u v = LAppend u  (general_omega v v).
Proof.
  intros.
  induction H0.
  - assert (OMEGA_OF_NIL_RIGHT: general_omega u LNil = u).
    LList_unfold (general_omega u LNil).
    destruct u; auto.
    rewrite OMEGA_OF_NIL_RIGHT.

    assert (OMEGA_OF_NIL_BOTH: general_omega LNil LNil = LNil (A := A)).
    LList_unfold (general_omega LNil LNil (A := A)).
    simpl.
    auto.
    rewrite OMEGA_OF_NIL_BOTH.
    rewrite LAppend_RNil_finite; auto.


  - induction H.
Abort.


    
Theorem omega_of_finite: forall (A: Set) (u: LList A),
    Finite A u ->
    lomega u = LAppend u (lomega u).
Proof.
  intros.
  induction H.
  - rewrite LAppend_LNil.
    reflexivity.

  - subst.
    assert (LAppend (LCons a l) (lomega (LCons a l)) = LNil).
    LList_unfold (LAppend (LCons a l) (lomega (LCons a l))).
    simpl.
    assert (lomega (LCons a l) = LNil).
    LList_unfold (lomega (LCons a l)).
    simpl.
Abort.


(* Bisimulation *)
(* We know that this is a lost cause, we consider it
   to understand where this fails *)
Lemma Lappend_of_Infinite_doomed:
  forall (A: Set) (l: LList A),
    Infinite A l ->
    (forall (l': LList A), l = LAppend l l').
Proof.
  intros until l.
  intros L_INF.
  inversion L_INF.
  subst.
  intros.
  rewrite LAppend_LCons.
  assert (DESTRUCT_CONSTRUCTOR: l0 = LAppend l0 l' -> LCons a l0 = LCons a (LAppend l0 l')).
  intros L0_EQ.
  rewrite <- L0_EQ.
  auto.
  apply DESTRUCT_CONSTRUCTOR.
  (* We were asked to bring the proof to this state *)
Abort.


CoInductive bisimilar {A: Set}: LList A -> LList A -> Prop :=
| bisim0 : bisimilar LNil LNil
| bisim1: forall (a: A) (l l': LList A),
    bisimilar l l' -> bisimilar (LCons a l) (LCons a l').

Check (reflexive).
Lemma bisimilar_reflexive: forall (A: Set),
    reflexive (LList A) (bisimilar (A := A)).
Proof.
  intros.
  unfold reflexive.
  cofix.
  destruct x.
  - apply bisim0.
    Guarded.
  - constructor.
    apply bisimilar_reflexive.
    Guarded.
Qed.

Lemma bisimilar_symmetric:  forall (A: Set),
    symmetric (LList A) (bisimilar (A := A)).
Proof.
  intros A.
  unfold symmetric.
  cofix.

  intros.
  destruct x.
  - inversion H.
    apply bisim0.
    Guarded.
  - inversion H.
    subst.
    Guarded.
    apply bisim1.
    apply bisimilar_symmetric; auto.
    Guarded.
Qed.



Lemma bisimilar_trans:  forall (A: Set),
    transitive (LList A) (bisimilar (A := A)).
Proof.
  intros A.
  unfold transitive.
  cofix.

  intros until z.
  intros XY YZ.

  destruct x.
  - inversion XY.
    subst.
    inversion YZ.
    subst.
    apply bisim0.
    Guarded.

  - inversion XY. subst.
    inversion YZ. subst.
    apply bisim1.
    eapply bisimilar_trans with (y := l'); auto.
    Guarded.
Qed.

Lemma bisimilar_equiv: forall (A: Set),
    equiv (LList A) (bisimilar (A := A)).
Proof.
  unfold equiv.
  intros.
  repeat split.
  apply bisimilar_reflexive.
  apply bisimilar_trans.
  apply bisimilar_symmetric.
Qed.

Fixpoint LNth {A: Set} (n: nat) (l: LList A) {struct n} : option A :=
  match l with
  | LNil => None
  | LCons a l' => match n with
                 | O => Some a
                 | S n' => LNth  n' l'
                 end
  end.

Lemma LNth_of_Sn: forall {A: Set} (n: nat) (l: LList A) (a: A),
    LNth (S n) (LCons a l) = LNth n l.
Proof.
  intros.
  destruct l; auto.
Qed.
  

Lemma bisimilar_LNth:
  forall (A: Set) (n: nat) (l1 l2: LList A),
    bisimilar l1 l2 -> LNth  n l1 = LNth n l2.
Proof.
  intros until n.
  induction n; intros; destruct l1; inversion H; auto; subst.
  repeat (rewrite LNth_of_Sn).
  apply IHn; auto.
Qed.

Lemma Nth_bisimilar:
  forall (A: Set)(l1 l2: LList A),
    (forall (n: nat), LNth n l1 = LNth n l2) -> bisimilar l1 l2.
Proof.
  intros A.
  cofix.
  intros.
  destruct l1.

  - specialize (H 0).
  simpl in H.
  destruct l2; try (discriminate H).
  apply bisim0.

  - destruct l2.
    ++ specialize (H 0). simpl in H. discriminate H.
       Guarded.
    ++ 
      assert (FSTEQ: a0 = a).
       specialize (H 0). simpl in H. inversion H. reflexivity.
       subst.
       Guarded.

       apply bisim1.
       assert (NTH_ON_SUBLIST: forall n: nat, LNth n l1 = LNth n l2).
       intros.
       specialize (H (S n)%nat).
       repeat (rewrite LNth_of_Sn in H).
       auto.
       apply Nth_bisimilar; auto.
Qed.
  
    
Lemma bisimilar_of_finite_is_finite:
  forall (A: Set) (l1 l2: LList A),
    Finite A l1 ->
    bisimilar l1 l2 ->
    Finite A l2.
Proof.
  intros until l2.
  intros FINL1.
  
  generalize dependent l2.
  induction FINL1.

  - intros.
    inversion H. subst. constructor.

  - intros.
    inversion H. subst.
    constructor.
    apply IHFINL1; auto.
Qed.


Lemma bisimilar_of_infinite_is_infinite:
  forall (A: Set) (l1 l2: LList A),
    Infinite A l1 ->
    bisimilar l1 l2 ->
    Infinite A l2.
Proof.
  intros A.
  cofix.
  
  intros until l2.
  intros INFL1.
  intros  BISIM.

  inversion BISIM; subst.
  - inversion INFL1.
    Guarded.

  - inversion INFL1. subst.
    Guarded.
    constructor.
    eapply bisimilar_of_infinite_is_infinite; eassumption.
    Guarded.
Qed.
            
  
  
    

             