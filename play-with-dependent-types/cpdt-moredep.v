(* Solving MoreDep: http://adam.chlipala.net/cpdt/html/MoreDep.html *)
(* Required to solve dependent type code *)
Require Import Gt.
Require Import Arith Bool List Omega.

(* Require Import Cpdt.CpdtTactics Cpdt.MoreSpecif. *)

Require Extraction.

Set Implicit Arguments.
Set Asymmetric Patterns.

(*
Definition useGt0 (n: nat) (witness: n > 0) : nat :=
  10.

Definition createGt0 (n : nat) : nat :=
  match n as x return (n = x -> nat) with
  | O => fun _ => 42
  | S n' => fun E => useGt0 n (eq_ind_r (fun n => n > 0) (gt_Sn_O n') E)
  end eq_refl.

Require Import Program.

Program Definition createGt0' (n : nat) : nat :=
  match n with
  | O => 42
  | S n' => useGt0 n _
  end.
Next Obligation. apply gt_Sn_O. Qed.

Definition createGt0'' (n : nat) : nat.
Proof.
  destruct n eqn:E.
  - exact 42.
  - refine (useGt0 n _).
    rewrite E.
    apply gt_Sn_O.
Defined.
 *)


Section ilist.
  Variable A : Set.

  Inductive ilist : nat -> Set :=
  | Nil : ilist O
  | Cons : forall n, A -> ilist n -> ilist (S n).


  Fixpoint app n1 (ls1 : ilist n1) n2 (ls2 : ilist n2) : ilist (n1 + n2) :=
    match ls1 with
    | Nil => ls2
    | Cons _ x ls1' => Cons x (app ls1' ls2)
    end.

  Fixpoint app' n1 (ls1 : ilist n1) n2 (ls2 : ilist n2) : ilist (n1 + n2) :=
    match ls1 in (ilist n1) return (ilist (n1 + n2)) with
    | Nil => ls2
    | Cons _ x ls1' => Cons x (app' ls1' ls2)
    end.


  Inductive type : Set :=
  | Nat : type
  | Bool : type
  | Prod : type -> type -> type.

  Inductive exp : type -> Set :=
  | NConst : nat -> exp Nat
  | Plus : exp Nat -> exp Nat -> exp Nat
  | Eq : exp Nat -> exp Nat -> exp Bool

  | BConst : bool -> exp Bool
  | And : exp Bool -> exp Bool -> exp Bool
  | If : forall t, exp Bool -> exp t -> exp t -> exp t

  | Pair : forall t1 t2, exp t1 -> exp t2 -> exp (Prod t1 t2)
  | Fst : forall t1 t2, exp (Prod t1 t2) -> exp t1
  | Snd : forall t1 t2, exp (Prod t1 t2) -> exp t2.

 Fixpoint typeDenote (t : type) : Set :=
  match t with
    | Nat => nat
    | Bool => bool
    | Prod t1 t2 => typeDenote t1 * typeDenote t2
  end%type