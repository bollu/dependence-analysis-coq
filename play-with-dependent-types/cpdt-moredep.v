(* Solving MoreDep: http://adam.chlipala.net/cpdt/html/MoreDep.html *)
(* Required to solve dependent type code *)
Require Import Gt.

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