Require Import Omega.

Inductive revlist: nat ->  Type :=
| CSeq: forall (n: nat), revlist n -> nat -> revlist (n + 1)
| CBegin: revlist 0.

(* Reasoning about this definition is impossible, because when "omega" usage leads to unreadable definitions of getNatAt inside proofs *)

Fixpoint getNatAt (n: nat) (c: revlist n) (i: nat) (witness_ub: i <= n) (witness_lb: i >= 1)  :=
  match c in (revlist n) return (i <= n -> i >= 1 -> nat) with
  | CBegin => fun E1 E2 => 0
  | CSeq n' c' curval => fun E1 E2 => 1
  end.


  (* Now what? how do I reason about the relationship between n and i? *)
Abort.

 
(* How do I write the same thing with dependent type style + actual computation, not tactic / proof based? *)