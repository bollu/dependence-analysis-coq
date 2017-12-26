Require Import Arith.
Require Import Coq.ZArith.BinInt.
Require Import Coq.Numbers.BinNums.
Require Import Coq.Lists.List.


(* An index into memory *)
Definition Ix := Z.

(* values in memory *)
Definition MemValue := Z.

(* factor used in building expressions *)
Inductive Factor : Set := Raw : MemValue -> Factor.

(* A statement in our grammar *)
Inductive Stmt : Type := Write : Z -> Factor -> Stmt.

(* A program is a list of statements *)
Definition Program := list Stmt.

(* Memory is a function from an index to a value *)
Definition Memory :=  Ix -> MemValue.

Definition initMemory : Memory := fun ix => Z0.