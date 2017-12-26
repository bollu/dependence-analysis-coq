Require Import Arith.
Require Import Coq.ZArith.BinInt.
Require Import Coq.Numbers.BinNums.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.Zbool.


(* An index into memory *)
Definition Ix := Z.

(* values in memory *)
Definition MemValue := Z.

(* factor used in building expressions *)
(*Inductive Factor : Set := Raw : MemValue -> Factor. *)

(* A statement in our grammar *)
Inductive Stmt : Type := Write : Z -> MemValue -> Stmt.

(* A program is a list of statements *)
Definition Program := list Stmt.

(* Memory is a function from an index to a value *)
Definition Memory :=  Ix -> MemValue.

(* initial state of memory *)
Definition initMemory : Memory := fun ix => Z0.

(* currently, program state is just memory *)
(* Definition ProgramState := Memory. *)

(* Model the effect of memory writes on memory. *)
Definition modelStmtMemorySideEffect (s: Stmt) (mold: Memory) : Memory :=
  match s with
  | Write wix wval => (fun ix => if (Zeq_bool ix wix) then wval else Z0)
  end.
       
