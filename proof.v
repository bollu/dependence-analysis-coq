Require Import Arith.
Require Import Coq.ZArith.BinInt.
Require Import Coq.Numbers.BinNums.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.Zbool.
Require Import Coq.Sorting.Permutation.


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

(* Runner for function that models memoru side effects of entire programs *)
Fixpoint modelProgramMemorySideEffect_go (p: Program) (mold: Memory) : Memory :=
  match p with
  | nil => mold
  | x :: xs => modelProgramMemorySideEffect_go xs (modelStmtMemorySideEffect x mold)
  end.

Definition modelProgramMemorySideEffect (p: Program) : Memory :=
  modelProgramMemorySideEffect_go p initMemory.

                                
(* A timepoint for a schedule *)
Definition Timepoint := nat. 

(* A schedule maps statements to time points *)
Definition ScheduleMap := Stmt -> Timepoint.

(* A schedule is a permutation of a program *)
(* Definition SchedulePerm (p: Program) (q: Program) := Permutation p q. *)

(* How to leormalise a dependence? *)
(* Inductive DependenceOnScheduleMap : Type := (smap: ScheduleMap) -> (s1: Stmt) -> (s2: Stmt) -> (lt (smap s1) (smap s2)) -> DependenceOnScheduleMap. *)

Inductive ScheduleAdmitsDep:  ScheduleMap -> Stmt -> Stmt -> Prop -> Type :=
  Dep : forall (smap : ScheduleMap) (s1: Stmt) (s2: Stmt), ScheduleAdmitsDep smap s1 s2 (smap s1 < smap s2).
