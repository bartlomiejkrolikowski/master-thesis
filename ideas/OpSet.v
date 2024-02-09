(* a set of primitive, constant-time operations *)

Require Import List.
Import ListNotations.
Require Import ZArith.

(* (temporarily) everything is just a pointer to a memory cell *)
Definition Condition := Z.
Definition Instruction := nat.
Definition Reference := Z.
Definition Value := Z.

Inductive ops : Set :=
| assign : Reference -> Value -> ops
| read   : Reference -> ops
| add    : Value -> Value -> ops
| neg    : Value -> ops
| sub    : Value -> Value -> ops
| mult   : Value -> Value -> ops
| div    : Value -> Value -> ops
| bor    : Condition -> Condition -> ops
| bnot   : Condition -> ops
| band   : Condition -> Condition -> ops
| beq    : Value -> Value -> ops
| blt    : Value -> Value -> ops
| bgt    : Value -> Value -> ops
| bif    : Condition -> Instruction -> Instruction -> ops
| bloop  : Condition -> Instruction -> ops
.

Require RAMmachine.
Module RM := RAMmachine.

Definition assignInstr (ref : Reference) (v : Value) : list RM.Instruction :=
  [
    RM.load v;
    RM.storeI ref
  ].

(* I should store the value somewhere else, but I'll think about it later *)
Definition readInstr (ref : Reference) : list RM.Instruction :=
  [
    RM.loadI ref
  ].

Definition addInstr (x y : Value) : list RM.Instruction :=
  [
    RM.load x;
    RM.add y
  ].

Definition negInstr (x : Value) : list RM.Instruction :=
  [
    RM.load x;
    RM.neg
  ].

Definition subInstr (x y : Value) : list RM.Instruction :=
  [
    RM.load y;
    RM.neg;
    RM.load x
  ].

Definition multInstr (x y : Value) : list RM.Instruction :=
  [
    RM.load x;
    RM.mul y
  ].

Definition divInstr (x y : Value) : list RM.Instruction :=
  [
    RM.load x;
    RM.div y
  ].

Definition borInstr (c c' : Condition) : list RM.Instruction :=
  [
    RM.load c;
    RM.mul c';
    (* TODO: decide where to jump *)
    RM.jumpZero 0
  ].

Definition bnotInstr (c : Condition) : list RM.Instruction :=
  [
    RM.setR 1%Z;
    (* TODO: decide where to store *)
    RM.store 0%Z;
    RM.load c;
    RM.neg;
    RM.add 0%Z;
    (* TODO: decide where to jump *)
    RM.jumpZero 0
  ].

Definition bandInstr (c c' : Condition) : list RM.Instruction :=
  [
    RM.setR 1%Z;
    (* TODO: decide where to store *)
    RM.store 0%Z;
    RM.load c;
    RM.neg;
    RM.add 0%Z;
    (* TODO: decide where to store *)
    RM.store 1%Z;
    RM.load c;
    RM.neg;
    RM.add 0%Z;
    RM.mul 1%Z;
    (* TODO: decide where to jump *)
    RM.jumpZero 0
  ].

Definition beqInstr (x y : Value) : list RM.Instruction :=
  [
    RM.load x;
    RM.neg;
    RM.add y;
    (* TODO: decide where to jump *)
    RM.jumpZero 0
  ].

Definition bltInstr (x y : Value) : list RM.Instruction :=
  [
    RM.load x;
    RM.neg;
    RM.add y;
    (* TODO: decide where to jump *)
    RM.jumpPos 0
  ].

Definition bgtInstr (x y : Value) : list RM.Instruction :=
  [
    RM.load x;
    RM.neg;
    RM.add y;
    RM.neg;
    (* TODO: decide where to jump *)
    RM.jumpPos 0
  ].

Definition bifInstr (c : Condition) (i j : Instruction) : list RM.Instruction :=
  [
    RM.load c;
    RM.jumpZero i;
    RM.setR 0%Z;
    RM.jumpZero j
  ].

(* if condition is not satisfied jumps out of the loop *)
Definition bloopInstr (c : Condition) (i : Instruction) : list RM.Instruction :=
  [
    RM.setR (-1)%Z;
    RM.add c;
    RM.jumpZero i
  ].
  
Definition toRMinstructions (o : ops) : list RM.Instruction :=
  match o with
  | assign ref v => assignInstr ref v
  | read ref     => readInstr ref
  | add x y      => addInstr x y
  | neg x        => negInstr x
  | sub x y      => subInstr x y
  | mult x y     => multInstr x y
  | div x y      => divInstr x y
  | bor c c'     => borInstr c c'
  | bnot c       => bnotInstr c
  | band c c'    => bandInstr c c'
  | beq x y      => beqInstr x y
  | blt x y      => bltInstr x y
  | bgt x y      => bgtInstr x y
  | bif c i j    => bifInstr c i j
  | bloop c i    => bloopInstr c i
  end.
