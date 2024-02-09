(* a set of primitive, constant-time operations *)

Require Import List.
Import ListNotations.
Require Import String.
Require Import ZArith.

Inductive Value : Set :=
| Const : Z -> Value.
(*| Var   : string -> Value*)

Inductive RefValue : Set :=
| RVar : string -> RefValue.

Inductive BValue : Set :=
| BConst : bool -> BValue.

Inductive Expr : Set :=
| Val   : Value -> Expr
| EAdd  : Expr -> Expr -> Expr
| ESub  : Expr -> Expr -> Expr
| EMult : Expr -> Expr -> Expr
| EDiv  : Expr -> Expr -> Expr
| ENeg  : Expr -> Expr
| ERead : RefExpr -> Expr
with RefExpr : Set :=
| RVal   : RefValue -> RefExpr
| RRead  : RefExpr -> RefExpr
(* pointer arithmetic *)
| RShift : RefExpr -> Expr -> RefExpr.

Inductive BExpr : Set :=
| BVal : BValue -> BExpr
| BOr  : BExpr -> BExpr -> BExpr
| BAnd : BExpr -> BExpr -> BExpr
| BNot : BExpr -> BExpr
(* value comparison *)
| BEq  : Expr -> Expr -> BExpr
| BLt  : Expr -> Expr -> BExpr
| BGt  : Expr -> Expr -> BExpr.

Inductive Instr : Set :=
| Assign  : RefExpr -> Expr -> Instr
| RAssign : RefExpr -> RefExpr -> Instr
| If      : BExpr -> list Instr -> list Instr -> Instr
| While   : BExpr -> list Instr -> Instr.

Definition Program : Set := list Instr.

Require RAMmachine.
Module RM := RAMmachine.

Definition Address : Set := Z.

(* mapping of used variable names to their locaitons *)
Definition varMap : Set := string -> option Address.

Definition compileValue (v : Value) :
  option (Address * list RM.Instruction).
Admitted.

(* returns also a pointer to the cell with a computed value *)
Fixpoint compileExpr (m : varMap) (e : Expr) :
  option (Address * list RM.Instruction).
Admitted.

Definition compileAssign (m : varMap) : Empty_set. Admitted.

Definition compile (p : Program) : list RM.Instruction.
Admitted.
