Require List.
Import List.ListNotations.

Require Import src.LambdaRef.

(* a type with unification variables *)
Inductive uni_type (V : Set) : Set :=
| uVar : V -> uni_type V
| uUnit : uni_type V
| uArrow : uni_type V -> uni_type V -> uni_type V
| uRefT : uni_type V -> uni_type V
.

(* TODO: maybe unnecessary *)
