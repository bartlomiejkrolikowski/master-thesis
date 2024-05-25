Require List.
Import List.ListNotations.
Require Import String.
Require Import ZArith.

Require Import src.LambdaRef.
Require Export src.LambdaAssertions.

(* hoare triple for one step of reduction *)
Definition step_hoare_triple {V : Set}
  (e : Expr V) (P Q : StateAssertion V) : Prop :=
  forall (e' : Expr V) (m m' : Map V),
    R[e, m ~~> e', m'] ->
    P m -> Q m.

Definition hoare_triple {V : Set}
  (e : Expr V)
  (P : StateAssertion V) (Q : Value V -> nat -> StateAssertion V) : Prop :=
  forall (v : Value V) (c : nat) (m m' : Map V),
    C[e, m ~~> v, m' | c] ->
    P m -> Q v c m'.
