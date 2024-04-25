Require List.
Import List.ListNotations.
Require Import String.
Require Import ZArith.

Require Import src.LambdaRef.

Definition StateAssertion (V : Set) :=
  Map V -> Prop.

(* hoare triple for one step of reduction *)
Definition step_hoare_triple {V : Set}
  (P Q : StateAssertion V) (e : Expr V) : Prop :=
  forall (e' : Expr V) (m m' : Map V),
    R[e, m ~~> e', m'] ->
    P m -> Q m.

Definition hoare_triple {V : Set}
  (P : StateAssertion V) (Q : Value V -> nat -> StateAssertion V)
  (e : Expr V) : Prop :=
  forall (v : Value V) (m m' : Map V) (c : nat),
    C[e, m ~~> v, m' | c] ->
    P m -> Q v c m'.
(* TODO *)
