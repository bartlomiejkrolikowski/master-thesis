Require List.
Import List.ListNotations.
Require Import String.
Require Import ZArith.

Require Import src.LambdaRef.
Require Export src.LambdaAssertions_credits.

(* hoare triple for one step of reduction *)
Definition step_hoare_triple {V : Set}
  (e : Expr V) (P Q : StateAssertion V) : Prop :=
  forall (c : nat) (m : Map V),
    P (1+c) m ->
    exists (e' : Expr V) (m' : Map V),
      R[e, m ~~> e', m'] /\
      Q c m.

Definition hoare_triple {V : Set}
  (e : Expr V)
  (P : StateAssertion V) (Q : Value V -> StateAssertion V) : Prop :=
  forall (c1 : nat) (m : Map V),
    P c1 m ->
    exists (v : Value V) (c c2 : nat) (m' : Map V),
      C[e, m ~~> v, m' | c] /\
      Q v c2 m' /\
      c1 = c + c2.

Definition triple {V : Set}
  (e : Expr V)
  (P : StateAssertion V) (Q : Value V -> StateAssertion V) : Prop :=
  forall H, hoare_triple e (P <*> H) (Q <*>+ H).
