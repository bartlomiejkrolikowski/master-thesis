Require List.
Import List.ListNotations.
Require Import String.
Require Import ZArith.

Require Import src.LambdaRef.
Require Export src.LambdaAssertions_credits_perm.
Require Import src.Permutation.

(* hoare triple for one step of reduction *)
Definition step_hoare_triple {V : Set}
  (e : Expr V) (P Q : StateAssertion V) : Prop :=
  forall (c : nat) ((*m*) m' : Map V),
    P (1+c) m' ->
    (*Permutation m m' ->*)
    exists (e' : Expr V) (m'' (*m'''*) : Map V),
      R[e, m' ~~> e', m''] /\
      (*Permutation m'' m''' /\*)
      Q c m''.

Definition hoare_triple {V : Set}
  (e : Expr V)
  (P : StateAssertion V) (Q : Value V -> StateAssertion V) : Prop :=
  forall (c1 : nat) ((*mp*) m : Map V),
    P c1 m ->
    (*Permutation mp m ->*)
    exists (v : Value V) (c c2 : nat) (m' (*mq*) : Map V),
      C[e, m ~~> v, m' | c] /\
      Q v c2 m' /\
      (*Permutation m' mq /\*)
      c1 = c + c2.

Definition triple {V : Set}
  (e : Expr V)
  (P : StateAssertion V) (Q : Value V -> StateAssertion V) : Prop :=
  forall H, hoare_triple e (P <*> H) (Q <*>+ H).
