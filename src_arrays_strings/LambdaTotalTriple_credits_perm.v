Require List.
Import List.ListNotations.
Require Import String.
Require Import ZArith.

Require Import src_arrays.LambdaRef.
Require Export src_arrays.LambdaAssertions_credits_perm.

(* hoare triple for one step of reduction *)
Definition step_hoare_triple {V : Set}
  (e : Expr V) (P Q : StateAssertion V) : Prop :=
  forall (c : nat) ((*m*) m' : Map V),
    Is_Valid_Map m' ->
    P (1+c) m' ->
    (*Permutation m m' ->*)
    exists (e' : Expr V) (m'' (*m'''*) : Map V),
      R[e, m' ~~> e', m''] /\
      (*Permutation m'' m''' /\*)
      Is_Valid_Map m'' /\
      Q c m''.

Definition hoare_triple {V : Set}
  (e : Expr V)
  (P : StateAssertion V) (Q : Value V -> StateAssertion V) : Prop :=
  forall (c1 : nat) ((*mp*) m : Map V),
    Is_Valid_Map m ->
    P c1 m ->
    (*Permutation mp m ->*)
    exists (v : Value V) (c c2 : nat) (m' (*mq*) : Map V),
      C[e, m ~~> v, m' | c] /\
      Q v c2 m' /\
      (*Permutation m' mq /\*)
      Is_Valid_Map m' /\
      c1 = c + c2.

Definition triple {V : Set}
  (e : Expr V)
  (P : StateAssertion V) (Q : Value V -> StateAssertion V) : Prop :=
  forall H, hoare_triple e (P <*> H) (Q <*>+ H).

Definition triple_fun {V : Set}
  (v : Value V)
  (P Q : Value V -> StateAssertion V) : Prop :=
  forall v' : Value V, triple (v <* v') (P v') Q.
