Require List.
Import List.ListNotations.
Require Import String.
Require Import ZArith.

Require Import src.LambdaRef.

Definition StateAssertion (V : Set) :=
  Map V -> Prop.

Definition subst_map {V : Set} (m : Map (inc_set V)) (v : Value V) : Map V :=
  List.map (fun '(l,v') => (l, subst_v v' v)) m.

Definition subst_sa {V : Set} (A : StateAssertion V) (v : Value V) :
  StateAssertion (inc_set V) :=
  fun m => A (subst_map m v).

Definition sa_empty {V : Set} : StateAssertion V :=
  fun m => m = []%list.

Definition sa_pure {V : Set} (P : Prop) : StateAssertion V :=
  fun m => P /\ sa_empty m.

Definition sa_single {V : Set} (l : Label) (v : Value V) : StateAssertion V :=
  fun m => m = [(l,v)]%list.

Definition disjoint_maps {V : Set} (m1 m2 : Map V) : Prop :=
  forall p, List.In p m1 -> List.In p m2 -> False.

Definition sa_star {V : Set} (A1 A2 : StateAssertion V) : StateAssertion V :=
  fun m => exists m1 m2,
    A1 m1 /\
    A2 m2 /\
    disjoint_maps m1 m2 /\
    m = (m1 ++ m2)%list.

Definition sa_exists {V T : Set} (F : T -> StateAssertion V) : StateAssertion V :=
  fun m => exists x : T, F x m.

Definition sa_implies {V : Set} (A1 A2 : StateAssertion V) : Prop :=
  forall m, A1 m -> A2 m.

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
