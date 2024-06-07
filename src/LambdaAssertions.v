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
  forall p, List.In p (labels m1) -> List.In p (labels m2) -> False.

Definition sa_star {V : Set} (A1 A2 : StateAssertion V) : StateAssertion V :=
  fun m => exists m1 m2,
    A1 m1 /\
    A2 m2 /\
    disjoint_maps m1 m2 /\
    m = (m1 ++ m2)%list.

Definition sa_exists {T} {V : Set} (F : T -> StateAssertion V) : StateAssertion V :=
  fun m => exists x : T, F x m.

Definition sa_implies {V : Set} (A1 A2 : StateAssertion V) : Prop :=
  forall m, A1 m -> A2 m.

Notation "<[]>" := (sa_empty).
Notation "<[ P ]>" := (sa_pure P).
Notation "<( l :== v )>" := (sa_single l v).
Notation "P <*> Q" := (sa_star P Q) (at level 40).
Notation "P <*>+ Q" := (fun v c => sa_star (P v c) Q) (at level 40).
Notation "'<exists>' x .. y , p" :=
  (sa_exists (fun x => .. (sa_exists (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' '<exists>' '/ ' x .. y , '/ ' p ']'")
  : type_scope.
Notation "P ->> Q" := (sa_implies P Q) (at level 50).
Notation "P -->> Q" := (forall v c, sa_implies (P v c) (Q v c)) (at level 50).

Notation "P <<->> Q" := (P ->> Q /\ Q ->> P) (at level 50).
Notation "P <<-->> Q" := (P -->> Q /\ Q -->> P) (at level 50).

Global Hint Unfold subst_map : st_assertions.
Global Hint Unfold subst_sa : st_assertions.
Global Hint Unfold sa_empty : st_assertions.
Global Hint Unfold sa_pure : st_assertions.
Global Hint Unfold sa_single : st_assertions.
Global Hint Unfold disjoint_maps : st_assertions.
Global Hint Unfold sa_star : st_assertions.
Global Hint Unfold sa_exists : st_assertions.
Global Hint Unfold sa_implies : st_assertions.
