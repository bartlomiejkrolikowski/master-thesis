Require List.
Import List.ListNotations.
Require Import String.
Require Import ZArith.

Require Import src_arrays.LambdaRef.
Require Import src_arrays.Interweave.

Definition StateAssertion (V : Set) :=
  nat -> Map V -> Prop.

Definition subst_map {V : Set} (m : Map (inc_set V)) (v : Value V) : Map V :=
  List.map (fun '(l,ov) => (l, option_map (fun v' => subst_v v' v) ov)) m.

Definition subst_sa {V : Set} (A : StateAssertion V) (v : Value V) :
  StateAssertion (inc_set V) :=
  fun c m => A c (subst_map m v).

Definition sa_empty {V : Set} : StateAssertion V :=
  fun c m => c = 0 /\ m = []%list.

Definition sa_pure {V : Set} (P : Prop) : StateAssertion V :=
  fun c m => P /\ sa_empty c m.

Definition sa_single_any {V : Set} (l : Label) (ov : option (Value V)) :
  StateAssertion V :=
  fun c m => c = 0 /\ m = [(l,ov)]%list.

Definition sa_single {V : Set} (l : Label) (v : Value V) : StateAssertion V :=
  fun c m => c = 0 /\ m = [(l,Some v)]%list.

Definition sa_single_decl {V : Set} (l : Label) : StateAssertion V :=
  fun c m => c = 0 /\ m = [(l,None)]%list.

Definition sa_array_decl {V : Set} (l : Label) (n : nat) : StateAssertion V :=
  fun c m => c = 0 /\ m = n_new_cells_from l n.

Definition sa_credits {V : Set} (k : nat) : StateAssertion V :=
  fun c m => c = k /\ m = []%list.

Definition disjoint_maps {V : Set} (m1 m2 : Map V) : Prop :=
  forall p, List.In p (labels m1) -> List.In p (labels m2) -> False.

Definition sa_star {V : Set} (A1 A2 : StateAssertion V) : StateAssertion V :=
  fun c m => exists c1 m1 c2 m2,
    A1 c1 m1 /\
    A2 c2 m2 /\
    c = c1 + c2 /\
    disjoint_maps m1 m2 /\
    Interweave m1 m2 m.

Definition sa_and {V : Set} (A1 A2 : StateAssertion V) : StateAssertion V :=
  fun c m => A1 c m /\ A2 c m.

Definition sa_exists {T} {V : Set} (F : T -> StateAssertion V) : StateAssertion V :=
  fun c m => exists x : T, F x c m.

Definition sa_forall {T} {V : Set} (F : T -> StateAssertion V) : StateAssertion V :=
  fun c m => forall x : T, F x c m.

Definition sa_implies {V : Set} (A1 A2 : StateAssertion V) : Prop :=
  forall c m, A1 c m -> A2 c m.

Notation "<[]>" := (sa_empty).
Notation "<[ P ]>" := (sa_pure P).
Notation "<( l :?= v )>" := (sa_single_any l v).
Notation "<( l :== v )>" := (sa_single l v).
Notation "<( l :\= )>" := (sa_single_decl l).
Notation "<( l :\ n \= )>" := (sa_array_decl l n).
Notation "P <*> Q" := (sa_star P Q) (at level 40).
Notation "P <*>+ Q" := (fun v => sa_star (P v) Q) (at level 40).
Notation "P </\> Q" := (sa_and P Q) (at level 20).
Notation "'<exists>' x .. y , p" :=
  (sa_exists (fun x => .. (sa_exists (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' '<exists>' '/ ' x .. y , '/ ' p ']'")
  : type_scope.
Notation "'<forall>' x .. y , p" :=
  (sa_forall (fun x => .. (sa_forall (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' '<forall>' '/ ' x .. y , '/ ' p ']'")
  : type_scope.
Notation "P ->> Q" := (sa_implies P Q) (at level 50).
Notation "P -->> Q" := (forall v, sa_implies (P v) (Q v)) (at level 50).

Notation "P <<->> Q" := (P ->> Q /\ Q ->> P) (at level 50).
Notation "P <<-->> Q" := (P -->> Q /\ Q -->> P) (at level 50).

Global Hint Unfold subst_map : st_assertions.
Global Hint Unfold subst_sa : st_assertions.
Global Hint Unfold sa_empty : st_assertions.
Global Hint Unfold sa_pure : st_assertions.
Global Hint Unfold sa_single_any : st_assertions.
Global Hint Unfold sa_single : st_assertions.
Global Hint Unfold sa_single_decl : st_assertions.
Global Hint Unfold sa_array_decl : st_assertions.
Global Hint Unfold sa_credits : st_assertions.
Global Hint Unfold disjoint_maps : st_assertions.
Global Hint Unfold sa_star : st_assertions.
Global Hint Unfold sa_and : st_assertions.
Global Hint Unfold sa_exists : st_assertions.
Global Hint Unfold sa_forall : st_assertions.
Global Hint Unfold sa_implies : st_assertions.
