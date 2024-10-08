Require List.
Import List.ListNotations.
Require Vector.
Require Import String.
Require Import ZArith.

Require Import src.LambdaRef.
Require Export src.LambdaAssertions_credits_perm.

(* hoare triple for one step of reduction *)
Definition step_hoare_triple {V : Set}
  (e : Expr V) (P Q : StateAssertion V) : Prop :=
  forall (c : nat) ((*m*) m' : Map V),
    Is_Valid_Map m' ->
    P (1+c) m' ->
    exists (e' : Expr V) (m'' : Map V),
      R[e, m' ~~> e', m''] /\
      Is_Valid_Map m'' /\
      Q c m''.

Definition hoare_triple {V : Set}
  (e : Expr V)
  (P : StateAssertion V) (Q : Value V -> StateAssertion V) : Prop :=
  forall (c1 : nat) ((*mp*) m : Map V),
    Is_Valid_Map m ->
    P c1 m ->
    exists (v : Value V) (c c2 : nat) (m' (*mq*) : Map V),
      C[e, m ~~> v, m' | c] /\
      Q v c2 m' /\
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

Fixpoint n_ary_app {V : Set} (e : Expr V) (es : list (Expr V)) : Expr V :=
  match es with
  | [] => e
  | (e'::es') => n_ary_app (e <* e') es'
  end%list.

Fixpoint n_ary_fun_type (n : nat) (A B : Type) : Type :=
  match n with
  | 0 => B
  | S n' => A -> n_ary_fun_type n' A B
  end.

Fixpoint n_ary_fun_app {A B : Type} (xs : list A) :
  n_ary_fun_type (List.length xs) A B -> B :=
  match xs with
  | [] => fun f => f
  | (x::xs') => fun f => n_ary_fun_app xs' (f x)
  end%list.

Fixpoint n_ary_forall n [A : Type] : n_ary_fun_type n A Type -> Type :=
  match n with
  | 0 => fun B => B
  | S n' => fun B => forall x : A, n_ary_forall n' (B x)
  end.

Fixpoint to_n_ary_fun {A B} (n : nat) :
  (Vector.t A n -> B) -> n_ary_fun_type n A B :=
  match n return (Vector.t A n -> B) -> n_ary_fun_type n A B with
  | 0 => fun f => f (Vector.nil _)
  | S n' => fun f x => to_n_ary_fun n' (fun xs => f (Vector.cons _ x _ xs))
  end.

Fixpoint to_n_ary_fun' {A B} (n : nat) (f : (list A -> B)) :
  n_ary_fun_type n A B :=
  match n return n_ary_fun_type n A B with
  | 0 => f nil
  | S n' => fun x => to_n_ary_fun' n' (fun xs => f (cons x xs))
  end.

(* a triple for n+1-argument function *)
Fixpoint triple_fun_n_ary n {V : Set}
  (v : Value V) :
  (Value V -> n_ary_fun_type n (Value V) (StateAssertion V)) ->
  (Value V -> Value V -> n_ary_fun_type n (Value V) (StateAssertion V)) ->
    Prop :=
  match n with
  | 0 => fun P Q => forall x, triple_fun v (fun v => $1 <*> <[v = x]> <*> P x) (Q x)
  | S n' => fun P Q => forall x,
    triple_fun v
    (fun v => $1 <*> <[v = x]>)
    (fun v => <[
      triple_fun_n_ary n' v (P x) (Q x)
    ]>)
  end.

Fixpoint triple_list {V : Set}
  (es : list (Expr V))
  (P : StateAssertion V) :
  n_ary_fun_type (List.length es) (Value V) (StateAssertion V) ->
    Prop :=
  match es return n_ary_fun_type (List.length es) (Value V) (StateAssertion V) -> Prop with
  | [] => fun Q => P ->> Q
  | (e::es') => fun Q =>
    exists Q', triple e P Q' /\
      forall v, triple_list es' (Q' v) (Q v)
  end%list.
