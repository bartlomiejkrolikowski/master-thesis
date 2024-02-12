(* a simple lambda calculus with mutable references *)

Require Import Nat.
Require List.
Import List.ListNotations.

Definition inc_set (A : Set) : Set :=
  option A.

(*
Inductive Label : Set :=
| OfNat : nat -> Label.
*)

Parameter Label : Set.

Inductive Value (V : Set) :=
| U_val : Value V
| Var : V -> Value V
| Lab : Label -> Value V (* label *)
| Lam : Expr (inc_set V) -> Value V
with Expr (V : Set) :=
| Val : Value V -> Expr V
| App : Expr V -> Expr V -> Expr V
| Ref : Expr V -> Expr V (* mutable reference *)
| Deref : Expr V -> Expr V
| Assign : Expr V -> Expr V -> Expr V
| Seq : Expr V -> Expr V -> Expr V
.

Inductive type :=
| Unit : type
| Arrow : type -> type -> type
| RefT : type -> type (* reference *)
.

Arguments U_val {V}.
Arguments Var {V}.
Arguments Lab {V}.
Arguments Lam {V}.
Arguments Ref {V}.
Arguments Val {V}.
Arguments App {V}.
Arguments Deref {V}.
Arguments Assign {V}.
Arguments Seq {V}.

Coercion Val : Value >-> Expr.

Fixpoint shift_v {V : Set} (v : Value V) : Value (inc_set V) :=
  match v with
  | U_val => U_val
  | Var x => Var (Some x)
  | Lab l => Lab l
  | Lam e => Lam (shift_e e)
  end
with shift_e {V : Set} (e : Expr V) : Expr (inc_set V) :=
  match e with
  | Val v => shift_v v
  | App e1 e2 => App (shift_e e1) (shift_e e2)
  | Ref e => Ref (shift_e e)
  | Deref e => Deref (shift_e e)
  | Assign e1 e2 => Assign (shift_e e1) (shift_e e2)
  | Seq e1 e2 => Seq (shift_e e1) (shift_e e2)
  end.

Definition subst_inc_set {V : Set}
  (x : inc_set V) (e' : Expr V) : Expr V :=
  match x with
  | None => e'
  | Some x => Var x
  end.

Fixpoint subst_v {V : Set}
  (v : Value (inc_set V)) (e' : Expr V) : Expr V :=
  match v with
  | U_val => U_val
  | Var x => subst_inc_set x e'
  | Lab l => Lab l
  | Lam e => Lam (subst_e e (shift_e e'))
  end
with subst_e {V : Set}
  (e : Expr (inc_set V)) (e' : Expr V) : Expr V :=
  match e with
  | Val v => subst_v v e'
  | App e1 e2 => App (subst_e e1 e') (subst_e e2 e')
  | Ref e => Ref (subst_e e e')
  | Deref e => Deref (subst_e e e')
  | Assign e1 e2 => Assign (subst_e e1 e') (subst_e e2 e')
  | Seq e1 e2 => Seq (subst_e e1 e') (subst_e e2 e')
  end.

Definition Map (V : Set) : Set := list (Label * (Value V)).

(*Definition extend {V L : Set} (m : Map V L) (v : Value V L)
  : Map V (inc_set L) :=
  fun (l : inc_set L) =>
    match l with
    | Some l => shift_v (m l)
    | None   => shift_v v
    end.

Definition assign {V L : Set} (m : Map V L) (l : L) (v : Value V L) : Map V L.
Admitted.

Definition max_label {V : Set} (m : Map V) : Label :=
  List.fold_right
    (fun '(OfNat n, _) '(OfNat m) => OfNat (max n m)) (OfNat 0) m.
*)

Definition labels {V : Set} (m : Map V) : list Label :=
  List.map fst m.

Definition Is_fresh_label {V : Set} (l : Label) (m : Map V) : Prop :=
  ~ List.In l (labels m).

Definition Is_Valid_Map {V : Set} (m : Map V) : Prop :=
  List.NoDup (labels m).

Inductive Lookup {V : Set} (l : Label) : Map V -> Value V -> Prop :=
| Lookup_hd (m : Map V) (v : Value V) : Lookup l ((l,v) :: m)%list v
| Lookup_tl (a : Label * Value V) (m : Map V) (v : Value V) :
    Lookup l m v -> Lookup l (a :: m)%list v
.

Inductive Assignment {V : Set} (l : Label) (v : Value V) :
  Map V -> Map V -> Prop :=
| Assignment_hd (v0 : Value V) (m m' : Map V) :
    Assignment l v ((l,v0) :: m)%list ((l,v) :: m')%list
| Assignment_tl (a : Label * Value V) (m m' : Map V) :
    Assignment l v m m' ->
    Assignment l v (a :: m)%list (a :: m')%list
.

(* SOS semantics *)
Inductive red {V : Set} :
  Expr V -> Map V ->
  Expr V -> Map V ->
  Prop :=

| red_lam : forall m e (v : Value _),
    red (App (Lam e) v) m (subst_e e v) m

| red_ref : forall m l (v : Value _),
    Is_fresh_label l m ->
    red (Ref v) m (Lab l) ((l,v) :: m)%list

| red_deref : forall m l v,
    Lookup l m v ->
    red (Deref (Lab l)) m v m

| red_assign : forall m m' l v,
    Assignment l v m m' ->
    red (Assign (Lab l) v) m U_val m'

| red_seq : forall m (v : Value _),
    red (Seq U_val v) m v m

(* structural rules *)
| red_app1 : forall m m' e1 e1' e2,
    red e1 m e1' m' ->
    red (App e1 e2) m (App e1' e2) m'

| red_app2 : forall m m' (v : Value _) e e',
    red e m e' m' ->
    red (App v e) m (App v e') m'

| red_ref_e : forall m m' e e',
    red e m e' m' ->
    red (Ref e) m (Ref e') m'

| red_deref_e : forall m m' e e',
    red e m e' m' ->
    red (Deref e) m (Deref e') m'

| red_assign1 : forall m m' e1 e1' e2,
    red e1 m e1' m' ->
    red (Assign e1 e2) m (Assign e1' e2) m'

| red_assign2 : forall m m' (v : Value _) e e',
    red e m e' m' ->
    red (Assign v e) m (Assign v e') m'

| red_seq1 : forall m m' e1 e1' e2,
    red e1 m e1' m' ->
    red (Seq e1 e2) m (Seq e1' e2) m'

| red_seq2 : forall m m' (v : Value _) e e',
    red e m e' m' ->
    red (Seq v e) m (Seq v e') m'
.

(* cost semantics *)
Inductive cost_red {V : Set}
  (e : Expr V)  (m : Map V) :
  Expr V -> Map V ->
  nat -> Prop :=

| no_red : cost_red e m e m 0

| S_red (c : nat) (e' e'' : Expr V) (m' m'' : Map V) :
    red e m e' m' ->
    cost_red e' m' e'' m'' c ->
    cost_red e m e'' m'' (S c)
.

(* type system *)
Definition env (V : Set) : Set := V -> type.
Definition env_empty : env Empty_set :=
  fun x => match x with end.

Definition ext_fun {A B : Set}
  (f : A -> B) (y : B) (x : inc_set A) : B :=
  match x with
  | None => y
  | Some x' => f x'
  end.

Reserved Notation "'T[' G '|-' e ':::' t ']'".

Inductive typing {V : Set} (G : env V) :
  Expr V -> type -> Prop :=

| T_Unit : T[ G |- U_val ::: Unit ]

| T_Var : forall x, T[ G |- Var x ::: (G x) ]

| T_Lam : forall e t1 t2,
    T[ ext_fun G t1 |- e ::: t2 ] ->
    T[ G |- Lam e ::: Arrow t1 t2 ]

| T_App : forall e1 e2 t2 t1,
    T[ G |- e1 ::: Arrow t2 t1 ] ->
    T[ G |- e2 ::: t2 ] ->
    T[ G |- App e1 e2 ::: t1 ]

| T_Ref : forall e t,
    T[ G |- e ::: t ] ->
    T[ G |- Ref e ::: RefT t ]

| T_Deref : forall e t,
    T[ G |- e ::: RefT t ] ->
    T[ G |- Deref e ::: t ]

| T_Assign : forall e1 e2 t,
    T[ G |- e1 ::: RefT t ] ->
    T[ G |- e2 ::: t ] ->
    T[ G |- Assign e1 e2 ::: Unit ]

| T_Seq : forall e1 e2 t,
    T[ G |- e1 ::: Unit ] ->
    T[ G |- e2 ::: t ] ->
    T[ G |- Seq e1 e2 ::: t ]

where "T[ G |- e ::: t ]" := (@typing _ G e t).

(* NOTATIONS *)

Notation "'$' x" := (Some x) (at level 50).

Notation "'-\' e" := (Lam e) (at level 100).

Notation "e1 '<*' e2" :=
  (App e1 e2)
  (at level 50, left associativity).

Notation "'!' e" := (Deref e) (at level 50).

Notation "e1 '<-' e2" :=
  (Assign e1 e2)
  (at level 70, no associativity).

Notation "e1 ';;' e2" :=
  (Seq e1 e2)
  (at level 90, right associativity).
