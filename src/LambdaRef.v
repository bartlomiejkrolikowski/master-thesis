(* a simple lambda calculus with mutable references *)

Require Import Nat.
Require List.
Import List.ListNotations.
Require Import String.

Definition inc_set (A : Set) : Set :=
  option A.

Definition inc_fun {A B : Set}
  (f : A -> B) (y : B) (x : inc_set A) : B :=
  match x with
  | None => y
  | Some x' => f x'
  end.

Inductive Label : Set :=
| OfNat : nat -> Label.

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

Fixpoint map_v {A B : Set} (f : A -> B) (v : Value A) : Value B :=
  match v with
  | U_val => U_val
  | Var x => Var (f x)
  | Lab l => Lab l
  | Lam e => Lam (map_e (option_map f) e)
  end
with map_e {A B : Set} (f : A -> B) (e : Expr A) : Expr B :=
  match e with
  | Val v => map_v f v
  | App e1 e2 => App (map_e f e1) (map_e f e2)
  | Ref e => Ref (map_e f e)
  | Deref e => Deref (map_e f e)
  | Assign e1 e2 => Assign (map_e f e1) (map_e f e2)
  | Seq e1 e2 => Seq (map_e f e1) (map_e f e2)
  end.

Definition shift_v {V : Set} : Value V -> Value (inc_set V) :=
  map_v Some.

Definition shift_e {V : Set} : Expr V -> Expr (inc_set V) :=
  map_e Some.

Definition subst_inc_set {V : Set}
  (x : inc_set V) (e' : Expr V) : Expr V :=
  inc_fun (fun y => Val (Var y)) e' x.

(* lifting of substitution *)
Definition liftS {A B : Set} (f : A -> Value B) (x : inc_set A) :
  Value (inc_set B) :=
  match x with
  | None => Var None
  | Some x' => shift_v (f x')
  end.

(* bind, but only for functions mapping to values *)
Fixpoint bind_v {A B : Set}
  (f : A -> Value B) (v : Value A) : Value B :=
  match v with
  | U_val => U_val
  | Var x => f x
  | Lab l => Lab l
  | Lam e => Lam (bind_e (liftS f) e)
  end
with bind_e {A B : Set}
  (f : A -> Value B) (e : Expr A) : Expr B :=
  match e with
  | Val v => bind_v f v
  | App e1 e2 => App (bind_e f e1) (bind_e f e2)
  | Ref e => Ref (bind_e f e)
  | Deref e => Deref (bind_e f e)
  | Assign e1 e2 => Assign (bind_e f e1) (bind_e f e2)
  | Seq e1 e2 => Seq (bind_e f e1) (bind_e f e2)
  end.

Definition subst_v {V : Set}
  (v : Value (inc_set V)) (v' : Value V) : Value V :=
  bind_v (inc_fun Var v') v.

Definition subst_e {V : Set}
  (e : Expr (inc_set V)) (v' : Value V) : Expr V :=
  bind_e (inc_fun Var v') e.

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

Reserved Notation "'T[' G '|-' e ':::' t ']'".

Inductive typing {V : Set} (G : env V) :
  Expr V -> type -> Prop :=

| T_Unit : T[ G |- U_val ::: Unit ]

| T_Var : forall x, T[ G |- Var x ::: (G x) ]

| T_Lam : forall e t1 t2,
    T[ inc_fun G t1 |- e ::: t2 ] ->
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

Notation "t1 --> t2" :=
  (Arrow t1 t2)
  (at level 60, right associativity).

Notation "[let] e1 [in] e2" :=
  ((-\ e2) <* e1)
  (at level 50, no associativity).


Definition StringLam (x : string) (e : Expr string) :
  Value string :=
  Lam (map_e (fun y => if x =? y then None else $ y)%string e).

(*
Class EqBool (A : Set) : Set := {
  eqB : A -> A -> bool;
}.

Global Instance StringEqB : EqBool string := {|
  eqB := eqb;
|}.

Global Instance OptionEqB (A : Set) `{EqBool A} :
  EqBool (option A) := {|
  eqB x y := match x, y with
  | None, None => true
  | Some x', Some y' => eqB x' y'
  | _, _ => false
  end;
|}.

Definition StringLam' {A : Set} `{EqBool A} (x : A) (e : Expr A) :
  Value A :=
  Lam (map_e (fun y => if eqB x y then None else $ y) e).
*)

Notation "'[-\]' x ',' e" :=
  (StringLam x e)
  (at level 100, no associativity).

Notation "'[let' x ']' e1 '[in]' e2" :=
  (([-\] x, e2) <* e1)
  (at level 50, no associativity).


(* ------------------------LEMMAS-------------------------------------*)

(*(* reordering in context *)
Lemma reordering (V : Set) (G : env V) (e : Expr _) (t t' t'' : type) :
  T[ inc_fun (inc_fun G t'') t' |- shift_e e ::: t] ->
  T[ inc_fun (inc_fun G t') t'' |- map_e (option_map Some) e ::: t].
Proof.
  (*remember (inc_fun (inc_fun G t') t'') as G'.*)
  remember (inc_fun (inc_fun G t'') t') as G''.
  (*remember (map_e (option_map Some) e) as e'.*)
  remember (shift_e e) as e''.
  intro H. induction H.
  - econstructor.
Qed.
*)
(* weakening lemma *)
Lemma weakening (V : Set) (G : env V) (e : Expr V) (t t' : type) :
  T[ G |- e ::: t ] ->
  T[ inc_fun G t' |- shift_e e ::: t].
Proof.
  intro H. induction H; cbn; econstructor; try eassumption.
Abort.

(*
(* uniqueness of reduction results *)
Lemma uniqueness (V : Set)
  (e e' e'' : Expr V) (m m' m'' : Map V) :
  red e m e' m' ->
  red e m e'' m'' ->
  e' = e'' /\ m' = m''.
Proof.
  intro H'. revert e'' m''. induction H'; intros e'' m'' H''.
  - inversion H''; [ easy | | ];
    match goal with
    | [ H : red (Val _) _ _ _ |- _ ] => inversion H
    end.
  - inversion H''.
    (* TODO *)
Admitted.

Lemma uniqueness_full (V : Set)
  (e e' e'' : Expr V) (m m' m'' : Map V) (c' c'' : nat) :
  cost_red e m e' m' c' ->
  cost_red e m e'' m'' c'' ->
  e' = e'' /\ m' = m'' /\ c' = c''.
Proof.
  intros H' H''.
Admitted.
*)

