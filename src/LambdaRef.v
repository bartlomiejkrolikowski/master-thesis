(* a simple lambda calculus with mutable references,
  inspired by formalizations from https://github.com/ppolesiuk/type-systems-notes
  (especially, safe de Brujn indices with map and bind) *)

Require Import Nat.
Require List.
Import List.ListNotations.
Require Import String.
Require Import ZArith.

Definition inc_set : Set -> Set := option.

Definition inc_fun {A B : Set}
  (f : A -> B) (y : B) (x : inc_set A) : B :=
  match x with
  | None => y
  | Some x' => f x'
  end.

Inductive Label : Set :=
| OfNat : nat -> Label.

Definition of_label '(OfNat n) := n.
Definition lift {A} (f : nat -> A) (l : Label) : A := f (of_label l).
Definition lift2 {A} (f : nat -> nat -> A) (l l' : Label) : A :=
  lift (lift f l) l'.

Definition label_eqb : Label -> Label -> bool := lift2 Nat.eqb.
Definition label_ltb : Label -> Label -> bool  := lift2 Nat.ltb.

Definition label_lt : Label -> Label -> Prop  := lift2 Nat.lt.

Declare Scope label_scope.

Notation "l =? l'" := (label_eqb l l') : label_scope.
Notation "l <? l'" := (label_ltb l l') : label_scope.

Notation "l < l'" := (label_lt l l') : label_scope.

Global Hint Unfold of_label : label.
Global Hint Unfold lift2 : label.
Global Hint Unfold lift  : label.
Global Hint Unfold label_eqb : label.
Global Hint Unfold label_ltb : label.
Global Hint Unfold label_lt  : label.

Inductive BoolUnOpKind : Set :=
| BNeg (* Boolean negation *)
.

Inductive IntUnOpKind : Set :=
| INeg (* Integer negation *)
.

Inductive UnOpKind : Set :=
| BUOp : BoolUnOpKind -> UnOpKind
| IUOp : IntUnOpKind -> UnOpKind
.

Inductive BoolBinOpKind : Set :=
| BOr
| BAnd
.

Inductive IntBinOpKind : Set :=
| IAdd
| ISub
| IMul
| IDiv
.

(* Conditions *)
Inductive CondBinOpKind : Set :=
| CLt (* x < y *)
| CEq (* x = y *)
.

Inductive BinOpKind : Set :=
| BBOp : BoolBinOpKind -> BinOpKind
| IBOp : IntBinOpKind -> BinOpKind
| CBOp : CondBinOpKind -> BinOpKind
.

Inductive Value (V : Set) :=
| U_val : Value V
| Var : V -> Value V
| Int : Z -> Value V (* integer *)
| Bool : bool -> Value V
| Lab : Label -> Value V (* label *)
| RecV : list (Value V) -> Value V (* record value *)
| Lam : Expr (inc_set V) -> Value V
with Expr (V : Set) :=
| Val : Value V -> Expr V
| App : Expr V -> Expr V -> Expr V
| UnOp : UnOpKind -> Expr V -> Expr V
| BinOp : BinOpKind -> Expr V -> Expr V -> Expr V
| RecE : list (Expr V) -> Expr V (* record expression *)
| Get : nat -> Expr V -> Expr V (* get nth field of a record *)
| Ref : Expr V -> Expr V (* mutable reference *)
| NewArray : Expr V -> Expr V (* an array consisting of contiguous memory cells *)
| Deref : Expr V -> Expr V (* read a single value from the memory *)
| Shift : Expr V -> Expr V -> Expr V (* shift a label by a nonnegative integer *)
| Assign : Expr V -> Expr V -> Expr V
| Free : Expr V -> Expr V (* free the given memory cell *)
| Seq : Expr V -> Expr V -> Expr V
| If : Expr V -> Expr V -> Expr V -> Expr V
| While : Expr V -> Expr V -> Expr V
.

Arguments U_val {V}.
Arguments Var {V}.
Arguments Int {V}.
Arguments Bool {V}.
Arguments Lab {V}.
Arguments RecV {V}.
Arguments Lam {V}.
Arguments Val {V}.
Arguments App {V}.
Arguments UnOp {V}.
Arguments BinOp {V}.
Arguments RecE {V}.
Arguments Get {V}.
Arguments NewArray {V}.
Arguments Ref {V}.
Arguments Deref {V}.
Arguments Shift {V}.
Arguments Assign {V}.
Arguments Free {V}.
Arguments Seq {V}.
Arguments If {V}.
Arguments While {V}.

Coercion Val : Value >-> Expr.

Global Hint Constructors Value : lamref.
Global Hint Constructors Expr : lamref.

Definition vals2exprs {V : Set} : list (Value V) -> list (Expr V) :=
  List.map Val.

Fixpoint map_v {A B : Set} (f : A -> B) (v : Value A) : Value B :=
  match v with
  | U_val => U_val
  | Var x => Var (f x)
  | Int i => Int i
  | Bool i => Bool i
  | Lab l => Lab l
  | RecV vs => RecV (List.map (map_v f) vs)
  | Lam e => Lam (map_e (option_map f) e)
  end
with map_e {A B : Set} (f : A -> B) (e : Expr A) : Expr B :=
  match e with
  | Val v => map_v f v
  | App e1 e2 => App (map_e f e1) (map_e f e2)
  | UnOp k e => UnOp k (map_e f e)
  | BinOp k e1 e2 => BinOp k (map_e f e1) (map_e f e2)
  | RecE es => RecE (List.map (map_e f) es)
  | Get n e => Get n (map_e f e)
  | Ref e => Ref (map_e f e)
  | NewArray e => NewArray (map_e f e)
  | Deref e => Deref (map_e f e)
  | Shift e1 e2 => Shift (map_e f e1) (map_e f e2)
  | Assign e1 e2 => Assign (map_e f e1) (map_e f e2)
  | Free e => Free (map_e f e)
  | Seq e1 e2 => Seq (map_e f e1) (map_e f e2)
  | If e1 e2 e3 => If (map_e f e1) (map_e f e2) (map_e f e3)
  | While e1 e2 => While (map_e f e1) (map_e f e2)
  end.

(* is value with limited range of variables *)
Definition is_limited_value (A : Set) [B : Set] (f : A -> B) (v : Value B) :
  Prop :=
  exists (v' : Value A), v = map_v f v'.

(* is expression with limited range of variables *)
Definition is_limited_expr (A : Set) [B : Set] (f : A -> B) (e : Expr B) :
  Prop :=
  exists (e' : Expr A), e = map_e f e'.

Definition is_closed_value {A} : Value A -> Prop :=
  is_limited_value Empty_set (fun x => match x with end).
Global Hint Unfold is_closed_value : is_closed_db.

Definition is_closed_expr {A} : Expr A -> Prop :=
  is_limited_expr Empty_set (fun x => match x with end).
Global Hint Unfold is_closed_expr : is_closed_db.

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
  | Int i => Int i
  | Bool i => Bool i
  | Lab l => Lab l
  | RecV vs => RecV (List.map (bind_v f) vs)
  | Lam e => Lam (bind_e (liftS f) e)
  end
with bind_e {A B : Set}
  (f : A -> Value B) (e : Expr A) : Expr B :=
  match e with
  | Val v => bind_v f v
  | App e1 e2 => App (bind_e f e1) (bind_e f e2)
  | UnOp k e => UnOp k (bind_e f e)
  | BinOp k e1 e2 => BinOp k (bind_e f e1) (bind_e f e2)
  | RecE es => RecE (List.map (bind_e f) es)
  | Get n e => Get n (bind_e f e)
  | Ref e => Ref (bind_e f e)
  | NewArray e => NewArray (bind_e f e)
  | Deref e => Deref (bind_e f e)
  | Shift e1 e2 => Shift (bind_e f e1) (bind_e f e2)
  | Assign e1 e2 => Assign (bind_e f e1) (bind_e f e2)
  | Free e => Free (bind_e f e)
  | Seq e1 e2 => Seq (bind_e f e1) (bind_e f e2)
  | If e1 e2 e3 => If (bind_e f e1) (bind_e f e2) (bind_e f e3)
  | While e1 e2 => While (bind_e f e1) (bind_e f e2)
  end.

Definition subst_v {V : Set}
  (v : Value (inc_set V)) (v' : Value V) : Value V :=
  bind_v (inc_fun Var v') v.

Definition subst_e {V : Set}
  (e : Expr (inc_set V)) (v' : Value V) : Expr V :=
  bind_e (inc_fun Var v') e.

(* transformation on labels *)
Fixpoint map_labels_v {V : Set} (f : Label -> Label) (v : Value V) : Value V :=
  match v with
  | U_val => U_val
  | Var x => Var x
  | Int i => Int i
  | Bool i => Bool i
  | Lab l => Lab (f l)
  | RecV vs => RecV (List.map (map_labels_v f) vs)
  | Lam e => Lam (map_labels_e f e)
  end
with map_labels_e {V : Set} (f : Label -> Label) (e : Expr V) : Expr V :=
  match e with
  | Val v => map_labels_v f v
  | App e1 e2 => App (map_labels_e f e1) (map_labels_e f e2)
  | UnOp k e => UnOp k (map_labels_e f e)
  | BinOp k e1 e2 => BinOp k (map_labels_e f e1) (map_labels_e f e2)
  | RecE es => RecE (List.map (map_labels_e f) es)
  | Get n e => Get n (map_labels_e f e)
  | Ref e => Ref (map_labels_e f e)
  | NewArray e => NewArray (map_labels_e f e)
  | Deref e => Deref (map_labels_e f e)
  | Shift e1 e2 => Shift (map_labels_e f e1) (map_labels_e f e2)
  | Assign e1 e2 => Assign (map_labels_e f e1) (map_labels_e f e2)
  | Free e => Free (map_labels_e f e)
  | Seq e1 e2 => Seq (map_labels_e f e1) (map_labels_e f e2)
  | If e1 e2 e3 =>
    If (map_labels_e f e1) (map_labels_e f e2) (map_labels_e f e3)
  | While e1 e2 => While (map_labels_e f e1) (map_labels_e f e2)
  end.

Definition Map (V : Set) : Set := list (Label * option (Value V)).

Definition labels {V : Set} (m : Map V) : list Label :=
  List.map fst m.

Definition Is_fresh_label {V : Set} (l : Label) (m : Map V) : Prop :=
  ~ List.In l (labels m).

Definition Is_Valid_Map {V : Set} (m : Map V) : Prop :=
  List.NoDup (labels m).

Global Hint Unfold labels : lamref.
Global Hint Unfold Is_fresh_label : lamref.
Global Hint Unfold Is_Valid_Map : lamref.

Inductive Lookup {V : Set} (l : Label) : Map V -> Value V -> Prop :=
| Lookup_hd (m : Map V) (v : Value V) : Lookup l ((l, Some v) :: m)%list v
| Lookup_tl (a : Label * option (Value V)) (m : Map V) (v : Value V) :
    Lookup l m v -> Lookup l (a :: m)%list v
.

Inductive Assignment {V : Set} (l : Label) (v : Value V) :
  Map V -> Map V -> Prop :=
| Assignment_hd (ov : option (Value V)) (m : Map V) :
    Assignment l v ((l,ov) :: m)%list ((l, Some v) :: m)%list
| Assignment_tl (a : Label * option (Value V)) (m m' : Map V) :
    Assignment l v m m' ->
    Assignment l v (a :: m)%list (a :: m')%list
.

Inductive Dealloc {V : Set} (l : Label) : Map V -> Map V -> Prop :=
| Dealloc_hd (m : Map V) (ov : option (Value V)) : Dealloc l ((l,ov)::m)%list m
| Dealloc_tl (m m' : Map V) (a : Label * option (Value V)) :
    Dealloc l m m' ->
    Dealloc l (a::m)%list (a::m')%list
.

Inductive Nth {A : Type} : nat -> list A -> A -> Prop :=
| Nth_zero (x : A) (xs : list A) : Nth 0 (x::xs) x
| Nth_succ (n : nat) (x y : A) (xs : list A) :
    Nth n xs y -> Nth (S n) (x::xs) y
.

Inductive SplitAt {A : Type} :
  list A ->
  list A -> A -> list A -> Prop :=
| SplitAt_hd (x : A) (xs : list A) :
    SplitAt (x::xs) [] x xs
| SplitAt_tl (x : A) (xs ys : list A) (y : A) (ys' : list A) :
    SplitAt xs ys y ys' ->
    SplitAt (x::xs) (x::ys) y ys'
.

Global Hint Constructors Assignment : lamref.
Global Hint Constructors Lookup     : lamref.
Global Hint Constructors Nth        : lamref.
Global Hint Constructors SplitAt    : lamref.

Notation "'L[' xs '~~>' ys '|' y '|' zs ']'" := (@SplitAt _ xs ys y zs).
Section label_section.
Open Scope label_scope.
Fixpoint lookup {V : Set} (l : Label) (m : Map V) : option (Value V) :=
  match m with
  | nil => None
  | (l', v) :: m' => if l =? l' then v else lookup l m'
  end%list.

Fixpoint update {V : Set} (l : Label) (v : Value V) (m : Map V) : Map V :=
  match m with
  | nil => [(l, Some v)]
  | (l', v') :: m' =>
    if l =? l' then ((l', Some v) :: m') else (l', v') :: (update l v m')
  end%list.

Fixpoint free {V : Set} (l : Label) (m : Map V) : Map V :=
  match m with
  | nil => nil
  | (l', v) :: m' =>
    if l =? l' then m' else (l', v) :: (free l m')
  end%list.
End label_section.

Definition list_max (l : list nat) : nat :=
  List.fold_right max 0 l.

Definition new_label {V : Set} (m : Map V) : Label :=
  OfNat (1 + list_max (List.map of_label (labels m))).

Fixpoint n_new_cells_from {V : Set} l n : Map V :=
  match n with
  | 0 => []
  | S n => let 'OfNat n' := l in
    (l, None) :: n_new_cells_from (OfNat (1+n')) n
  end%list.

Definition alloc_array {V : Set} n (m : Map V) : Map V * Label :=
  let init := new_label m in
  (n_new_cells_from init n ++ m, init)%list.

Global Hint Unfold alloc_array : lamref.

(* SOS semantics *)
Reserved Notation "'R[' e1 ',' m1 '~~>' e2 ',' m2 ']'".

Inductive red {V : Set} :
  Expr V -> Map V ->
  Expr V -> Map V ->
  Prop :=

| red_lam : forall m e (v : Value _),
    R[App (Lam e) v , m ~~> subst_e e v , m]

| red_bneg : forall m b,
    R[UnOp (BUOp BNeg) (Bool b), m ~~> Bool (negb b), m]

| red_ineg : forall m i,
    R[UnOp (IUOp INeg) (Int i), m ~~> Int (- i), m]

| red_bor : forall m b1 b2,
    R[BinOp (BBOp BOr) (Bool b1) (Bool b2), m ~~> Bool (b1 || b2), m]

| red_band : forall m b1 b2,
    R[BinOp (BBOp BAnd) (Bool b1) (Bool b2), m ~~> Bool (b1 && b2), m]

| red_iadd : forall m i1 i2,
    R[BinOp (IBOp IAdd) (Int i1) (Int i2), m ~~> Int (i1 + i2), m]

| red_isub : forall m i1 i2,
    R[BinOp (IBOp ISub) (Int i1) (Int i2), m ~~> Int (i1 - i2), m]

| red_imul : forall m i1 i2,
    R[BinOp (IBOp IMul) (Int i1) (Int i2), m ~~> Int (i1 * i2), m]

| red_idiv : forall m i1 i2,
    R[BinOp (IBOp IDiv) (Int i1) (Int i2), m ~~> Int (i1 / i2), m]

| red_clt : forall m i1 i2,
    R[BinOp (CBOp CLt) (Int i1) (Int i2), m ~~> Bool (i1 <? i2)%Z, m]

| red_ceq : forall m i1 i2,
    R[BinOp (CBOp CEq) (Int i1) (Int i2), m ~~> Bool (i1 =? i2)%Z, m]

| red_rec_e2v : forall m vs,
    R[RecE (vals2exprs vs), m ~~> RecV vs, m]

| red_rec_get : forall n m vs v,
    Nth n vs v ->
    R[Get n (RecV vs), m ~~> v, m]

| red_ref : forall m l (v : Value _),
    l = new_label m ->
    R[Ref v, m ~~> Lab l, ((l, Some v) :: m)%list]

| red_new_array : forall i m m' l,
    (i >= 0)%Z ->
    (m', l) = alloc_array (Z.to_nat i) m ->
    R[NewArray (Int i), m ~~> Lab l, m']

| red_deref : forall m l v,
    Lookup l m v ->
    R[Deref (Lab l), m ~~> v, m]

| red_shift : forall m n i,
    (i >= 0)%Z ->
    R[Shift (Lab (OfNat n)) (Int i), m ~~> Lab (OfNat (n + Z.to_nat i)), m]

| red_assign : forall m m' l v,
    Assignment l v m m' ->
    R[Assign (Lab l) v, m ~~> U_val, m']

| red_free : forall m m' l,
    Dealloc l m m' ->
    R[Free (Lab l), m ~~> U_val, m']

| red_seq : forall m e,
    R[Seq U_val e, m ~~> e, m]

| red_if : forall b m e1 e2,
    R[If (Bool b) e1 e2, m ~~> if b then e1 else e2, m]

| red_while : forall m e1 e2,
    R[While e1 e2, m
      ~~>
      If e1 (Seq e2 (While e1 e2)) U_val, m]

(* structural rules *)
| red_app1 : forall m m' e1 e1' e2,
    R[e1, m ~~> e1', m'] ->
    R[App e1 e2, m ~~> App e1' e2, m']

| red_app2 : forall m m' (v : Value _) e e',
    R[e, m ~~> e', m'] ->
    R[App v e, m ~~> App v e', m']

| red_unop : forall k m m' e e',
    R[e, m ~~> e', m'] ->
    R[UnOp k e, m ~~> UnOp k e', m']

| red_binop1 : forall k m m' e1 e1' e2,
    R[e1, m ~~> e1', m'] ->
    R[BinOp k e1 e2, m ~~> BinOp k e1' e2, m']

| red_binop2 : forall k m m' (v : Value _) e e',
    R[e, m ~~> e', m'] ->
    R[BinOp k v e, m ~~> BinOp k v e', m']

| red_rec_split : forall m m' es es' vs0 e e' es0,
    L[es  ~~> vals2exprs vs0 | e | es0] ->
    L[es' ~~> vals2exprs vs0 | e' | es0] ->
    R[e, m ~~> e', m'] ->
    R[RecE es, m ~~> RecE es', m']

| red_rec_get_e : forall n m m' e e',
    R[e, m ~~> e', m'] ->
    R[Get n e, m ~~> Get n e', m']

| red_ref_e : forall m m' e e',
    R[e, m ~~> e', m'] ->
    R[Ref e, m ~~> Ref e', m']

| red_new_array_e : forall m m' e e',
    R[e, m ~~> e', m'] ->
    R[NewArray e, m ~~> NewArray e', m']

| red_deref_e : forall m m' e e',
    R[e, m ~~> e', m'] ->
    R[Deref e, m ~~> Deref e', m']

| red_shift1 : forall m m' e1 e1' e2,
    R[e1, m ~~> e1', m'] ->
    R[Shift e1 e2, m ~~> Shift e1' e2, m']

| red_shift2 : forall m m' (v : Value _) e e',
    R[e, m ~~> e', m'] ->
    R[Shift v e, m ~~> Shift v e', m']

| red_assign1 : forall m m' e1 e1' e2,
    R[e1, m ~~> e1', m'] ->
    R[Assign e1 e2, m ~~> Assign e1' e2, m']

| red_assign2 : forall m m' (v : Value _) e e',
    R[e, m ~~> e', m'] ->
    R[Assign v e, m ~~> Assign v e', m']

| red_free_e : forall m m' e e',
    R[e, m ~~> e', m'] ->
    R[Free e, m ~~> Free e', m']

| red_seq1 : forall m m' e1 e1' e2,
    R[e1, m ~~> e1', m'] ->
    R[Seq e1 e2, m ~~> Seq e1' e2, m']

| red_cond_if : forall m m' e1 e1' e2 e3,
    R[e1, m ~~> e1', m'] ->
    R[If e1 e2 e3, m ~~> If e1' e2 e3, m']

where "'R[' e1 ',' m1 '~~>' e2 ',' m2 ']'" :=
  (@red _ e1 m1 e2 m2).

Global Hint Constructors red : lamref.

(* cost semantics *)
Reserved Notation "'C[' e1 ',' m1 '~~>' e2 ',' m2 '|' c ']'".

Inductive cost_red {V : Set}
  (e : Expr V)  (m : Map V) :
  Expr V -> Map V ->
  nat -> Prop :=

| no_red : C[e, m ~~> e, m | 0]

| S_red (c : nat) (e' e'' : Expr V) (m' m'' : Map V) :
    red e m e' m' ->
    cost_red e' m' e'' m'' c ->
    cost_red e m e'' m'' (S c)

where "'C[' e1 ',' m1 '~~>' e2 ',' m2 '|' c ']'" :=
    (@cost_red _ e1 m1 e2 m2 c).

Global Hint Constructors cost_red : lamref.

(* NOTATIONS *)

Notation "'-\' e" := (Lam e) (at level 100).

Notation "e1 '<*' e2" :=
  (App e1 e2)
  (at level 59, left associativity).

Notation "'[~]' e" := (UnOp (BUOp BNeg) e) (at level 50).
Notation "'[--]' e" := (UnOp (IUOp INeg) e) (at level 50).
Notation "e1 '[||]' e2" := (BinOp (BBOp BOr) e1 e2) (at level 50).
Notation "e1 '[&&]' e2" := (BinOp (BBOp BAnd) e1 e2) (at level 50).
Notation "e1 '[+]' e2" := (BinOp (IBOp IAdd) e1 e2) (at level 50).
Notation "e1 '[-]' e2" := (BinOp (IBOp ISub) e1 e2) (at level 50).
Notation "e1 '[*]' e2" := (BinOp (IBOp IMul) e1 e2) (at level 50).
Notation "e1 '[/]' e2" := (BinOp (IBOp IDiv) e1 e2) (at level 50).
Notation "e1 '[<]' e2" := (BinOp (CBOp CLt) e1 e2) (at level 50).
Notation "e1 '[=]' e2" := (BinOp (CBOp CEq) e1 e2) (at level 50).

Notation "'!' e" := (Deref e) (at level 50).

Notation "e1 '>>' e2" :=
  (Shift e1 e2)
  (at level 70, no associativity).

Notation "e1 '<-' e2" :=
  (Assign e1 e2)
  (at level 70, no associativity).

Notation "e1 ';;' e2" :=
  (Seq e1 e2)
  (at level 90, right associativity).

Notation "[let] e1 [in] e2 [end]" :=
  ((-\ e2) <* e1)
  (at level 50, no associativity).

Notation "[if] e1 [then] e2 [else] e3 [end]" :=
  (If e1 e2 e3)
  (at level 50, no associativity).

Notation "[while] e1 [do] e2 [end]" :=
  (While e1 e2)
  (at level 50, no associativity).


Definition StringLam (x : string) (e : Expr string) :
  Value string :=
  Lam (map_e (fun y => if x =? y then None else Some y)%string e).

Notation "'[-\]' x ',' e" :=
  (StringLam x e)
  (at level 100, no associativity).

Notation "'[let' x ']' e1 '[in]' e2 [end]" :=
  (([-\] x, e2) <* e1)
  (at level 50, no associativity).
