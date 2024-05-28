(* a simple lambda calculus with mutable references *)

Require Import Nat.
Require List.
Import List.ListNotations.
Require Import String.
Require Import ZArith.

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
| Deref : Expr V -> Expr V
| Assign : Expr V -> Expr V -> Expr V
| Seq : Expr V -> Expr V -> Expr V
| If : Expr V -> Expr V -> Expr V -> Expr V
| While : Expr V -> Expr V -> Expr V
.
(*
Inductive type :=
| Unit : type
| IntT : type (* integer *)
| BoolT : type (* bool *)
| Arrow : type -> type -> type
| RefT : type -> type (* reference *)
| RecT : list type -> type (* record *)
.
*)

Arguments U_val {V}.
Arguments Var {V}.
Arguments Int {V}.
Arguments Bool {V}.
Arguments Lab {V}.
Arguments RecV {V}.
Arguments Lam {V}.
Arguments Ref {V}.
Arguments Val {V}.
Arguments App {V}.
Arguments UnOp {V}.
Arguments BinOp {V}.
Arguments RecE {V}.
Arguments Get {V}.
Arguments Deref {V}.
Arguments Assign {V}.
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
  | Deref e => Deref (map_e f e)
  | Assign e1 e2 => Assign (map_e f e1) (map_e f e2)
  | Seq e1 e2 => Seq (map_e f e1) (map_e f e2)
  | If e1 e2 e3 => If (map_e f e1) (map_e f e2) (map_e f e3)
  | While e1 e2 => While (map_e f e1) (map_e f e2)
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
  | Deref e => Deref (bind_e f e)
  | Assign e1 e2 => Assign (bind_e f e1) (bind_e f e2)
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
  | Deref e => Deref (map_labels_e f e)
  | Assign e1 e2 => Assign (map_labels_e f e1) (map_labels_e f e2)
  | Seq e1 e2 => Seq (map_labels_e f e1) (map_labels_e f e2)
  | If e1 e2 e3 =>
    If (map_labels_e f e1) (map_labels_e f e2) (map_labels_e f e3)
  | While e1 e2 => While (map_labels_e f e1) (map_labels_e f e2)
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

Global Hint Unfold labels : lamref.
Global Hint Unfold Is_fresh_label : lamref.
Global Hint Unfold Is_Valid_Map : lamref.

Inductive Lookup {V : Set} (l : Label) : Map V -> Value V -> Prop :=
| Lookup_hd (m : Map V) (v : Value V) : Lookup l ((l,v) :: m)%list v
| Lookup_tl (a : Label * Value V) (m : Map V) (v : Value V) :
    Lookup l m v -> Lookup l (a :: m)%list v
.

Inductive Assignment {V : Set} (l : Label) (v : Value V) :
  Map V -> Map V -> Prop :=
| Assignment_hd (v0 : Value V) (m : Map V) :
    Assignment l v ((l,v0) :: m)%list ((l,v) :: m)%list
| Assignment_tl (a : Label * Value V) (m m' : Map V) :
    Assignment l v m m' ->
    Assignment l v (a :: m)%list (a :: m')%list
.

Inductive Nth {A : Set} : nat -> list A -> A -> Prop :=
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
  | (l', v) :: m' => if l =? l' then Some v else lookup l m'
  end%list.

Fixpoint update {V : Set} (l : Label) (v : Value V) (m : Map V) : Map V :=
  match m with
  | nil => [(l, v)]
  | (l', v') :: m' =>
    if l =? l' then ((l', v) :: m') else (l', v') :: (update l v m')
  end%list.
End label_section.

Definition list_max (l : list nat) : nat :=
  List.fold_right max 0 l.

Definition new_label {V : Set} (m : Map V) : Label :=
  OfNat (1 + list_max (List.map of_label (labels m))).

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
    R[Ref v, m ~~> Lab l, ((l,v) :: m)%list]

| red_deref : forall m l v,
    Lookup l m v ->
    R[Deref (Lab l), m ~~> v, m]

| red_assign : forall m m' l v,
    Assignment l v m m' ->
    R[Assign (Lab l) v, m ~~> U_val, m']

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

| red_deref_e : forall m m' e e',
    R[e, m ~~> e', m'] ->
    R[Deref e, m ~~> Deref e', m']

| red_assign1 : forall m m' e1 e1' e2,
    R[e1, m ~~> e1', m'] ->
    R[Assign e1 e2, m ~~> Assign e1' e2, m']

| red_assign2 : forall m m' (v : Value _) e e',
    R[e, m ~~> e', m'] ->
    R[Assign v e, m ~~> Assign v e', m']

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

(*
(* type system *)
Definition env (V : Set) : Set := V -> type.
Definition env_empty : env Empty_set :=
  fun x => match x with end.

Reserved Notation "'T[' G '|-' e ':::' t ']'".

Inductive typing {V : Set} (G : env V) :
  Expr V -> type -> Prop :=

| T_Unit : T[ G |- U_val ::: Unit ]

| T_Var : forall x, T[ G |- Var x ::: (G x) ]

| T_Int : forall i, T[ G |- Int i ::: IntT ]

| T_Bool : forall b, T[ G |- Bool b ::: BoolT ]

| T_RecV : forall vs ts,
    List.Forall2 (fun (v : Value _) t => T[ G |- v ::: t ]) vs ts ->
    T[ G |- RecV vs ::: RecT ts ]

| T_Lam : forall e t1 t2,
    T[ inc_fun G t1 |- e ::: t2 ] ->
    T[ G |- Lam e ::: Arrow t1 t2 ]

| T_App : forall e1 e2 t2 t1,
    T[ G |- e1 ::: Arrow t2 t1 ] ->
    T[ G |- e2 ::: t2 ] ->
    T[ G |- App e1 e2 ::: t1 ]

| T_BUOp : forall e k,
    T[ G |- e ::: BoolT ] ->
    T[ G |- UnOp (BUOp k) e ::: BoolT ]

| T_IUOp : forall e k,
    T[ G |- e ::: IntT ] ->
    T[ G |- UnOp (IUOp k) e ::: IntT ]

| T_BBOp : forall e1 e2 k,
    T[ G |- e1 ::: BoolT ] ->
    T[ G |- e2 ::: BoolT ] ->
    T[ G |- BinOp (BBOp k) e1 e2 ::: BoolT ]

| T_IBOp : forall e1 e2 k,
    T[ G |- e1 ::: IntT ] ->
    T[ G |- e2 ::: IntT ] ->
    T[ G |- BinOp (IBOp k) e1 e2 ::: IntT ]

| T_CBOp : forall e1 e2 k,
    T[ G |- e1 ::: IntT ] ->
    T[ G |- e2 ::: IntT ] ->
    T[ G |- BinOp (CBOp k) e1 e2 ::: BoolT ]

| T_RecE : forall es ts,
    List.Forall2 (fun e t => T[ G |- e ::: t ]) es ts ->
    T[ G |- RecE es ::: RecT ts ]

| T_Get : forall n e ts t,
    Nth n ts t ->
    T[ G |- e ::: RecT ts ] ->
    T[ G |- Get n e ::: t ]

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

| T_If : forall e1 e2 e3 t,
    T[ G |- e1 ::: BoolT ] ->
    T[ G |- e2 ::: t ] ->
    T[ G |- e2 ::: t ] ->
    T[ G |- If e1 e2 e3 ::: t ]

| T_While : forall e1 e2,
    T[ G |- e1 ::: BoolT ] ->
    T[ G |- e2 ::: Unit ] ->
    T[ G |- While e1 e2 ::: Unit ]

where "T[ G |- e ::: t ]" := (@typing _ G e t).
*)
(* NOTATIONS *)

Notation "'$' x" := (Some x) (at level 50).

Notation "'-\' e" := (Lam e) (at level 100).

Notation "e1 '<*' e2" :=
  (App e1 e2)
  (at level 50, left associativity).

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

Notation "e1 '<-' e2" :=
  (Assign e1 e2)
  (at level 70, no associativity).

Notation "e1 ';;' e2" :=
  (Seq e1 e2)
  (at level 90, right associativity).
(*
Notation "t1 --> t2" :=
  (Arrow t1 t2)
  (at level 60, right associativity).
*)
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

Notation "'[let' x ']' e1 '[in]' e2 [end]" :=
  (([-\] x, e2) <* e1)
  (at level 50, no associativity).


(* ------------------------LEMMAS-------------------------------------*)
(*Fixpoint bind_shift_v (A : Set) x (a : _ A) :
  bind_v (inc_fun Var x) (shift_v a) = a
with bind_shift_e (A : Set) x (a : _ A) :
  bind_e (inc_fun Var x) (shift_e a) = a.
Proof.
  - destruct a; simpl; try reflexivity.
    + f_equal. induction l; simpl.
      * reflexivity.
      * f_equal; eauto.
    + f_equal. Print liftS. eapply bind_shift_e.
*)

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
(* weakening lemma *)
Lemma weakening (V : Set) (G : env V) (e : Expr V) (t t' : type) :
  T[ G |- e ::: t ] ->
  T[ inc_fun G t' |- shift_e e ::: t].
Proof.
  intro H. induction H; cbn; econstructor; try eassumption.
Abort.
*)
