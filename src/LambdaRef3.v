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

Definition label_eqb '(OfNat n) '(OfNat n') : bool := n =? n'.
Notation "l =? l'" := (label_eqb l l').

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

Inductive type :=
| Unit : type
| IntT : type (* integer *)
| BoolT : type (* bool *)
| Arrow : type -> type -> type
| RefT : type -> type (* reference *)
| RecT : list type -> type (* record *)
.

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

(* change between LambdaRef.v and LambdaRef3.v: map as function *)
Definition Map (V : Set) : Set := Label -> option (Value V).

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

Definition Is_fresh_label {V : Set} (l : Label) (m : Map V) : Prop :=
  m l = None.

Definition Lookup {V : Set} (l : Label) (m : Map V) (v : Value V) : Prop :=
  m l = Some v.

Definition empty {V : Set} : Map V := fun l => None.

Definition update {V : Set} (l : Label) (m : Map V) (v : Value V) : Map V :=
  fun l' => if l =? l' then Some v else m l.

Definition Assignment {V : Set} (l : Label) (v : Value V)
  (m m' : Map V) : Prop :=
  forall l', m' l' = update l m v l'.

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

Notation "'L[' xs '~~>' ys '|' y '|' zs ']'" := (@SplitAt _ xs ys y zs).

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
    Is_fresh_label l m ->
    R[Ref v, m ~~> Lab l, update l m v]

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

Notation "t1 --> t2" :=
  (Arrow t1 t2)
  (at level 60, right associativity).

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

(*
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
*)