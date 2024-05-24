(* a simple lambda calculus with mutable references *)

Require Import Nat.
Require List.
Import List.ListNotations.
Require Import String.
Require Import ZArith.

(*
Definition inc_set (A : Set) : Set :=
  option A.

Definition inc_fun {A B : Set}
  (f : A -> B) (y : B) (x : inc_set A) : B :=
  match x with
  | None => y
  | Some x' => f x'
  end.
*)

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

Hint Unfold of_label : label.
Hint Unfold lift2 : label.
Hint Unfold lift  : label.
Hint Unfold label_eqb : label.
Hint Unfold label_ltb : label.
Hint Unfold label_lt  : label.

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

Inductive Value :=
| U_val : Value
| Var : string -> Value
| Int : Z -> Value (* integer *)
| Bool : bool -> Value
| Lab : Label -> Value (* label *)
| RecV : list Value -> Value (* record value *)
| Lam : string -> Expr -> Value
with Expr :=
| Val : Value -> Expr
| App : Expr -> Expr -> Expr
| UnOp : UnOpKind -> Expr -> Expr
| BinOp : BinOpKind -> Expr -> Expr -> Expr
| RecE : list Expr -> Expr (* record expression *)
| Get : nat -> Expr -> Expr (* get nth field of a record *)
| Ref : Expr -> Expr (* mutable reference *)
| Deref : Expr -> Expr
| Assign : Expr -> Expr -> Expr
| Seq : Expr -> Expr -> Expr
| If : Expr -> Expr -> Expr -> Expr
| While : Expr -> Expr -> Expr
.

Inductive type :=
| Unit : type
| IntT : type (* integer *)
| BoolT : type (* bool *)
| Arrow : type -> type -> type
| RefT : type -> type (* reference *)
| RecT : list type -> type (* record *)
.

Coercion Val : Value >-> Expr.

Definition vals2exprs : list Value -> list Expr :=
  List.map Val.
(*
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
*)

(* variable substitution (unsafe) *)
Fixpoint subst_v
  (v : Value) (x : string) (v' : Value) : Value :=
  match v with
  | U_val => U_val
  | Var x' => if x =? x' then v' else Var x'
  | Int i => Int i
  | Bool i => Bool i
  | Lab l => Lab l
  | RecV vs => RecV (List.map (fun v => subst_v v x v') vs)
  | Lam x' e => if x =? x' then Lam x' e else Lam x' (subst_e e x v')
  end%string
with subst_e
  (e : Expr) (x : string) (v' : Value) : Expr :=
  match e with
  | Val v => subst_v v x v'
  | App e1 e2 => App (subst_e e1 x v') (subst_e e2 x v')
  | UnOp k e => UnOp k (subst_e e x v')
  | BinOp k e1 e2 => BinOp k (subst_e e1 x v') (subst_e e2 x v')
  | RecE es => RecE (List.map (fun e => subst_e e x v') es)
  | Get n e => Get n (subst_e e x v')
  | Ref e => Ref (subst_e e x v')
  | Deref e => Deref (subst_e e x v')
  | Assign e1 e2 => Assign (subst_e e1 x v') (subst_e e2 x v')
  | Seq e1 e2 => Seq (subst_e e1 x v') (subst_e e2 x v')
  | If e1 e2 e3 => If (subst_e e1 x v') (subst_e e2 x v') (subst_e e3 x v')
  | While e1 e2 => While (subst_e e1 x v') (subst_e e2 x v')
  end.

(* transformation on labels *)
Fixpoint map_labels_v (f : Label -> Label) (v : Value) : Value :=
  match v with
  | U_val => U_val
  | Var x => Var x
  | Int i => Int i
  | Bool i => Bool i
  | Lab l => Lab (f l)
  | RecV vs => RecV (List.map (map_labels_v f) vs)
  | Lam x e => Lam x (map_labels_e f e)
  end
with map_labels_e (f : Label -> Label) (e : Expr) : Expr :=
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

Definition Map : Set := list (Label * Value).

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

Definition labels (m : Map) : list Label :=
  List.map fst m.

Definition Is_fresh_label (l : Label) (m : Map) : Prop :=
  ~ List.In l (labels m).

Definition Is_Valid_Map (m : Map) : Prop :=
  List.NoDup (labels m).

Inductive Lookup (l : Label) : Map -> Value -> Prop :=
| Lookup_hd (m : Map) (v : Value) : Lookup l ((l,v) :: m)%list v
| Lookup_tl (a : Label * Value) (m : Map) (v : Value) :
    Lookup l m v -> Lookup l (a :: m)%list v
.

Inductive Assignment (l : Label) (v : Value) :
  Map -> Map -> Prop :=
| Assignment_hd (v0 : Value) (m : Map) :
    Assignment l v ((l,v0) :: m)%list ((l,v) :: m)%list
| Assignment_tl (a : Label * Value) (m m' : Map) :
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

Notation "'L[' xs '~~>' ys '|' y '|' zs ']'" := (@SplitAt _ xs ys y zs).
Section label_section.
Open Scope label_scope.
Fixpoint lookup (l : Label) (m : Map) : option Value :=
  match m with
  | nil => None
  | (l', v) :: m' => if l =? l' then Some v else lookup l m'
  end%list.

Fixpoint update (l : Label) (v : Value) (m : Map) : Map :=
  match m with
  | nil => [(l, v)]
  | (l', v') :: m' =>
    if l =? l' then ((l', v) :: m') else (l', v') :: (update l v m')
  end%list.
End label_section.

Definition list_max (l : list nat) : nat :=
  List.fold_right max 0 l.

Definition new_label (m : Map) : Label :=
  OfNat (1 + list_max (List.map of_label (labels m))).

(* SOS semantics *)
Reserved Notation "'R[' e1 ',' m1 '~~>' e2 ',' m2 ']'".

Inductive red :
  Expr -> Map ->
  Expr -> Map ->
  Prop :=

| red_lam : forall m x e (v : Value),
    R[App (Lam x e) v , m ~~> subst_e e x v , m]

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

| red_ref : forall m l (v : Value),
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

| red_app2 : forall m m' (v : Value) e e',
    R[e, m ~~> e', m'] ->
    R[App v e, m ~~> App v e', m']

| red_unop : forall k m m' e e',
    R[e, m ~~> e', m'] ->
    R[UnOp k e, m ~~> UnOp k e', m']

| red_binop1 : forall k m m' e1 e1' e2,
    R[e1, m ~~> e1', m'] ->
    R[BinOp k e1 e2, m ~~> BinOp k e1' e2, m']

| red_binop2 : forall k m m' (v : Value) e e',
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

| red_assign2 : forall m m' (v : Value) e e',
    R[e, m ~~> e', m'] ->
    R[Assign v e, m ~~> Assign v e', m']

| red_seq1 : forall m m' e1 e1' e2,
    R[e1, m ~~> e1', m'] ->
    R[Seq e1 e2, m ~~> Seq e1' e2, m']

| red_cond_if : forall m m' e1 e1' e2 e3,
    R[e1, m ~~> e1', m'] ->
    R[If e1 e2 e3, m ~~> If e1' e2 e3, m']

where "'R[' e1 ',' m1 '~~>' e2 ',' m2 ']'" :=
  (red e1 m1 e2 m2).

(* cost semantics *)
Reserved Notation "'C[' e1 ',' m1 '~~>' e2 ',' m2 '|' c ']'".

Inductive cost_red
  (e : Expr)  (m : Map) :
  Expr -> Map ->
  nat -> Prop :=

| no_red : C[e, m ~~> e, m | 0]

| S_red (c : nat) (e' e'' : Expr) (m' m'' : Map) :
    red e m e' m' ->
    cost_red e' m' e'' m'' c ->
    cost_red e m e'' m'' (S c)

where "'C[' e1 ',' m1 '~~>' e2 ',' m2 '|' c ']'" :=
    (cost_red e1 m1 e2 m2 c).

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

Notation "'[-\]' x ',' e" := (Lam x e) (at level 100, no associativity).

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

Notation "[let] x ':=' e1 [in] e2 [end]" :=
  (([-\] x , e2) <* e1)
  (at level 50, no associativity).

Notation "[if] e1 [then] e2 [else] e3 [end]" :=
  (If e1 e2 e3)
  (at level 50, no associativity).

Notation "[while] e1 [do] e2 [end]" :=
  (While e1 e2)
  (at level 50, no associativity).
