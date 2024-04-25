Require List.
Import List.ListNotations.
Require Import String.
Require Import ZArith.

Require Import src.LambdaRef.

(* evaluator *)

(* computation monad*)
Definition CompMonad (V A : Set) : Set := Map V -> option (A * Map V).

Definition mreturn {V A : Set} (x : A) : CompMonad V A :=
  fun (s : Map V) => Some (x, s).

Definition mbind {V A B : Set}
  (m : CompMonad V A) (f : A -> CompMonad V B) : CompMonad V B :=
  fun (s : Map V) =>
  match m s with
  | Some (x, s) => f x s
  | None => None
  end.

Definition mmap {V A B : Set}
  (f : A -> B) (m : CompMonad V A) : CompMonad V B :=
  mbind m (fun x => mreturn (f x)).

Definition mfail {V A : Set} : CompMonad V A :=
  fun (s : Map V) => None.

Definition eqb_label '(OfNat n : Label) '(OfNat m : Label) : bool :=
  n =? m.

Notation "l =? ll" := (eqb_label l ll).

Definition mnew {V : Set} : CompMonad V Label :=
  fun (s : Map V) => Some (new_label s, s).

Definition mload_at {V : Set} (l : Label) : CompMonad V (Value V) :=
  fun (s : Map V) => option_map (fun v => (v, s)) (lookup l s).

Definition mstore_at {V : Set} (l : Label) (v : Value V) : CompMonad V unit :=
  fun (s : Map V) => Some (tt, update l v s).

Definition of_option {V A : Set} (ox : option A) : CompMonad V A :=
  match ox with
  | Some x => mreturn x
  | None => mfail
  end.

(* translation of operators *)

(* unary *)

Definition fun_BoolUnOpKind (buok : BoolUnOpKind) : bool -> bool :=
  match buok with
  | BNeg => negb
  end.

Definition fun_IntUnOpKind (iuok : IntUnOpKind) : Z -> Z :=
  match iuok with
  | INeg => Z.opp
  end.

Definition type_of_UnOpKind_arg (uok : UnOpKind) : Set :=
  match uok with
  | BUOp _ => bool
  | IUOp _ => Z
  end.

Definition type_of_UnOpKind_ret (uok : UnOpKind) : Set :=
  type_of_UnOpKind_arg uok.

Definition type_of_UnOpKind (uok : UnOpKind) : Set :=
  type_of_UnOpKind_arg uok -> type_of_UnOpKind_ret uok.

Definition fun_UnOpKind (uok : UnOpKind) : type_of_UnOpKind uok :=
  match uok return type_of_UnOpKind uok with
  | BUOp buok => fun_BoolUnOpKind buok
  | IUOp iuok => fun_IntUnOpKind iuok
  end.

Definition step_UnOp {V A : Set} (uok : UnOpKind) (v : Value V) (default : A) :
  (type_of_UnOpKind_arg uok -> (type_of_UnOpKind_ret uok -> Value V) -> A) -> A :=
  match uok return
    (type_of_UnOpKind_arg uok -> (type_of_UnOpKind_ret uok -> Value V) -> A) -> A
  with
  | BUOp buok => fun f =>
    match v with
    | Bool b => f b Bool
    | _ => default
    end
  | IUOp iuok => fun f =>
    match v with
    | Int i => f i Int
    | _ => default
    end
  end.

(* binary *)

Definition fun_BoolBinOpKind (bbok : BoolBinOpKind) : bool -> bool -> bool :=
  match bbok with
  | BOr => orb
  | BAnd => andb
  end.

Definition fun_IntBinOpKind (ibok : IntBinOpKind) : Z -> Z -> Z :=
  match ibok with
  | IAdd => Z.add
  | ISub => Z.sub
  | IMul => Z.mul
  | IDiv => Z.div
  end.

Definition fun_CondBinOpKind (cbok : CondBinOpKind) : Z -> Z -> bool :=
  match cbok with
  | CLt => Z.ltb
  | CEq => Z.eqb
  end.

Definition type_of_BinOpKind_arg (bok : BinOpKind) : Set :=
  match bok with
  | BBOp _ => bool
  | IBOp _ => Z
  | CBOp _ => Z
  end.

Definition type_of_BinOpKind_ret (bok : BinOpKind) : Set :=
  match bok with
  | BBOp _ => bool
  | IBOp _ => Z
  | CBOp _ => bool
  end.

Definition type_of_BinOpKind (bok : BinOpKind) : Set :=
  type_of_BinOpKind_arg bok -> type_of_BinOpKind_arg bok ->
    type_of_BinOpKind_ret bok.

Definition fun_BinOpKind (bok : BinOpKind) : type_of_BinOpKind bok :=
  match bok return type_of_BinOpKind bok with
  | BBOp bbok => fun_BoolBinOpKind bbok
  | IBOp ibok => fun_IntBinOpKind ibok
  | CBOp cbok => fun_CondBinOpKind cbok
  end.

Definition step_BinOp {V A : Set}
  (bok : BinOpKind) (v1 v2 : Value V) (default : A) :
  (type_of_BinOpKind_arg bok -> type_of_BinOpKind_arg bok ->
    (type_of_BinOpKind_ret bok -> Value V) -> A) -> A :=
  match bok return
    (type_of_BinOpKind_arg bok -> type_of_BinOpKind_arg bok ->
      (type_of_BinOpKind_ret bok -> Value V) -> A) -> A
  with
  | BBOp bbok => fun f =>
    match v1, v2 with
    | Bool b1, Bool b2 => f b1 b2 Bool
    | _, _ => default
    end
  | IBOp ibok => fun f =>
    match v1, v2 with
    | Int i1, Int i2 => f i1 i2 Int
    | _, _ => default
    end
  | CBOp cbok => fun f =>
    match v1, v2 with
    | Int i1, Int i2 => f i1 i2 Bool
    | _, _ => default
    end
  end.

(* stepping in records *)

Inductive step_record_result (V : Set) : Set :=
| rec_val  : list (Value V) -> step_record_result V
| rec_expr : list (Expr V)  -> step_record_result V
.

Arguments rec_val  {V}.
Arguments rec_expr {V}.

Definition extend_step_rec_res {V : Set}
  (v : Value V) (srr : step_record_result V) : step_record_result V :=
  match srr with
  | rec_val vs  => rec_val (v :: vs)
  | rec_expr es => rec_expr (Val v :: es)
  end.

Definition step_rec_res_to_expr {V : Set}
  (srr : step_record_result V) : Expr V :=
  match srr with
  | rec_val vs  => RecV vs
  | rec_expr es => RecE es
  end.

Definition step_record {V : Set} step_expr :
  list (Expr V) -> CompMonad V (step_record_result V) :=
  fix step_record (es : list (Expr V)) :=
  match es with
  | nil => mreturn (rec_val nil)
  | (Val v :: es') => mmap (extend_step_rec_res v) (step_record es')
  | (e :: es') =>
    mbind (step_expr e) (fun e' => mreturn (rec_expr (e' :: es')))
  end%list.

(* one step of reduction *)
Fixpoint step_expr {V : Set} (e : Expr V) :
  CompMonad V (Expr V) :=
  match e with
  | Val v => mfail
  | App (Lam e) (Val v) => mreturn (subst_e e v)
  | UnOp k (Val v) =>
    step_UnOp k v mfail (fun x constr => mreturn (Val (constr (fun_UnOpKind k x))))
  | BinOp k (Val v1) (Val v2) =>
    step_BinOp k v1 v2 mfail
      (fun x1 x2 constr => mreturn (Val (constr (fun_BinOpKind k x1 x2))))
  | RecE es => mmap step_rec_res_to_expr (step_record step_expr es)
  | Get n (RecV vs) => of_option (option_map Val (List.nth_error vs n))
  | Ref (Val v) => mbind mnew
    (fun l => mbind (mstore_at l v)
      (fun _ => mreturn (Val (Lab l))))
  | Deref (Lab l) => mmap Val (mload_at l)
  | Assign (Lab l) (Val v) =>
    mbind (mstore_at l v) (fun _ => mreturn (Val U_val))
  | Seq U_val e => mreturn e
  | If (Bool b) e1 e2 => mreturn (if b then e1 else e2)
  | While e1 e2 => mreturn (If e1 (Seq e2 (While e1 e2)) U_val)
(* structural rules *)
  | App (Val v) e => mbind (step_expr e) (fun e' => mreturn (App v e'))
  | App e1 e2 => mbind (step_expr e1)
    (fun e1' => mreturn (App e1' e2))
  | UnOp k e => mbind (step_expr e) (fun e' => mreturn (UnOp k e'))
  | BinOp k (Val v) e => mbind (step_expr e) (fun e' => mreturn (BinOp k v e'))
  | BinOp k e1 e2 => mbind (step_expr e1)
    (fun e1' => mreturn (BinOp k e1' e2))
  | Ref e => mbind (step_expr e) (fun e' => mreturn (Ref e'))
  | Deref e => mbind (step_expr e) (fun e' => mreturn (Deref e'))
  | Assign (Val v) e => mbind (step_expr e) (fun e' => mreturn (Assign v e'))
  | Assign e1 e2 => mbind (step_expr e1)
    (fun e1' => mreturn (Assign e1' e2))
  | Seq (Val v) e => mbind (step_expr e) (fun e' => mreturn (Seq v e'))
  | Seq e1 e2 => mbind (step_expr e1)
    (fun e1' => mreturn (Seq e1' e2))
  | If e1 e2 e3 => mbind (step_expr e1)
    (fun e1' => mreturn (If e1' e2 e3))
(* invalid patterns *)
  | _ => mfail
  end
.

(* computation of an expression *)
Fixpoint compute_expr {V : Set} (e : Expr V) (fuel : nat) :
  CompMonad V (Value V) :=
  match e with
  | Val v => mreturn v
  | e =>
    match fuel with
    | O => mfail
    | S fuel' => mbind (step_expr e) (fun e' => compute_expr e' fuel')
    end
  end.

(* alternative evaluator *)

(* computation monad with fuel *)
Definition FuelCompMonad (V A : Set) := nat -> CompMonad V (A * nat).

Definition fmreturn {V A : Set} (x : A) : FuelCompMonad V A :=
  fun (fuel : nat) => mreturn (x, fuel).

Definition fmbind {V A B : Set}
  (m : FuelCompMonad V A) (f : A -> FuelCompMonad V B) : FuelCompMonad V B :=
  fun (fuel : nat) => mbind (m fuel)
    (fun '(x, fuel') => f x fuel').

Definition fmmap {V A B : Set}
  (f : A -> B) (m : FuelCompMonad V A) : FuelCompMonad V B :=
  fmbind m (fun x => fmreturn (f x)).

Definition flift {V A : Set} (m : CompMonad V A) : FuelCompMonad V A :=
  fun (fuel : nat) => mmap (fun x => (x, fuel)) m.

Definition fmfail {V A : Set} : FuelCompMonad V A := flift mfail.

Definition fmconsume_fuel {V A : Set}
  (m : FuelCompMonad V A) : FuelCompMonad V A :=
  fun (fuel : nat) =>
  match fuel with
  | O => mfail
  | S fuel' => m fuel'
  end.

(* different computation of an expression *)
Fixpoint pre_compute_expr' {V : Set} (fuel' : nat) (e : Expr V) : FuelCompMonad V (Value V) :=
  match fuel' with
  | O => fmfail
  | S fuel' => let pre_compute_expr' := pre_compute_expr' fuel' in
  (* ^^^ a hack to convince the termination checker ^^^ *)
  fmconsume_fuel
  match e with
  | Val v => fmreturn v
  | App e' e'' =>
    fmbind (pre_compute_expr' e')
    (fun v' => match v' with
      | Lam vf => fmbind (pre_compute_expr' e'')
        (fun v'' => pre_compute_expr' (subst_e vf v''))
      | _ => fmfail
      end)
  | UnOp k e =>
    fmbind (pre_compute_expr' e)
    (fun v => step_UnOp k v fmfail
      (fun x constr => fmreturn (constr (fun_UnOpKind k x))))
  | BinOp k e1 e2  =>
    fmbind (pre_compute_expr' e1)
    (fun v1 => fmbind (pre_compute_expr' e2)
    (fun v2 => step_BinOp k v1 v2 fmfail
        (fun x1 x2 constr => fmreturn (constr (fun_BinOpKind k x1 x2)))))
  | RecE es =>
    fmbind (List.fold_right
      (fun mv macc => fmbind mv
        (fun v => fmbind macc
          (fun acc => fmreturn (v::acc)%list)))
      (fmreturn []%list)
      (List.map pre_compute_expr' es))
      (fun vs => fmreturn (RecV vs))
  | Get n e => fmbind (pre_compute_expr' e)
    (fun v => match v with
      | RecV vs => flift (of_option (List.nth_error vs n))
      | _ => fmfail
      end)
  | Ref e => fmbind (pre_compute_expr' e)
    (fun v => fmbind (flift mnew)
      (fun l => fmbind (flift (mstore_at l v))
        (fun _ => fmreturn (Lab l))))
  | Deref e => fmbind (pre_compute_expr' e)
    (fun v => match v with
      | Lab l => flift (mload_at l)
      | _ => fmfail
      end)
  | Assign e1 e2 => fmbind (pre_compute_expr' e1)
    (fun v1 => match v1 with
      | Lab l => fmbind (pre_compute_expr' e2)
        (fun v2 => fmbind (flift (mstore_at l v2)) (fun _ => fmreturn U_val))
      | _ => fmfail
      end)
  | Seq e1 e2 => fmbind (pre_compute_expr' e1)
    (fun v1 => match v1 with
      | U_val => pre_compute_expr' e2
      | _ => fmfail
      end)
  | If e1 e2 e3 => fmbind (pre_compute_expr' e1)
    (fun v1 => match v1 with
      | Bool b => pre_compute_expr' (if b then e1 else e2)
      | _ => fmfail
      end)
  | While e1 e2 => pre_compute_expr' (If e1 (Seq e2 (While e1 e2)) U_val)
  end
  end.

Definition compute_expr' {V : Set} (e : Expr V) (fuel : nat) :
  CompMonad V (Value V) :=
  mmap fst (pre_compute_expr' (S fuel) e (S fuel)).
