Require List.
Import List.ListNotations.
Require Import String.
Require Import ZArith.

Require Import src.LambdaRef.
Require Import src.LambdaEval.

Definition inc_fun_T {A B : Type} (f : A -> B) (b : B) (oa : option A) : B :=
  match oa with
  | Some a => f a
  | None => b
  end.

(* an expected type of a value *)
Fixpoint type_for_value {V : Set} (f : V -> Set) (v : Value V) : Set :=
  match v with
  | U_val => unit
  | Var x => f x
  | Int _ => Z
  | Bool _ => bool
  | Lab l => Label (* TODO: rethink *)
  | RecV vs => let fix type_for_rec (vs : list (Value V)) :=
      match vs with
      | nil => unit
      | v :: vs' => type_for_value f v * type_for_rec vs'
      end%list%type
    in type_for_rec vs
  | Lam e => type_for_expr (inc_fun_T f unit) e (* TODO: return an arrow type *)
  end
with type_for_expr {V : Set} (f : V -> Set) (e : Expr V) : Set :=
  match e with
  | Val v => type_for_value f v
  | App e1 e2 => type_for_expr f e1 (* TODO: return the codomain of e1 *)
  | UnOp k e => type_of_UnOpKind_ret k
  | BinOp k e1 e2 => type_of_BinOpKind_ret k
  | RecE es => let fix type_for_rec (es : list (Expr V)) :=
      match es with
      | nil => unit
      | e :: es' => type_for_expr f e * type_for_rec es'
      end%list%type
    in type_for_rec es
  | Get n e => Empty_set (* TODO: return the nth type *)
  | Ref e => Label (* TODO: rethink *)
  | Deref e => Empty_set (* TODO: return the type of the stored value *)
  | Assign e1 e2 => unit
  | Seq e1 e2 => type_for_expr f e2
  | If e1 e2 e3 => Empty_set (* TODO: return the type of the expressions *)
  | While e1 e2 => unit
  end.
