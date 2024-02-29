Require Import src.LambdaRef2.

Inductive is_value {V : Set} : Expr V -> Prop :=
| is_val : forall v : Value V, is_value v.

(** Safety property *)
Definition Safe {V : Set} (e : Expr V) : Prop :=
  forall m e' m' c, cost_red e m e' m' c ->
    is_value e' \/ exists e'' m'', red e' m' e'' m''.


