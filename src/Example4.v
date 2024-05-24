Require List.
Import List.ListNotations.
Require Import String.
Require Import ZArith.

Require Import src.LambdaRef.
Require Import src.Tactics.

(* finite list *)

Fixpoint fl_type (n : nat) : type :=
  match n with
  | 0 => Unit
  | S n' => RecT [
    IntT;
    fl_type n'
  ]
  end.

Definition cons : Value :=
  (
    [-\] "x",
      [-\] "xs",
        RecV [
          Var "x";
          Var "xs"
        ]
  )%string.

Fixpoint finite_list_value (n : nat) : Value :=
  match n with
  | 0 => U_val
  | S n' => RecV [
    Int 0;
    finite_list_value n'
  ]
  end.

Fixpoint finite_list_expr (n : nat) : Expr :=
  match n with
  | 0 => U_val
  | S n' => cons <* Int 0 <* finite_list_expr n'
  end.

Goal forall n m,
  exists c, C[finite_list_expr n, m ~~> finite_list_value n, m | c].
Proof.
  intros. induction n; eexists; simpl.
  - solve_computation.
  - econstructor. econstructor. econstructor. cbn. econstructor.
    eapply red_app2.
    Abort.
(*    destruct IHn as [c H]. econstructor.
Qed.*)
