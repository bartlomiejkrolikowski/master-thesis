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

Definition cons : Value string :=
  (
    [-\] "x",
      [-\] "xs",
        RecV [
          Var "x";
          Var "xs"
        ]
  )%string.
(*
Fact cons_type :
  forall G n,
    T[ G |- cons ::: IntT --> fl_type n --> fl_type (S n)].
Proof.
  solve_typing.
Qed.
*)
Fixpoint finite_list_value {V : Set} (n : nat) : Value V :=
  match n with
  | 0 => U_val
  | S n' => RecV [
    Int 0;
    finite_list_value n'
  ]
  end.
(*
Goal forall V G n,
  T[ G |- finite_list_value (V := V) n ::: fl_type n ].
Proof.
  intros ? ? ?. induction n.
  - solve_typing.
  - cbn. repeat constructor. assumption.
Qed.
*)
Fixpoint finite_list_expr (n : nat) : Expr string :=
  match n with
  | 0 => U_val
  | S n' => cons <* Int 0 <* finite_list_expr n'
  end.
(*
Goal forall G n,
  T[ G |- finite_list_expr n ::: fl_type n ].
Proof.
  intros ? ?. induction n.
  - solve_typing.
  - cbn. econstructor.
    + econstructor.
      * apply cons_type.
      * constructor.
    + assumption.
Qed.
*)
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
