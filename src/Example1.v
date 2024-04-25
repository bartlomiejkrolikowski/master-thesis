Require List.
Import List.ListNotations.

Require Import src.LambdaRef.
Require Import src.Tactics.

Definition e : Expr Empty_set := (
  ([let]
  (-\ -\ -\ -\ -\ -\ -\ (
    (Var ($ $ $ $ $ None) <* Var ($ $ $ $ None)) <* Var ($ $ $ None);;
    Var ($ $ $ $ $ $ None) <- (! Var ($ $ None)) <* Var ($ None);;
    Var None
  ))
  [in]
  (-\ (
    Var None <- ! Var None;;
    U_val;;
    Var ($ None)
    <* Var None
    <* (-\ Var None)
    <* (-\ Var ($ None) <- ! (Var None);; U_val)
    <* Var None
    <* Ref (-\ U_val)
    <* (! Var None)
    <* Var None
  ))
  <* Ref U_val
  [end])
).

(* e typechecks *)
Goal T[ env_empty |- e ::: RefT Unit ].
Proof.
  solve_typing.
Qed.

(* trivial proof: e can be reduced to e *)
Goal forall m, exists c, cost_red e m e m c.
Proof.
  solve_computation.
Qed.

(* interesting proof *)
Goal exists l m c,
  cost_red e []%list (Lab l) m c /\
    List.In (l, U_val) m.
Proof.
  unfold e.
  solve_computation.
Qed.
