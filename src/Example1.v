Require List.
Import List.ListNotations.
Require Import String.

Require Import src.LambdaRef.
Require Import src.Tactics.

Definition e : Expr := (
  ([let] "s" :=
  ([-\] "x", [-\] "y", [-\] "z", [-\] "u", [-\] "v", [-\] "w", [-\] "t", (
    (Var "y" <* Var "z") <* Var "u";;
    Var "x" <- (! Var "v") <* Var "w";;
    Var "t"
  ))
  [in]
  ([-\] "x", (
    Var "x" <- ! Var "x";;
    U_val;;
    Var "s"
    <* Var "x"
    <* ([-\] "y", Var "y")
    <* ([-\] "z", Var "x" <- ! (Var "z");; U_val)
    <* Var "x"
    <* Ref ([-\] "u", U_val)
    <* (! Var "x")
    <* Var "x"
  ))
  <* Ref U_val
  [end])
).

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
