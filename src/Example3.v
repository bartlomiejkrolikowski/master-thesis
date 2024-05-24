Require List.
Import List.ListNotations.
Require Import String.

Require Import src.LambdaRef.
Require Import src.Tactics.
Compute (
  [let] "y" :=
  Ref U_val
  [in]
  [let] "x" :=
  ([-\] "x", [-\] "y", [-\] "z", [-\] "u", [-\] "v", [-\] "w",
    [-\] "t", (
    (Var "y" <* Var "z") <* Var "u";;
    Var "x" <- (! Var "v") <* Var "w";;
    Var "t"
  ))
  [in]
  (
    Var "y" <- ! Var "y";;
    U_val;;
    Var "x"
    <* Var "y"
    <* ([-\] "z", Var "z")
    <* ([-\] "u", Var "y" <- ! (Var "u");; U_val)
    <* Var "y"
    <* Ref ([-\] "v", U_val)
    <* (! Var "y")
    <* Var "y"
  )
  [end]
  [end]
)%string.
Definition e : Expr := (
  [let] "y" :=
  Ref U_val
  [in]
  [let] "x" :=
  ([-\] "x", [-\] "y", [-\] "z", [-\] "u", [-\] "v", [-\] "w",
    [-\] "t", (
    (Var "y" <* Var "z") <* Var "u";;
    Var "x" <- (! Var "v") <* Var "w";;
    Var "t"
  ))
  [in]
  (
    Var "y" <- ! Var "y";;
    U_val;;
    Var "x"
    <* Var "y"
    <* ([-\] "z", Var "z")
    <* ([-\] "u", Var "y" <- ! (Var "u");; U_val)
    <* Var "y"
    <* Ref ([-\] "v", U_val)
    <* (! Var "y")
    <* Var "y"
  )
  [end]
  [end]
)%string.

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
