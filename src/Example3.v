Require List.
Import List.ListNotations.
Require Import String.

Require Import src.LambdaRef.
Require Import src.Tactics.
Compute (
  [let "y"]
  Ref U_val
  [in]
  [let "x"]
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
    <* (-\ Var None)
    <* (-\ Var ($ "y") <- ! (Var None);; U_val)
    <* Var "y"
    <* Ref (-\ U_val)
    <* (! Var "y")
    <* Var "y"
  )
)%string.
Definition e : Expr _ := (
  [let "y"]
  Ref U_val
  [in]
  [let "x"]
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
    <* (-\ Var None)
    <* (-\ Var ($ "y") <- ! (Var None);; U_val)
    <* Var "y"
    <* Ref (-\ U_val)
    <* (! Var "y")
    <* Var "y"
  )
)%string.

(* e typechecks *)
Goal forall G, T[ G |- e ::: RefT Unit ].
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
  Unshelve.
  { econstructor. exact 0. }
  { exact []%list. }
  { econstructor. exact 1. }
  { exact []%list. }
  { exact []%list. }
  { simpl. intros [ ? | [] ]. easy. }
Qed.