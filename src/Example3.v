Require List.
Import List.ListNotations.
Require Import String.

Require Import src.LambdaRef.
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
  repeat econstructor; simpl;
  match goal with
  | [ |- T[ ?G |- Val (Var ?x) ::: ?t ] ] => apply (T_Var G x)
  end.
Qed.

(* trivial proof: e can be reduced to e *)
Goal forall m, exists c, cost_red e m e m c.
Proof.
  exists 0. constructor.
Qed.

Ltac solve_cost_red x :=
  repeat (eapply no_red || (eapply S_red; [ x | ])).

Ltac solve_red :=
  repeat (cbn; (
    match goal with
    | [ |- exists _, _ ] => eexists
    | [ |- Is_fresh_label _ _ ] =>
      unfold Is_fresh_label; try easy; shelve
    | [ |- _ /\ _ ] => split
    | [ |- Lookup ?l ((?l, _) :: _ )%list _ ] => eapply Lookup_hd
    | [ |- Lookup _ _ _ ] => eapply Lookup_tl
    | [ |- Assignment ?l _ ((?l, _) :: _ )%list _ ] => eapply Assignment_hd
    | [ |- Assignment _ _ _ _ ] => eapply Assignment_tl
    | [ |- cost_red ?e _ ?e _ _ ] => eapply no_red
    | [ |- cost_red _ _ _ _ _ ] => eapply S_red
    | [ |- red (App (Val _) (Val _)) _ _ _ ] => eapply red_lam
    | [ |- red (Ref (Val _)) _ _ _ ] => eapply red_ref
    | [ |- red (Deref (Val _)) _ _ _ ] => eapply red_deref
    | [ |- red (Assign (Val _) (Val _)) _ _ _ ] => eapply red_assign
    | [ |- red (Seq (Val _) (Val _)) _ _ _ ] => eapply red_seq
    | [ |- red (App (Val _) _) _ _ _ ] => eapply red_app2
    | [ |- red (App _ _) _ _ _ ] => eapply red_app1
    | [ |- red (Ref _) _ _ _ ] => eapply red_ref_e
    | [ |- red (Deref _) _ _ _ ] => eapply red_deref_e
    | [ |- red (Assign (Val _) _) _ _ _ ] => eapply red_assign2
    | [ |- red (Assign _ _) _ _ _ ] => eapply red_assign1
    | [ |- red (Seq (Val _) _) _ _ _ ] => eapply red_seq2
    | [ |- red (Seq _ _) _ _ _ ] => eapply red_seq1
    end
  )).

Ltac solve_computation := solve_cost_red solve_red.

(* interesting proof *)
Goal exists l m c,
  cost_red e []%list (Lab l) m c /\
    List.In (l, U_val) m.
Proof.
  unfold e.
  repeat eexists.
  {
    solve_computation.
  }
  {
    simpl. eauto.
  }
  Unshelve.
  { econstructor. exact 0. }
  { exact []%list. }
  { econstructor. exact 1. }
  { exact []%list. }
  { exact []%list. }
  { simpl. intros [ ? | [] ]. easy. }
Qed.
