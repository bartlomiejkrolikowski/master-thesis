Require Import src.LambdaRef.

Ltac solve_typing :=
  repeat econstructor; simpl;
  match goal with
  | [ |- T[ ?G |- Val (Var ?x) ::: ?t ] ] => apply (T_Var G x)
  end.

Ltac solve_cost_red x :=
  repeat (eapply no_red || (eapply S_red; [ x | ])).

Ltac solve_red :=
  repeat (cbn; (
    match goal with
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

Ltac solve_computation :=
  intros;
  repeat eexists;
  solve_cost_red solve_red;
  simpl; eauto.
