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
    | [ |- red (UnOp (BUOp BNeg) (Bool _)) _ _ _ ] => eapply red_bneg
    | [ |- red (UnOp (IUOp INeg) (Int _)) _ _ _ ] => eapply red_ineg
    | [ |- red (BinOp (BBOp BOr) (Bool _) (Bool _)) _ _ _ ] => eapply red_bor
    | [ |- red (BinOp (BBOp BAnd) (Bool _) (Bool _)) _ _ _ ] => eapply red_band
    | [ |- red (BinOp (IBOp IAdd) (Int _) (Int _)) _ _ _ ] => eapply red_iadd
    | [ |- red (BinOp (IBOp ISub) (Int _) (Int _)) _ _ _ ] => eapply red_isub
    | [ |- red (BinOp (IBOp IMul) (Int _) (Int _)) _ _ _ ] => eapply red_imul
    | [ |- red (BinOp (IBOp IDiv) (Int _) (Int _)) _ _ _ ] => eapply red_idiv
    | [ |- red (BinOp (CBOp CLt) (Int _) (Int _)) _ _ _ ] => eapply red_clt
    | [ |- red (BinOp (CBOp CEq) (Int _) (Int _)) _ _ _ ] => eapply red_ceq
    | [ |- red (RecE _) _ _ _ ] => eapply red_rec_e2v
    | [ |- red (Get _ (RecV _)) _ _ _ ] => eapply red_rec_get
    | [ |- red (Ref (Val _)) _ _ _ ] => eapply red_ref
    | [ |- red (Deref (Val _)) _ _ _ ] => eapply red_deref
    | [ |- red (Assign (Val _) (Val _)) _ _ _ ] => eapply red_assign
    | [ |- red (Seq (Val _) _) _ _ _ ] => eapply red_seq
    | [ |- red (If (Bool _) _ _) _ _ _ ] => eapply red_if
    | [ |- red (While (Bool _) _) _ _ _ ] => eapply red_while
    | [ |- red (App (Val _) _) _ _ _ ] => eapply red_app2
    | [ |- red (App _ _) _ _ _ ] => eapply red_app1
    | [ |- red (Ref _) _ _ _ ] => eapply red_ref_e
    | [ |- red (Deref _) _ _ _ ] => eapply red_deref_e
    | [ |- red (Assign (Val _) _) _ _ _ ] => eapply red_assign2
    | [ |- red (Assign _ _) _ _ _ ] => eapply red_assign1
    | [ |- red (Seq _ _) _ _ _ ] => eapply red_seq1
    | [ |- red (If _ _ _) _ _ _ ] => eapply red_cond_if
    end
  )).

Ltac solve_computation :=
  intros;
  repeat eexists;
  solve_cost_red solve_red;
  simpl; eauto.
