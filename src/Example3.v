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

(* interesting proof *)
Goal exists l m c,
  cost_red e []%list (Lab l) m c /\
    List.In (l, U_val) m.
Proof.
  unfold e.
  do 30 try (cbn; (
    match goal with
    | [ |- exists _, _ ] => eexists
    end
    + match goal with
      | [ |- _ /\ _ ] => split
      end
    + easy
    + match goal with
      | [ |- Lookup ?l ((?l, _) :: _ )%list _ ] => eapply Lookup_hd
      | [ |- Lookup _ _ _ ] => eapply Lookup_tl
      end
    + match goal with
      | [ |- Assignment ?l _ ((?l, _) :: _ )%list _ ] => eapply Assignment_hd
      | [ |- Assignment _ _ _ _ ] => eapply Assignment_tl
      end
    + match goal with
      | [ |- cost_red ?e _ ?e _ _ ] => eapply no_red
      | [ |- cost_red _ _ _ _ _ ] => eapply S_red
      end
    + match goal with
      | [ |- red (App (Val _) (Val _)) _ _ _ ] => eapply red_lam
      end
    + match goal with
      | [ |- red (Ref (Val _)) _ _ _ ] => eapply red_ref
      end
    + match goal with
      | [ |- red (Deref (Val _)) _ _ _ ] => eapply red_deref
      end
    + match goal with
      | [ |- red (Assign (Val _) (Val _)) _ _ _ ] => eapply red_assign
      end
    + match goal with
      | [ |- red (Seq (Val _) (Val _)) _ _ _ ] => eapply red_seq
      end
    + match goal with
      | [ |- red (App (Val _) _) _ _ _ ] => eapply red_app2
      end
    + match goal with
      | [ |- red (App _ _) _ _ _ ] => eapply red_app1
      end
    + match goal with
      | [ |- red (Ref _) _ _ _ ] => eapply red_ref_e
      end
    + match goal with
      | [ |- red (Deref _) _ _ _ ] => eapply red_deref_e
      end
    + match goal with
      | [ |- red (Assign (Val _) _) _ _ _ ] => eapply red_assign2
      end
    + match goal with
      | [ |- red (Assign _ _) _ _ _ ] => eapply red_assign1
      end
    + match goal with
      | [ |- red (Seq (Val _) _) _ _ _ ] => eapply red_seq2
      end
    + match goal with
      | [ |- red (Seq _ _) _ _ _ ] => eapply red_seq1
      end
    + match goal with
      | [ |- red (subst_e _ _) _ _ _ ] => cbn
      end
    + match goal with
      | [ |- red (Val _) _ _ _ ] => fail
      end
  ); cbn).
  2:econstructor.
  2:econstructor.
  2:econstructor.
unfold Is_fresh_label. simpl.
Qed.
