Require List.
Import List.ListNotations.
Require Import String.
Require Import ZArith.

Require Import src.LambdaRef.
Require Import src.LamRefFacts.
Require Import src.Tactics.

(* lists *)

Definition nil {A : Set} : Value A :=
  (
    RecV [
      Int 0
    ]
  ).

Definition cons : Value string :=
  (
    [-\] "x",
      [-\] "xs",
        RecV [
          Int 1;
          Var "x";
          Var "xs"
        ]
  )%string.

Definition is_nil : Value _ :=
  (
    [-\] "xs",
      Get 0 (Var "xs") [=] Int 0
  )%string.

Definition is_cons : Value _ :=
  (
    [-\] "xs",
      Get 0 (Var "xs") [=] Int 1
  )%string.

Fixpoint list_0_expr (n : nat) : Expr string :=
  match n with
  | 0 => nil
  | S n' => cons <* Int 0 <* Ref (list_0_expr n')
  end.

Fixpoint of_list (l : list Z) : Expr string :=
  match l with
  | []%list => nil
  | (x::xs)%list => cons <* Int x <* Ref (of_list xs)
  end.

Definition list_length : Value string :=
  (
    [-\] "xs",
      [let "xs'"] Ref (Var "xs") [in]
      [let "cnt"] Ref (Int 0) [in]
      [while] is_cons <* ! (Var "xs'") [do]
        Var "cnt" <- ! (Var "cnt") [+] Int 1;;
        Var "xs'" <- Get 2 (! (Var "xs'"))
      [end];;
      ! Var "cnt"
      [end]
      [end]
  )%string.

Goal forall n, list_0_expr n = of_list (List.repeat 0%Z n).
Proof.
  induction n.
  - simpl. reflexivity.
  - simpl. f_equal. f_equal. assumption.
Qed.

Fixpoint of_list_reduced {V} (l : list Z) : Expr V :=
  match l with
  | []%list => nil
  | (x::xs)%list =>
    RecE [
      Val (Int 1);
      Val (Int x);
      Ref (of_list_reduced xs)
    ]
  end.

Require Import src.LamRefFacts.

Goal forall l m mm (v : Value _) mm' c,
  C[ of_list_reduced l, mm ~~> v, mm' | c ] ->
  exists m' c',
  C[ of_list l, m ~~> v, m' | c' ].
Proof.
  intros l m mm v mm' c. generalize dependent v. induction l.
  - simpl. intros v HCRed. apply cost_red_value in HCRed as [Hv [Hmm Hc]].
    rewrite Hv. repeat eexists. econstructor.
  - simpl. intros v HCRed. inversion HCRed. subst.
    inversion H.
    + subst. specialize vals2exprs_are_vals with _ vs as Hvs.
      rewrite H2 in Hvs.
      match goal with
      | [H : List.Forall ?P ?l |- _] =>
        destruct (List.Forall_forall P l) as [Hlemma _]
      end.
      apply Hlemma with (Ref (of_list_reduced l)) in Hvs as [v' Heqv'].
      * discriminate.
      * simpl. auto.
    + subst. destruct is_value_or_not with (e := e) as [[v' Hisval] | Hnval].
      * subst. apply red_value in H4. contradiction.
      * apply SplitAt_spec_eq in H2.
        specialize List.in_elt with _ e (vals2exprs vs0) es0 as Hin_elt.
        simpl in H2. rewrite <- H2 in Hin_elt.
        simpl in Hin_elt.
        destruct Hin_elt as [He | [He | [He | He]]];
        try match goal with
        | [H : Val ?v = e |- _] => symmetry in H; apply Hnval in H
        end;
        try contradiction.
        subst.
        inversion H4.
        -- subst.
        assert (vs0 = [Int 1; Int a] /\ es0 = [])%list as [Hvs0 Hes0].
        { admit. }
        subst. simpl in H2.
        eauto. discriminate.
    destruct IHl as [m'' [c'' Hred'']].
    + assumption.
   repeat eexists. simpl.
    eapply cost_red_comp.
    { eapply cost_red_app1. eapply cost_red_comp.
      { eapply cost_red_app2. econstructor. }
      { eapply S_red.
        { solve_red. }
        { cbn. econstructor. }
      }
    }
    { eapply cost_red_comp.
      { eapply cost_red_app2. eapply cost_red_ref_e.
        eapply Hred.
      }
      { (* TODO*) }
    }
Admitted.

Goal forall (l : list Z) m, exists m' c,
  C[ list_length <* of_list l, m ~~> Int (Z.of_nat (List.length l)), m' | c ].
Proof.
  repeat eexists.
  eapply cost_red_comp.
  { eapply cost_red_app2. admit. }
Admitted.

(*Goal forall (l : list Z) (v : Value _) m0 m c,
  C[ of_list l, m0 ~~> v, m | c ] -> exists m' c',
  C[ list_length <* v, m ~~> Int (Z.of_nat (List.length l)), m' | c' ].
Proof.
  repeat eexists.
  econstructor.
  { econstructor. }
  { cbn. econstructor.
      { eapply red_app2. econstructor. exact (has_fresh _ m). }
      { econstructor.
        { econstructor. }
        { cbn. econstructor.
          { eapply red_app2. econstructor. exact (has_fresh _ (_ :: m)%list). }
          { econstructor.
            { econstructor. }
            { cbn. econstructor.
              { econstructor. revert l v m0 m c H. induction l.
  - cbn. intros. inversion H. 2:inversion H0. subst.
    eapply red_while with (e1 := ((-\ Get 0 (Var None) [=] Int 1) <* (! Lab (get_fresh m)))).
  - (* TODO *) cbn in *. intros. inversion H. subst. inversion H0. subst.
    inversion H7.
    { cbn in *. subst. destruct get_fresh. eapply red_while. inversion H1. subst.
    inversion H2.
    { subst. inversion H10. }
    { subst. inversion H10.
      { subst. } } }
   econstructor. eapply red_app2. econstructor.
                eapply Lookup_tl. econstructor. }
               econstructor. eapply red_app2. econstructor.
                eapply Lookup_tl. econstructor. }
              { econstructor.
                { econstructor. econstructor. econstructor. }
                { cbn. econstructor.
                  { econstructor. econstructor. econstructor. econstructor. econstructor. }
                  { econstructor.
                    { econstructor. econstructor. econstructor. }
                    { cbn. econstructor.
                      { econstructor. econstructor. }
                      { econstructor.
                        { eapply red_seq2. econstructor. econstructor. }
                        { econstructor.
                          { econstructor. }
                          { econstructor. }
                         }
                      }
                    }
                  }
                }
              }
             }
           }
         }
       }
  }
  induction l.
  + (*solve_computation.*) cbn.
    repeat eexists. econstructor.
    { econstructor. }
    { cbn. econstructor.
      { eapply red_app2. econstructor. unfold Is_fresh_label. cbn. easy. }
      { econstructor.
        { econstructor. }
        { cbn. econstructor.
          { eapply red_app2. econstructor. unfold Is_fresh_label. cbn. shelve. }
          { econstructor.
            { econstructor. }
            { cbn. econstructor.
              { econstructor. econstructor. eapply red_app2. econstructor.
                eapply Lookup_tl. econstructor. }
              { econstructor.
                { econstructor. econstructor. econstructor. }
                { cbn. econstructor.
                  { econstructor. econstructor. econstructor. econstructor. econstructor. }
                  { econstructor.
                    { econstructor. econstructor. econstructor. }
                    { cbn. econstructor.
                      { econstructor. econstructor. }
                      { econstructor.
                        { eapply red_seq2. econstructor. econstructor. }
                        { econstructor.
                          { econstructor. }
                          { econstructor. }
                         }
                      }
                    }
                  }
                }
              }
             }
           }
         }
       }
    }
    Unshelve.
    { constructor. exact 0. }
    { constructor. exact 1. }
    { intros [ H' | [] ]. discriminate. }
  + repeat eexists. cbn. rewrite Zpos_P_of_succ_nat. econstructor.
Qed.
*)
(*Goal forall (l : list Z) , exists m' c,
  C[ list_length <* of_list l, []%list ~~> Int (Z.of_nat (List.length l)), m' | c ].
Proof.
  induction l.
  + (*solve_computation.*) cbn.
    repeat eexists. econstructor.
    { econstructor. }
    { cbn. econstructor.
      { eapply red_app2. econstructor. unfold Is_fresh_label. cbn. easy. }
      { econstructor.
        { econstructor. }
        { cbn. econstructor.
          { eapply red_app2. econstructor. unfold Is_fresh_label. cbn. shelve. }
          { econstructor.
            { econstructor. }
            { cbn. econstructor.
              { econstructor. econstructor. eapply red_app2. econstructor.
                eapply Lookup_tl. econstructor. }
              { econstructor.
                { econstructor. econstructor. econstructor. }
                { cbn. econstructor.
                  { econstructor. econstructor. econstructor. econstructor. econstructor. }
                  { econstructor.
                    { econstructor. econstructor. econstructor. }
                    { cbn. econstructor.
                      { econstructor. econstructor. }
                      { econstructor.
                        { eapply red_seq2. econstructor. econstructor. }
                        { econstructor.
                          { econstructor. }
                          { econstructor. }
                         }
                      }
                    }
                  }
                }
              }
             }
           }
         }
       }
    }
    Unshelve.
    { constructor. exact 0. }
    { constructor. exact 1. }
    { intros [ H | [] ]. discriminate. }
  + repeat eexists. cbn. econstructor.
Qed.
*)