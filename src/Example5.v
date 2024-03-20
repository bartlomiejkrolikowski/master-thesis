Require List.
Import List.ListNotations.
Require Import String.
Require Import ZArith.

Require Import src.LambdaRef.
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

Definition get_fresh {V : Set} (m : Map V) : Label :=
  List.fold_right
    (fun '(OfNat l, _) '(OfNat acc) => OfNat (S (max l acc))) (OfNat 0) m.

Lemma has_fresh : forall V (m : Map V), Is_fresh_label (get_fresh m) m.
Proof.
  induction m.
  + unfold Is_fresh_label. cbn. easy.
  + unfold Is_fresh_label. destruct a. destruct l. simpl. destruct (get_fresh m).
    intro.
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