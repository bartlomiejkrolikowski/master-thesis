Require List.
Import List.ListNotations.
Require Import String.

Require Import src.LambdaRef.
Compute (-\ [-\] "y", -\ -\ -\ -\ -\ (
  (Var ($ $ $ $ $ "y") <* Var ($ $ $ $ None)) <* Var ($ $ $ None);;
  Var ($ $ $ $ $ "x") <- (! Var ($ $ None)) <* Var ($ None);;
  Var None
))%string.
Definition e : Expr _ := (
  ([let]
  ([-\] "x", [-\] "y", -\ -\ -\ -\ -\ (
    (Var ($ $ $ $ $ "y") <* Var ($ $ $ $ None)) <* Var ($ $ $ None);;
    Var ($ $ $ $ $ "x") <- (! Var ($ $ None)) <* Var ($ None);;
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
  )
)%string.

(* e typechecks *)
Goal T[ env_empty |- e ::: RefT Unit ].
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
  eexists. eexists. eexists. econstructor.
  { (*match goal with
  | [ |- cost_red _ _ _ _ _ ] => eapply S_red
  end.
  match goal with
  | [ |- red (App _ _) _ _ _ ] => eapply red_app1
  end.
  match goal with
  | [ |- cost_red ?x _ ?x _ _ ] => eapply no_red
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
  end.
  cbn.
    do 15 try (cbn; match goal with
  | [ |- cost_red ?x _ ?x _ _ ] => eapply no_red
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
  end; cbn).
  idtac 1.
  econstructor.
  eapply red_app1.*)
  (**)
    econstructor.
    { econstructor. econstructor. }
    { cbn. econstructor.
      { apply red_app2. econstructor. unfold Is_fresh_label.
        simpl. easy.
      }
      { econstructor.
        { econstructor. }
        { cbn. econstructor.
          { econstructor. apply red_assign2.
            econstructor. econstructor.
          }
          { econstructor.
            { econstructor. econstructor. econstructor. }
            { econstructor.
              { apply red_seq2, red_seq2. econstructor. econstructor.
                econstructor. econstructor. econstructor. econstructor.
                econstructor.
              }
              { cbn. econstructor.
                { apply red_seq2, red_seq2. econstructor. econstructor.
                  econstructor. econstructor. econstructor. econstructor.
                }
                { cbn. econstructor.
                  { apply red_seq2, red_seq2. econstructor. econstructor.
                    econstructor. econstructor. econstructor.
                  }
                  { cbn. econstructor.
                    { apply red_seq2, red_seq2. econstructor.
                      econstructor. econstructor. econstructor.
                    }
                    { cbn. econstructor.
                      { apply red_seq2, red_seq2. econstructor.
                        econstructor. apply red_app2.
                        econstructor. unfold Is_fresh_label.
                        simpl. shelve.
                      }
                      { econstructor.
                        { apply red_seq2, red_seq2. econstructor.
                          econstructor. econstructor.
                        }
                        { cbn. econstructor.
                          { apply red_seq2, red_seq2. econstructor.
                            apply red_app2. econstructor.
                            apply Lookup_tl, Lookup_hd.
                          }
                          { econstructor.
                            { apply red_seq2, red_seq2. econstructor.
                              econstructor.
                            }
                            { cbn. econstructor.
                              { apply red_seq2, red_seq2. econstructor.
                              }
                              { cbn. econstructor.
                                { apply red_seq2, red_seq2. econstructor.
                                  econstructor. econstructor.
                                }
                                { cbn. econstructor.
                                  { apply red_seq2, red_seq2.
                                    econstructor. econstructor.
                                  }
                                  { cbn. econstructor.
                                    { apply red_seq2, red_seq2.
                                      econstructor. econstructor.
                                      apply red_assign2. econstructor.
                                      apply Lookup_tl, Lookup_hd.
                                    }
                                    { econstructor.
                                      { apply red_seq2, red_seq2.
                                        econstructor. econstructor.
                                        econstructor.
                                        apply Assignment_tl, Assignment_hd.
                                      }
                                      { econstructor.
                                        { apply red_seq2, red_seq2.
                                          econstructor. econstructor.
                                        }
                                        { econstructor.
                                          { apply red_seq2, red_seq2,
                                              red_seq2.
                                            econstructor.
                                            apply red_assign2.
                                            econstructor. econstructor.
                                            econstructor.
                                          }
                                          { econstructor.
                                            { apply red_seq2, red_seq2,
                                                red_seq2.
                                              econstructor.
                                              apply red_assign2.
                                              econstructor.
                                            }
                                            { cbn. econstructor.
                                              { apply red_seq2, red_seq2,
                                                  red_seq2.
                                                econstructor.
                                                econstructor.
                                                apply Assignment_tl,
                                                  Assignment_hd.
                                              }
                                              { econstructor.
                                                { apply red_seq2,
                                                    red_seq2, red_seq2.
                                                  econstructor.
                                                }
                                                { econstructor.
                                                  { apply red_seq2,
                                                      red_seq2.
                                                    econstructor.
                                                  }
                                                  { econstructor.
                                                    { apply red_seq2.
                                                      econstructor.
                                                    }
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
        }
      }
    }
  }
  { simpl. right. left. reflexivity. }
  Unshelve.
  { constructor. exact 0. }
  { exact []%list. }
  { constructor. exact 1. }
  { simpl. intros [H | []]. easy. }
  { exact []%list. }
  { exact []%list. }
Qed.
