Require List.
Import List.ListNotations.

Require Import src.LambdaRef.

Definition e : Expr Empty_set := (
  ([let]
  (-\ -\ -\ -\ -\ -\ -\ (
    (Var ($ $ $ $ $ None) <* Var ($ $ $ $ None)) <* Var ($ $ $ None);;
    Var ($ $ $ $ $ $ None) <- (! Var ($ $ None)) <* Var ($ None);;
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
).

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
  eexists. eexists. eexists. econstructor.
  { econstructor.
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
