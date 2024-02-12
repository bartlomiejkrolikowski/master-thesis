Require List.
Import List.ListNotations.

Require Import src.LambdaRef.

Definition t : Expr Empty_set := (
  (-\ -\ (
    Var ($ None) <- Var ($ None);;
    U_val;;
    Var None
    <* Var ($ None)
    <* (-\ Var ($ $ None))
    <* (-\ Var ($ None) <- ! (Var ($ $ None));; U_val)
    <* Var ($ None)
    <* Ref (-\ U_val)
    <* ! Var ($ None)
    <* Var ($ None)
  ))
  <* (-\ -\ -\ -\ -\ -\ -\ (
    Var ($ None) <* Var ($ $ None) <* Var ($ $ $ None);;
    Var None <- (! Var ($ $ $ $ None)) <* Var ($ $ $ $ $ $ None);;
    Var ($ $ $ $ $ None)
  ))
  <* Ref U_val
).

(* t typechecks *)
Goal T[ env_empty |- t ::: RefT Unit ].
Proof.
  econstructor.
  { econstructor.
    { econstructor. econstructor. econstructor.
      { econstructor.
        { shelve. }
        { econstructor. }
      }
      { econstructor.
        { econstructor. }
        { econstructor.
          { econstructor.
            { econstructor.
              { econstructor.
                { econstructor.
                  { econstructor.
                    { shelve. }
                    { econstructor. }
                  }
                  { econstructor. econstructor. }
                }
                { econstructor. econstructor.
                  { econstructor.
                    { shelve. }
                    { shelve. }
                  }
                  { econstructor. }
                }
              }
              { econstructor. }
            }
            { econstructor. econstructor. econstructor. }
          }
          { econstructor.
            { econstructor. shelve. }
            { econstructor. }
          }
        }
      }
    }
    { econstructor. econstructor. econstructor. econstructor.
      econstructor. econstructor. econstructor. econstructor.
      { econstructor.
        { econstructor.
          { shelve. }
          { econstructor. }
        }
        { econstructor. }
      }
      { econstructor.
        { econstructor.
          { shelve. }
          { econstructor.
            { econstructor. shelve. }
            { econstructor. }
          }
        }
        { econstructor. }
      }
    }
  }
  { econstructor. econstructor. }
  Unshelve. all: simpl.
  (* TODO *)
  { simpl. econstructor. }
Qed.

(* trivial proof: t can be reduced to t *)
Goal forall m, exists c, cost_red t m t m c.
Proof.
  exists 0. constructor.
Qed.

(* interesting proof *)
Goal exists c l,
  cost_red
    t []%list
    (Lab l) [(l, U_val)]%list
    c.
Proof.
  eexists. eexists. econstructor.
  { econstructor. econstructor. }
  { simpl. econstructor.
    { apply red_app2. econstructor. unfold Is_fresh_label.
      simpl. easy.
    }
    { econstructor.
      { econstructor. }
      { simpl. econstructor.
  { econstructor. econstructor. econstructor. }
  { econstructor.
    { apply red_seq2, red_seq2.
      econstructor. econstructor. econstructor. econstructor.
      econstructor. econstructor. }
    { simpl. econstructor.
      { apply red_seq2, red_seq2.
        econstructor. econstructor. econstructor. econstructor.
        econstructor.
      }
      { simpl. econstructor.
        { apply red_seq2, red_seq2.
          econstructor. econstructor. econstructor. econstructor.
        }
        { simpl. econstructor.
          { apply red_seq2, red_seq2.
            econstructor. econstructor. econstructor.
          }
          { simpl. econstructor.
            { apply red_seq2, red_seq2.
              econstructor. apply red_app2.
              econstructor. unfold Is_fresh_label. simpl. intro H.
              shelve.
            }
            { econstructor.
              { apply red_seq2, red_seq2.
                econstructor. econstructor.
              }
              { simpl. econstructor.
                { apply red_seq2, red_seq2.
                  apply red_app2.
                  econstructor. econstructor. econstructor.
                }
                { econstructor.
                  { apply red_seq2, red_seq2. apply red_app2.
                    econstructor.
                  }
                  { simpl. econstructor.
                  { apply red_seq2, red_seq2.
                    econstructor.
                  }
                  { simpl. econstructor.
                    { apply red_seq2, red_seq2.
                      econstructor. econstructor. econstructor.
                    }
                    { simpl. econstructor.
                      { apply red_seq2, red_seq2.
                        econstructor. econstructor.
                      }
                      { simpl. econstructor.
                        { apply red_seq2, red_seq2.
                          econstructor. econstructor. apply red_assign2.
                          econstructor. econstructor. econstructor.
                        }
                        { econstructor.
                          { apply red_seq2, red_seq2.
                            econstructor. econstructor. econstructor.
                            econstructor. econstructor.
                          }
                          { econstructor.
                            { apply red_seq2, red_seq2.
                              econstructor. econstructor.
                            }
                            { econstructor.
                              { apply red_seq2, red_seq2, red_seq2.
                                econstructor. apply red_assign2.
                                econstructor. econstructor.
                                econstructor.
                              }
                              { econstructor.
                                { apply red_seq2, red_seq2, red_seq2.
                                  econstructor. apply red_assign2.
                                  econstructor.
                                }
                                { simpl. econstructor.
                                  { apply red_seq2, red_seq2, red_seq2.
                                    econstructor. econstructor.
                                    econstructor. econstructor.
                                  }
                                  { econstructor.
                                    { apply red_seq2, red_seq2, red_seq2.
                                      econstructor.
                                    }
                                    { econstructor.
                                      { apply red_seq2, red_seq2.
                                        econstructor.
                                      }
                                      { econstructor.
                                        { apply red_seq2.
                                          econstructor.
                                        }
                                        { econstructor.
                                          { econstructor. }
                                          { eapply no_red. }
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
  Unshelve.
  { exact []%list. }
  { simpl in H. exact H. }
  { exact []%list. }
Qed.
