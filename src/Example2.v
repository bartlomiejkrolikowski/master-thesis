Require List.
Import List.ListNotations.
Require Import String.

Require Import src.LambdaRef.
Require Import src.Tactics.

(* map for Ref *)
Definition e : Expr := (
  [-\] "x", [-\] "y",  Ref (Var "x" <* ! Var "y")
).

(* map for Ref in place *)
Definition e' : Expr := (
  [-\] "x", [-\] "y", Var "y" <- (Var "x" <* ! Var "y")
).

Definition e_id : Expr := (
  [-\] "x", Var "x"
).

Definition e_ref_u : Expr := (
  Ref U_val
).

(* -------------------------------------------------------- *)

Definition ex : Expr := e <* e_id <* e_ref_u.

Goal exists l m c,
  cost_red ex []%list (Lab l) m c /\
  List.In (l, U_val) m.
Proof.
  eexists. eexists. eexists. constructor.
  { econstructor.
    { econstructor. econstructor. }
    { cbn. econstructor.
      { apply red_app2. econstructor. simpl. easy. }
      { econstructor.
        { econstructor. }
        { cbn. econstructor.
          { econstructor. apply red_app2. econstructor. econstructor. }
          { econstructor.
            { econstructor. econstructor. }
            { cbn. econstructor.
              { econstructor. reflexivity. }
              { econstructor. }
            }
          }
        }
      }
    }
  }
  { econstructor. econstructor. }
Qed.

Definition ex' : Expr := e' <* e_id <* e_ref_u.

Definition ex'' : Expr :=
  ([-\] "x", e' <* e_id <* Var "x" ;; Var "x") <* e_ref_u.

Goal exists l m c,
  cost_red ex'' []%list (Lab l) m c /\
  List.In (l, U_val) m.
Proof.
  eexists. eexists. eexists. constructor.
  { econstructor.
    { eapply red_app2. econstructor. unfold Is_fresh_label.
      simpl. easy.
    }
    { cbn. econstructor.
      { econstructor. }
      { cbn. econstructor.
        { econstructor. econstructor. econstructor. }
        { cbn. econstructor.
          { econstructor. econstructor. }
          { cbn. econstructor.
            { econstructor. apply red_assign2. apply red_app2.
              econstructor. econstructor.
            }
            { econstructor.
              { econstructor. apply red_assign2. econstructor. }
              { econstructor.
                { cbn. econstructor. econstructor. econstructor. }
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
  { constructor. constructor. }
Qed.
