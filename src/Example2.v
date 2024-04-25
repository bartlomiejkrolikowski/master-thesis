Require List.
Import List.ListNotations.

Require Import src.LambdaRef.
Require Import src.Tactics.

(* map for Ref *)
Definition e : Expr Empty_set := (
  -\ -\ Ref (Var ($ None) <* ! Var None)
).

(* e typechecks *)
Fact type_e (t1 t2 : type) :
  T[ env_empty |- e ::: (t1 --> t2) --> (RefT t1) --> (RefT t2) ].
Proof.
  solve_typing.
Qed.

(* map for Ref in place *)
Definition e' : Expr Empty_set := (
  -\ -\ Var None <- (Var ($ None) <* ! Var None)
).

(* e' typechecks *)
Fact type_e' (t : type) :
  T[ env_empty |- e' ::: (t --> t) --> (RefT t) --> Unit ].
Proof.
  solve_typing.
Qed.

Definition e_id : Expr Empty_set := (
  -\ Var None
).

(* e_id typechecks *)
Fact type_e_id (t : type) :
  T[ env_empty |- e_id ::: t --> t ].
Proof.
  solve_typing.
Qed.

Definition e_ref_u : Expr Empty_set := (
  Ref U_val
).

(* e_ref_u typechecks *)
Fact type_e_ref_u : T[ env_empty |- e_ref_u ::: RefT Unit ].
Proof.
  solve_typing.
Qed.

(* -------------------------------------------------------- *)

Definition ex : Expr Empty_set := e <* e_id <* e_ref_u.

Fact type_ex : T[ env_empty |- ex ::: RefT Unit ].
Proof.
  solve_typing.
Qed.

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

Definition ex' : Expr Empty_set := e' <* e_id <* e_ref_u.

Fact type_ex' : T[ env_empty |- ex' ::: Unit ].
Proof.
  solve_typing.
Qed.

Definition ex'' : Expr Empty_set :=
  (-\ shift_e e' <* shift_e e_id <* Var None ;; Var None) <* e_ref_u.

Fact type_ex'' : T[ env_empty |- ex'' ::: RefT Unit ].
Proof.
  solve_typing.
Qed.

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
