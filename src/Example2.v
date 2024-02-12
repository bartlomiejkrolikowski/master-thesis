Require List.
Import List.ListNotations.

Require Import src.LambdaRef.

(* map for Ref *)
Definition e : Expr Empty_set := (
  -\ -\ Ref (Var ($ None) <* ! Var None)
).

(* e typechecks *)
Fact type_e (t1 t2 : type) :
  T[ env_empty |- e ::: (t1 --> t2) --> (RefT t1) --> (RefT t2) ].
Proof.
  econstructor. econstructor. econstructor. econstructor.
  Unshelve.
  3:{ exact t1. }
  all: repeat econstructor.
Qed.

(* map for Ref in place *)
Definition e' : Expr Empty_set := (
  -\ -\ Var None <- (Var ($ None) <* ! Var None)
).

(* e' typechecks *)
Fact type_e' (t : type) :
  T[ env_empty |- e' ::: (t --> t) --> (RefT t) --> Unit ].
Proof.
  econstructor. econstructor. econstructor.
  Unshelve.
  3:{ exact t. }
  { econstructor. }
  { econstructor.
    Unshelve.
    3:{ exact t. }
    all: repeat econstructor.
  }
Qed.

Definition e_id : Expr Empty_set := (
  -\ Var None
).

(* e_id typechecks *)
Fact type_e_id (t : type) :
  T[ env_empty |- e_id ::: t --> t ].
Proof.
  econstructor. econstructor.
Qed.

Definition e_ref_u : Expr Empty_set := (
  Ref U_val
).

(* e_ref_u typechecks *)
Fact type_e_ref_u : T[ env_empty |- e_ref_u ::: RefT Unit ].
Proof.
  econstructor. econstructor.
Qed.

(* -------------------------------------------------------- *)

Definition ex : Expr Empty_set := e <* e_id <* e_ref_u.

Fact type_ex : T[ env_empty |- ex ::: RefT Unit ].
Proof.
  econstructor.
  { econstructor.
    { apply type_e. }
    { apply type_e_id. }
  }
  { apply type_e_ref_u. }
Qed.

Goal exists l m c,
  cost_red ex []%list (Lab l) m c /\
  List.In (l, U_val) m.
Proof.
  eexists. eexists. eexists. constructor.
  { econstructor.
    { econstructor. econstructor. }
    { cbn. econstructor.
      { apply red_app2. econstructor. unfold Is_fresh_label.
        simpl. easy.
      }
      { econstructor.
        { econstructor. }
        { cbn. econstructor.
          { econstructor. apply red_app2. econstructor. econstructor. }
          { econstructor.
            { econstructor. econstructor. }
            { cbn. econstructor.
              { econstructor. unfold Is_fresh_label. simpl. shelve. }
              { econstructor. }
            }
          }
        }
      }
    }
  }
  { econstructor. econstructor. }
  Unshelve.
  { constructor. exact 0. }
  { constructor. exact 1. }
  { intro H. destruct H as [H | []]. injection H. easy. }
Qed.

Definition ex' : Expr Empty_set := e' <* e_id <* e_ref_u.

Fact type_ex' : T[ env_empty |- ex' ::: Unit ].
Proof.
  econstructor.
  { econstructor.
    { apply type_e'. }
    { apply type_e_id. }
  }
  { apply type_e_ref_u. }
Qed.

Definition ex'' : Expr Empty_set :=
  (-\ shift_e e' <* shift_e e_id <* Var None ;; Var None) <* e_ref_u.

Fact type_ex'' : T[ env_empty |- ex'' ::: RefT Unit ].
Proof.
  econstructor.
  { econstructor. econstructor.
    { econstructor.
      { econstructor.
        { apply weakening. apply type_e'. }
        { apply weakening. apply type_e_id. }
      }
      { shelve. }
    }
    { shelve. }
  }
  { apply type_e_ref_u. }
  Unshelve.
  { exact Unit. }
  all: constructor.
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
  Unshelve.
  { constructor. exact 0. }
  { exact []%list. }
Qed.
