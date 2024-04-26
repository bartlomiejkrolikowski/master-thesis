Require List.
Import List.ListNotations.
Require Import String.
Require Import ZArith.

Require Import src.LambdaRef.
Require Import src.LamRefFacts.
Require Import src.LambdaAssertions.
Require Import src.Tactics.

(* lists *)
Definition v_nil {A : Set} : Value A :=
  (
    RecV [
      Int 0
    ]
  ).

(* cons as a value *)
Definition v_cons {A : Set} (v : Value A) (l : Label) : Value A :=
  (
    RecV [
        Int 1;
        v;
        Lab l
    ]
  )%string.

(* cons as a function *)
Definition f_cons : Expr string :=
  (
    [-\] "x",
      [-\] "xs",
        RecV [
          Int 1;
          Var "x";
          Var "xs"
        ]
  )%string.

Inductive is_list {A : Set} : Value A -> StateAssertion A :=
| is_nil m : is_list v_nil m
| is_cons m : forall v l v',
    Lookup l m v' ->
    is_list v' m ->
    is_list (v_cons v l) m
.

Definition v_of_list {A : Set} (xs : list (Value A)) : Value A * Map A :=
  List.fold_right
    (fun x '(v, m) => let l := new_label m in (v_cons x l, update l v m))
    (v_nil, nil)
    xs.

Fixpoint of_list (l : list (Value string)) : Expr string :=
  match l with
  | []%list => v_nil
  | (x::xs)%list => f_cons <* x <* Ref (of_list xs)
  end.

Lemma is_list_update (A : Set) (v : Value A) (m : Map A) l v' :
  Is_fresh_label l m ->
  is_list v m ->
  is_list v (update l v' m).
Proof with auto.
  intros Hfresh His_list. induction His_list.
  - constructor.
  - econstructor...
    + apply Lookup_update.
      * intros Heq. subst. apply Lookup_success in H...
      * eassumption.
Qed.

(* goal 1 *)
Lemma v_of_list_is_list :
  forall (A : Set) xs (v : Value A) (m : Map A),
    v_of_list xs = (v, m) ->
    is_list v m.
Proof.
  intros. generalize dependent m. generalize dependent v.
  induction xs; simpl; intros v m Heq.
  - injection Heq as [] []. constructor.
  - destruct v_of_list. injection Heq as [] [].
    econstructor.
    + apply Lookup_spec_eq. apply lookup_same.
    + apply is_list_update; auto. apply new_label_is_fresh.
Qed.

Lemma is_list_cons_map (A : Set) (v : Value A) (m : Map A) l v' :
  Is_fresh_label l m ->
  is_list v m ->
  is_list v ((l, v') :: m)%list.
Proof with auto.
  intros Hfresh His_list. induction His_list.
  - constructor.
  - econstructor...
    + constructor...
Qed.

(* goal 2 *)
Lemma f_cons_is_list :
  forall (v vl vl' : Value _) (m m' : Map _) c,
    C[f_cons <* v <* (Ref vl), m ~~> vl', m' | c] ->
    is_list vl m ->
    is_list vl' m'.
Proof.
  intros v vl vl' m m' c Hred. (*remember (f_cons <* v <* vl) as e eqn:He.*)
  repeat match goal with
  | [Hred : cost_red _ _ _ _ _ |- _] =>
    inversion Hred;
    repeat match goal with
    | [H : red _ _ _ _ |- _] => inversion H; subst; clear H
    end;
    cbn in *;
    clear Hred
  end.
  intro His_list.
  fold
    (v_cons
      (bind_v (inc_fun Var (Lab (new_label m'0))) (shift_v v))
      (new_label m'0)).
  econstructor.
  - constructor 1.
  - auto using is_list_cons_map, new_label_is_fresh.
Qed.
