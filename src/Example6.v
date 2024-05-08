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
Definition f_cons : Value string :=
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

Fixpoint e_of_list (l : list (Value string)) : Expr string :=
  match l with
  | []%list => v_nil
  | (x::xs)%list => f_cons <* x <* Ref (e_of_list xs)
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

Fact f_cons_app_expr :
  forall (e : Expr _) (v vl : Value _) (m m' m'' : Map _) c c',
    C[e, m ~~> v, m' | c] ->
    C[f_cons <* v, m' ~~> vl, m'' | c'] ->
    C[f_cons <* e, m ~~> vl, m'' | c + c'].
Proof.
  eauto using cost_red_comp, cost_red_app2.
Qed.

Fact f_cons_app_expr2 :
  forall (e el : Expr _) (v vl vl' : Value _) (m m' m'' m''' : Map _) c c' c'',
    Is_Valid_Map m ->
    C[e, m ~~> v, m' | c] ->
    C[el, m' ~~> vl, m'' | c'] ->
    C[f_cons <* v <* vl, m'' ~~> vl', m''' | c''] ->
    exists c''', C[f_cons <* e <* el, m ~~> vl', m''' | c'''].
Proof.
  intros e el v vl vl' m m' m'' m''' c c' c'' Hvalid Hred1 Hred2 Hred3.
  eassert (forall m0, C[f_cons <* v, m0 ~~> _, m0 | 1]) as Hred.
  { econstructor 2; cbn; econstructor. }
  cbn in *. remember (-\ RecV [Int 1; shift_v v; Var None]) as vl'' eqn:Hvl''.
  assert (C[f_cons <* e, m ~~> vl'', m' | c + 1]) as Hred'.
  { subst. eapply f_cons_app_expr; eauto. }
  eassert (forall m0, C[ vl'' <* vl, m0 ~~> _, m0 | 1]) as Hred''.
  { subst. econstructor 2; cbn; econstructor. }
  cbn in *.
  remember (RecV [Int 1; bind_v (inc_fun Var vl) (shift_v v); vl])
    as vl''' eqn:Hvl'''.
  assert (C[f_cons <* e <* el, m ~~> vl'' <* vl, m'' | (c + 1) + c'])
    as Hred'''.
  { eapply cost_red_comp.
    + eapply cost_red_app1. eassumption.
    + eapply cost_red_app2. eassumption. }
  assert (C[f_cons <* e <* el, m ~~> vl''', m'' | ((c + 1) + c') + 1])
    as Hred''''.
  { eapply cost_red_comp; eauto. }
  assert (forall m0, C[f_cons <* v <* vl, m0 ~~> vl'' <* vl, m0 | 1])
    as Hred'''''.
  { subst. econstructor 2; repeat econstructor. }
  assert (forall m0, C[f_cons <* v <* vl, m0 ~~> vl''', m0 | 2])
    as Hred''''''.
  { subst. econstructor 2; repeat econstructor. }
  assert (Is_Valid_Map m') as Hvalid'.
  { edestruct uniqueness_full as [? [? ?]].
    + eassumption.
    + apply Hred1.
    + eassumption.
    + assumption. }
  assert (Is_Valid_Map m'') as Hvalid''.
  { edestruct uniqueness_full as [? [? ?]].
    + eassumption.
    + apply Hred2.
    + eassumption.
    + assumption. }
  destruct (uniqueness_full _ _ _ _ _ _ _ _ _ Hvalid'' Hred3 (Hred'''''' m''))
    as [? [? ?]].
  subst. eauto.
Qed.

(* goal 3 *)
Lemma f_cons_red_to_list :
  forall (e el : Expr _) l (v vl vl' : Value _) (m m' m'' m''' m'''' : Map _)
    c c' c'' c''',
    Is_Valid_Map m ->
    C[e, m ~~> v, m' | c] ->
    C[el, m' ~~> vl, m'' | c'] ->
    C[Ref vl, m'' ~~> Lab l, m''' | c''] ->
    C[f_cons <* e <* Ref el, m ~~> vl', m'''' | c'''] ->
    is_list vl m'' ->
    is_list vl' m''''.
Proof.
  intros e el l v vl vl' m m' m'' m''' m'''' c c' c'' c'''
    Hvalid Hred Hred1 Hred2 Hred3 His_list.
  assert (Is_Valid_Map m') as Hvalid'.
  { edestruct uniqueness_full as [? [? ?]].
    + eassumption.
    + apply Hred.
    + eassumption.
    + assumption. }
  assert (Is_Valid_Map m'') as Hvalid''.
  { edestruct uniqueness_full as [? [? ?]].
    + eassumption.
    + apply Hred1.
    + eassumption.
    + assumption. }
  eassert (C[Ref el, m' ~~> Lab l, m''' | c' + c'']) as Hred'.
  { eapply cost_red_comp.
    + eapply cost_red_ref_e. eassumption.
    + eassumption. }
  eassert (Lookup l m''' vl /\ is_list vl m''') as [Hlookup His_list'].
  { inversion Hred2. subst. inversion H; try discriminate_red_Val.
    subst. inversion H0; try discriminate_red_Val. subst. split.
    + constructor.
    + apply is_list_cons_map.
      * apply new_label_is_fresh.
      * assumption. }
  eassert (forall m0, C[f_cons <* v <* vl, m0 ~~> _, m0 | 2])
    as Hred''.
  { econstructor.
    + repeat econstructor.
    + cbn. econstructor.
      * econstructor.
      * cbn. econstructor. }
  remember (RecV [Int 1; bind_v (inc_fun Var vl) (shift_v v); vl]) as v'
    eqn:Hv'.
  specialize Hred'' with m''' as Hred'''.
  edestruct f_cons_app_expr2 as [c'''' Hred''''].
  - eapply Hvalid.
  - eapply Hred.
  - eapply Hred'.
  - econstructor 2.
    + repeat econstructor.
    + cbn. econstructor 2.
      * repeat econstructor.
      * cbn. econstructor.
  - destruct (uniqueness_full _ _ _ _ _ _ _ _ _ Hvalid Hred3 Hred'''')
      as [? [? ?]].
    subst. econstructor; eauto.
Qed.

Lemma e_of_list_v_of_list :
  forall xs v m, exists c,
    v_of_list xs = (v, m) ->
    C[e_of_list xs, nil ~~> v, m | c].
Proof.
  induction xs; simpl.
  - intros v m. eexists. intros Heq. injection Heq as [] []. constructor.
  - intros v m. destruct v_of_list. destruct (IHxs v0 m0). eexists. intros Heq.
    injection Heq as [] []. eapply cost_red_comp.
    + eapply cost_red_app1. econstructor 2.
      * econstructor.
      * cbn. econstructor.
    + eapply cost_red_comp.
      * eapply cost_red_app2, cost_red_ref_e. auto.
      * econstructor 2.
        -- eapply red_app2. econstructor. reflexivity.
        -- econstructor 2.
          ++ econstructor.
          ++ cbn. unfold v_cons. admit. (* econstructor 1.*)
Admitted.

(* goal 4 *)
Lemma e_of_list_is_list :
  forall xs (v : Value _) (m m' : Map _) c,
    Is_Valid_Map m ->
    C[e_of_list xs, m ~~> v, m' | c] ->
    is_list v m'.
Proof.
  intros xs v m m' c Hvalid Hred.
  destruct (v_of_list xs) eqn:Hxs.
  destruct e_of_list_v_of_list with xs v0 m0. specialize (H Hxs).
  eapply extend_state in H.
  - inversion Hred; [constructor | discriminate_red_Val].
  - eapply f_cons_red_to_list.
(*
  induction xs; simpl; intros v m m' c Hvalid Hred.
  - inversion Hred; [constructor | discriminate_red_Val].
  - eapply f_cons_red_to_list.
    + eassumption.
    + econstructor 1.
    +
  
   inversion Hred; subst.
    repeat match goal with
    | [H : red _ _ _ _ |- _] =>
      inversion H; subst; cbn in *; clear H
    end.
    inversion H0; subst.
    inversion H; subst; cbn in *; clear H; try discriminate_red_Val.
    destruct xs; simpl in *.
    inversion H7; subst; cbn in *; clear H7.
    + unfold e_of_list in H. destruct xs; try discriminate.
      injection H. intro. subst. simpl in *. eapply IHxs.
        .
    repeat match goal with
    | [H : red _ _ _ _ |- _] =>
      inversion H; subst; cbn in *; clear H
    end.
   eapply f_cons_is_list.
    + exact Hred. eassumption.
   destruct v_of_list. injection Heq as [] [].
    econstructor.
    + apply Lookup_spec_eq. apply lookup_same.
    + apply is_list_update; auto. apply new_label_is_fresh.
Qed.
*)
Admitted.