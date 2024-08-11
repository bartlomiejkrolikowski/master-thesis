Require List.
Import List.ListNotations.
Require Import String.
Require Import ZArith.

Require Import src_arrays.LambdaRef.
Require Import src_arrays.LamRefFacts.
Require Import src_arrays.LambdaAssertions_credits_perm.
Require Import src_arrays.LambdaTotalTriple_credits_perm.
Require Import src_arrays.LamRefLogicFactsTotal_credits_perm.
Require Import Lia.
Require Import src_arrays.Tactics.
Require Import src_arrays.Interweave.

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

Inductive is_list {A : Set} : list (Value A) -> Value A -> StateAssertion A :=
| is_nil c m : is_list []%list v_nil c m
| is_cons c m : forall v L l v',
    Lookup l m v' ->
    is_list L v' c m ->
    is_list (v::L)%list (v_cons v l) c m
.

Definition v_of_list {A : Set} (xs : list (Value A)) : Value A * Map A :=
  List.fold_right
    (fun x '(v, m) => let l := new_label m in (v_cons x l, cons (l, Some v) m))
    (v_nil, nil)
    xs.

Fixpoint e_of_list (l : list (Value string)) : Expr string :=
  match l with
  | []%list => v_nil
  | (x::xs)%list => f_cons <* x <* Ref (e_of_list xs)
  end.

Lemma is_list_update (A : Set) L (v : Value A) c (m : Map A) l v' :
  Is_fresh_label l m ->
  is_list L v c m ->
  is_list L v c (update l v' m).
Proof with auto.
  intros Hfresh His_list. induction His_list.
  - constructor.
  - econstructor...
    + apply Lookup_update.
      * intros Heq. subst. apply Lookup_success in H...
      * eassumption.
Qed.

Lemma is_list_cons_map (A : Set) L (v : Value A) c (m : Map A) l v' :
  Is_fresh_label l m ->
  is_list L v c m ->
  is_list L v c ((l, v') :: m)%list.
Proof with auto.
  intros Hfresh His_list. induction His_list.
  - constructor.
  - econstructor...
    + constructor...
Qed.

Lemma is_list_any_credits (A : Set) L (v : Value A) c c' m :
  is_list L v c m ->
  is_list L v c' m.
Proof.
  intros His_list. induction His_list; econstructor; eauto.
Qed.

Lemma Lookup_in (A : Set) l v (m : Map A) :
  Lookup l m v ->
  List.In (l, Some v) m.
Proof with auto.
  intros Hlookup. induction Hlookup; simpl...
Qed.

Lemma Is_Valid_Map_Interweave_fresh (A : Set) l v (m m' : Map A) :
  Is_fresh_label l m ->
  Is_Valid_Map m ->
  Interweave [(l,v)] m m' ->
  Is_Valid_Map m'.
Proof.
  unfold Is_fresh_label, Is_Valid_Map, labels, not.
  intros Hfresh Hvalid Hinter. remember [(l,v)]%list as ml eqn:Hml.
  generalize dependent v. generalize dependent l.
  induction Hinter; simpl in *; intros.
  - constructor.
  - injection Hml as -> ->. invert_Intwv_nil. simpl.
    constructor; assumption.
  - constructor.
    * unfold not. subst. intros.
      apply map_Interweave with (f := fst) in Hinter.
      eapply in_Interweave_or in Hinter; eauto.
      simpl in *. destruct Hinter as [[-> | []] | ?]; auto. inversion Hvalid.
      auto.
    * eapply IHHinter; eauto. inversion Hvalid. auto.
Qed.

Lemma Is_Valid_Map_Interweave_fresh_inv (A : Set) l v (m m' : Map A) :
  Is_fresh_label l m ->
  Is_Valid_Map m' ->
  Interweave [(l,v)] m m' ->
  Is_Valid_Map m.
Proof.
  unfold Is_fresh_label, Is_Valid_Map, labels, not.
  intros Hfresh Hvalid Hinter. remember [(l,v)]%list as ml eqn:Hml.
  generalize dependent v. generalize dependent l.
  induction Hinter; simpl in *; intros.
  - constructor.
  - injection Hml as -> ->. invert_Intwv_nil. simpl in *. inversion Hvalid.
    assumption.
  - constructor.
    * unfold not. subst. intros. inversion Hvalid.
      apply map_Interweave with (f := fst) in Hinter.
      eapply in_or_Interweave in Hinter; eauto.
    * eapply IHHinter; eauto. inversion Hvalid. auto.
Qed.

Lemma is_list_Interweave_map (A : Set) L (v : Value A) c (m m' : Map A) l v' :
  Interweave [(l,v')] m m' ->
  is_list L v c m ->
  is_list L v c m'.
Proof with auto.
  intros Hinter His_list. induction His_list.
  - constructor.
  - econstructor...
    + eauto using valid_map_Lookup, in_or_Interweave, Lookup_in.
Qed.

(* goal 1 *)
Lemma v_of_list_is_list :
  forall (A : Set) xs (v : Value A) c (m : Map A),
    v_of_list xs = (v, m) ->
    is_list xs v c m.
Proof.
  intros. generalize dependent m. generalize dependent v.
  induction xs; simpl; intros v m Heq.
  - injection Heq as [] []. constructor.
  - destruct v_of_list. injection Heq as [] [].
    econstructor.
    + apply Lookup_spec_eq. simpl. unfold_all_lab.
      rewrite Nat.eqb_refl. reflexivity.
    + apply is_list_cons_map; auto. apply new_label_is_fresh.
Qed.

(* goal 2 *)
Lemma triple_f_cons :
  forall L (v vl : Value _),
    triple (f_cons <* v <* (Ref vl))
      (sa_credits 3 <*> is_list L vl)
      (is_list (v::L)).
Proof.
  intros L v vl.
  eapply triple_weaken.
    { eapply implies_trans.
      { apply star_implies_mono.
        { eapply credits_star_r with (c1 := 1) (c2 := 2). auto. }
        { apply implies_refl. } }
      { apply star_assoc. } }
    { apply implies_post_spec. eauto. }
  apply triple_app with
    (P2 := sa_credits 1 <*> (is_list L vl))
    (Q2 := fun v' => <exists> l v'', <[v' = Lab l]> <*> <(l :== v'')> <*> (<[v'' = vl]> <*> (is_list L vl))).
  2:{ apply triple_ref; auto. eapply triple_weaken.
      3:apply triple_frame, triple_value.
      { apply empty_star_l_intro. }
      { intros. simpl. apply implies_refl. } }
  - eapply triple_weaken with
      (P := sa_credits 1 <*> (sa_credits 1 <*> is_list L vl))
      (Q := fun v0 => (<exists> e1', <[v0 = (-\ e1') /\ _]>) <*> (sa_credits 1 <*> is_list L vl)).
    { eapply implies_trans.
      { apply star_implies_mono.
        { apply credits_star_r with (c1 := 1) (c2 := 1). auto. }
        { apply implies_refl. } }
      { apply star_assoc. } }
    { intros. apply implies_spec. intros. destruct H. edestruct_direct.
      normalize_star. edestruct_direct. subst. invert_Intwv_nil.
      solve_star. split; auto. eassumption. }
    eapply triple_app with
      (P2 := sa_credits 1 <*> is_list L vl)
      (Q2 := fun v' => <[v' = v]> <*> (sa_credits 1 <*> is_list L vl)).
    2:{ eapply triple_weaken, triple_frame with (H := sa_credits 1 <*> is_list L vl), triple_value.
        { apply empty_star_l_intro. }
        { intros. apply implies_spec. auto. }
      }
    + eapply triple_weaken with
        (P := <[]> <*> (sa_credits 1 <*> is_list L vl)).
      3:{ eapply triple_frame. eapply triple_value. }
      { eapply empty_star_l_intro. }
      { unfold f_cons, "->>", StringLam. intros. normalize_star. solve_star.
        split_all; eauto. intros. cbn.
        apply triple_frame. apply triple_pure. intros ->. eapply triple_weaken.
        3:{ apply triple_value. }
        { apply implies_refl. }
        { intros. apply implies_spec. intros. destruct H1 as (?&?&?). subst. solve_star.
          apply pure_spec. split_all; auto.
          intros. cbn. rewrite bind_v_shift, bind_v_id.
          apply -> triple_exists. intros.
          apply -> triple_exists. intros.
          eapply triple_weaken_valid, triple_frame, triple_value.
          { intros c' m' _. revert c' m'. apply empty_star_l_intro. }
          { simpl. intros. normalize_star. subst.
            fold (v_cons v x). edestruct H3. edestruct_direct. normalize_star.
            subst. unfold_all_in H. edestruct_direct. simpl in *.
            unfold_all_in H3. edestruct_direct. invert_Intwv_nil.
            repeat econstructor.
            { apply valid_map_Lookup; auto. unfold_all_in H3. edestruct_direct.
              eapply in_or_Interweave; eauto. simpl. auto. }
            { eapply is_list_any_credits. simpl in *.
              eapply is_list_Interweave_map; unfold Is_fresh_label; eauto. } } } }
Qed.

(* goal 3 *)
Lemma e_of_list_is_list :
  forall L, triple (e_of_list L) (sa_credits (3 * List.length L)) (is_list L).
Proof.
  induction L; simpl.
  - unfold v_nil.
    apply triple_weaken with (P := <[]>) (Q := fun v => <[v = v_nil]>),
      triple_value.
    + apply implies_refl.
    + intros. apply implies_spec. intros. apply -> pure_spec in H.
      destruct H as (->&_&_). constructor.
  - eapply triple_weaken.
    { eapply implies_trans.
      { eapply implies_trans.
        { eapply credits_star_r with (c1 := 3) (c2 := 3*List.length L). lia. }
        { apply star_implies_mono.
          { eapply credits_star_r with (c1 := 1) (c2 := 2). reflexivity. }
          { apply implies_refl. }
        }
      }
      { apply star_assoc. }
    }
    { apply implies_post_spec. eauto. }
    apply triple_app with
      (P2 := sa_credits 1 <*> sa_credits (3*List.length L))
      (Q2 := fun v' => <exists> l v'', <[v' = Lab l]> <*> <(l :== v'')> <*> (is_list L v'')).
    2:{ apply triple_ref; auto. }
    + eapply triple_weaken with
        (P := sa_credits 1 <*> (sa_credits 1 <*> sa_credits (3 * List.length L)))
        (Q := fun v0 => (<exists> e1', <[v0 = (-\ e1') /\ _]>) <*> (sa_credits 1 <*> sa_credits (3 * List.length L))).
      { eapply implies_trans.
        { apply star_implies_mono.
          { apply credits_star_r with (c1 := 1) (c2 := 1). auto. }
          { apply implies_refl. } }
        { apply star_assoc. } }
      { intros. apply implies_spec. intros. destruct H. edestruct_direct.
        normalize_star. edestruct_direct. subst. invert_Intwv_nil.
        solve_star. split; auto. eassumption. }
      eapply triple_app with
        (P2 := (<[]> <*> (sa_credits 1 <*> sa_credits (3 * List.length L)))).
      2:{ apply triple_frame, triple_value. }
      * eapply triple_weaken with
          (P := <[]> <*> (<[]> <*> (sa_credits 1 <*> sa_credits (3*List.length L)))).
        3:{ eapply triple_frame. eapply triple_value. }
        { eapply implies_trans; eapply empty_star_l_intro. }
        { unfold f_cons, "->>", StringLam. intros. normalize_star. solve_star.
          split_all; eauto. intros. cbn.
          apply triple_frame. apply triple_pure. intros ->. eapply triple_weaken.
          3:{ apply triple_value. }
          { apply implies_refl. }
          { intros. apply implies_spec. intros. destruct H1 as (?&?&?). subst. solve_star.
            apply pure_spec. split_all; auto.
            intros. cbn. rewrite bind_v_shift, bind_v_id.
            apply -> triple_exists. intros.
            apply -> triple_exists. intros.
            eapply triple_weaken_valid, triple_frame, triple_value.
            { intros c' m' _. revert c' m'. apply empty_star_l_intro. }
            { simpl. intros. normalize_star. subst.
              fold (v_cons a x). edestruct H3. edestruct_direct. normalize_star.
              subst. unfold_all_in H. edestruct_direct. simpl in *.
              unfold_all_in H3. edestruct_direct.
              repeat econstructor.
              { apply valid_map_Lookup; auto. unfold_all_in H3. edestruct_direct.
                eapply in_or_Interweave; eauto. simpl. auto. }
              { eapply is_list_any_credits. simpl in *.
                eapply is_list_Interweave_map; unfold Is_fresh_label; eauto. } } } }
Qed.

Lemma triple_fun_f_cons :
  forall L (v : Value _),
    triple_fun f_cons (fun v' => sa_credits 1 <*> <[v' = v]>)
      (fun vf =>
        <[triple_fun vf
          (fun v' => <exists> l vl, sa_credits 1 <*> <[v' = Lab l]> <*> <(l :== vl)> <*> is_list L vl) (is_list (v::L))]>).
Proof.
  unfold triple_fun. intros. eapply triple_app.
  2:apply triple_value.
  eapply triple_weaken, triple_frame, triple_value.
  { apply empty_star_l_intro. }
  { simpl. intros. apply implies_spec. intros. normalize_star. subst.
    unfold f_cons, StringLam. simpl.
    solve_star.
    2:apply empty_spec; auto.
    split_all; eauto.
    intros. cbn. eapply triple_weaken, triple_frame, triple_value.
    { apply empty_star_l_intro. }
    { simpl. intros. apply implies_spec. intros. normalize_star.
      rewrite pure_spec in *. edestruct_direct. split_all; auto. intros.
      do 2 (apply -> triple_exists; intro).
      eapply triple_weaken, triple_app, triple_frame, triple_value; eauto 2 using implies_trans, star_assoc_r, implies_refl.
      eapply triple_weaken, triple_frame, triple_value; eauto 1 using empty_star_l_intro.
      simpl. intros. apply implies_spec. intros. normalize_star. subst. solve_star.
      2:apply empty_star_l_intro; eassumption.
      split_all; auto.
      intros. cbn. rewrite bind_v_shift, bind_v_id. eapply triple_weaken_valid, triple_frame, triple_value.
      { intros. unfold_all. split_all; eauto using Interweave_nil_l. }
      simpl. intros. normalize_star. subst. fold (v_cons v x). find_star_and_unfold_all. edestruct_direct.
      simpl. econstructor.
      { apply valid_map_Lookup; auto. eapply in_or_Interweave; eauto. simpl. auto. }
      eapply is_list_Interweave_map; eauto. } }
Qed.

Lemma e_of_list_is_list' :
  forall L, triple (e_of_list L) (sa_credits (3 * List.length L)) (is_list L).
Proof.
  induction L; simpl.
  - unfold v_nil.
    apply triple_weaken with (P := <[]>) (Q := fun v => <[v = v_nil]>),
      triple_value.
    + apply implies_refl.
    + intros. apply implies_spec. intros. apply -> pure_spec in H.
      destruct H as (->&_&_). constructor.
  - specialize triple_fun_f_cons with L a as Hfun.
    eapply triple_fun_app2 with (e1 := f_cons <* a) (e2 := Ref (e_of_list L)).
    + specialize (Hfun a). simpl in Hfun. eapply triple_weaken, triple_frame.
      { apply credits_star_r with (c1 := 1) (c2 := 2 + 3*List.length L). lia. }
      { simpl. intro. apply implies_refl. }
      eapply triple_weaken with (P := sa_credits 1 <*> <[a = a]>).
      { eapply implies_trans.
        { apply empty_star_r_intro. }
        { apply star_implies_mono.
          { apply implies_refl. }
          { apply implies_spec. intros. apply pure_spec. rewrite empty_spec in *. auto. } } }
      { simpl. intro. apply implies_refl. }
      eassumption.
    + eapply triple_weaken with (Q := fun v => (<exists> (l : Label)(vl : Value string), ((<[ v = Lab l ]>) <*> <( l :== vl )>) <*> is_list L vl) <*> sa_credits 1), triple_frame.
      { eapply implies_trans.
        { apply credits_star_r with (c1 := 1 + 3*List.length L) (c2 := 1). lia. }
        { apply star_implies_mono.
          { apply credits_star_r with (c1 := 1) (c2 := 3*List.length L). reflexivity. }
          { apply implies_refl. } } }
      { apply implies_post_spec. intros. normalize_star. solve_star. apply star_comm. solve_star. assumption. }
      apply triple_ref. assumption.
Qed.

Definition v_repeat : Value string :=
  ([-\] "x", [-\] "n",
    [let "res"] Ref v_nil [in]
    [let "i"] Ref (Int 0) [in]
    [while] ! (Var "i") [<] Var "n" [do]
      (Var "res") <- (f_cons <* (Var "x") <* Ref (! Var "res"));;
      (Var "i") <- (! Var "i" [+] Int 1)
    [end];;
    Free (Var "i");;
    [let "tmp"] ! (Var "res") [in]
      Free (Var "res");;
      Var "tmp"
    [end]
    [end]
    [end])%string.

Theorem star_exists_l' V A P (Q : StateAssertion V) :
  (<exists> x : A, P x) <*> Q ->> <exists> x : A, P x <*> Q.
Proof.
  unfold sa_implies. intros. apply star_exists_l. assumption.
Qed.

Ltac extract_exists P H :=
  match P with
  | <exists> x, _ => idtac
  | (<exists> x, _) <*> ?Q' => apply star_exists_l' in H
  | ?Q <*> (<exists> x, _) => apply star_comm in H; apply star_exists_l' in H
  | ?Q <*> ?Q' => eapply star_implies_mono in H; [clear H; apply implies_spec; intro H; extract_exists Q H|apply implies_refl]; apply star_exists_l' in H
  | ?Q <*> ?Q' => apply star_comm in H; eapply star_implies_mono in H; [clear H; apply implies_spec; intro H; extract_exists Q H|apply implies_refl]; extract_exists Q' H; apply star_exists_l' in H
  end.

Ltac extract_exists_in H :=
  match type of H with
  | ?P ?c ?m => extract_exists P H
  end.

Ltac extract_pure P H :=
  multimatch P with
  | <[_]> => idtac
  | <[_]> <*> ?Q' => idtac
  | ?Q <*> <[_]> => apply star_comm in H
  | ?Q <*> ?Q' => eapply star_implies_mono in H; [|clear H; apply implies_spec; intro H; extract_pure Q H|apply implies_refl]; apply star_assoc_l in H
  | ?Q <*> ?Q' => apply star_comm in H; eapply star_implies_mono in H; [|clear H; apply implies_spec; intro H; extract_pure Q H|apply implies_refl]; apply star_assoc_l in H
  end.

Ltac extract_pure_in H :=
  match type of H with
  | ?P ?c ?m => extract_pure P H
  end.
Ltac id' H :=
  match ltac:(H) with
  | ?X => exact X
  end.

Ltac reorder_pure P :=
  match P with
  | ?Q <*> ?Q' =>
    match ltac:(eval simpl in (ltac:(reorder_pure Q) <*> ltac:(reorder_pure Q'))) with
    | <[?P']> <*> ?Q1' => exact (<[P']> <*> ltac:(reorder_pure Q1'))
    | (<[?P']> <*> ?Q1) <*> ?Q1' => exact (<[P']> <*> ltac:(reorder_pure (Q1 <*> Q1')))
    | ?Q1 <*> <[?P']> => exact (<[P']> <*> ltac:(reorder_pure Q1))
    | ?Q1 <*> (<[?P']> <*> ?Q1') => exact (<[P']> <*> ltac:(reorder_pure (Q1' <*> Q1)))
    end
  | _ => exact P
  end.

Ltac prove_implies_reorder_pure :=
  match goal with
  | [|- ?Q <*> ?Q' ->> _] =>
    eapply implies_trans;
    [apply star_implies_mono; prove_implies_reorder_pure|];
    match goal with
    | [|- <[?P]> <*> ?Q1' ->> _ ] =>
      apply star_implies_mono; [apply implies_refl|];
      prove_implies_reorder_pure
    | [|- (<[?P]> <*> ?Q1) <*> ?Q1' ->> _ ] =>
      eapply implies_trans; [apply star_assoc_r|];
      apply star_implies_mono; [apply implies_refl|];
      prove_implies_reorder_pure
    | [|- ?Q1 <*> <[?P]> ->> _ ] =>
      eapply implies_trans; [apply star_comm|];
      apply star_implies_mono; [apply implies_refl|];
      prove_implies_reorder_pure
    | [|- ?Q1 <*> (<[?P]> <*> ?Q1') ->> _ ] =>
      eapply implies_trans; [apply star_comm|];
      eapply implies_trans; [apply star_assoc_r|];
      apply star_implies_mono; [apply implies_refl|];
      prove_implies_reorder_pure
    end
  | [|- ?P ->> _] => apply implies_refl
  end.
(*
Ltac prove_implies_reorder_pure_bwd :=
  match goal with
  | [|- _ ->> ?Q <*> ?Q'] =>
    eapply implies_trans;
    [|apply star_implies_mono; prove_implies_reorder_pure_bwd];
    match goal with
    | [|- _ ->> <[?P]> <*> ?Q1' ] =>
      apply star_implies_mono; [apply implies_refl|];
      prove_implies_reorder_pure_bwd
    | [|- _ ->> (<[?P]> <*> ?Q1) <*> ?Q1' ] =>
      eapply implies_trans; [|apply star_assoc_r];
      apply star_implies_mono; [apply implies_refl|];
      prove_implies_reorder_pure_bwd
    | [|- _ ->> ?Q1 <*> <[?P]> ] =>
      eapply implies_trans; [|apply star_comm];
      apply star_implies_mono; [apply implies_refl|];
      prove_implies_reorder_pure_bwd
    | [|- _ ->> ?Q1 <*> (<[?P]> <*> ?Q1') ] =>
      eapply implies_trans; [|apply star_comm];
      eapply implies_trans; [|apply star_assoc_r];
      apply star_implies_mono; [apply implies_refl|];
      prove_implies_reorder_pure_bwd
    end
  | [|- _ ->> ?P] => apply implies_refl
  end.
*)
Ltac triple_reorder_pure :=
  match goal with
  | [|- triple ?e ?P' ?Q'] =>
    apply triple_weaken with (P := ltac:(reorder_pure P')) (Q := Q');
      [prove_implies_reorder_pure|intros; apply implies_refl|]
  end.

Ltac triple_pull_pure :=
  match goal with
  | [|- triple ?e <[?P]> ?Q] =>
    apply -> triple_pure; intro
  | [|- triple ?e (<[?P]> <*> ?Q) ?Q'] =>
    apply -> triple_pure_star; intro
  end.

Ltac triple_pull_exists :=
  match goal with
  | [|- triple ?e (<exists> _, _) ?Q] =>
    apply -> triple_exists; intro
  | [|- triple ?e (?Q <*> <exists> _, _) ?Q'] =>
    apply -> triple_exists_star; intro
  end.

Ltac reorder_credits P :=
  match P with
  | ?Q <*> ?Q' =>
    match ltac:(eval simpl in (ltac:(reorder_credits Q) <*> ltac:(reorder_credits Q'))) with
    | sa_credits ?n <*> ?Q1' => exact (sa_credits n <*> ltac:(reorder_credits Q1'))
    | (sa_credits ?n <*> ?Q1) <*> ?Q1' => exact (sa_credits n <*> ltac:(reorder_credits (Q1 <*> Q1')))
    | ?Q1 <*> sa_credits ?n => exact (sa_credits n <*> ltac:(reorder_credits Q1))
    | ?Q1 <*> (sa_credits ?n <*> ?Q1') => exact (sa_credits n <*> ltac:(reorder_credits (Q1' <*> Q1)))
    end
  | _ => exact P
  end.

(*Check ltac:(reorder_credits (<[]> <*> (<[1=1]> <*> <[2=2]> <*> (sa_credits 2 <*> <[3=3]> <*> sa_credits 4) <*> sa_credits 5) : StateAssertion string)).*)

Ltac prove_implies_reorder_credits :=
  match goal with
  | [|- ?Q <*> ?Q' ->> _] =>
    eapply implies_trans;
    [apply star_implies_mono; prove_implies_reorder_credits|];
    match goal with
    | [|- sa_credits _ <*> ?Q1' ->> _ ] =>
      apply star_implies_mono; [apply implies_refl|];
      prove_implies_reorder_credits
    | [|- (sa_credits _ <*> ?Q1) <*> ?Q1' ->> _ ] =>
      eapply implies_trans; [apply star_assoc_r|];
      apply star_implies_mono; [apply implies_refl|];
      prove_implies_reorder_credits
    | [|- ?Q1 <*> sa_credits _ ->> _ ] =>
      eapply implies_trans; [apply star_comm|];
      apply star_implies_mono; [apply implies_refl|];
      prove_implies_reorder_credits
    | [|- ?Q1 <*> (sa_credits _ <*> ?Q1') ->> _ ] =>
      eapply implies_trans; [apply star_comm|];
      eapply implies_trans; [apply star_assoc_r|];
      apply star_implies_mono; [apply implies_refl|];
      prove_implies_reorder_credits
    end
  | [|- ?P ->> _] => apply implies_refl
  end.

Ltac triple_reorder_credits :=
  match goal with
  | [|- triple ?e ?P' ?Q'] =>
    apply triple_weaken with (P := ltac:(reorder_credits P')) (Q := Q');
      [prove_implies_reorder_credits|intros; apply implies_refl|]
  end.
(*
Ltac prove_implies_pull_credits n :=
  match goal with
  | [|- ?Q <*> ?Q' ->> _] =>
    eapply implies_trans;
    [apply star_implies_mono; [prove_implies_pull_credits n|apply implies_refl]|];
    match goal with
    | [|- sa_credits _ <*> ?Q1' ->> _ ] => idtac
    | [|- (sa_credits _ <*> ?Q1) <*> ?Q1' ->> _ ] =>
      eapply implies_trans; [apply star_assoc_r|]
    end
  | [|- ?Q <*> ?Q' ->> _] =>
    eapply implies_trans;
    [apply star_implies_mono; [apply implies_refl|prove_implies_pull_credits n]|];
    match goal with
    | [|- ?Q1 <*> sa_credits _ ->> _ ] =>
      eapply implies_trans; [apply star_comm|]
    | [|- ?Q1 <*> (sa_credits _ <*> ?Q1') ->> _ ] =>
      eapply implies_trans; [apply star_comm|];
      eapply implies_trans; [apply star_assoc_r|]
    end
  | [|- sa_credits _ <*> ?Q ->> _ ] =>
    eapply star_implies_mono;
    [eapply credits_star_r with (c1 := n); reflexivity|apply implies_refl]
  | [|- sa_credits _ ->> _] => eapply credits_star_r with (c1 := n); reflexivity
  | [|- ?P ->> _] => apply implies_refl
  end.
Ltac triple_pull_credits n :=
  match goal with
  | [|- triple ?e ?P' ?Q'] =>
    eapply triple_weaken with (Q := Q');
      [prove_implies_reorder_credits n|intros; apply implies_refl|]
  end.
*)

Ltac triple_pull_credits n :=
  match goal with
  | [|- triple ?e (sa_credits _) ?Q' ] =>
    eapply triple_weaken with (Q := Q');
    [eapply credits_star_r with (c1 := n); reflexivity
    |intros; apply implies_refl
    |]
  | [|- triple ?e (sa_credits _ <*> ?P') ?Q' ] =>
    eapply triple_weaken with (Q := Q');
    [eapply star_implies_mono;
      [eapply credits_star_r with (c1 := n); reflexivity|apply implies_refl]
    |intros; apply implies_refl
    |]
  end.

Ltac triple_pull_1_credit :=
  triple_reorder_credits; triple_pull_credits 1; triple_reorder_credits.

Ltac reorder X P :=
  match P with
  | ?Q <*> ?Q' =>
    match ltac:(eval simpl in (ltac:(reorder X Q) <*> ltac:(reorder X Q'))) with
    | X <*> ?Q1' => exact (X <*> ltac:(reorder X Q1'))
    | (X <*> ?Q1) <*> ?Q1' => exact (X <*> ltac:(reorder X (Q1 <*> Q1')))
    | ?Q1 <*> X => exact (X <*> ltac:(reorder X Q1))
    | ?Q1 <*> (X <*> ?Q1') => exact (X <*> ltac:(reorder X (Q1' <*> Q1)))
    end
  | _ => exact P
  end.
(*Check (fun x (y : Expr (_ string)) => ltac:(reorder (<(x :== -\ y)>) (<[]> <*> <[1=1]> <*> (<[2=2]> <*> (<[3=3]> <*> <[]> <*> <[4=4]> <*> (<[5=5]> <*> <(x :== -\ y)>) <*> <[6=6]>))))).*)
Ltac prove_implies_reorder X :=
  match goal with
  | [|- ?Q <*> ?Q' ->> _] =>
    eapply implies_trans;
    [apply star_implies_mono; prove_implies_reorder X|];
    match goal with
    | [|- X <*> ?Q1' ->> _ ] =>
      apply star_implies_mono; [apply implies_refl|];
      prove_implies_reorder X
    | [|- (X <*> ?Q1) <*> ?Q1' ->> _ ] =>
      eapply implies_trans; [apply star_assoc_r|];
      apply star_implies_mono; [apply implies_refl|];
      prove_implies_reorder X
    | [|- ?Q1 <*> X ->> _ ] =>
      eapply implies_trans; [apply star_comm|];
      apply star_implies_mono; [apply implies_refl|];
      prove_implies_reorder X
    | [|- ?Q1 <*> (X <*> ?Q1') ->> _ ] =>
      eapply implies_trans; [apply star_comm|];
      eapply implies_trans; [apply star_assoc_r|];
      apply star_implies_mono; [apply implies_refl|];
      prove_implies_reorder X
    end
  | [|- ?P ->> _] => apply implies_refl
  end.

Ltac prove_implies_reorder_bwd X :=
  match goal with
  | [|- _ ->> ?Q <*> ?Q'] =>
    eapply implies_trans;
    [|apply star_implies_mono; prove_implies_reorder_bwd X];
    match goal with
    | [|- _ ->> X <*> ?Q1' ] =>
      apply star_implies_mono; [apply implies_refl|];
      prove_implies_reorder_bwd X
    | [|- _ ->> (X <*> ?Q1) <*> ?Q1' ] =>
      eapply implies_trans; [|apply star_assoc_l];
      apply star_implies_mono; [apply implies_refl|];
      prove_implies_reorder_bwd X
    | [|- _ ->> ?Q1 <*> X ] =>
      eapply implies_trans; [|apply star_comm];
      apply star_implies_mono; [apply implies_refl|];
      prove_implies_reorder_bwd X
    | [|- _ ->> ?Q1 <*> (X <*> ?Q1') ] =>
      eapply implies_trans; [|apply star_comm];
      eapply implies_trans; [|apply star_assoc_l];
      apply star_implies_mono; [apply implies_refl|];
      prove_implies_reorder_bwd X
    end
  | [|- ?P ->> _] => apply implies_refl
  end.

Ltac triple_reorder X :=
  match goal with
  | [|- triple ?e ?P' ?Q'] =>
    eapply triple_weaken with (P := ltac:(reorder X P')) (Q := Q');
      [prove_implies_reorder X|intros; apply implies_refl|]
  end.

Ltac prove_implies_refl :=
  intros; simpl; apply implies_refl.

Ltac rewrite_empty_spec :=
  match goal with
  | [H : <[]> ?c ?m |- _] => apply empty_spec in H as (->&->)
  end.

Ltac unify_not_evar X Y :=
  not_evar Y; unify X Y.

Ltac remove X P :=
  lazymatch ltac:(type of X) with
  | StateAssertion ?V =>
    match P with
    | ?Y => unify_not_evar X Y; exact (sa_empty : StateAssertion V)
    | ?Q <*> ?Q' =>
      match ltac:(eval simpl in (ltac:(remove X Q))) with
      | <[]> => exact Q'
      | ?Q1 => exact (Q1 <*> Q')
      end
    | ?Q <*> ?Q' =>
      match ltac:(eval simpl in (ltac:(remove X Q'))) with
      | <[]> => exact Q
      | ?Q1' => exact (Q <*> Q1')
      end
    end
  end.

Ltac prove_implies_reorder1 X :=
  match goal with
  | [|- ?Y ->> _] => unify_not_evar X Y; apply implies_refl
  | [|- ?Q <*> ?Q' ->> _] =>
    eapply implies_trans;
    [apply star_implies_mono; [prove_implies_reorder1 X|apply implies_refl]|];
    lazymatch goal with
    | [|- (?Y <*> ?Q1) <*> ?Q1' ->> _ ] => unify_not_evar X Y; apply star_assoc_r
    | [|- ?Y <*> ?Q1' ->> _ ] => unify_not_evar X Y; apply implies_refl
    end
  | [|- ?Q <*> ?Q' ->> _] =>
    eapply implies_trans;
    [apply star_implies_mono; [apply implies_refl|prove_implies_reorder1 X]|];
    lazymatch goal with
    | [|- ?Q1 <*> (?Y <*> ?Q1') ->> _ ] =>
      unify_not_evar X Y;
      eapply implies_trans;
      [apply star_assoc_l|];
      eapply implies_trans;
      [apply star_implies_mono; [apply star_comm|apply implies_refl]|];
      apply star_assoc_r
    | [|- ?Q1 <*> ?Y ->> _ ] => unify_not_evar X Y; apply star_comm
    end
  | [|- ?P ->> ?Q] => unify_not_evar Q P; apply implies_refl
  end.

Ltac prove_implies_reorder1_bwd X :=
  match goal with
  | [|- _ ->> ?Y] => unify_not_evar X Y; apply implies_refl
  | [|- _ ->> ?Q <*> ?Q'] =>
    eapply implies_trans;
    [|apply star_implies_mono; [prove_implies_reorder1_bwd X|apply implies_refl]];
    lazymatch goal with
    | [|- _ ->> (?Y <*> ?Q1) <*> ?Q1' ] => unify_not_evar X Y; apply star_assoc_l
    | [|- _ ->> ?Y <*> ?Q1' ] => unify_not_evar X Y; apply implies_refl
    end
  | [|- _ ->> ?Q <*> ?Q'] =>
    eapply implies_trans;
    [|apply star_implies_mono; [apply implies_refl|prove_implies_reorder1_bwd X]];
    lazymatch goal with
    | [|- _ ->> ?Q1 <*> (?Y <*> ?Q1') ] =>
      unify_not_evar X Y;
      eapply implies_trans;
      [|apply star_assoc_r];
      eapply implies_trans;
      [|apply star_implies_mono; [apply star_comm|apply implies_refl]];
      apply star_assoc_l
    | [|- _ ->> ?Q1 <*> ?Y ] => unify_not_evar X Y; apply star_comm
    end
  | [|- ?P ->> ?Q] => unify_not_evar P Q; apply implies_refl
  end.

Ltac triple_reorder1 X :=
  match goal with
  | [|- triple ?e ?P' ?Q'] =>
    apply triple_weaken with (P := X <*> ltac:(remove X P')) (Q := Q');
      [prove_implies_reorder1 X|prove_implies_refl|]
  end.

Ltac clear_empty P :=
  lazymatch P with
  | ?Q <*> ?Q' => (*idtac Q Q';*)
    match ltac:(eval simpl in (ltac:(clear_empty Q) <*> ltac:(clear_empty Q'))) with
    | <[]> <*> ?Q1' => (*idtac 1 Q1';*) exact Q1'
    | ?Q1 <*> <[]> => (*idtac 2 Q1;*) exact Q1
    | ?Q1 => (*idtac 3 Q1;*) exact Q1
    end
  | <exists> t : ?T, @?Q t => (*idtac t T Q;*)
    let Q' := ltac:(eval simpl in ltac:(clear_empty Q)) in
    (*idtac T Q'; idtac ">";*) exact (<exists> t : T, Q' t) (*; idtac "OK") || idtac "!")*)
  | fun t : ?T => @?Q t => (*idtac t T Q;*)
    let u := fresh t in(*exact (fun x : T => ltac:(eval simpl in ltac:(clear_empty Q)))*)
    let Q' := ltac:(eval simpl in (fun u =>ltac:(clear_empty ltac:(eval simpl in (Q u))))) in
    (*idtac t T Q'; idtac ">!";*) exact Q' (*; idtac "OK!") || idtac "!!")*)
  | _ => exact P (*; idtac "<>"*)
  end.

(*Goal True.
match constr:(fun x => x + 1) with
| fun t => @?y t => let a := fresh t in let b := constr:(fun a => y a) in idtac a b y
end.
Abort.
Check (ltac:(clear_empty ltac:(eval simpl in (fun (x:Label) (y : Expr (inc_set string)) =>  (<[]> <*> <[1=1]> <*> (<[2=2]> <*> <exists> n m : nat, (<[n=m]> <*> <[]> <*> <[4=4]> <*> (<[5=5]> <*> <(x :== -\y)>) <*> <[]> <*> <[6=6]>)):StateAssertion string))))).
Goal True. match constr:(fun x xx : nat => ((fun t => t + xx) x + 1) * 3) with
| fun z v => @?y z v * 3 => idtac "y =" y; pose (fun z : nat => ltac:(
  match ltac:(eval simpl in (fun v : nat => y z v)) with
  | fun r => @?a r => idtac "r =" r "; a =" a; let aa := (ltac:(eval simpl in (a))) in exact (aa 8)
  end) * 5)
end.*)

Ltac prove_implies_clear_empty :=
  lazymatch goal with
  | [|- ?Q <*> ?Q' ->> _ ] =>
    eapply implies_trans;
    [apply star_implies_mono; prove_implies_clear_empty|];
    lazymatch goal with
    | [|- <[]> <*> ?Q1' ->> _] => apply empty_star_l_cancel
    | [|- ?Q1 <*> <[]> ->> _] => apply empty_star_r_cancel
    | [|- ?Q1 ->> _] => apply implies_refl
    end
  | [|- (<exists> x, @?P' x) ->> _] =>
    apply exists_implies with (P := P'); prove_implies_clear_empty
  | [|- forall x, ?Q ->> _] =>
    intros; prove_implies_clear_empty
  | [|- ?P ->> _] => apply implies_refl
  end.

Ltac prove_implies_clear_empty_bwd :=
  lazymatch goal with
  | [|- _ ->> ?Q <*> ?Q' ] =>
    eapply implies_trans;
    [|apply star_implies_mono; prove_implies_clear_empty_bwd];
    lazymatch goal with
    | [|- _ ->> <[]> <*> ?Q1'] => apply empty_star_l_intro
    | [|- _ ->> ?Q1 <*> <[]>] => apply empty_star_r_intro
    | [|- _ ->> ?Q1] => apply implies_refl
    end
  | [|- _ ->> (<exists> x, @?Q' x)] =>
    apply exists_implies with (Q := Q'); prove_implies_clear_empty_bwd
  | [|- forall x, ?Q ->> _] =>
    intros; prove_implies_clear_empty_bwd
  | [|- _ ->> ?P] => apply implies_refl
  end.

Ltac triple_clear_empty :=
  match goal with
  | [|- triple ?e ?P' ?Q'] =>
    apply triple_weaken with (P := ltac:(clear_empty P')) (Q := Q');
      [prove_implies_clear_empty|prove_implies_refl|]
  end.

Ltac triple_clear_empty_r :=
  match goal with
  | [|- triple ?e ?P' ?Q'] =>
    apply triple_weaken with (P := P') (Q := ltac:(clear_empty Q'));
      [prove_implies_refl|prove_implies_clear_empty_bwd|]
  end.
(*Check (fun x (y : Expr (_ string)) => ltac:(clear_empty ltac:(eval simpl in ltac:(remove (<(x :== -\y)>) (<[]> <*> <[1=1]> <*> (<[2=2]> <*> (<[3=3]> <*> <[]> <*> <[4=4]> <*> (<[5=5]> <*> <(x :== -\ y)>) <*> <[]> <*> <[6=6]>))))))).*)
(*
Goal True.
eassert (option (Value string)). shelve.
eassert (H = _). shelve.
lazymatch goal with
| [_ : H = ?yy |- _] =>
  epose (fun x (y : Expr (_ string)) => ltac:(clear_empty ltac:(eval simpl in ltac:(remove (<(x :?= Some (-\ y))> : StateAssertion string) (<[]> <*> <[1=1]> <*> (<[2=2]> <*> (<[3=3]> <*> <[]> <*> <[4=4]> <*> (<[5=5]> <*> <(x :== -\ y)>) <*> <[]> <*> <[6=6]>)))))))
end.
lazymatch goal with
| [_ : H = ?yy |- _] =>
  epose (fun x (y : Expr (_ string)) => ltac:(clear_empty ltac:(eval simpl in ltac:(remove (<(x :?= yy)> : StateAssertion string) (<[]> <*> <[1=1]> <*> (<[2=2]> <*> (<[3=3]> <*> <[]> <*> <[4=4]> <*> (<[5=5]> <*> <(x :== @U_val string)>) <*> <[]> <*> <[6=6]>)))))))
end.
Abort.

Ltac tmp P :=
  lazymatch P with
  | ?Q <*> ?Q' => (*idtac Q Q';*)
    tmp Q; tmp Q'
  | <exists> t : ?T, @?Q t => (*idtac t T Q;*)
    tmp Q
  | fun t : ?T => @?Q t => (*idtac t T Q;*)
    let u := fresh t in(*exact (fun x : T => ltac:(eval simpl in ltac:(clear_empty Q)))*)
    tmp (Q u)
  | ?X => (is_evar X; idtac "is_evar -" X) || idtac "!" X
  end.
*)

Ltac get_leftmost P :=
  lazymatch P with
  | ?Q <*> ?Q' => exact ltac:(get_leftmost Q)
  | _ => exact P
  end.

Ltac reorder_leftmost P :=
  let l := (ltac:(eval simpl in ltac:(get_leftmost P))) in
  exact (l <*> ltac:(remove l P)).
(*Check (fun x (y : Expr (_ string)) => ltac:(reorder_leftmost (((<[1=1]> <*> <[8=8]>) <*> <[7=7]>) <*> (<[2=2]> <*> (<[3=3]> <*> <[]> <*> <[4=4]> <*> (<[5=5]> <*> <(x :== -\ y)>) <*> <[]> <*> <[6=6]>))))).*)
Ltac prove_implies1 :=
  lazymatch goal with
  | [|- ?P ->> ?QQ] =>
    (unify P QQ; apply implies_refl) ||
    (let l := (ltac:(eval simpl in ltac:(get_leftmost P))) in
     let P' := (ltac:(eval simpl in ltac:(remove l P))) in
     let Q' := (ltac:(eval simpl in ltac:(remove l QQ))) in
     apply implies_trans with (Q := l <*> P');
     [prove_implies_reorder1 l|];
     apply implies_trans with (Q := l <*> Q');
     [|prove_implies_reorder1_bwd l];
     apply star_implies_mono;
     [apply implies_refl|])
  end.

Ltac prove_implies1_rev :=
  lazymatch goal with
  | [|- ?P ->> ?QQ] =>
    (unify P QQ; apply implies_refl) ||
    (let l := (ltac:(eval simpl in ltac:(get_leftmost QQ))) in
     let P' := (ltac:(eval simpl in ltac:(remove l P))) in
     let Q' := (ltac:(eval simpl in ltac:(remove l QQ))) in
     apply implies_trans with (Q := l <*> Q');
     [|prove_implies_reorder1_bwd l];
     apply implies_trans with (Q := l <*> P');
     [prove_implies_reorder1 l|];
     apply star_implies_mono;
     [apply implies_refl|])
  end.

Ltac prove_implies :=
  repeat prove_implies1.
Ltac prove_implies_rev :=
  repeat prove_implies1_rev.

Ltac fold_implies :=
  lazymatch goal with
  | [|- forall c m, ?P c m -> ?Q c m] => fold (P ->> Q)
  end.

Ltac revert_implies :=
  lazymatch goal with
  | [H : ?P ?c ?m |- ?Q ?c ?m] => revert c m H; fold_implies
  end.

Ltac triple_value_revert :=
  match goal with
  | [v : Value _ |- triple (Val ?v') _ _] => unify v v'; generalize dependent v
  | [|- triple (Val ?v') _ _] => remember v' as t; generalize dependent t
  end.

Ltac eta_expand_pre_triple_value :=
  triple_value_revert;
  lazymatch goal with
  | [|- forall v : ?T, triple (Val v) (@?P v) ?Q] =>
    change (forall v : T, triple v (P v) Q)
  | [|- forall (v : ?T) (x : ?H), triple (Val v) (@?P v) ?Q] =>
    change (forall (v : T) (x : H), triple v (P v) Q)
  end;
  intros.

Ltac solve_simple_value :=
  apply triple_value_implies; apply implies_spec; intros; solve_star;
  try eassumption.

Ltac solve_value_unify :=
  match goal with
  | [|- triple (Val ?v) ?P ?Q] =>
    unify P (Q v); apply triple_value_implies; apply implies_refl
  end.

Ltac app_lambda :=
  lazymatch goal with
  | [|- triple (Val (-\ ?e1') <* Val ?v2) (sa_credits 1 <*> ?P) ?Q] => (*idtac e1' v2 P Q;*)
    eapply triple_app with (P2 := P); [|eta_expand_pre_triple_value; solve_value_unify]
  | [|- triple (Val (-\ ?e1') <* ?e2) (sa_credits 1 <*> ?P) ?Q] => (*idtac e1' e2 P Q;*)
    eapply triple_app with (P2 := P)
  end.

Ltac triple_expand_empty_pre_r :=
  lazymatch goal with
  | [|- triple ?e ?P' ?Q'] =>
    apply triple_weaken with (P := P' <*> <[]>) (Q := Q');
      [apply empty_star_r_intro|prove_implies_refl|]
  end.

Theorem triple_fun_v_repeat v n :
  triple_fun v_repeat
    (fun v' => sa_credits 1 <*> <[v' = v]>)
    (fun vf => <[
      triple_fun vf
        (fun v' => sa_credits (16 + n*14) <*> <[v' = Int (Z.of_nat n)]>)
        (is_list (List.repeat v n))
    ]>).
Proof.
  unfold triple_fun, v_repeat, StringLam. simpl. intros. app_lambda.
  solve_simple_value.
  { split_all; auto.
    intros. cbn.
    triple_pull_pure.
    solve_simple_value.
    { rewrite pure_spec in *.
      rewrite_empty_spec. split_all; auto. intros.
      triple_pull_1_credit.
      app_lambda. simpl. subst.
      solve_simple_value.
      { split_all; auto. cbn. intros.
        triple_reorder_pure.
        triple_pull_pure. subst.
        triple_pull_1_credit.
        eapply triple_app.
        2:apply triple_ref, triple_frame, triple_value.
        triple_pull_1_credit. triple_clear_empty_r.
        solve_simple_value; swap_star_ctx; normalize_star; subst.
        { split_all; auto. intros. cbn.
          repeat triple_pull_exists. triple_reorder_pure.
          repeat triple_pull_pure. subst. triple_pull_1_credit.
          eapply triple_app.
          2:eapply triple_ref, triple_frame, triple_value.
          simpl. triple_clear_empty_r. triple_pull_1_credit. solve_simple_value.
          { split_all; auto.
            intros. cbn.
            repeat triple_pull_exists.
            triple_reorder_pure.
            repeat triple_pull_pure. subst.
            triple_pull_1_credit.
            eapply triple_seq.
            - triple_pull_credits 2.
              triple_reorder_credits.
              eapply triple_weaken with (P := sa_credits 2 <*> (<exists> i vl, <[i <= n]> <*> sa_credits (8+((n-i)*14)) <*> <( x :== vl )> <*> <( x0 :== (Int (Z.of_nat i)) )> <*> is_list (List.repeat v i) vl)).
              { apply star_implies_mono.
                { apply implies_refl. }
                { apply implies_spec. intros. unfold sa_exists.
                  exists 0, (RecV [Int 0]). solve_star; [lia|]. simpl. rewrite Nat.sub_0_r.
                  apply star_assoc. apply star_assoc. eapply star_implies_mono.
                  { apply star_assoc. }
                  { apply implies_spec. intros. constructor. }
                  apply empty_star_r_intro. assumption. } }
              { intros. apply implies_refl. }
              eapply triple_while with
                (Q := fun b : bool => <exists> (i : nat) (vl : Value _), <[i <= n]> <*> sa_credits (6 + (n-i)*14) <*> <(x :== vl)> <*> <(x0 :== Int (Z.of_nat i))> <*> is_list (List.repeat v i) vl <*> <[(Z.of_nat i <? Z.of_nat n)%Z = b]>).
              + repeat triple_pull_exists.
                triple_reorder_pure.
                repeat triple_pull_pure.
                triple_pull_1_credit.
                eapply triple_weaken with
                  (Q := fun v0 => <exists> i1 i2 : Z, <[v0 = Bool (i1 <? i2)%Z]> <*> (<[i1 = Z.of_nat x1]> <*> <[i2 = Z.of_nat n]> <*> <exists> (i : nat) (vl : Value _), _)).
                { prove_implies_refl. }
                { apply implies_post_spec. intros.
                  lazymatch goal with
                  | [HH : _ ?c ?m |- _ ?c ?m] => destruct HH as (?&?&?);
                    apply star_pure_l in HH; destruct HH
                  end.
                  lazymatch goal with
                  | [HH : _ ?c ?m |- _ ?c ?m] =>
                    apply star_assoc in HH; apply star_pure_l in HH; destruct HH
                  end.
                  lazymatch goal with
                  | [HH : _ ?c ?m |- _ ?c ?m] =>
                    apply star_pure_l in HH; destruct HH
                  end.
                  eexists. eapply star_implies_mono.
                  { apply implies_spec. intros. apply pure_spec. split.
                    { eassumption. }
                    { apply -> empty_spec. eassumption. } }
                  { prove_implies_refl. }
                  revert_implies. prove_implies_clear_empty_bwd. }
                eapply triple_clt; [|intros; solve_value_unify].
                * triple_pull_1_credit.
                  eapply triple_weaken, triple_deref; [| |solve_simple_value].
                  { prove_implies_rev. }
                  { apply implies_post_spec. intros. normalize_star. subst.
                    eexists. apply star_pure_l. split; [reflexivity|].
                    eexists. apply star_pure_l. split; [reflexivity|].
                    apply star_assoc. apply star_pure_l. split; [reflexivity|].
                    apply star_pure_l. split; [reflexivity|].
                    do 2 eexists. repeat apply star_assoc_l. apply star_pure_l. split; [eassumption|].
                    swap_star. solve_star. swap_star. solve_star. swap_star. solve_star. swap_star. solve_star.
                    swap_star. solve_star. swap_star. solve_star. eapply star_implies_mono; eauto.
                    { prove_implies_refl. }
                    { prove_implies. } }
              + repeat triple_pull_exists.
                triple_reorder_pure.
                repeat triple_pull_pure.
                lazymatch goal with
                | [H : (_ <? _)%Z = true |- _] => apply Z.ltb_lt in H; apply Nat2Z.inj_lt in H
                end.
                assert (n - x1 = S (n - S x1)) as -> by lia. simpl.
                triple_pull_1_credit.
                eapply triple_seq.
                * triple_pull_credits 1. triple_reorder_credits.
                  eapply triple_weaken, triple_assign;
                    [prove_implies_rev|prove_implies_refl|solve_simple_value|].
                  -- triple_pull_1_credit.
                    eapply triple_app; [|apply triple_ref, triple_deref; solve_simple_value].
                    simpl. repeat rewrite bind_v_liftS_shift_swap.
                    repeat rewrite bind_v_shift. repeat rewrite bind_v_id.
                    triple_pull_1_credit.
                    eapply triple_app.
                    2:apply triple_frame, triple_value.
                    simpl. triple_clear_empty_r. solve_simple_value.
                    split; auto. intros. cbn.
                    triple_pull_pure. subst.
                    triple_pull_credits 2. triple_pull_1_credit. solve_simple_value.
                    2:{ revert_implies. prove_implies_rev. }
                    split; auto. intros. cbn.
                    repeat triple_pull_exists. triple_reorder_pure. repeat triple_pull_pure. subst.
                    triple_reorder <(x :== x2)>.
                    solve_simple_value. rewrite bind_v_shift, bind_v_id.
                    lazymatch goal with
                    | [_ : (?P <*> (?P1 <*> (?P2 <*> is_list (List.repeat ?v ?n) _) <*> ?P4)) ?c ?m|- (?P <*> _ (RecV [Int 1; ?v; Lab ?l])) ?c ?m] =>
                      fold (v_cons v l);
                      eassert ((P <*> (fun vl => P1 <*> P2 <*> is_list (List.repeat v (n+1)) vl) (v_cons v l)) c m)
                    end.
                    { eapply star_implies_mono; eauto.
                      { apply implies_refl. }
                      { apply implies_spec. intros. normalize_star. solve_star. eapply star_implies_mono; eauto.
                        { apply implies_refl. }
                        { eapply implies_trans.
                          { apply star_assoc. }
                          { apply star_implies_mono.
                            { apply implies_refl. }
                            { apply implies_spec. intros. rewrite Nat.add_1_r. simpl.
                              lazymatch goal with
                              | [H : _ ?c ?m |- _ ?c ?m] => unfold_all_in H
                              end. edestruct_direct.
                              econstructor.
                              { apply valid_map_Lookup. eapply in_or_Interweave; eauto. simpl. auto. }
                              { eapply is_list_Interweave_map; eauto using Interweave_comm.
                                rewrite Nat.add_0_r. assumption. } } } } } }
                    lazymatch goal with
                    | [|- (_ <*> _ ?v) _ _] =>
                      eapply star_implies_mono; eauto; [|generalize v]; prove_implies_refl
                    end.
                * triple_pull_exists.
                  triple_pull_1_credit. eapply triple_weaken, triple_assign; [prove_implies_rev| |solve_simple_value|].
                  { apply implies_post_spec. intros. normalize_star. subst. solve_star.
                    eapply star_implies_mono.
                    { apply implies_refl. }
                    { apply implies_spec. intros. solve_star. }
                    eapply star_implies_mono.
                    { apply implies_refl. }
                    { apply star_comm. }
                    lazymatch goal with
                    | [HH : (<(?l :== ?v)> <*> ?Q) ?c ?m |- _ ?c ?m] =>
                      eassert ((<[v = Int (Z.of_nat _)]> <*> <(l:==v)> <*> _) c m)
                    end.
                    { apply star_assoc_l, star_comm, star_assoc_l.
                      lazymatch goal with
                      | [|- (?P1 <*> (?P2 <*> <[ ?j = ?i ]>)) ?c ?m] =>
                        change ((P1 <*> (fun t => P2 <*> <[ t = i ]>) j) c m)
                      end.
                      eassumption. }
                    simpl in *. swap_star. solve_star. normalize_star. subst. eassumption. }
                  -- triple_pull_1_credit. eapply triple_weaken, triple_iadd.
                    { prove_implies. }
                    { apply implies_post_spec. intros. normalize_star. subst. revert_implies. prove_implies. }
                    ++ triple_pull_1_credit. eapply triple_weaken, triple_deref; [| |solve_simple_value].
                      { prove_implies_rev. }
                      { intros. simpl. apply implies_spec. intros. normalize_star. subst. solve_star.
                        lazymatch goal with
                        | [HH : _ ?c ?m |- _ ?c ?m] =>
                          apply empty_star_l_intro in HH; eapply star_implies_mono in HH
                        end.
                        2:{ apply implies_spec. intros. rewrite_empty_spec.
                            apply pure_spec with (P := Z.of_nat x1 = Z.of_nat x1). auto. }
                        2:{ apply implies_refl. }
                        match goal with
                        | [H : (<[?j = ?j]> <*> (<(?v :== Int ?j)> <*> ?Q)) ?c ?m |- _ ?j ?c ?m] =>
                          change ((fun i : Z => <[i = j]> <*> (<(v :== Int i)> <*> Q)) j c m) in H
                        end. eassumption. }
                    ++ intros. solve_simple_value. normalize_star. subst.
                      apply star_assoc. swap_star. solve_star.
                      { f_equal.
                        match goal with
                        | [|- (Z.of_nat ?n1 + 1)%Z = Z.of_nat ?n2] =>
                          change (Z.of_nat n1 + Z.of_nat 1 = Z.of_nat n2)%Z
                        end.
                        rewrite Nat2Z.inj_add. reflexivity. }
                      { lazymatch goal with
                        | [HH : _ ?c ?m |- _ ?c ?m] => unfold_all_in HH
                        end.
                        unfold_all. edestruct_direct. invert_Intwv_nil.
                        split_all; eauto using Interweave_nil_l, Interweave_nil_r; simpl in *; eauto; lia. }
            - repeat triple_pull_exists.
              triple_reorder_pure. repeat triple_pull_pure.
              rewrite Z.ltb_nlt in *. assert (x1 = n) as -> by lia.
              rewrite Nat.sub_diag. simpl.
              triple_pull_1_credit.
              eapply triple_seq.
              + triple_pull_1_credit.
                eapply triple_weaken, triple_free; [|prove_implies_refl|solve_simple_value].
                prove_implies_rev.
              + triple_pull_1_credit. eapply triple_app.
                * solve_simple_value. split; auto. intros. cbn.
                  eapply triple_seq; [apply triple_free|]; solve_simple_value.
                * triple_pull_1_credit. eapply triple_weaken, triple_deref.
                  { prove_implies_rev. }
                  { apply implies_post_spec. intros. normalize_star. subst.
                    revert_implies. prove_implies. }
                  triple_pull_1_credit.
                  solve_simple_value. revert_implies. prove_implies. } } } } }
Qed.
