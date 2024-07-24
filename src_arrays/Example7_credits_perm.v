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
  Is_Valid_Map m ->
  Is_fresh_label l m ->
  Interweave [(l,v')] m m' ->
  is_list L v c m ->
  is_list L v c m'.
Proof with auto.
  intros Hvalid Hfresh Hinter His_list. induction His_list.
  - constructor.
  - econstructor...
    + apply valid_map_Lookup.
      * eapply Is_Valid_Map_Interweave_fresh; eauto.
      * eauto using in_or_Interweave, Lookup_in.
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
            { eapply is_list_any_credits. simpl in *. eapply is_list_Interweave_map. 3:eauto.
              all:unfold Is_fresh_label; eauto. eapply Is_Valid_Map_Interweave_fresh_inv; eauto. unfold Is_fresh_label, labels; eauto. } } } }
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
              { eapply is_list_any_credits. simpl in *. eapply is_list_Interweave_map. 3:eauto.
                all:unfold Is_fresh_label; eauto. eapply Is_Valid_Map_Interweave_fresh_inv; eauto. unfold Is_fresh_label, labels; eauto. } } } }
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
      eapply is_list_Interweave_map.
      { eapply Interweave_valid_r; eauto. }
      { unfold Is_fresh_label, not, labels. simpl in *. eauto. }
      { eauto. }
      { auto. } } }
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
      (Var "res") <- (f_cons <* (Var "x") <* (Var "res"));;
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

Ltac triple_reorder X :=
  match goal with
  | [|- triple ?e ?P' ?Q'] =>
    eapply triple_weaken with (P := ltac:(reorder X P')) (Q := Q');
      [prove_implies_reorder X|intros; apply implies_refl|]
  end.

Theorem triple_fun_v_repeat v n :
  triple_fun v_repeat
    (fun v' => sa_credits 1 <*> <[v' = v]>)
    (fun vf => <[
      triple_fun vf
        (fun v' => sa_credits (16 + n*12) <*> <[v' = Int (Z.of_nat n)]>)
        (is_list (List.repeat v n))
    ]>).
Proof.
  unfold triple_fun, v_repeat, StringLam. simpl. intros. eapply triple_app.
  2:apply triple_value.
  apply triple_pure. intros ->.
  eapply triple_weaken, triple_value.
  { apply implies_refl. }
  { simpl. intros. apply implies_spec. intros. rewrite pure_spec in *.
    edestruct_direct. solve_star.
    2:apply empty_spec; auto.
    split_all; auto.
    intros. cbn.
    apply triple_pure. intros ->.
    eapply triple_weaken, triple_value.
    { apply implies_refl. }
    { simpl. intros. apply implies_spec. intros. rewrite pure_spec in *.
      edestruct_direct. split_all; auto. intros. eapply triple_weaken.
      { eapply implies_trans.
        { apply star_implies_mono.
          { apply credits_star_r with (c1 := 1). reflexivity. }
          { apply implies_refl. } }
        { apply star_assoc. } }
      { intros. apply implies_refl. }
      eapply triple_app.
      2:apply triple_frame, triple_value.
      eapply triple_weaken, triple_frame, triple_value.
      { apply empty_star_l_intro. }
      { simpl. intros. apply implies_spec. intros. normalize_star.
        apply star_comm in H0. normalize_star. subst.
        solve_star.
        2:apply empty_star_l_intro; eassumption.
        split_all; auto. cbn. intros.
        eapply triple_weaken.
        { eapply implies_trans.
          { apply star_implies_mono.
            { apply implies_refl. }
            { apply credits_star_r with (c1 := 1). reflexivity. } }
          { eapply implies_trans.
            { apply star_comm. }
            { apply star_assoc. } } }
        { intros. apply implies_refl. }
        eapply triple_app.
        2:apply triple_ref, triple_frame, triple_value.
        eapply triple_weaken, triple_frame, triple_value.
        { apply empty_star_l_intro. }
        { simpl. intros. apply implies_spec. intros. normalize_star.
          apply star_comm in H0. normalize_star. subst. solve_star.
          2:eapply star_implies_mono; [apply implies_refl|apply empty_star_l_intro|eapply credits_star_r]; eauto.
          split_all; auto.
          intros. cbn. do 2 (apply -> triple_exists; intros).
          eapply triple_weaken.
          { eapply implies_trans.
            { apply star_comm. }
            { eapply implies_trans.
              { apply star_implies_mono.
                { eapply implies_trans.
                  { apply star_comm. }
                  { apply star_implies_mono.
                    { apply credits_star_r with (c1 := 1). reflexivity. }
                    { apply implies_refl. } } }
                { apply implies_refl. } }
              { eapply implies_trans.
                { apply star_assoc. }
                { apply star_assoc. } } } }
          { intros. apply implies_refl. }
          eapply triple_app.
          2:eapply triple_ref, triple_frame, triple_value.
          simpl. eapply triple_weaken, triple_frame, triple_value.
          { apply empty_star_l_intro. }
          { simpl. intros. apply implies_spec. intros. normalize_star. apply star_comm in H0. normalize_star.
            subst. solve_star.
            2:apply star_comm; solve_star; eapply empty_star_l_intro, star_assoc_l, star_implies_mono; [apply implies_refl|eapply implies_trans; [apply credits_star_r with (c1:=1); reflexivity|apply star_comm]|eassumption].
            split_all; auto.
            intros. cbn.
            do 2 (apply -> triple_exists; intros).
            eapply triple_weaken.
            { eapply implies_trans.
              { apply star_assoc. }
              { eapply star_implies_mono.
                { apply implies_refl. }
                { eapply implies_trans.
                  { apply star_assoc. }
                  { eapply implies_trans.
                    { apply star_implies_mono.
                      { apply star_comm. }
                      { apply star_comm. } }
                    { eapply implies_trans.
                      { apply star_assoc. }
                      { apply star_implies_mono.
                        { apply implies_refl. }
                        { eapply implies_trans.
                          { apply star_comm. }
                          { eapply implies_trans.
                            { apply star_assoc. }
                            { eapply implies_trans.
                              { apply star_implies_mono.
                                { eapply implies_trans.
                                  { eapply implies_trans.
                                    { apply credits_star_r with (c1 := 3). reflexivity. }
                                    { apply star_implies_mono.
                                      { apply credits_star_r with (c1 := 1). reflexivity. }
                                      { apply implies_refl. } } }
                                  { apply star_assoc. } }
                                { apply implies_refl. } }
                              { eapply implies_trans.
                                { apply star_assoc. }
                                { apply star_implies_mono.
                                  { apply implies_refl. }
                                  { apply star_assoc. } } } } } } } } } } } }
            { intros. apply implies_refl. }
            do 2 (apply triple_pure_star; intros ->).
            eapply triple_seq.
            - eapply triple_weaken with (P := sa_credits 2 <*> (<exists> i vl, <[i <= n]> <*> sa_credits (8+((n-i)*12)) <*> <( x :== vl )> <*> <( x0 :== (Int (Z.of_nat i)) )> <*> is_list (List.repeat v i) vl)).
              { apply star_implies_mono.
                { apply implies_refl. }
                { apply implies_spec. intros. unfold sa_exists.
                  exists 0, (RecV [Int 0]). solve_star; [lia|]. simpl. rewrite Nat.sub_0_r.
                  apply star_assoc. apply star_assoc. eapply star_implies_mono.
                  { apply star_assoc. }
                  { apply implies_spec. intros. constructor. }
                  apply empty_star_r_intro. assumption. } }
              { intros. apply implies_refl. }
              (*eapply triple_weaken.
              { apply implies_spec. intros. extract_exists_in H. normalize_star. }*)
              eapply triple_while with
                (Q := fun b : bool => <exists> (i : nat) (vl : Value _), <[i <= n]> <*> sa_credits (6 + (n-i)*12) <*> <(x :== vl)> <*> <(x0 :== Int (Z.of_nat i))> <*> is_list (List.repeat v i) vl <*> <[(Z.of_nat i <? Z.of_nat n)%Z = b]>).
              + do 2 (apply -> triple_exists; intros).
                eapply triple_weaken.
                { eapply implies_trans.
                  { apply star_assoc. }
                  { eapply implies_trans.
                    { apply star_assoc. }
                    { apply star_assoc. } } }
                { intros. apply implies_refl. }
                apply triple_pure_star. intros.
                eapply triple_weaken.
                { eapply implies_trans.
                  { apply star_implies_mono.
                    { apply credits_star_r with (c1 := 1). reflexivity. }
                    { apply implies_refl. } }
                  { simpl. apply star_assoc. } }
                { intros. apply implies_refl. }
                eapply triple_weaken with
                  (Q := fun v0 => <exists> i1 i2 : Z, <[v0 = Bool (i1 <? i2)%Z]> <*> (<[i1 = Z.of_nat x1]> <*> <[i2 = Z.of_nat n]> <*> <exists> (i : nat) (vl : Value _), _)).
                { apply implies_refl. }
                { apply implies_post_spec. intros. destruct H0 as (?&?&?). (* TODO: extract_exists_in H0. *)
                  apply star_pure_l in H0. destruct H0.
                  apply star_assoc in H3. apply star_pure_l in H3. destruct H3.
                  apply star_pure_l in H5. destruct H5.
                  eexists. eapply star_implies_mono.
                  { apply implies_spec. intros. apply pure_spec. split.
                    { eassumption. }
                    { apply -> empty_spec. eassumption. } }
                  { eapply implies_refl. }
                  apply empty_star_l_intro. eassumption. }
                eapply triple_clt.
                2:{ intros. eapply triple_weaken, triple_frame, triple_value.
                  { apply empty_star_l_intro. }
                  { intros. simpl. apply implies_spec. intros. normalize_star. subst. apply H3. } }
                * eapply triple_weaken, triple_deref, triple_weaken, triple_frame, triple_value.
                  { eapply implies_trans.
                    { apply star_implies_mono.
                      { apply credits_star_r with (c1 := 1). reflexivity. }
                      { apply star_comm. } }
                    { eapply implies_trans.
                      { apply star_assoc. }
                      { eapply implies_trans.
                        { apply star_implies_mono.
                          { apply implies_refl. }
                          { eapply implies_trans.
                            { apply star_assoc. }
                            { eapply implies_trans.
                              { apply star_implies_mono.
                                { eapply implies_trans.
                                  { apply star_comm. }
                                  { apply star_assoc. } }
                                { apply implies_refl. } }
                              { apply star_assoc. } } } }
                        { apply star_assoc. } } } }
                  2:apply empty_star_l_intro.
                  2:{ apply implies_post_spec. intros. apply star_assoc_l. eassumption. }
                  { apply implies_post_spec. intros. normalize_star. subst.
                    eexists. apply star_pure_l. split; [reflexivity|].
                    eexists. apply star_pure_l. split; [reflexivity|].
                    apply star_assoc. apply star_pure_l. split; [reflexivity|].
                    apply star_pure_l. split; [reflexivity|].
                    do 2 eexists. repeat apply star_assoc_l. apply star_pure_l. split; [eassumption|].
                    swap_star. solve_star. swap_star. solve_star. swap_star. solve_star. swap_star. solve_star.
                    swap_star. solve_star. swap_star. solve_star. eapply star_implies_mono.
                    { apply implies_refl. }
                    { apply star_assoc. }
                    eassumption. }
              + repeat triple_pull_exists.
                triple_reorder_pure.
                repeat triple_pull_pure.
                apply Z.ltb_lt in H0. apply Nat2Z.inj_lt in H0 as H'.
                assert (n - x1 = S (n - S x1)) as -> by lia. simpl.
                triple_pull_1_credit.
                eapply triple_seq.
                * triple_pull_credits 1. triple_reorder_credits.
                  eapply triple_weaken.
                  { eapply implies_trans.
                    { apply star_implies_mono.
                      { apply implies_refl. }
                      { prove_implies_reorder <(x :== x2)>. } }
                    { apply star_assoc. } }
                  { intros. apply star_assoc_r. }
                  eapply triple_assign.
                  -- apply triple_value_implies.
                    apply implies_spec. intros. solve_star. eassumption.
                  -- triple_pull_1_credit.
                    eapply triple_app.
                    2:apply triple_frame, triple_value.
                    simpl. triple_pull_1_credit.
                    eapply triple_app.
                    2:apply triple_frame, triple_value.
                    simpl. apply triple_value_implies.
                    apply implies_spec. intros. solve_star.
                    2:apply empty_star_l_intro; eassumption.
                    split; auto. intros. apply triple_value_implies. simpl.
                    apply implies_spec. intros. normalize_star. subst. solve_star.
                    2:apply empty_star_l_intro; eassumption.
                    split; auto. intros. cbn. triple_pull_pure. subst.
                    triple_reorder <(x :== x2)>.
                    apply triple_value_implies. apply implies_spec. intros.
                    solve_star. eassumption.
                * triple_pull_1_credit. eapply triple_weaken, triple_assign.
                  { eapply implies_trans.
                    { apply star_implies_mono.
                      { apply implies_refl. }
                      { prove_implies_reorder <(x0 :== @Int string (Z.of_nat x1))>. } }
                    { apply star_assoc. } }
                  { apply implies_post_spec. intros. normalize_star. subst. solve_star.
                    eapply star_implies_mono.
                    { apply implies_refl. }
                    { apply implies_spec. intros. solve_star. }
                    eapply star_implies_mono.
                    { apply implies_refl. }
                    { apply star_comm. }
                    swap_star. solve_star. }
                  -- apply triple_value_implies. apply implies_spec. intros.
                    solve_star. eassumption.
                  -- triple_pull_1_credit. eapply triple_weaken, triple_iadd.
                    { apply implies_refl. }
                    { apply implies_post_spec. intros. normalize_star. subst. apply H5. }
                    ++ triple_pull_1_credit. eapply triple_weaken, triple_deref.
                      { eapply implies_trans.
                        { apply star_implies_mono.
                          { apply implies_refl. }
                          { apply implies_spec. intros. conormalize_star. swap_star_ctx. eassumption. } }
                        { apply star_assoc. } }
                      { intros. simpl. apply implies_spec. intros. normalize_star. subst. solve_star.
                        apply empty_star_l_intro in H5. eapply star_implies_mono in H5.
                        2:{ apply implies_spec. intros. apply empty_spec in H3 as (->&->).
                            apply pure_spec with (P := Z.of_nat x1 = Z.of_nat x1). auto. }
                        2:{ apply implies_refl. }
                        match goal with
                        | [H : (<[?j = ?j]> <*> (<(?v :== Int ?j)> <*> ?Q)) ?c ?m |- _ ?j ?c ?m] =>
                          change ((fun i : Z => <[i = j]> <*> (<(v :== Int i)> <*> Q)) j c m) in H
                        end. eassumption. }
                      apply triple_value_implies. apply implies_spec. intros. solve_star. eassumption.
                    ++ intros. apply triple_value_implies. apply implies_spec. intros. normalize_star. subst. solve_star.
                      { f_equal.
                        match goal with
                        | [|- (Z.of_nat ?n1 + 1)%Z = Z.of_nat ?n2] =>
                          change (Z.of_nat n1 + Z.of_nat 1 = Z.of_nat n2)%Z
                        end.
                        rewrite Nat2Z.inj_add. reflexivity. }
                      { unfold_all_in H5. unfold_all. edestruct_direct. invert_Intwv_nil. split_all; eauto using Interweave_nil_l, Interweave_nil_r; simpl in *; eauto; try lia. admit. }
            - repeat triple_pull_exists.
              triple_reorder_pure. repeat triple_pull_pure.
              rewrite Z.ltb_nlt in *. assert (x1 = n) as -> by lia.
              rewrite Nat.sub_diag. simpl.
              triple_pull_1_credit.
              eapply triple_seq.
              + triple_pull_1_credit. eapply triple_weaken, triple_free.
                { eapply implies_trans.
                  { apply star_implies_mono.
                    { apply implies_refl. }
                    { prove_implies_reorder (<(x0 :== Int (Z.of_nat n))> : _ string). } }
                  { apply star_assoc. } }
                { intros. simpl. apply implies_refl. }
                apply triple_value_implies. apply implies_spec. intros. solve_star. eassumption.
              + triple_pull_1_credit. eapply triple_app.
                * apply triple_value_implies. apply implies_spec. intros. solve_star; [|eassumption].
                  split; auto. intros. cbn. eapply triple_seq.
                  -- apply triple_free, triple_value_implies, implies_spec. intros. solve_star. eassumption.
                  -- apply triple_value_implies, implies_refl.
                * triple_pull_1_credit. eapply triple_weaken, triple_deref.
                  { eapply implies_trans.
                    { apply star_implies_mono.
                      { apply implies_refl. }
                      { apply implies_spec. intros. swap_star_ctx. normalize_star. eassumption. } }
                    { apply star_assoc. } }
                  { apply implies_post_spec. intros. normalize_star. subst. swap_star. apply star_assoc.
                    eapply star_implies_mono.
                    { apply star_comm. }
                    { apply implies_refl. }
                    apply star_assoc_l. eassumption. }
                    apply triple_value_implies. apply implies_spec. intros. solve_star.
                    eapply star_implies_mono.
                    3:eassumption.
                    { apply implies_refl. }
                    { apply implies_spec. intros. swap_star. apply star_assoc.
                      eapply star_implies_mono.
                      3:eassumption.
                      { apply implies_refl. }
                      { apply credits_star_r. reflexivity. } } } } } } }
Admitted.
(*
(* vvvv TODO vvvv *)
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
  { edestruct uniqueness_full as [? [? [? ?]]].
    + eassumption.
    + apply Hred1.
    + eassumption.
    + assumption. }
  assert (Is_Valid_Map m'') as Hvalid''.
  { edestruct uniqueness_full as [? [? [? ?]]].
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
  forall L (e el : Expr _) l (v vl vl' : Value _) c1 c1' (m m' m'' m''' m'''' : Map _)
    c c' c'' c''',
    Is_Valid_Map m ->
    C[e, m ~~> v, m' | c] ->
    C[el, m' ~~> vl, m'' | c'] ->
    C[Ref vl, m'' ~~> Lab l, m''' | c''] ->
    C[f_cons <* e <* Ref el, m ~~> vl', m'''' | c'''] ->
    is_list L vl c1 m'' ->
    is_list (v::L) vl' c1' m''''.
Proof.
  intros L e el l v vl vl' c1 c1' m m' m'' m''' m'''' c c' c'' c'''
    Hvalid Hred Hred1 Hred2 Hred3 His_list.
  assert (Is_Valid_Map m') as Hvalid'.
  { edestruct uniqueness_full as [? [? [? ?]]].
    + eassumption.
    + apply Hred.
    + eassumption.
    + assumption. }
  assert (Is_Valid_Map m'') as Hvalid''.
  { edestruct uniqueness_full as [? [? [? ?]]].
    + eassumption.
    + apply Hred1.
    + eassumption.
    + assumption. }
  eassert (C[Ref el, m' ~~> Lab l, m''' | c' + c'']) as Hred'.
  { eapply cost_red_comp.
    + eapply cost_red_ref_e. eassumption.
    + eassumption. }
  eassert (Lookup l m''' vl /\ is_list L vl c1 m''') as [Hlookup His_list'].
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
    subst. rewrite bind_v_shift, bind_v_id. econstructor; eauto.
Qed.

(* alternative goal 4 *)
Lemma e_of_list_v_of_list :
  forall xs v m,
    v_of_list xs = (v, m) ->
    exists c, C[e_of_list xs, nil ~~> v, m | c].
Proof.
  induction xs; simpl; intros v m Heq.
  - eexists. injection Heq as [] []. constructor.
  - destruct v_of_list. destruct (IHxs v0 m0); trivial. eexists.
    injection Heq as [] []. eapply cost_red_comp.
    + eapply cost_red_app1. econstructor 2.
      * econstructor.
      * cbn. econstructor.
    + eapply cost_red_comp.
      * eapply cost_red_app2, cost_red_ref_e. eauto.
      * econstructor 2.
        -- eapply red_app2. econstructor. reflexivity.
        -- econstructor 2.
          ++ econstructor.
          ++ cbn. unfold v_cons. rewrite bind_v_shift, bind_v_id.
            econstructor.
Qed.

Lemma e_of_list_shift f xs :
  map_labels_e f (e_of_list xs) = e_of_list (List.map (map_labels_v f) xs).
Proof.
  induction xs; simpl; repeat f_equal. assumption.
Qed.

Corollary v_of_list_e_of_list :
  forall xs (v : Value _) m c,
    C[e_of_list xs, nil ~~> v, m | c] ->
    v_of_list xs = (v, m).
Proof.
  intros xs v m c Hred. destruct v_of_list as (v', m') eqn:Heq.
  apply e_of_list_v_of_list in Heq as [c' Hred'].
  eapply uniqueness_full in Hred as [? [? [? ?]]];
    [| constructor | eassumption].
  now subst.
Qed.

Corollary e_of_list_v_of_list_general :
  forall xs xs2 n v v2 m m' m2,
    v_of_list xs = (v, m) ->
    S n = of_label (new_label m') ->
    xs2 = List.map (map_labels_v (lift (fun n' => OfNat (plus n n')))) xs ->
    m2 = List.map (fun '(OfNat n', v) => (OfNat (n + n'), map_labels_v (lift (fun n' => OfNat (plus n n'))) v)) m ->
    v2 = map_labels_v (lift (fun n' => OfNat (plus n n'))) v ->
    exists c, C[e_of_list xs2, m' ~~> v2, m2 ++ m' | c]%list.
Proof.
  intros xs xs2 n v v2 m m' m2 Heq. intros. subst.
  apply e_of_list_v_of_list in Heq as [c Hred].
  eexists.
  match goal with
  | [|- cost_red ?e ?m ?e' ?m' ?c] => change (cost_red e ([]++m)%list e' m' c)
  end.
  eapply cost_red_shift; eauto; simpl; trivial.
  now rewrite e_of_list_shift.
Qed.

Corollary v_of_list_e_of_list_general :
  forall xs xs2 n (v v2 : Value _) m m' m2 c,
    Is_Valid_Map m' ->
    C[e_of_list xs2, m' ~~> v2, m2 ++ m' | c]%list ->
    S n = of_label (new_label m') ->
    xs2 = List.map (map_labels_v (lift (fun n' => OfNat (plus n n')))) xs ->
    m2 = List.map (fun '(OfNat n', v) => (OfNat (n + n'), map_labels_v (lift (fun n' => OfNat (plus n n'))) v)) m ->
    v2 = map_labels_v (lift (fun n' => OfNat (plus n n'))) v ->
    v_of_list xs = (v, m).
Proof.
  intros xs xs2 n v v2 m m'' m2 c Hvalid Hred. intros. subst.
  destruct v_of_list as (v', m') eqn:Heq.
  eapply e_of_list_v_of_list_general in Heq as [c' Hred']; eauto.
  eapply uniqueness_full in Hred as [Hv [Hm [Hc ?]]]; try eassumption.
  apply shift_inj_v in Hv; [|
    intros ? ? Heq'; apply lift_inj in Heq'; auto; intros ? ? Heq''; injection Heq''; lia
  ].
  apply List.app_inv_tail, list_map_inj in Hm.
  - now subst.
  - intros [[n0] v0] [[n0'] v0'] Heq. injection Heq as Hn0 Hv0.
    apply shift_inj_v in Hv0; [|
      intros ? ? Heq'; apply lift_inj in Heq'; auto; intros ? ? Heq''; injection Heq''; lia
    ].
    subst; repeat f_equal. lia.
Qed.

(* goal 4 *)
Lemma e_of_list_is_list :
  forall xs xs2 n (v : Value _) c1 (m m' : Map _) c,
    Is_Valid_Map m ->
    C[e_of_list xs2, m ~~> v, m' | c] ->
    S n = of_label (new_label m) ->
    xs2 = List.map (map_labels_v (lift (fun n' => OfNat (plus n n')))) xs ->
    is_list xs2 v c1 m'.
Proof.
  intros xs xs2 n v m m' c Hvalid Hred. intros; subst.
(*  eapply v_of_list_e_of_list_general in Hred as Heq.
  destruct (v_of_list xs) eqn:Hxs.
  destruct e_of_list_v_of_list with xs v0 m0. specialize (H Hxs).*)
(*
  eapply extend_state in H.
  - inversion Hred; [constructor | discriminate_red_Val].
  - eapply f_cons_red_to_list.

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
Abort.
*)