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
Require Import src_arrays.SA_Tactics.
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
