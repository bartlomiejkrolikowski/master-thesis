Require List.
Import List.ListNotations.
Require Import String.
Require Import ZArith.

Require Import src.LambdaRef.
Require Import src.LamRefFacts.
Require Import src.LambdaAssertions_credits_perm.
Require Import src.LambdaTotalTriple_credits_perm.
Require Import src.LamRefLogicFactsTotal_credits_perm.
Require Import Lia.
Require Import src.Tactics.
Require Import src.SA_Tactics.
Require Import src.Interweave.

Definition assign_array_at : Value string :=
  ([-\] "array", [-\] "index", [-\] "value",
    (Var "array" >> Var "index") <- Var "value")%string.

Definition read_array_at : Value string :=
  ([-\] "array", [-\] "index", ! (Var "array" >> Var "index"))%string.

Definition incr : Value string :=
  ([-\] "p", Var "p" <- ! Var "p" [+] Int 1)%string.

Definition init_array : Value string :=
  [-\] "array", [-\] "size", [-\] "value",
    [let "i"] Ref (Int 0) [in]
      [while] ! Var "i" [<] Var "size" [do]
        (*(Var "array" >> ! Var "i") <- Var "value";;*)
        assign_array_at <* Var "array" <* ! Var "i" <* Var "value";;
        incr <* Var "i"
      [end];;
      Free (Var "i")
    [end]%string.

Definition free_array_at : Value string :=
  ([-\] "array", [-\] "i", Free (Var "array" >> ! Var "i"))%string.

Definition free_array : Value string :=
  [-\] "array", [-\] "size",
    [let "i"] Ref (Int 0) [in]
      [while] ! Var "i" [<] Var "size" [do]
        (*Free (Var "array" >> ! Var "i");;
        Var "i" <- ! Var "i" [+] Int 1*)
        free_array_at <* Var "array" <* Var "i";;
        incr <* Var "i"
      [end];;
      Free (Var "i")
    [end]%string.

Lemma only_lab_is_array V A a c m :
  @array_content V A a c m ->
  exists n, a = Lab (OfNat n).
Proof.
  intros [].
  - destruct l. eauto.
  - eauto.
Qed.

Ltac injection_ctx :=
  match goal with
  | [H : ?f _ = ?f _ |- _] => injection H; clear H; intros; subst
  end.

Lemma triple_fun_assign_array_at A A' A1 ov A2 a i x :
  List.length A1 = i ->
  A = (A1 ++ ov::A2)%list ->
  A' = (A1 ++ Some x::A2)%list ->
  triple_fun assign_array_at
    (fun v => $1 <*> <[v = a]>)
    (fun v => <[
      triple_fun v
        (fun v => $1 <*> <[v = Int (Z.of_nat i)]>)
        (fun v => <[
          triple_fun v
            (fun v => $3 <*> <[v = x]> <*> array_content A a)
            (fun v => <[v = U_val]> <*> array_content A' a)
        ]>)
    ]>).
Proof.
  intros. subst. unfold triple_fun, assign_array_at, StringLam. simpl. intros.
  app_lambda. solve_simple_value. normalize_star. subst. split_all; auto.
  intros. cbn. solve_simple_value. normalize_star. subst. split_all; auto.
  intros. app_lambda. solve_simple_value. normalize_star. split_all; auto.
  intros. cbn. solve_simple_value. normalize_star. subst. split_all; auto.
  intros. triple_pull_1_credit. app_lambda. solve_simple_value.
  swap_star_ctx. normalize_star. subst. split_all; auto. intros. cbn.
  rewrite_all_binds. unfold sa_star, sa_credits in * |-. edestruct_direct.
  match goal with
  | [H : array_content _ _ _ _ |- _] => apply only_lab_is_array in H as (?&->)
  end.
  eapply triple_weaken.
  1-2:intros; repeat (apply star_implies_mono; [prove_implies_refl|]);
    apply implies_spec; intros ? ? ?%array_content_app; eassumption.
  eapply triple_weaken.
  1-2:intros; repeat (apply star_implies_mono; [prove_implies_refl|]);
    apply implies_spec; intros ? ? ?%array_content_cons; eassumption.
  triple_reorder_exists. triple_pull_exists.
  triple_reorder_pure. repeat triple_pull_pure. subst. injection_ctx.
  triple_pull_1_credit.
  eapply triple_weaken, triple_frame,
    triple_assign with (Q2 := fun v' => <[v' = x]> <*> _).
  { prove_implies_rev. }
  { intros. simpl. prove_implies_rev. apply implies_spec. intros. normalize_star.
    swap_star_ctx. normalize_star. subst.
    match goal with
    | [H : _ ?c ?m |- _ ?c ?m] => apply empty_star_l_cancel in H
    end.
    solve_star. revert_implies. prove_implies. }
  2:solve_simple_value.
  triple_reorder_credits.
  lazymatch goal with
  | [|- triple (Val (Lab (OfNat ?n)) >> Val (Int ?i)) _ _] =>
    eapply triple_weaken, triple_shift with
      (Q1 := fun n' => <[n' = n]> <*> _)
      (Q2 := fun n' i' => <[n' = n]> <*> <[i' = i]> <*> _)
  end.
  { prove_implies. }
  { intros. simpl. apply implies_spec. intros. normalize_star. swap_star.
    solve_star. apply empty_star_l_intro. subst. rewrite Nat2Z.id.
    solve_star; eauto. }
  - solve_simple_value.
  - intros. simpl. solve_simple_value; normalize_star; eauto. lia.
Qed.

Lemma triple_fun_n_ary_assign_array_at A A' A1 ov A2 i x :
  List.length A1 = i ->
  A = (A1 ++ ov::A2)%list ->
  A' = (A1 ++ Some x::A2)%list ->
  triple_fun_n_ary 2 assign_array_at
    (fun a v2 v3 =>
      $2 <*> <[v2 = Int (Z.of_nat i)]> <*> <[v3 = x]> <*> array_content A a)
    (fun a v2 v3 v => <[v = U_val]> <*> array_content A' a).
Proof.
  simpl.
  intros. subst. unfold triple_fun, assign_array_at, StringLam. simpl. intros.
  app_lambda. solve_simple_value. normalize_star. subst. split_all; auto.
  intros. cbn. solve_simple_value. normalize_star. subst. split_all; auto.
  intros. app_lambda. solve_simple_value. normalize_star. split_all; auto.
  intros. cbn. solve_simple_value. normalize_star. subst. split_all; auto.
  intros. triple_reorder_credits. app_lambda. solve_simple_value.
  swap_star_ctx. normalize_star. subst. split_all; auto. intros. cbn.
  rewrite_all_binds. unfold sa_star, sa_credits in * |-. edestruct_direct.
  match goal with
  | [H : array_content _ _ _ _ |- _] => apply only_lab_is_array in H as (?&->)
  end.
  eapply triple_weaken.
  { intros. apply star_implies_mono; [prove_implies_refl|].
    apply star_implies_mono; [|prove_implies_refl].
    repeat (apply star_implies_mono; [prove_implies_refl|]).
    apply implies_spec. intros ? ? ?%array_content_app. revert_implies.
    repeat (apply star_implies_mono; [prove_implies_refl|]).
    apply implies_spec. intros ? ? ?%array_content_cons. eassumption. }
  { intros. repeat (apply star_implies_mono; [prove_implies_refl|]).
    apply implies_spec. intros. apply array_content_app. revert_implies.
    repeat (apply star_implies_mono; [prove_implies_refl|]).
    apply implies_spec. intros. apply array_content_cons. eassumption. }
  triple_reorder_exists. triple_pull_exists.
  triple_reorder_pure. repeat triple_pull_pure. subst. injection_ctx.
  triple_pull_1_credit.
  eapply triple_weaken, triple_frame,
    triple_assign with (Q2 := fun v' => <[v' = x]> <*> _).
  { prove_implies_rev. }
  { intros. simpl. prove_implies_rev. apply implies_spec. intros. normalize_star.
    swap_star_ctx. normalize_star. subst.
    match goal with
    | [H : _ ?c ?m |- _ ?c ?m] => apply empty_star_l_cancel in H
    end.
    solve_star. revert_implies. prove_implies. }
  2:solve_simple_value.
  triple_reorder_credits.
  lazymatch goal with
  | [|- triple (Val (Lab (OfNat ?n)) >> Val (Int ?i)) _ _] =>
    eapply triple_weaken, triple_shift with
      (Q1 := fun n' => <[n' = n]> <*> _)
      (Q2 := fun n' i' => <[n' = n]> <*> <[i' = i]> <*> _)
  end.
  { prove_implies. }
  { intros. simpl. apply implies_spec. intros. normalize_star. swap_star.
    solve_star. apply empty_star_l_intro. subst. rewrite Nat2Z.id.
    solve_star; eauto. }
  - apply triple_value_implies. apply implies_spec. intros. eexists.
    do 2 (apply star_pure_l; split; auto). eassumption.
  - intros. simpl. solve_simple_value; normalize_star; eauto. lia.
Qed.

Hint Unfold inc_set : is_closed_db.

Lemma is_closed_value_assign_array_at :
  is_closed_value assign_array_at.
Proof.
  unfold assign_array_at, StringLam. simpl.
  fold_all_inc_set_string.
  auto 20 with is_closed_db.
Qed.

Global Opaque assign_array_at.

Corollary is_limited_value_assign_array_at :
  is_limited_value Empty_set (fun x => match x with end) assign_array_at.
Proof.
  apply is_closed_value_assign_array_at.
Qed.

Global Hint Resolve is_closed_value_assign_array_at : is_closed_db.
Global Hint Resolve is_limited_value_assign_array_at : is_closed_db.

Lemma triple_fun_n_ary_read_array_at A A1 x A2 i :
  List.length A1 = i ->
  A = (A1 ++ Some x::A2)%list ->
  triple_fun_n_ary 1 read_array_at
    (fun a v2 => $2 <*> <[v2 = Int (Z.of_nat i)]> <*> array_content A a)
    (fun a v2 v => <[v = x]> <*> array_content A a).
Proof.
  simpl.
  intros. subst. unfold triple_fun, read_array_at, StringLam. simpl. intros.
  app_lambda. solve_simple_value. normalize_star. subst. split_all; auto.
  intros. cbn. solve_simple_value. normalize_star. subst. split_all; auto.
  intros. triple_reorder_credits. app_lambda. solve_simple_value.
  swap_star_ctx. normalize_star. subst. split_all; auto. intros. cbn.
  rewrite_all_binds. unfold sa_star, sa_credits in * |-. edestruct_direct.
  match goal with
  | [H : array_content _ _ _ _ |- _] => apply only_lab_is_array in H as (?&->)
  end.
  eapply triple_weaken.
  { intros. apply star_implies_mono; [prove_implies_refl|].
    apply star_implies_mono; [|prove_implies_refl].
    repeat (apply star_implies_mono; [prove_implies_refl|]).
    apply implies_spec. intros ? ? ?%array_content_app. revert_implies.
    repeat (apply star_implies_mono; [prove_implies_refl|]).
    apply implies_spec. intros ? ? ?%array_content_cons. eassumption. }
  { intros. repeat (apply star_implies_mono; [prove_implies_refl|]).
    apply implies_spec. intros. apply array_content_app. revert_implies.
    repeat (apply star_implies_mono; [prove_implies_refl|]).
    apply implies_spec. intros. apply array_content_cons. eassumption. }
  triple_reorder_exists. triple_pull_exists.
  triple_reorder_pure. repeat triple_pull_pure. subst. injection_ctx.
  triple_pull_1_credit.
  eapply triple_weaken, triple_deref.
  { prove_implies_rev. }
  { apply implies_post_spec. intros. normalize_star. solve_star. swap_star.
    solve_star. swap_star. solve_star. swap_star. solve_star. swap_star.
    revert_implies. prove_implies_rev. }
  triple_reorder_credits.
  lazymatch goal with
  | [|- triple (Val (Lab (OfNat ?n)) >> Val (Int ?i)) _ _] =>
    eapply triple_weaken, triple_shift with
      (Q1 := fun n' => <[n' = n]> <*> _)
      (Q2 := fun n' i' => <[n' = n]> <*> <[i' = i]> <*> _)
  end.
  { prove_implies. }
  { intros. simpl. apply implies_spec. intros. normalize_star. subst.
    solve_star. }
  - apply triple_value_implies. apply implies_spec. intros. eexists.
    do 2 (apply star_pure_l; split; auto). eassumption.
  - intros. simpl. solve_simple_value; normalize_star; eauto; repeat f_equal;
      try lia.
    revert_implies. prove_implies.
Qed.

Lemma is_closed_value_read_array_at :
  is_closed_value read_array_at.
Proof.
  unfold read_array_at, StringLam. simpl.
  fold_all_inc_set_string.
  auto 20 with is_closed_db.
Qed.

Global Opaque read_array_at.

Corollary is_limited_value_read_array_at :
  is_limited_value Empty_set (fun x => match x with end) read_array_at.
Proof.
  apply is_closed_value_read_array_at.
Qed.

Global Hint Resolve is_closed_value_read_array_at : is_closed_db.
Global Hint Resolve is_limited_value_read_array_at : is_closed_db.

Lemma triple_fun_incr l i :
  triple_fun incr
    (fun v => $4 <*> <[v = Lab l]> <*> <(l :== Int i)>)
    (fun v => <[v = U_val]> <*> <(l :== Int (i+1))>).
Proof.
  unfold triple_fun, incr, StringLam. simpl. intros. triple_pull_1_credit.
  app_lambda. solve_simple_value. split_all; auto. intros. cbn.
  triple_reorder_pure. triple_pull_pure. subst. triple_pull_1_credit.
  eapply triple_weaken, triple_assign with (Q2 := fun v' => <[v' = Int (i+1)]>).
  { prove_implies_rev. }
  { intros. simpl. prove_implies. apply implies_spec. intros. normalize_star.
    swap_star_ctx. normalize_star. subst. assumption. }
  - solve_simple_value.
  - triple_pull_1_credit.
    eapply triple_weaken, triple_iadd with
      (Q1 := fun i1 => <[i1 = i]> <*> _)
      (Q2 := fun i1 i2 => <[i1 = i]> <*> <[i2 = 1%Z]> <*> _).
    { prove_implies. }
    { apply implies_post_spec. intros. normalize_star. subst. swap_star.
      solve_star. eassumption. }
    + eapply triple_weaken, triple_deref.
      { apply empty_star_r_intro. }
      { apply implies_post_spec. intros. normalize_star. subst. solve_star.
        eassumption. }
      solve_simple_value.
    + intros. triple_pull_pure. subst. solve_simple_value. revert_implies.
      apply empty_star_r_cancel.
Qed.

Lemma triple_fun_n_ary_incr l i :
  triple_fun_n_ary 0 incr
    (fun v => $3 <*> <[v = Lab l]> <*> <(l :== Int i)>)
    (fun v res => <[res = U_val]> <*> <(l :== Int (i+1))>).
Proof.
  simpl.
  unfold triple_fun, incr, StringLam. simpl. intros. triple_reorder_credits.
  app_lambda. solve_simple_value. split_all; auto. intros. cbn.
  triple_reorder_pure. repeat triple_pull_pure. subst. triple_pull_1_credit.
  eapply triple_weaken, triple_assign with (Q2 := fun v' => <[v' = Int (i+1)]>).
  { prove_implies_rev. }
  { intros. simpl. prove_implies. apply implies_spec. intros. normalize_star.
    swap_star_ctx. normalize_star. subst. assumption. }
  - solve_simple_value.
  - triple_pull_1_credit.
    eapply triple_weaken, triple_iadd with
      (Q1 := fun i1 => <[i1 = i]> <*> _)
      (Q2 := fun i1 i2 => <[i1 = i]> <*> <[i2 = 1%Z]> <*> _).
    { prove_implies. }
    { apply implies_post_spec. intros. normalize_star. subst. swap_star.
      solve_star. eassumption. }
    + eapply triple_weaken, triple_deref.
      { apply empty_star_r_intro. }
      { apply implies_post_spec. intros. normalize_star. subst. solve_star.
        eassumption. }
      solve_simple_value.
    + intros. triple_pull_pure. subst. solve_simple_value. revert_implies.
      apply empty_star_r_cancel.
Qed.

Lemma is_closed_value_incr :
  is_closed_value incr.
Proof.
  unfold incr, StringLam. simpl.
  fold_all_inc_set_string.
  auto 20 with is_closed_db.
Qed.

Global Opaque incr.

Corollary is_limited_value_incr :
  is_limited_value Empty_set (fun x => match x with end) incr.
Proof.
  apply is_closed_value_incr.
Qed.

Global Hint Resolve is_closed_value_incr : is_closed_db.
Global Hint Resolve is_limited_value_incr : is_closed_db.

Ltac omit_subst H :=
  revert H; subst; intro.

Lemma triple_fun_init_array A a s x :
  s = List.length A ->
  triple_fun init_array
    (fun v => $1 <*> <[v = a]>)
    (fun v => <[
      triple_fun v
        (fun v => $1 <*> <[v = Int (Z.of_nat s)]>)
        (fun v => <[
          triple_fun v
            (fun v => <[v = x]> <*> $ (9 + s*16) <*> array_content A a)
            (fun v => <[v = U_val]> <*> array_content (List.repeat (Some x) s) a)
        ]>)
    ]>).
Proof.
  unfold triple_fun, init_array, StringLam. simpl. intros.
  repeat (rewrite map_v_shift_closed;
    [|repeat apply map_v_closed_value; auto with is_closed_db]).
  app_lambda. solve_simple_value. normalize_star. subst.
  split_all; auto. intros. cbn. subst. triple_pull_pure. subst.
  solve_simple_value. rewrite_empty_spec. rewrite pure_spec. split_all; auto.
  intros. app_lambda. solve_simple_value. normalize_star. subst.
  split_all; auto. intros. cbn. triple_pull_pure. subst. solve_simple_value.
  rewrite_empty_spec. rewrite pure_spec. split_all; auto. intros.
  triple_pull_1_credit. app_lambda. solve_simple_value. swap_star_ctx.
  normalize_star. subst. split_all; auto. intros. cbn.
  triple_reorder_pure. triple_pull_pure. subst. triple_pull_1_credit.
  app_lambda.
  2:{ triple_pull_1_credit.
      eapply triple_ref with (Q := fun v => <[v = Int 0]> <*> _).
      solve_simple_value. }
  solve_simple_value. split_all; auto. intros. cbn. repeat triple_pull_exists.
  triple_reorder_pure. triple_pull_pure. subst. triple_pull_1_credit.
  remember (List.length A) as s eqn:Hs.
  rewrite_all_binds. eapply triple_seq.
  - triple_reorder_pure. triple_pull_pure. omit_subst Hs.
    triple_reorder_credits. triple_pull_credits 2. triple_reorder_credits.
    eapply triple_weaken with
      (P := $2 <*> <exists> i A',
        $(3+(s-Z.to_nat i)*_) <*>
        (array_content (List.repeat (Some x) (Z.to_nat i) ++ A') a <*>
        <(x0 :== Int i)> <*> <[(i >= 0)%Z]> <*> <[(i <= Z.of_nat s)%Z]> <*>
        <[List.length A' = s - Z.to_nat i]>)%list).
    { prove_implies. apply implies_spec. intros. exists 0%Z, A. simpl.
      rewrite Nat.sub_0_r. revert_implies. prove_implies. apply implies_spec.
      intros. swap_star. solve_star. swap_star. solve_star; lia. }
    { prove_implies_refl. }
    apply triple_while with
      (Q := fun b => <exists> i A', $(1+(s - Z.to_nat i)*16) <*>
        (array_content (List.repeat (Some x) (Z.to_nat i) ++ A') a <*>
        <(x0 :== Int i)>) <*> (<[(i >= 0)%Z]> <*> <[(i <= Z.of_nat s)%Z]> <*>
        <[List.length A' = s - Z.to_nat i]> <*> <[b = (i <? Z.of_nat s)%Z]>)).
    + repeat triple_pull_exists. triple_pull_1_credit.
      eapply triple_weaken, triple_clt with
        (Q1 := fun i1 => <exists> A',
          $_ <*> (_ <*> <(x0 :== Int i1)>) <*>
          (<[(i1 >= 0)%Z]> <*> <[(i1 <= Z.of_nat s)%Z]> <*>
          <[List.length A' = _]>))
        (Q2 := fun i1 i2 => <[i2 = Z.of_nat s]> <*> <exists> A',
          ($_ <*> (_ <*> <(x0 :== Int i1)>)) <*>
          (<[(i1 >= 0)%Z]> <*> <[(i1 <= Z.of_nat s)%Z]> <*>
          <[List.length A' = _]>)).
      { prove_implies_refl. }
      { apply implies_post_spec. intros. normalize_star. omit_subst Hs.
        solve_star. do 2 apply star_assoc_r. swap_star. solve_star. }
      * triple_pull_1_credit. eapply triple_weaken, triple_deref.
        { prove_implies_rev. }
        { apply implies_post_spec. intros. normalize_star. omit_subst Hs.
          solve_star. swap_star. do 2 apply star_assoc_l. swap_star.
          apply star_assoc_l. eassumption. }
        solve_simple_value. revert_implies. prove_implies_rev.
      * intros. simpl. solve_simple_value.
    + repeat triple_pull_exists. triple_reorder_pure. repeat triple_pull_pure.
      match goal with
      | [H : true = (_ <? _)%Z |- _] => symmetry in H; apply Z.ltb_lt in H
      end.
      destruct s; [simpl in *; lia|]. rewrite Nat.sub_succ_l in *; try lia.
      lazymatch goal with
      | [H : List.length ?L = S (_ - _) |- _] =>
        destruct L; [discriminate|injection H as H]
      end.
      simpl "*".
      pose proof triple_fun_n_ary_app as Hn_ary.
      pose proof triple_fun_n_ary_frame as Hframe.
      pose proof triple_fun_n_ary_weaken as Hweaken.
      triple_pull_1_credit.
      eapply triple_seq with (Q1 := (array_content _ a <*> _) <*> ($ _)).
      * triple_pull_credits 6. triple_reorder_credits.
        triple_pull_credits 5. triple_reorder_credits.
        triple_pull_credits 2. triple_reorder_credits.
        repeat match goal with
        | [H : ?T _ _ |- _] =>
          let TT := ltac:(type of T) in
          unify TT (StateAssertion string);
          (*idtac H T;*) clear H
        end.
        eapply triple_weaken with
          (P := ($_ <*> ($_ <*> ($_ <*> (array_content _ _ <*> _)))) <*> ($ _)).
        { prove_implies. }
        { intros. apply star_assoc. }
        apply triple_frame. revert a.
        match goal with
        | [|-
          forall a,
            triple (Val (@?f a) <* (@?e1 a) <* (@?e2 a) <* (@?e3 a))
              ($2 <*> (@?P0 a))
              (@?Q1 a)
          ] =>
          intros a;
          specialize Hn_ary with
            (v := f a) (e := e1 a) (es := [e2 a;e3 a]%list)
            (P := P0 a) (Q2 := fun a _ _ => Q1 a)
        end.
        pose proof triple_fun_n_ary_assign_array_at as Hassign_array_at.
        specialize (Hframe _ assign_array_at 2).
        specialize (Hweaken _ assign_array_at 2).
        simpl in Hn_ary, Hassign_array_at, Hframe, Hweaken. eapply Hn_ary.
        { eapply Hweaken.
          { intros. apply implies_refl. }
          { intros. apply star_assoc_r. }
          simpl. eapply Hframe.
          eapply Hassign_array_at with
            (A1 := List.repeat (Some x) (Z.to_nat _));
          eauto. }
        { solve_simple_value. revert_implies. prove_implies_refl. }
        { triple_pull_1_credit.
          eapply triple_weaken, triple_deref;
            [prove_implies_rev| |solve_simple_value].
          apply implies_post_spec. intros. normalize_star. subst. solve_star.
          revert_implies.
          lazymatch goal with
          | [|- _ ->> _ ?x] =>
            let t := ltac:(fresh "x") in remember x as t
          end.
          prove_implies_refl. }
        { solve_simple_value. revert_implies. prove_implies_refl. }
        { simpl. apply implies_spec. intros. do 2 (swap_star; solve_star).
          { f_equal. rewrite List.repeat_length. symmetry. apply Z2Nat.id. lia. }
          revert_implies. prove_implies. }
      * triple_reorder_credits.
        triple_pull_credits 7. triple_reorder_credits.
        triple_pull_credits 4. triple_reorder_credits.
        triple_pull_credits 3. triple_reorder_credits.
        triple_pull_credits 0. triple_reorder_credits.
        repeat match goal with
        | [H : ?T _ _ |- _] =>
          let TT := ltac:(type of T) in
          unify TT (StateAssertion string);
          (*idtac H T;*) clear H
        end.
        eapply triple_weaken with
          (P := ($_ <*> ($_ <*> ($_ <*> ($_ <*> <(_ :== _)>)))) <*>
            (array_content _ _ <*> $ _))
          (Q := fun v => $3 <*> (<[_ = _]> <*> <(_ :== _)>) <*>
            (array_content _ _ <*> $ _)).
        { prove_implies. }
        { apply implies_post_spec. intros. normalize_star. swap_star_ctx.
          normalize_star. solve_star; eauto. swap_star. apply star_exists_l.
          eexists (Z.succ _). solve_star. swap_star. solve_star. swap_star.
          solve_star. swap_star. solve_star.
          { rewrite Z.ge_le_iff in *. eauto using Z.le_le_succ_r. }
          { lia. }
          { rewrite Z2Nat.inj_succ; try lia. simpl. eassumption. }
          rewrite Z2Nat.inj_succ; try lia. simpl List.repeat.
          rewrite List.repeat_cons, <- List.app_assoc. simpl.
          swap_star. revert_implies. prove_implies. }
        apply triple_frame.
        lazymatch goal with
        | [|- triple (_ <* Val ?v) _ _] =>
          let x := ltac:(fresh "v") in
          remember v as x; generalize dependent x
        end.
        match goal with
        | [|-
          forall a, _ ->
            triple (Val (@?f a) <* (@?e1 a))
              ($0 <*> (@?P0 a))
              (@?Q1 a)
          ] =>
          let x := ltac:(fresh a) in
          intros x ?;
          specialize Hn_ary with
            (v := f x) (e := e1 x) (es := []%list)
            (P := P0 x) (Q2 := fun x => Q1 x)
        end.
        pose proof triple_fun_n_ary_incr as Hincr.
        specialize (Hframe _ incr 0).
        specialize (Hweaken _ incr 0).
        simpl in Hn_ary, Hincr, Hframe, Hweaken. eapply Hn_ary.
        { rewrite <- Z.add_1_r. eapply Hweaken, Hframe, Hincr.
          { intros. apply implies_refl. }
          { intros. simpl. prove_implies. } }
        { solve_simple_value. revert_implies. prove_implies_refl. }
        { simpl. apply implies_spec. intros. do 2 (swap_star; solve_star).
          revert_implies. prove_implies. }
  - repeat triple_pull_exists. triple_reorder_pure. repeat triple_pull_pure.
    lazymatch goal with
    | [H : List.length ?L = s - ?n |- _] =>
      assert (n = s /\ List.length L = 0) as (->&?) by lia;
      destruct L; [|discriminate]
    end.
    rewrite Nat.sub_diag, List.app_nil_r. simpl.
    eapply triple_weaken, triple_free.
    { prove_implies_rev. }
    { intros. prove_implies. }
    solve_simple_value.
Qed.

Lemma triple_fun_n_ary_init_array A s :
  s = List.length A ->
  triple_fun_n_ary 2 init_array
    (fun a v2 x => <[v2 = Int (Z.of_nat s)]> <*> $ (8 + s*16) <*> array_content A a)
    (fun a _ x v => <[v = U_val]> <*> array_content (List.repeat (Some x) s) a).
Proof.
  unfold triple_fun_n_ary, triple_fun, init_array, StringLam. simpl. intros Hs a ?.
  repeat (rewrite map_v_shift_closed;
    [|repeat apply map_v_closed_value; auto with is_closed_db]).
  app_lambda. solve_simple_value. normalize_star. subst.
  split_all; auto. intros. cbn. subst. triple_pull_pure. subst.
  solve_simple_value. rewrite_empty_spec. rewrite pure_spec. split_all; auto.
  intros v2 ?. app_lambda. solve_simple_value. normalize_star. subst.
  split_all; auto. intros. cbn. triple_pull_pure. subst. solve_simple_value.
  rewrite_empty_spec. rewrite pure_spec. split_all; auto. intros x ?.
  triple_reorder_credits. app_lambda. solve_simple_value. swap_star_ctx.
  normalize_star. subst. split_all; auto. intros. cbn.
  triple_reorder_pure. triple_pull_pure. subst. triple_pull_1_credit.
  app_lambda.
  2:{ triple_pull_1_credit.
      eapply triple_ref with (Q := fun v => <[v = Int 0]> <*> _).
      solve_simple_value. }
  solve_simple_value. split_all; auto. intros. cbn. repeat triple_pull_exists.
  triple_reorder_pure. repeat triple_pull_pure. subst. triple_pull_1_credit.
  remember (List.length A) as s eqn:Hs.
  rewrite_all_binds. eapply triple_seq.
  - triple_reorder_credits. triple_pull_credits 2. triple_reorder_credits.
    eapply triple_weaken with
      (P := $2 <*> <exists> i A',
        $(3+(s-Z.to_nat i)*_) <*>
        (array_content (List.repeat (Some x) (Z.to_nat i) ++ A') a <*>
        <(x0 :== Int i)> <*> <[(i >= 0)%Z]> <*> <[(i <= Z.of_nat s)%Z]> <*>
        <[List.length A' = s - Z.to_nat i]>)%list).
    { prove_implies. apply implies_spec. intros. exists 0%Z, A. simpl.
      rewrite Nat.sub_0_r. revert_implies. prove_implies. apply implies_spec.
      intros. swap_star_ctx. normalize_star. subst.
      swap_star. solve_star. swap_star. solve_star; lia. }
    { prove_implies_refl. }
    apply triple_while with
      (Q := fun b => <exists> i A', $(1+(s - Z.to_nat i)*16) <*>
        (array_content (List.repeat (Some x) (Z.to_nat i) ++ A') a <*>
        <(x0 :== Int i)>) <*> (<[(i >= 0)%Z]> <*> <[(i <= Z.of_nat s)%Z]> <*>
        <[List.length A' = s - Z.to_nat i]> <*> <[b = (i <? Z.of_nat s)%Z]>)).
    + repeat triple_pull_exists. triple_pull_1_credit.
      eapply triple_weaken, triple_clt with
        (Q1 := fun i1 => <exists> A',
          $_ <*> (_ <*> <(x0 :== Int i1)>) <*>
          (<[(i1 >= 0)%Z]> <*> <[(i1 <= Z.of_nat s)%Z]> <*>
          <[List.length A' = _]>))
        (Q2 := fun i1 i2 => <[i2 = Z.of_nat s]> <*> <exists> A',
          ($_ <*> (_ <*> <(x0 :== Int i1)>)) <*>
          (<[(i1 >= 0)%Z]> <*> <[(i1 <= Z.of_nat s)%Z]> <*>
          <[List.length A' = _]>)).
      { prove_implies_refl. }
      { apply implies_post_spec. intros. normalize_star. omit_subst Hs.
        solve_star. do 2 apply star_assoc_r. swap_star. solve_star. }
      * triple_pull_1_credit. eapply triple_weaken, triple_deref.
        { prove_implies_rev. }
        { apply implies_post_spec. intros. normalize_star. omit_subst Hs.
          solve_star. swap_star. do 2 apply star_assoc_l. swap_star.
          apply star_assoc_l. eassumption. }
        solve_simple_value. revert_implies. prove_implies_rev.
      * intros. simpl. solve_simple_value.
    + repeat triple_pull_exists. triple_reorder_pure. repeat triple_pull_pure.
      match goal with
      | [H : true = (_ <? _)%Z |- _] => symmetry in H; apply Z.ltb_lt in H
      end.
      destruct s; [simpl in *; lia|]. rewrite Nat.sub_succ_l in *; try lia.
      lazymatch goal with
      | [H : List.length ?L = S (_ - _) |- _] =>
        destruct L; [discriminate|injection H as H]
      end.
      simpl "*".
      pose proof triple_fun_n_ary_app as Hn_ary.
      pose proof triple_fun_n_ary_frame as Hframe.
      pose proof triple_fun_n_ary_weaken as Hweaken.
      triple_pull_1_credit.
      eapply triple_seq with (Q1 := (array_content _ a <*> _) <*> ($ _)).
      * triple_pull_credits 6. triple_reorder_credits.
        triple_pull_credits 5. triple_reorder_credits.
        triple_pull_credits 2. triple_reorder_credits.
        repeat match goal with
        | [H : ?T _ _ |- _] =>
          let TT := ltac:(type of T) in
          unify TT (StateAssertion string);
          (*idtac H T;*) clear H
        end.
        eapply triple_weaken with
          (P := ($_ <*> ($_ <*> ($_ <*> (array_content _ _ <*> _)))) <*> ($ _)).
        { prove_implies. }
        { intros. apply star_assoc. }
        apply triple_frame. revert a.
        match goal with
        | [|-
          forall a,
            triple (Val (@?f a) <* (@?e1 a) <* (@?e2 a) <* (@?e3 a))
              ($2 <*> (@?P0 a))
              (@?Q1 a)
          ] =>
          intros a;
          specialize Hn_ary with
            (v := f a) (e := e1 a) (es := [e2 a;e3 a]%list)
            (P := P0 a) (Q2 := fun a _ _ => Q1 a)
        end.
        pose proof triple_fun_n_ary_assign_array_at as Hassign_array_at.
        specialize (Hframe _ assign_array_at 2).
        specialize (Hweaken _ assign_array_at 2).
        simpl in Hn_ary, Hassign_array_at, Hframe, Hweaken. eapply Hn_ary.
        { eapply Hweaken.
          { intros. apply implies_refl. }
          { intros. apply star_assoc_r. }
          simpl. eapply Hframe.
          eapply Hassign_array_at with
            (A1 := List.repeat (Some x) (Z.to_nat _));
          eauto. }
        { solve_simple_value. revert_implies. prove_implies_refl. }
        { triple_pull_1_credit.
          eapply triple_weaken, triple_deref;
            [prove_implies_rev| |solve_simple_value].
          apply implies_post_spec. intros. normalize_star. subst. solve_star.
          revert_implies.
          lazymatch goal with
          | [|- _ ->> _ ?x] =>
            let t := ltac:(fresh "x") in remember x as t
          end.
          prove_implies_refl. }
        { solve_simple_value. revert_implies. prove_implies_refl. }
        { simpl. apply implies_spec. intros. do 2 (swap_star; solve_star).
          { f_equal. rewrite List.repeat_length. symmetry. apply Z2Nat.id. lia. }
          revert_implies. prove_implies. }
      * triple_reorder_credits.
        triple_pull_credits 7. triple_reorder_credits.
        triple_pull_credits 4. triple_reorder_credits.
        triple_pull_credits 3. triple_reorder_credits.
        triple_pull_credits 0. triple_reorder_credits.
        repeat match goal with
        | [H : ?T _ _ |- _] =>
          let TT := ltac:(type of T) in
          unify TT (StateAssertion string);
          (*idtac H T;*) clear H
        end.
        eapply triple_weaken with
          (P := ($_ <*> ($_ <*> ($_ <*> ($_ <*> <(_ :== _)>)))) <*>
            (array_content _ _ <*> $ _))
          (Q := fun v => $3 <*> (<[_ = _]> <*> <(_ :== _)>) <*>
            (array_content _ _ <*> $ _)).
        { prove_implies. }
        { apply implies_post_spec. intros. normalize_star. swap_star_ctx.
          normalize_star. solve_star; eauto. swap_star. apply star_exists_l.
          eexists (Z.succ _). solve_star. swap_star. solve_star. swap_star.
          solve_star. swap_star. solve_star.
          { rewrite Z.ge_le_iff in *. eauto using Z.le_le_succ_r. }
          { lia. }
          { rewrite Z2Nat.inj_succ; try lia. simpl. eassumption. }
          rewrite Z2Nat.inj_succ; try lia. simpl List.repeat.
          rewrite List.repeat_cons, <- List.app_assoc. simpl.
          swap_star. revert_implies. prove_implies. }
        apply triple_frame.
        lazymatch goal with
        | [|- triple (_ <* Val ?v) _ _] =>
          let x := ltac:(fresh "v") in
          remember v as x; generalize dependent x
        end.
        match goal with
        | [|-
          forall a, _ ->
            triple (Val (@?f a) <* (@?e1 a))
              ($0 <*> (@?P0 a))
              (@?Q1 a)
          ] =>
          let x := ltac:(fresh a) in
          intros x ?;
          specialize Hn_ary with
            (v := f x) (e := e1 x) (es := []%list)
            (P := P0 x) (Q2 := fun x => Q1 x)
        end.
        pose proof triple_fun_n_ary_incr as Hincr.
        specialize (Hframe _ incr 0).
        specialize (Hweaken _ incr 0).
        simpl in Hn_ary, Hincr, Hframe, Hweaken. eapply Hn_ary.
        { rewrite <- Z.add_1_r. eapply Hweaken, Hframe, Hincr.
          { intros. apply implies_refl. }
          { intros. simpl. prove_implies. } }
        { solve_simple_value. revert_implies. prove_implies_refl. }
        { simpl. apply implies_spec. intros. do 2 (swap_star; solve_star).
          revert_implies. prove_implies. }
  - repeat triple_pull_exists. triple_reorder_pure. repeat triple_pull_pure.
    lazymatch goal with
    | [H : List.length ?L = s - ?n |- _] =>
      assert (n = s /\ List.length L = 0) as (->&?) by lia;
      destruct L; [|discriminate]
    end.
    rewrite Nat.sub_diag, List.app_nil_r. simpl.
    eapply triple_weaken, triple_free.
    { prove_implies_rev. }
    { intros. prove_implies. }
    solve_simple_value.
Qed.

Lemma is_closed_value_init_array :
  is_closed_value init_array.
Proof.
  unfold init_array, StringLam. simpl.
  rewrite_all_map_v_closed.
  fold_all_inc_set_string.
  auto 40 with is_closed_db.
Qed.

Global Opaque init_array.

Corollary is_limited_value_init_array :
  is_limited_value Empty_set (fun x => match x with end) init_array.
Proof.
  apply is_closed_value_init_array.
Qed.

Global Hint Resolve is_closed_value_init_array : is_closed_db.
Global Hint Resolve is_limited_value_init_array : is_closed_db.


