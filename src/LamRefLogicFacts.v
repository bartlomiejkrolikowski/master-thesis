Require Arith.
Require List.
Import List.ListNotations.
Require Import String.
Require Import ZArith.

Require Import src.LambdaRef.
Require Import src.LamRefFacts.
Require Import src.LambdaPartialTriple.

(*
(*total correctness*)
Theorem triple_weaken (V : Set) (e : Expr V) P P' Q Q' :
  sa_implies P' P ->
  (forall v c, sa_implies (Q v c) (Q' v c)) ->
  hoare_triple e P Q ->
  hoare_triple e P' Q'.
Proof.
  unfold hoare_triple, sa_implies. intros HP HQ Hhoare v m p'.
  edestruct Hhoare as [? [? ?]]; eauto.
Qed.

Theorem triple_value (V : Set) (v : Value V) (P : StateAssertion V) :
  hoare_triple v P (fun _ c => sa_star (sa_pure (c = 0)) P).
Proof.
  unfold hoare_triple, sa_star, sa_pure, sa_empty, disjoint_maps.
  intros v' m p. repeat eexists; eauto.
Qed.

Theorem triple_value' (V : Set) (v : Value V) :
  hoare_triple v sa_empty (fun _ c => sa_pure (c = 0)).
Proof.
  unfold hoare_triple, sa_pure, sa_empty.
  intros v' m p. repeat eexists.
Qed.
*)

Theorem triple_weaken (V : Set) (e : Expr V) P P' Q Q' :
  sa_implies P' P ->
  (forall v c, sa_implies (Q v c) (Q' v c)) ->
  hoare_triple e P Q ->
  hoare_triple e P' Q'.
Proof.
  unfold hoare_triple, sa_implies. eauto.
Qed.

Theorem triple_value (V : Set) (v : Value V) (P : StateAssertion V) :
  hoare_triple v P (fun _ c => sa_star (sa_pure (c = 0)) P).
Proof.
  unfold hoare_triple, sa_star, sa_pure, sa_empty, disjoint_maps.
  intros v' c m m' Hred. inversion Hred.
  - intro p. repeat eexists; eauto.
  - discriminate_red_Val.
Qed.

Theorem triple_value' (V : Set) (v : Value V) :
  hoare_triple v sa_empty (fun _ c => sa_pure (c = 0)).
Proof.
  unfold hoare_triple, sa_pure, sa_empty.
  intros v' c m m' Hred. inversion Hred.
  - auto.
  - discriminate_red_Val.
Qed.

Theorem triple_value_untimed (V : Set) (v : Value V) (P : StateAssertion V) :
  hoare_triple v P (fun _ _ => P).
Proof.
  eapply triple_weaken; eauto using triple_value;
    unfold sa_implies, sa_star, sa_pure, sa_empty;
    [| intros v' c m [m1 [m2 [[? ?] [? [? ?]]]]]; subst ];
    eauto.
Qed.

Theorem triple_lam (V : Set) (e : Expr _) (v : Value V) P Q :
  hoare_triple (subst_e e v) P (fun v c => Q v (1+c)) ->
  hoare_triple ((-\e) <* v) P Q.
Proof.
  unfold hoare_triple. intros Hhoare v' c m m' Hred. inversion Hred. subst.
  eapply Hhoare. inversion H; subst; auto; discriminate_red_Val.
Qed.

Theorem triple_bneg (V : Set) (b : bool) :
  @hoare_triple V ([~] (Bool b))
    sa_empty
    (fun v c => sa_pure (v = Bool (negb b) /\ c = 1)).
Proof.
  unfold hoare_triple, sa_pure, sa_empty. intros v c m m' Hred p.
  inversion Hred. subst. inversion H; subst; try discriminate_red_Val.
  inversion H0; subst; auto. discriminate_red_Val.
Qed.

Theorem triple_ineg (V : Set) (i : Z) :
  @hoare_triple V ([--] Int i)
    sa_empty
    (fun v c => sa_pure (v = Int (- i) /\ c = 1)).
Proof.
  unfold hoare_triple, sa_pure, sa_empty. intros v c m m' Hred p.
  inversion Hred. subst. inversion H; subst; try discriminate_red_Val.
  inversion H0; subst; auto. discriminate_red_Val.
Qed.

Theorem triple_bor (V : Set) (b1 b2 : bool) :
  @hoare_triple V ((Bool b1) [||] (Bool b2))
    sa_empty
    (fun v c => sa_pure (v = Bool (b1 || b2) /\ c = 1)).
Proof.
  unfold hoare_triple, sa_pure, sa_empty. intros v c m m' Hred p.
  inversion Hred. subst. inversion H; subst; try discriminate_red_Val.
  inversion H0; subst; auto. discriminate_red_Val.
Qed.

Theorem triple_band (V : Set) (b1 b2 : bool) :
  @hoare_triple V ((Bool b1) [&&] (Bool b2))
    sa_empty
    (fun v c => sa_pure (v = Bool (b1 && b2) /\ c = 1)).
Proof.
  unfold hoare_triple, sa_pure, sa_empty. intros v c m m' Hred p.
  inversion Hred. subst. inversion H; subst; try discriminate_red_Val.
  inversion H0; subst; auto. discriminate_red_Val.
Qed.

Theorem triple_iadd (V : Set) (i1 i2 : Z) :
  @hoare_triple V (Int i1 [+] Int i2)
    sa_empty
    (fun v c => sa_pure (v = Int (i1 + i2) /\ c = 1)).
Proof.
  unfold hoare_triple, sa_pure, sa_empty. intros v c m m' Hred p.
  inversion Hred. subst. inversion H; subst; try discriminate_red_Val.
  inversion H0; subst; auto. discriminate_red_Val.
Qed.

Theorem triple_isub (V : Set) (i1 i2 : Z) :
  @hoare_triple V (Int i1 [-] Int i2)
    sa_empty
    (fun v c => sa_pure (v = Int (i1 - i2) /\ c = 1)).
Proof.
  unfold hoare_triple, sa_pure, sa_empty. intros v c m m' Hred p.
  inversion Hred. subst. inversion H; subst; try discriminate_red_Val.
  inversion H0; subst; auto. discriminate_red_Val.
Qed.

Theorem triple_imul (V : Set) (i1 i2 : Z) :
  @hoare_triple V (Int i1 [*] Int i2)
    sa_empty
    (fun v c => sa_pure (v = Int (i1 * i2) /\ c = 1)).
Proof.
  unfold hoare_triple, sa_pure, sa_empty. intros v c m m' Hred p.
  inversion Hred. subst. inversion H; subst; try discriminate_red_Val.
  inversion H0; subst; auto. discriminate_red_Val.
Qed.

Theorem triple_idiv (V : Set) (i1 i2 : Z) :
  @hoare_triple V (Int i1 [/] Int i2)
    sa_empty
    (fun v c => sa_pure (v = Int (i1 / i2) /\ c = 1)).
Proof.
  unfold hoare_triple, sa_pure, sa_empty. intros v c m m' Hred p.
  inversion Hred. subst. inversion H; subst; try discriminate_red_Val.
  inversion H0; subst; auto. discriminate_red_Val.
Qed.

Theorem triple_clt (V : Set) (i1 i2 : Z) :
  @hoare_triple V (Int i1 [<] Int i2)
    sa_empty
    (fun v c => sa_pure (v = Bool (i1 <? i2)%Z /\ c = 1)).
Proof.
  unfold hoare_triple, sa_pure, sa_empty. intros v c m m' Hred p.
  inversion Hred. subst. inversion H; subst; try discriminate_red_Val.
  inversion H0; subst; auto. discriminate_red_Val.
Qed.

Theorem triple_ceq (V : Set) (i1 i2 : Z) :
  @hoare_triple V (Int i1 [=] Int i2)
    sa_empty
    (fun v c => sa_pure (v = Bool (i1 =? i2)%Z /\ c = 1)).
Proof.
  unfold hoare_triple, sa_pure, sa_empty. intros v c m m' Hred p.
  inversion Hred. subst. inversion H; subst; try discriminate_red_Val.
  inversion H0; subst; auto. discriminate_red_Val.
Qed.

Theorem triple_rec_e2v (V : Set) (vs : list (Value V)) :
  hoare_triple (RecE (vals2exprs vs))
    sa_empty
    (fun v c => sa_pure (v = RecV vs /\ c = 1)).
Proof.
  unfold hoare_triple, sa_pure, sa_empty. intros v c m m' Hred p.
  inversion Hred. subst. inversion H; subst.
  - apply vals2exprs_inj in H2. subst. inversion H0; subst; auto.
    discriminate_red_Val.
  - apply SplitAt_spec_eq in H2. unfold vals2exprs in *.
    apply List.map_eq_app in H2 as [? [? [? [? ?]]]].
    destruct x0; try discriminate; simpl in *. injection H5 as ? ?. subst.
    discriminate_red_Val.
Qed.

Theorem triple_get (V : Set) (n : nat) (vs : list (Value V)) v :
  Nth n vs v ->
  @hoare_triple V (Get n (RecV vs))
    sa_empty
    (fun v' c => sa_pure (v' = v /\ c = 1)).
Proof.
  unfold hoare_triple, sa_pure, sa_empty. intros Hnth v' c m m' Hred p.
  inversion Hred. subst. inversion H; subst. apply Nth_spec in Hnth, H6.
  rewrite Hnth in *. injection H6 as ?. subst.
  inversion H0; subst; auto. discriminate_red_Val.
Qed.

Theorem triple_ref (V : Set) (v : Value V) :
  @hoare_triple V (Ref v)
    sa_empty
    (fun v' c => sa_exists
      (fun l => sa_star (sa_pure (v' = Lab l /\ c = 1)) (sa_single l v))).
Proof.
  unfold hoare_triple, sa_exists, sa_star, sa_single, sa_pure, sa_empty,
    disjoint_maps.
  intros v' c m m' Hred p. inversion Hred. subst.
  inversion H; subst; try discriminate_red_Val.
  inversion H0; subst; try discriminate_red_Val.
  repeat eexists. auto.
Qed.

Theorem triple_deref (V : Set) l (v : Value V) :
  @hoare_triple V (Deref (Lab l))
    (sa_single l v)
    (fun v' c => sa_star (sa_pure (v' = v /\ c = 1)) (sa_single l v)).
Proof.
  unfold hoare_triple, sa_star, sa_single, sa_pure, sa_empty, disjoint_maps.
  intros v' c m m' Hred p. inversion Hred. subst.
  inversion H; subst; try discriminate_red_Val. apply Lookup_spec in H2.
  - simpl in *. destruct l as [n]. unfold label_eqb, lift2, lift in *.
    rewrite Nat.eqb_refl in *. injection H2 as ?. subst.
    inversion H0; subst; try discriminate_red_Val.
    repeat eexists. auto.
  - unfold Is_Valid_Map. simpl. repeat econstructor. auto.
Qed.

Theorem triple_assign (V : Set) l (v v' : Value V) :
  @hoare_triple V (Assign (Lab l) v)
    (sa_single l v')
    (fun v'' c => sa_star (sa_pure (v'' = U_val /\ c = 1)) (sa_single l v)).
Proof.
  unfold hoare_triple, sa_star, sa_single, sa_pure, sa_empty, disjoint_maps.
  intros v'' c m m' Hred p. inversion Hred. subst.
  inversion H; subst; try discriminate_red_Val. apply Assignment_spec in H6 as [? ?].
  - simpl in *. destruct l as [n]. unfold label_eqb, lift2, lift in *.
    rewrite Nat.eqb_refl in *. subst.
    inversion H0; subst; try discriminate_red_Val.
    repeat eexists. auto.
  - unfold Is_Valid_Map. simpl. repeat econstructor. auto.
Qed.

Theorem triple_seq (V : Set) (e : Expr V) P Q :
  hoare_triple e P (fun v c => Q v (1+c)) ->
  hoare_triple (Seq U_val e) P Q.
Proof.
  unfold hoare_triple. intros Hhoare v' c m m' Hred. inversion Hred. subst.
  apply Hhoare. inversion H; subst; auto. discriminate_red_Val.
Qed.

Theorem triple_if (V : Set) (b : bool) (e1 e2 : Expr V) P Q :
  hoare_triple e1 (sa_star (sa_pure (is_true b)) P) (fun v c => Q v (1+c)) ->
  hoare_triple e2 (sa_star (sa_pure (~ is_true b)) P) (fun v c => Q v (1+c)) ->
  hoare_triple (If (Bool b) e1 e2) P Q.
Proof.
  unfold hoare_triple, sa_star, is_true, sa_pure, sa_empty, disjoint_maps.
  intros Hhoare1 Hhoare2 v' c m m' Hred p. inversion Hred. subst.
  destruct b; [eapply Hhoare1 | eapply Hhoare2]; try (repeat eexists; eauto);
    simpl; inversion H; subst; auto; discriminate_red_Val.
Qed.

Theorem triple_while (V : Set) (c1 c2 : nat) (e1 e2 : Expr V) P Q :
  hoare_triple e1
    P
    (fun v c1' => sa_exists
      (fun b => sa_star (sa_pure (v = Bool b /\ c1' = c1)) (Q b))) ->
  hoare_triple e2
    (Q true)
    (fun _ c2' => sa_star (sa_pure (c2' = c2)) P) ->
  hoare_triple (While e1 e2)
    P
    (fun _ c => sa_exists
      (fun n => sa_star (sa_pure (c = (n * (c1 + 1 + c2)) + c1 + 1)) (Q false))).
Proof.
  unfold hoare_triple, sa_exists, sa_star, is_true, sa_pure, sa_empty,
    disjoint_maps.
  intros Hhoare1 Hhoare2 v' c m m' Hred p.
  (** remember (While e1 e2) as e eqn:Hwhile.
  remember (Val v') as e' eqn:Hval. generalize dependent e'.
  generalize dependent e.*)
  induction c as [? IH] using (well_founded_ind lt_wf). inversion Hred. subst.
  inversion H. subst.
(*  destruct b; [eapply Hhoare1 | eapply Hhoare2]; try (repeat eexists; eauto);
    simpl; inversion H; subst; auto; discriminate_red_Val.*)
Admitted.

(*
| red_while : forall m e1 e2,
    R[While e1 e2, m
      ~~>
      If e1 (Seq e2 (While e1 e2)) U_val, m]

(* structural rules *)
| red_app1 : forall m m' e1 e1' e2,
    R[e1, m ~~> e1', m'] ->
    R[App e1 e2, m ~~> App e1' e2, m']

| red_app2 : forall m m' (v : Value _) e e',
    R[e, m ~~> e', m'] ->
    R[App v e, m ~~> App v e', m']

| red_unop : forall k m m' e e',
    R[e, m ~~> e', m'] ->
    R[UnOp k e, m ~~> UnOp k e', m']

| red_binop1 : forall k m m' e1 e1' e2,
    R[e1, m ~~> e1', m'] ->
    R[BinOp k e1 e2, m ~~> BinOp k e1' e2, m']

| red_binop2 : forall k m m' (v : Value _) e e',
    R[e, m ~~> e', m'] ->
    R[BinOp k v e, m ~~> BinOp k v e', m']

| red_rec_split : forall m m' es es' vs0 e e' es0,
    L[es  ~~> vals2exprs vs0 | e | es0] ->
    L[es' ~~> vals2exprs vs0 | e' | es0] ->
    R[e, m ~~> e', m'] ->
    R[RecE es, m ~~> RecE es', m']

| red_ref_e : forall m m' e e',
    R[e, m ~~> e', m'] ->
    R[Ref e, m ~~> Ref e', m']

| red_deref_e : forall m m' e e',
    R[e, m ~~> e', m'] ->
    R[Deref e, m ~~> Deref e', m']

| red_assign1 : forall m m' e1 e1' e2,
    R[e1, m ~~> e1', m'] ->
    R[Assign e1 e2, m ~~> Assign e1' e2, m']

| red_assign2 : forall m m' (v : Value _) e e',
    R[e, m ~~> e', m'] ->
    R[Assign v e, m ~~> Assign v e', m']

| red_seq1 : forall m m' e1 e1' e2,
    R[e1, m ~~> e1', m'] ->
    R[Seq e1 e2, m ~~> Seq e1' e2, m']

| red_cond_if : forall m m' e1 e1' e2 e3,
    R[e1, m ~~> e1', m'] ->
    R[If e1 e2 e3, m ~~> If e1' e2 e3, m']
*)