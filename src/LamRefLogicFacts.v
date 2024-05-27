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
  P' ->> P ->
  (forall v c, (Q v c) ->> (Q' v c)) ->
  hoare_triple e P Q ->
  hoare_triple e P' Q'.
Proof.
  unfold hoare_triple, sa_implies. eauto.
Qed.

Theorem triple_value (V : Set) (v : Value V) (P : StateAssertion V) :
  hoare_triple v P (fun _ c => <[c = 0]> <*> P).
Proof.
  unfold hoare_triple, sa_star, sa_pure, sa_empty, disjoint_maps.
  intros v' c m m' Hred. inversion Hred.
  - intro p. repeat eexists; eauto.
  - discriminate_red_Val.
Qed.

Theorem triple_value' (V : Set) (v : Value V) :
  hoare_triple v <[]> (fun _ c => <[c = 0]>).
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

Ltac inversion_red :=
  match goal with
  | [H : red _ _ _ _ |- _] =>
    inversion H; subst; clear H; try discriminate_red_Val
  end.

Ltac inversion_cost_red :=
  match goal with
  | [H : cost_red _ _ _ _ _ |- _] =>
    inversion H; subst; clear H; try discriminate_red_Val
  end.

Ltac find_red_cases :=
  unfold hoare_triple, sa_exists, sa_star, sa_single, sa_pure, sa_empty,
    disjoint_maps; intros;
  inversion_cost_red; inversion_red.

Ltac solve_red_cases :=
  find_red_cases; inversion_cost_red; subst; auto; discriminate_red_Val.

Theorem triple_bneg (V : Set) (b : bool) :
  @hoare_triple V ([~] (Bool b))
    <[]>
    (fun v c => <[v = Bool (negb b) /\ c = 1]>).
Proof.
  solve_red_cases.
Qed.

Theorem triple_ineg (V : Set) (i : Z) :
  @hoare_triple V ([--] Int i)
    <[]>
    (fun v c => <[v = Int (- i) /\ c = 1]>).
Proof.
  solve_red_cases.
Qed.

Theorem triple_bor (V : Set) (b1 b2 : bool) :
  @hoare_triple V ((Bool b1) [||] (Bool b2))
    <[]>
    (fun v c => <[v = Bool (b1 || b2) /\ c = 1]>).
Proof.
  solve_red_cases.
Qed.

Theorem triple_band (V : Set) (b1 b2 : bool) :
  @hoare_triple V ((Bool b1) [&&] (Bool b2))
    <[]>
    (fun v c => <[v = Bool (b1 && b2) /\ c = 1]>).
Proof.
  solve_red_cases.
Qed.

Theorem triple_iadd (V : Set) (i1 i2 : Z) :
  @hoare_triple V (Int i1 [+] Int i2)
    <[]>
    (fun v c => <[v = Int (i1 + i2) /\ c = 1]>).
Proof.
  solve_red_cases.
Qed.

Theorem triple_isub (V : Set) (i1 i2 : Z) :
  @hoare_triple V (Int i1 [-] Int i2)
    <[]>
    (fun v c => <[v = Int (i1 - i2) /\ c = 1]>).
Proof.
  solve_red_cases.
Qed.

Theorem triple_imul (V : Set) (i1 i2 : Z) :
  @hoare_triple V (Int i1 [*] Int i2)
    <[]>
    (fun v c => <[v = Int (i1 * i2) /\ c = 1]>).
Proof.
  solve_red_cases.
Qed.

Theorem triple_idiv (V : Set) (i1 i2 : Z) :
  @hoare_triple V (Int i1 [/] Int i2)
    <[]>
    (fun v c => <[v = Int (i1 / i2) /\ c = 1]>).
Proof.
  solve_red_cases.
Qed.

Theorem triple_clt (V : Set) (i1 i2 : Z) :
  @hoare_triple V (Int i1 [<] Int i2)
    <[]>
    (fun v c => <[v = Bool (i1 <? i2)%Z /\ c = 1]>).
Proof.
  solve_red_cases.
Qed.

Theorem triple_ceq (V : Set) (i1 i2 : Z) :
  @hoare_triple V (Int i1 [=] Int i2)
    <[]>
    (fun v c => <[v = Bool (i1 =? i2)%Z /\ c = 1]>).
Proof.
  solve_red_cases.
Qed.

Theorem triple_rec_e2v (V : Set) (vs : list (Value V)) :
  hoare_triple (RecE (vals2exprs vs))
    <[]>
    (fun v c => <[v = RecV vs /\ c = 1]>).
Proof.
  find_red_cases.
  - apply vals2exprs_inj in H0. subst. inversion_cost_red. auto.
  - apply SplitAt_spec_eq in H0. unfold vals2exprs in *.
    apply List.map_eq_app in H0 as [? [? [? [? ?]]]].
    destruct x0; try discriminate; simpl in *. injection H1 as ? ?. subst.
    discriminate_red_Val.
Qed.

Theorem triple_get (V : Set) (n : nat) (vs : list (Value V)) v :
  Nth n vs v ->
  @hoare_triple V (Get n (RecV vs))
    <[]>
    (fun v' c => <[v' = v /\ c = 1]>).
Proof.
  find_red_cases. apply Nth_spec in H, H7.
  rewrite H in *. injection H7 as ?. subst.
  inversion_cost_red. auto.
Qed.

Theorem triple_ref (V : Set) (v : Value V) :
  @hoare_triple V (Ref v)
    <[]>
    (fun v' c => <exists> l, <[v' = Lab l /\ c = 1]> <*> <( l :== v )>).
Proof.
  find_red_cases. inversion_cost_red. repeat eexists. auto.
Qed.

Theorem triple_deref (V : Set) l (v : Value V) :
  @hoare_triple V (Deref (Lab l))
    <(l :== v)>
    (fun v' c => <[v' = v /\ c = 1]> <*> <(l :== v)>).
Proof.
  find_red_cases.
  inversion_cost_red. apply Lookup_spec in H0.
  - simpl in *. destruct l as [n]. unfold label_eqb, lift2, lift in *.
    rewrite Nat.eqb_refl in *. injection H0 as ?. subst.
    repeat eexists. auto.
  - unfold Is_Valid_Map. simpl. repeat econstructor. auto.
Qed.

Theorem triple_assign (V : Set) l (v v' : Value V) :
  @hoare_triple V (Assign (Lab l) v)
    <(l :== v')>
    (fun v'' c => <[v'' = U_val /\ c = 1]> <*> <(l :== v)>).
Proof.
  find_red_cases. apply Assignment_spec in H6 as [? ?].
  - simpl in *. destruct l as [n]. unfold label_eqb, lift2, lift in *.
    rewrite Nat.eqb_refl in *. subst.
    inversion_cost_red. repeat eexists. auto.
  - unfold Is_Valid_Map. simpl. repeat econstructor. auto.
Qed.

Theorem triple_seq (V : Set) (e : Expr V) P Q :
  hoare_triple e P (fun v c => Q v (1+c)) ->
  hoare_triple (Seq U_val e) P Q.
Proof.
  find_red_cases. eauto.
Qed.

Theorem triple_if (V : Set) (b : bool) (e1 e2 : Expr V) P Q :
  hoare_triple e1 (<[is_true b]> <*> P) (fun v c => Q v (1+c)) ->
  hoare_triple e2 (<[~ is_true b]> <*> P) (fun v c => Q v (1+c)) ->
  hoare_triple (If (Bool b) e1 e2) P Q.
Proof.
  find_red_cases.
  destruct b; [eapply H | eapply H0]; try (repeat eexists; eauto);
    simpl; inversion_cost_red; auto with *.
Qed.

(*
Theorem triple_app (V : Set) (e1 e2 : Expr V) P1 P2 P3 Q1 Q2 Q3 :
  hoare_triple e1 P1 Q1 ->
  (forall c v, Q1 c v ->> P2) ->
  hoare_triple e2 P2 Q2 ->
  (forall c v, Q2 c v ->> P3) ->
  (forall c1 v1 c2 v2,
    Q1 c1 v1 ->
    Q2 c2 v2 ->
    hoare_triple (App v1 v2) P3 Q3) ->
  hoare_triple (App e1 e2) P1 Q3.
Proof.
  find_red_cases. apply Assignment_spec in H6 as [? ?].
  - simpl in *. destruct l as [n]. unfold label_eqb, lift2, lift in *.
    rewrite Nat.eqb_refl in *. subst.
    inversion_cost_red. repeat eexists. auto.
  - unfold Is_Valid_Map. simpl. repeat econstructor. auto.
Qed.
*)

(*
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

(*
| red_while : forall m e1 e2,
    R[While e1 e2, m
      ~~>
      If e1 (Seq e2 (While e1 e2)) U_val, m]
*)
Theorem triple_while (V : Set) (c1 c2 : nat) (e1 e2 : Expr V) P Q :
  hoare_triple e1
    P
    (fun v c1' => <exists> b, <[v = Bool b /\ c1' = c1]> <*> Q b) ->
  hoare_triple e2
    (Q true)
    (fun _ c2' => <[c2' = c2]> <*> P) ->
  hoare_triple (While e1 e2)
    P
    (fun _ c => <exists> n, <[c = (n * (c1 + 1 + c2)) + c1 + 1]> <*> Q false).
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
