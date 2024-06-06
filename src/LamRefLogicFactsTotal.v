Require Arith.
Require List.
Import List.ListNotations.
Require Import String.
Require Import ZArith.

Require Import src.LambdaRef.
Require Import src.LamRefFacts.
Require Import src.LambdaTotalTriple.

(*
(*total correctness*)
Theorem htriple_weaken (V : Set) (e : Expr V) P P' Q Q' :
  sa_implies P' P ->
  (forall v c, sa_implies (Q v c) (Q' v c)) ->
  hoare_triple e P Q ->
  hoare_triple e P' Q'.
Proof.
  unfold hoare_triple, sa_implies. intros HP HQ Hhoare v m p'.
  edestruct Hhoare as [? [? ?]]; eauto.
Qed.

Theorem htriple_value (V : Set) (v : Value V) (P : StateAssertion V) :
  hoare_triple v P (fun _ c => sa_star (sa_pure (c = 0)) P).
Proof.
  unfold hoare_triple, sa_star, sa_pure, sa_empty, disjoint_maps.
  intros v' m p. repeat eexists; eauto.
Qed.

Theorem htriple_value' (V : Set) (v : Value V) :
  hoare_triple v sa_empty (fun _ c => sa_pure (c = 0)).
Proof.
  unfold hoare_triple, sa_pure, sa_empty.
  intros v' m p. repeat eexists.
Qed.
*)
(*
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
*)

Ltac unfold_all :=
  unfold triple, hoare_triple, sa_exists, sa_star, sa_single, sa_pure,
    sa_empty, sa_implies, disjoint_maps, labels.

Ltac edestruct_direct :=
  repeat match goal with
  | [H : exists _, _ |- _] => edestruct H; eauto; clear H
  | [H : _ /\ _ |- _] => edestruct H; eauto; subst; clear H
  end.

Ltac edestruct_all_in n :=
  repeat match goal with
  | [p : ?P ?m, H : forall _, ?P _ -> exists _, _ |- _] =>
    destruct H with m; eauto n; clear H; edestruct_direct
  | [H : forall _, (exists _, _) -> exists _, _ |- _] =>
    edestruct H; eauto n; clear H; edestruct_direct
  | [H : forall _ _, (exists _, _) -> exists _, _ |- _] =>
    edestruct H; eauto n; clear H; edestruct_direct
  end.

Ltac edestruct_all := edestruct_all_in integer:(5).

Ltac solve_triple n H :=
  unfold_all;
  intros;
  edestruct_direct;
  edestruct_all;
  eauto n using H.

Ltac solve_triple_15 := solve_triple integer:(15).

Theorem htriple_of_triple (V : Set) (e : Expr V) P Q :
  triple e P Q ->
  hoare_triple e P Q.
Proof.
  unfold triple. intros Htriple. specialize Htriple with <[]>. revert Htriple.
  unfold_all. intros. edestruct_all_in integer:(10).
  repeat rewrite List.app_nil_r in *. eauto.
Qed.

Theorem htriple_weaken (V : Set) (e : Expr V) P P' Q Q' :
  P' ->> P ->
  (forall v c, (Q v c) ->> (Q' v c)) ->
  hoare_triple e P Q ->
  hoare_triple e P' Q'.
Proof.
  unfold hoare_triple, sa_implies. intros ? ? H ? ?.
  edestruct H as [? [? [? [? ?]]]]; eauto 10.
Qed.

Lemma implies_refl V (P : StateAssertion V) : P ->> P.
Proof.
  now unfold_all.
Qed.

Lemma star_implies_mono V (P : StateAssertion V) P' Q Q' :
  P ->> P' ->
  Q ->> Q' ->
  P <*> Q ->> P' <*> Q'.
Proof.
  unfold_all. intros. edestruct_direct. eauto 10.
Qed.

Lemma star_implies_mono_post
  (V : Set) (P : V -> nat -> StateAssertion V) P' Q Q' :
  P -->> P' ->
  Q ->> Q' ->
  P <*>+ Q -->> P' <*>+ Q'.
Proof.
  intros. now apply star_implies_mono.
Qed.

Theorem triple_weaken (V : Set) (e : Expr V) P P' Q Q' :
  P' ->> P ->
  (forall v c, (Q v c) ->> (Q' v c)) ->
  triple e P Q ->
  triple e P' Q'.
Proof.
  unfold triple. intros.
  eapply htriple_weaken with (P <*> _) (Q <*>+ _);
    eauto using star_implies_mono, implies_refl.
Qed.

Theorem htriple_pure (V : Set) (e : Expr V) P Q :
  (P -> hoare_triple e <[]> Q) <-> hoare_triple e <[P]> Q.
Proof.
  unfold hoare_triple, sa_pure, sa_empty.
  split; intros ? ? H; [destruct H|]; subst; auto.
Qed.

Theorem triple_pure (V : Set) (e : Expr V) P Q :
  (P -> triple e <[]> Q) <-> triple e <[P]> Q.
Proof.
  unfold_all.
  split; intros Htriple; intros; edestruct_direct; edestruct Htriple; eauto;
    repeat eexists; eauto.
Qed.

Theorem htriple_exists A (V : Set) (e : Expr V) P Q :
  (forall x : A, hoare_triple e (P x) Q) <->
    hoare_triple e (<exists> x, P x) Q.
Proof.
  unfold hoare_triple, sa_exists. split; intros ? ? H; [destruct H|]; eauto.
Qed.

Theorem triple_exists A (V : Set) (e : Expr V) P Q :
  (forall x : A, triple e (P x) Q) <-> triple e (<exists> x, P x) Q.
Proof.
  unfold_all.
  split; intros Htriple; intros; edestruct_direct; edestruct Htriple; eauto;
    repeat eexists; eauto.
Qed.

Theorem htriple_pure_post (V : Set) (e : Expr V) P Q :
  ((forall m, P m -> Q) /\ hoare_triple e P (fun _ _ => <[]>)) <->
    hoare_triple e P (fun _ _ => <[Q]>).
Proof.
  unfold hoare_triple, sa_pure, sa_empty. split.
  - intros [? Hhoare] ? ?.
    edestruct Hhoare as (?&?&?&?&->); repeat eexists; eauto.
  - intros Hhoare. split; intros; edestruct Hhoare as (?&?&?&?&?&->); eauto.
Qed.

Ltac solve_assoc :=
  repeat eexists; eauto using List.app_assoc; rewrite List.map_app in *; intros;
    try match goal with
    | [H : List.In _ (_ ++ _)%list |- _] => apply List.in_app_or in H as [? | ?]
    end;
    eauto using List.in_or_app.

Lemma star_assoc_l (V : Set) (P : StateAssertion V) Q R :
  P <*> (Q <*> R) ->> (P <*> Q) <*> R.
Proof.
  unfold_all. intros. edestruct_direct.
  solve_assoc.
Qed.

Lemma star_assoc_r (V : Set) (P : StateAssertion V) Q R :
  (P <*> Q) <*> R ->> P <*> (Q <*> R).
Proof.
  unfold_all. intros. edestruct_direct.
  solve_assoc.
Qed.

Lemma star_assoc (V : Set) (P : StateAssertion V) Q R :
  P <*> (Q <*> R) <<->> (P <*> Q) <*> R.
Proof.
  auto using star_assoc_l, star_assoc_r.
Qed.

Lemma star_assoc_post_l (V : Set) (P : V -> nat -> StateAssertion V) Q R :
  P <*>+ (Q <*> R) -->> (P <*>+ Q) <*>+ R.
Proof.
  simpl. auto using star_assoc_l.
Qed.

Lemma star_assoc_post_r (V : Set) (P : V -> nat -> StateAssertion V) Q R :
  (P <*>+ Q) <*>+ R -->> P <*>+ (Q <*> R).
Proof.
  simpl. auto using star_assoc_r.
Qed.

Lemma star_assoc_post (V : Set) (P : V -> nat -> StateAssertion V) Q R :
  P <*>+ (Q <*> R) <<-->> (P <*>+ Q) <*>+ R.
Proof.
  auto using star_assoc_post_l, star_assoc_post_r.
Qed.

Theorem triple_frame (V : Set) (e : Expr V) P Q H :
  triple e P Q ->
  triple e (P <*> H) (Q <*>+ H).
Proof.
  unfold triple. intros.
  eapply htriple_weaken with (P <*> (_ <*> _)) (Q <*>+ (_ <*> _));
    auto using star_assoc_r, star_assoc_l.
Qed.

Theorem htriple_value (V : Set) (v : Value V) :
  hoare_triple v <[]> (fun v' c => <[v' = v /\ c = 0]>).
Proof.
  unfold hoare_triple, sa_pure, sa_empty.
  intros m Hm. subst. eauto 10 with lamref.
Qed.

Ltac solve_simple_triple n :=
  unfold_all; intros; edestruct_direct; eauto n with lamref.
Ltac solve_simple_triple_20 :=
  solve_simple_triple integer:(20).

Theorem triple_value (V : Set) (v : Value V) :
  triple v <[]> (fun v' c => <[v' = v /\ c = 0]>).
Proof.
  solve_simple_triple integer:(15).
Qed.

Theorem htriple_value' (V : Set) (v : Value V) (P : StateAssertion V) :
  hoare_triple v P (fun v' c => <[v' = v /\ c = 0]> <*> P).
Proof.
  unfold hoare_triple, sa_star, sa_pure, sa_empty, disjoint_maps.
  eauto 15 with lamref.
Qed.

Theorem triple_value' (V : Set) (v : Value V) (P : StateAssertion V) :
  triple v P (fun v' c => <[v' = v /\ c = 0]> <*> P).
Proof.
  solve_simple_triple_20.
Qed.

Theorem htriple_value_untimed (V : Set) (v : Value V) (P : StateAssertion V) :
  hoare_triple v P (fun _ _ => P).
Proof.
  eapply htriple_weaken; eauto using htriple_value';
    unfold sa_implies, sa_star, sa_pure, sa_empty;
    [| intros v' c m [m1 [m2 [[? ?] [? [? ?]]]]]; subst ];
    eauto.
Qed.

Theorem triple_value_untimed (V : Set) (v : Value V) (P : StateAssertion V) :
  triple v P (fun _ _ => P).
Proof.
  eapply triple_weaken; eauto using triple_value';
    unfold sa_implies, sa_star, sa_pure, sa_empty;
    [| intros v' c m [m1 [m2 [[? ?] [? [? ?]]]]]; subst ];
    eauto.
Qed.

Theorem htriple_lam (V : Set) (e : Expr _) (v : Value V) P Q :
  hoare_triple (subst_e e v) P (fun v c => Q v (1+c)) ->
  hoare_triple ((-\e) <* v) P Q.
Proof.
  unfold hoare_triple. intros.
  edestruct H as [? [? [? [? ?]]]]; eauto 10 with lamref.
Qed.

Theorem triple_lam (V : Set) (e : Expr _) (v : Value V) P Q :
  triple (subst_e e v) P (fun v c => Q v (1+c)) ->
  triple ((-\e) <* v) P Q.
Proof.
  unfold_all. intros. edestruct_direct.
  edestruct H; edestruct_direct; repeat eexists; eauto with lamref.
Qed.

(*Theorem htriple_seq (V : Set) (e1 e2 : Expr V) P1 P2 Q1 Q2 :
  hoare_triple e1 P1 Q1 ->
  hoare_triple e2 P2 Q2 ->
  (forall v c, Q1 v c ->> P1) ->
  hoare_triple (e1 ;; e2) P1 Q2.
Proof.
  unfold hoare_triple, sa_exists, sa_star, sa_single, sa_pure, sa_empty,
    disjoint_maps.
  intros.
  inversion_cost_red. inversion_red.
*)

Theorem htriple_app (V : Set) (e1 e2 : Expr V) e1' (v2 : Value V)
  P1 P2 P3 Q3 c1 c2 :
  hoare_triple e1 P1 (fun v c => <[v = (-\e1') /\ c = c1]> <*> P2) ->
  hoare_triple e2 P2 (fun v c => <[v = v2 /\ c = c2]> <*> P3) ->
  hoare_triple (subst_e e1' v2) P3 (fun v c => Q3 v (c1 + c2 + 1 + c)) ->
  hoare_triple (App e1 e2) P1 Q3.
Proof.
  solve_triple integer:(10) big_red_app.
Qed.

Theorem htriple_bneg (V : Set) (e : Expr V) (b : bool) P Q :
  hoare_triple e P (fun v c => <[v = Bool b]> <*> Q (1+c)) ->
  hoare_triple ([~] e)
    P
    (fun v c => <[v = Bool (negb b)]> <*> Q c).
Proof.
  solve_triple_15 big_red_bneg.
Qed.

Theorem htriple_ineg (V : Set) (e : Expr V) (i : Z) P Q :
  hoare_triple e P (fun v c => <[v = Int i]> <*> Q (1+c)) ->
  hoare_triple ([--] e)
    P
    (fun v c => <[v = Int (- i)]> <*> Q c).
Proof.
  solve_triple_15 big_red_ineg.
Qed.

Theorem htriple_bor (V : Set) (e1 e2 : Expr V) (b1 b2 : bool)
  P1 P2 Q2 c1 :
  hoare_triple e1 P1 (fun v c => <[v = Bool b1 /\ c = c1]> <*> P2) ->
  hoare_triple e2 P2 (fun v c => <[v = Bool b2]> <*> Q2 (c1+c+1)) ->
  @hoare_triple V (e1 [||] e2)
    P1
    (fun v c => <[v = Bool (b1 || b2)]> <*> Q2 c).
Proof.
  solve_triple_15 big_red_bor.
Qed.

Theorem htriple_band (V : Set) (e1 e2 : Expr V) (b1 b2 : bool)
  P1 P2 Q2 c1 :
  hoare_triple e1 P1 (fun v c => <[v = Bool b1 /\ c = c1]> <*> P2) ->
  hoare_triple e2 P2 (fun v c => <[v = Bool b2]> <*> Q2 (c1+c+1)) ->
  @hoare_triple V (e1 [&&] e2)
    P1
    (fun v c => <[v = Bool (b1 && b2)]> <*> Q2 c).
Proof.
  solve_triple_15 big_red_band.
Qed.

Theorem htriple_iadd (V : Set) (e1 e2 : Expr V) (i1 i2 : Z)
  P1 P2 Q2 c1 :
  hoare_triple e1 P1 (fun v c => <[v = Int i1 /\ c = c1]> <*> P2) ->
  hoare_triple e2 P2 (fun v c => <[v = Int i2]> <*> Q2 (c1+c+1)) ->
  @hoare_triple V (e1 [+] e2)
    P1
    (fun v c => <[v = Int (i1 + i2)]> <*> Q2 c).
Proof.
  solve_triple_15 big_red_iadd.
Qed.

Theorem htriple_isub (V : Set) (e1 e2 : Expr V) (i1 i2 : Z)
  P1 P2 Q2 c1 :
  hoare_triple e1 P1 (fun v c => <[v = Int i1 /\ c = c1]> <*> P2) ->
  hoare_triple e2 P2 (fun v c => <[v = Int i2]> <*> Q2 (c1+c+1)) ->
  @hoare_triple V (e1 [-] e2)
    P1
    (fun v c => <[v = Int (i1 - i2)]> <*> Q2 c).
Proof.
  solve_triple_15 big_red_isub.
Qed.

Theorem htriple_imul (V : Set) (e1 e2 : Expr V) (i1 i2 : Z)
  P1 P2 Q2 c1 :
  hoare_triple e1 P1 (fun v c => <[v = Int i1 /\ c = c1]> <*> P2) ->
  hoare_triple e2 P2 (fun v c => <[v = Int i2]> <*> Q2 (c1+c+1)) ->
  @hoare_triple V (e1 [*] e2)
    P1
    (fun v c => <[v = Int (i1 * i2)]> <*> Q2 c).
Proof.
  solve_triple_15 big_red_imul.
Qed.

Theorem htriple_idiv (V : Set) (e1 e2 : Expr V) (i1 i2 : Z)
  P1 P2 Q2 c1 :
  hoare_triple e1 P1 (fun v c => <[v = Int i1 /\ c = c1]> <*> P2) ->
  hoare_triple e2 P2 (fun v c => <[v = Int i2]> <*> Q2 (c1+c+1)) ->
  @hoare_triple V (e1 [/] e2)
    P1
    (fun v c => <[v = Int (i1 / i2)]> <*> Q2 c).
Proof.
  solve_triple_15 big_red_idiv.
Qed.

Theorem htriple_clt (V : Set) (e1 e2 : Expr V) (i1 i2 : Z)
  P1 P2 Q2 c1 :
  hoare_triple e1 P1 (fun v c => <[v = Int i1 /\ c = c1]> <*> P2) ->
  hoare_triple e2 P2 (fun v c => <[v = Int i2]> <*> Q2 (c1+c+1)) ->
  @hoare_triple V (e1 [<] e2)
    P1
    (fun v c => <[v = Bool (i1 <? i2)%Z]> <*> Q2 c).
Proof.
  solve_triple_15 big_red_clt.
Qed.

Theorem htriple_ceq (V : Set) (e1 e2 : Expr V) (i1 i2 : Z)
  P1 P2 Q2 c1 :
  hoare_triple e1 P1 (fun v c => <[v = Int i1 /\ c = c1]> <*> P2) ->
  hoare_triple e2 P2 (fun v c => <[v = Int i2]> <*> Q2 (c1+c+1)) ->
  @hoare_triple V (e1 [=] e2)
    P1
    (fun v c => <[v = Bool (i1 =? i2)%Z]> <*> Q2 c).
Proof.
  solve_triple_15 big_red_ceq.
Qed.

Definition last_error {A} (xs : list A) := List.last (List.map Some xs) None.

Ltac injection_on_all constr :=
  repeat match goal with
  | [H : constr _ = constr _ |- _] => injection H as H
  end.

Ltac injection_on_all_Some :=
  repeat match goal with
  | [H : Some _ = Some _ |- _] => injection H as H
  end.

Ltac inversion_Nth_nil :=
  match goal with
  | [H : Nth _ []%list _ |- _] => inversion H; subst; clear H
  end.

Ltac inversion_Nth_cons :=
  match goal with
  | [H : Nth _ (_ :: _)%list _ |- _] => inversion H; subst; clear H
  end.

Ltac inversion_all_Nth_cons := repeat inversion_Nth_cons.

Theorem htriple_rec (V : Set) (es : list (Expr V)) (vs : list (Value V))
  n cs Ps P Q :
  n = List.length es ->
  n = List.length vs ->
  n = List.length cs ->
  1+n = List.length Ps ->
  Some P = List.head Ps ->
  Some Q = last_error Ps ->
  (forall i e v c P Q,
    Nth i es e ->
    Nth i vs v ->
    Nth i cs c ->
    Nth i Ps P ->
    Nth (1+i) Ps Q ->
    hoare_triple e
      P
      (fun v' c' => <[v' = v /\ c' = c]> <*> Q)) ->
  hoare_triple (RecE es)
    P
    (fun v c => <[v = RecV vs /\ c = List.list_sum cs + 1]> <*> Q).
Proof.
  unfold_all.
  intros.
  assert (exists ms m',
    1+n = List.length ms /\
    Some m = List.head ms /\
    Some m' = last_error ms /\
    Q m' /\
      forall i e v c m m',
        Nth i es e ->
        Nth i vs v ->
        Nth i cs c ->
        Nth i ms m ->
        Nth (1+i) ms m' ->
        C[e,m ~~> v,m'|c])
    as (ms&m'&?&?&?&?&?).
  { generalize dependent m. generalize dependent P.
    generalize dependent Ps. generalize dependent cs.
    generalize dependent vs. generalize dependent es.
    induction n; intros; destruct es, vs, cs, Ps;
      try discriminate; try destruct Ps; try discriminate;
      unfold last_error in *; simpl in *;
      injection_on_all_Some; injection_on_all S; subst.
    - exists [m]%list. repeat econstructor; auto. intros. inversion_Nth_nil.
    - edestruct H5 with (i := 0) as (v'&c'&m'&?&m1&m2&((?&?)&?)&?&?&?);
        eauto_lr.
      edestruct IHn with (Ps := (s0::Ps)%list) (m := m2) as (ms&m''&?&?&?&?&?);
        simpl; eauto 10 with lamref.
      destruct ms; [discriminate|]. simpl in *. injection_on_all S.
      injection_on_all_Some. exists (m::m0::ms)%list.
      repeat eexists; simpl in *; eauto. intros.
      inversion_all_Nth_cons; eauto with lamref. }
  eauto 15 using big_red_rec with lamref.
Qed.

Theorem htriple_get (V : Set) n (e : Expr V) (vs : list (Value V)) v P Q :
  Nth n vs v ->
  hoare_triple e P (fun v' c => <[v' = RecV vs]> <*> Q (1+c)) ->
  hoare_triple (Get n e)
    P
    (fun v' c => <[v' = v]> <*> Q c).
Proof.
  solve_triple_15 big_red_get.
Qed.

Theorem htriple_ref (V : Set) (e : Expr V) (v : Value V) P Q :
  hoare_triple e P (fun v' c => <[v' = v]> <*> Q (1+c)) ->
  hoare_triple (Ref e)
    P
    (fun v' c => <exists> l, <[v' = Lab l]> <*> <( l :== v )> <*> Q c).
Proof.
  pose proof new_label_is_fresh. unfold Is_fresh_label, not in *.
  unfold_all. intros. edestruct_all.
  repeat eexists; try (eapply big_red_ref; eauto); simpl; auto.
  intros ? [? | []] ?. subst. eauto.
Qed.

Theorem htriple_deref (V : Set) (e : Expr V) (v : Value V) l P Q :
  hoare_triple e
    (<(l :== v)> <*> P)
    (fun v' c => <[v' = Lab l]> <*> <(l :== v)> <*> Q (1+c)) ->
  hoare_triple (Deref e)
    (<(l :== v)> <*> P)
    (fun v' c => <[v' = v]> <*> <(l :== v)> <*> Q c).
Proof.
  unfold_all. intros. edestruct_all.
  repeat eexists; try eapply big_red_deref; simpl in *; eauto with lamref.
Qed.

Theorem htriple_assign (V : Set) (e1 e2 : Expr V) (v v' : Value V) l P1 P2 Q2 c1 :
  hoare_triple e1
    (<(l :== v)> <*> P1)
    (fun v'' c => <[v'' = Lab l /\ c = c1]> <*> <(l :== v)> <*> P2) ->
  hoare_triple e2
    (<(l :== v)> <*> P2)
    (fun v'' c => <[v'' = v']> <*> <(l :== v)> <*> Q2 (c1+c+1)) ->
  hoare_triple (Assign e1 e2)
    (<(l :== v)> <*> P1)
    (fun v'' c => <[v'' = U_val]> <*> <(l :== v')> <*> Q2 c).
Proof.
  unfold_all. intros. edestruct_direct.
  edestruct H; eauto 10. clear H. edestruct_direct.
  edestruct_all_in integer:(10).
  repeat eexists; try eapply big_red_assign; simpl in *; eauto with lamref.
  auto with lamref.
Qed.

Theorem htriple_seq (V : Set) (e1 e2 : Expr V) (v : Value V) P1 P2 Q2 c1 :
  hoare_triple e1
    P1
    (fun v' c => <[v' = U_val /\ c = c1]> <*> P2) ->
  hoare_triple e2
    P2
    (fun v' c => <[v' = v]> <*> Q2 (c1+1+c)) ->
  hoare_triple (Seq e1 e2)
    P1
    (fun v' c => <[v' = v]> <*> Q2 c).
Proof.
  solve_triple_15 big_red_seq.
Qed.

Theorem htriple_if_simple (V : Set) (e1 e2 e3 : Expr V) b P1 P2 Q2 c1 :
  hoare_triple e1
    P1
    (fun v' c => <[v' = Bool b /\ c = c1]> <*> P2 b) ->
  hoare_triple e2
    (P2 true)
    (fun v c => Q2 v (c1+1+c)) ->
  hoare_triple e3
    (P2 false)
    (fun v c => Q2 v (c1+1+c)) ->
  hoare_triple (If e1 e2 e3) P1 Q2.
Proof.
  destruct b.
  - solve_triple_15 big_red_if_true.
  - solve_triple_15 big_red_if_false.
Qed.

Theorem htriple_if (V : Set) (e1 e2 e3 : Expr V) P1 P2 Q2 c1 :
  hoare_triple e1
    P1
    (fun v' c => <exists> b, <[v' = Bool b /\ c = c1]> <*> P2 b) ->
  hoare_triple e2
    (P2 true)
    (fun v c => Q2 v (c1+1+c)) ->
  hoare_triple e3
    (P2 false)
    (fun v c => Q2 v (c1+1+c)) ->
  hoare_triple (If e1 e2 e3) P1 Q2.
Proof.
  unfold_all. intros. edestruct_all.
  match goal with [b : bool |- _] => destruct b end.
  - solve_triple_15 big_red_if_true.
  - solve_triple_15 big_red_if_false.
Qed.

Theorem htriple_while_true (V : Set) (e1 e2 : Expr V) c1 c2 P P2 P3 Q :
  hoare_triple e1
    P
    (fun v c => <[v = Bool true /\ c = c1]> <*> P2) ->
  hoare_triple e2
    P2
    (fun v c => <[v = U_val /\ c = c2]> <*> P3) ->
  hoare_triple (While e1 e2)
    P3
    (fun v c => <[v = U_val]> <*> Q (1+(c1+1+(c2+1+c)))) ->
  hoare_triple (While e1 e2)
    P
    (fun v c => <[v = U_val]> <*> Q c).
Proof.
  solve_triple_15 big_red_while_true.
Qed.

Theorem htriple_while_false (V : Set) (e1 e2 : Expr V) P Q :
  hoare_triple e1
    P
    (fun v c => <[v = Bool false]> <*> Q (1+(c+1))) ->
  hoare_triple (While e1 e2)
    P
    (fun v c => <[v = U_val]> <*> Q c).
Proof.
  solve_triple_15 big_red_while_false.
Qed.
(*
Theorem htriple_while (V : Set) (e1 e2 : Expr V) n P Q :
  (forall n,
    hoare_triple e1
      (P n)
      (fun v c => <exists> b, <[v = Bool b]> <*> Q b n c)) ->
  (forall n c,
    hoare_triple e2
      (Q true (S n) c)
      (fun v c' => <[v = U_val]> <*> P n)) ->
  hoare_triple (While e1 e2)
    (P n)
    (fun v c => <[v = U_val]> <*> Q false 0 c).
Proof.
  unfold_all. destruct n; simpl.
  solve_triple_15 big_red_while_false.
Qed.
*)
