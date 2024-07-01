Require Arith.
Require List.
Import List.ListNotations.
Require Import String.
Require Import ZArith.

Require Import src.LambdaRef.
Require Import src.LamRefFacts.
Require Import src.LambdaTotalTriple.

Definition hoare_quadruple {V : Set}
  (e : Expr V)
  (P : StateAssertion V)
  (Q : Value V -> StateAssertion V)
  (C : nat -> StateAssertion V) : Prop :=
  forall (m : Map V),
    P m ->
    exists (v : Value V) (c : nat) (m' : Map V),
      C[e, m ~~> v, m' | c] /\
      Q v m' /\ C c m.

Notation "P <*>+ Q" := (fun v => sa_star (P v) Q) (at level 40).

Definition quadruple {V : Set}
  (e : Expr V)
  (P : StateAssertion V)
  (Q : Value V -> StateAssertion V)
  (C : nat -> StateAssertion V) : Prop :=
  forall H, hoare_quadruple e (P <*> H) (Q <*>+ H) (C <*>+ H).

Ltac unfold_all :=
  unfold quadruple, hoare_quadruple, sa_exists, sa_star, sa_single, sa_pure,
    sa_empty, sa_implies, disjoint_maps, labels.

Ltac edestruct_direct :=
  repeat match goal with
  | [H : exists _, _ |- _] => edestruct H; eauto; clear H
  | [H : _ /\ _ |- _] => edestruct H; eauto; subst; clear H
  end.

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
  (V A : Set) (P : A -> StateAssertion V) P' Q Q' :
  (forall x : A, P x ->> P' x) ->
  Q ->> Q' ->
  forall x:A, (P <*>+ Q) x ->> (P' <*>+ Q') x.
Proof.
  intros. now apply star_implies_mono.
Qed.

Lemma star_pure_l (V : Set) P (Q : StateAssertion V) m :
  (<[P]> <*> Q) m <-> (P /\ Q m).
Proof.
  unfold_all. split; intros; edestruct_direct; eauto 10.
Qed.

Lemma star_exists_l A (V : Set) (P : A -> StateAssertion V) Q m :
  ((<exists> x, P x) <*> Q) m <-> exists x, (P x <*> Q) m.
Proof.
  unfold_all. split; intros H; edestruct_direct.
Qed.

Ltac edestruct_all_in n :=
  repeat match goal with
  | [p : ?P ?m, H : forall _, ?P _ -> exists _, _ |- _] =>
    destruct H with m; eauto n; clear H; edestruct_direct
  | [p : (?P <*> ?Q) ?m, H : forall _ _, (?P <*> _) _ -> exists _, _ |- _] =>
    destruct H with Q m; eauto n; clear H; edestruct_direct
  | [H : forall _, (exists _, _) -> exists _, _ |- _] =>
    edestruct H; eauto n; clear H; edestruct_direct
  | [H : forall _ _, (exists _, _) -> exists _, _ |- _] =>
    edestruct H; eauto n; clear H; edestruct_direct
  end.

Ltac edestruct_all := edestruct_all_in integer:(5).

Theorem hquad_of_quad (V : Set) (e : Expr V) P Q C :
  quadruple e P Q C ->
  hoare_quadruple e P Q C.
Proof.
  unfold quadruple. intros Hquad. specialize Hquad with <[]>. revert Hquad.
  unfold_all. intros. edestruct_all_in integer:(10).
  repeat rewrite List.app_nil_r in *. subst. eauto 10.
Qed.

Theorem hquad_weaken (V : Set) (e : Expr V) P P' Q Q' C C' :
  P' ->> P ->
  (forall v, (Q v) ->> (Q' v)) ->
  (forall c, (C c) ->> (C' c)) ->
  hoare_quadruple e P Q C ->
  hoare_quadruple e P' Q' C'.
Proof.
  unfold hoare_quadruple, sa_implies. intros ? ? ? H ? ?.
  edestruct H as (?&?&?&?&?&?); eauto 10.
Qed.

Theorem quad_weaken (V : Set) (e : Expr V) P P' Q Q' C C' :
  P' ->> P ->
  (forall v, (Q v) ->> (Q' v)) ->
  (forall c, (C c) ->> (C' c)) ->
  quadruple e P Q C ->
  quadruple e P' Q' C'.
Proof.
  unfold quadruple. intros.
  eapply hquad_weaken with (P <*> _) (Q <*>+ _) _;
    eauto using star_implies_mono, implies_refl.
  apply star_implies_mono_post; auto using implies_refl.
Qed.

Theorem hquad_pure (V : Set) (e : Expr V) P Q C :
  (P -> hoare_quadruple e <[]> Q C) <-> hoare_quadruple e <[P]> Q C.
Proof.
  unfold hoare_quadruple, sa_pure, sa_empty.
  split; intros ? ? H; [destruct H|]; subst; auto.
Qed.

Theorem quad_pure (V : Set) (e : Expr V) P Q C :
  (P -> quadruple e <[]> Q C) <-> quadruple e <[P]> Q C.
Proof.
  unfold_all.
  split; intros Hquad; intros; edestruct_direct; edestruct Hquad; eauto;
    repeat eexists; eauto.
Qed.

Theorem hquad_exists A (V : Set) (e : Expr V) P Q C :
  (forall x : A, hoare_quadruple e (P x) Q C) <->
    hoare_quadruple e (<exists> x, P x) Q C.
Proof.
  unfold hoare_quadruple, sa_exists. split; intros ? ? H; [destruct H|]; eauto.
Qed.

Theorem quad_exists A (V : Set) (e : Expr V) P Q C :
  (forall x : A, quadruple e (P x) Q C) <-> quadruple e (<exists> x, P x) Q C.
Proof.
  unfold_all.
  split; intros Hquad; intros; edestruct_direct; edestruct Hquad; eauto;
    repeat eexists; eauto.
Qed.

(*
Theorem htriple_pure_post (V : Set) (e : Expr V) P Q :
  ((forall m, P m -> Q) /\ hoare_triple e P (fun _ _ => <[]>)) <->
    hoare_triple e P (fun _ _ => <[Q]>).
Proof.
  unfold hoare_triple, sa_pure, sa_empty. split.
  - intros [? Hhoare] ? ?.
    edestruct Hhoare as (?&?&?&?&->); repeat eexists; eauto.
  - intros Hhoare. split; intros; edestruct Hhoare as (?&?&?&?&?&->); eauto.
Qed.
*)

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

Lemma star_assoc_post_l (V A : Set) (P : A -> StateAssertion V) Q R :
  forall x : A, (P <*>+ (Q <*> R)) x ->> ((P <*>+ Q) <*>+ R) x.
Proof.
  simpl. auto using star_assoc_l.
Qed.

Lemma star_assoc_post_r (V A : Set) (P : A -> StateAssertion V) Q R :
  forall x : A, ((P <*>+ Q) <*>+ R) x ->> (P <*>+ (Q <*> R)) x.
Proof.
  simpl. auto using star_assoc_r.
Qed.

Lemma star_assoc_post (V A : Set) (P : A -> StateAssertion V) Q R :
  forall x : A, (P <*>+ (Q <*> R)) x <<->> ((P <*>+ Q) <*>+ R) x.
Proof.
  auto using star_assoc_post_l, star_assoc_post_r.
Qed.

Theorem quad_frame (V : Set) (e : Expr V) P Q C H :
  quadruple e P Q C ->
  quadruple e (P <*> H) (Q <*>+ H) (C <*>+ H).
Proof.
  unfold quadruple. intros.
  eapply hquad_weaken with (P <*> (_ <*> _)) (Q <*>+ (_ <*> _)) (C <*>+ (_ <*> _));
    auto using star_assoc_r, star_assoc_l.
Qed.

Theorem hquad_value (V : Set) (v : Value V) :
  hoare_quadruple v <[]> (fun v' => <[v' = v]>) (fun c => <[c = 0]>).
Proof.
  unfold hoare_quadruple, sa_pure, sa_empty.
  intros m Hm. subst. eauto 10 with lamref.
Qed.

Ltac solve_simple_quad n :=
  unfold_all; intros; edestruct_direct; eauto n with lamref.
Ltac solve_simple_quad_30 :=
  solve_simple_quad integer:(30).

Theorem quad_value (V : Set) (v : Value V) :
  quadruple v <[]> (fun v' => <[v' = v]>) (fun c => <[c = 0]>).
Proof.
  solve_simple_quad integer:(20).
Qed.

Theorem hquad_value' (V : Set) (v : Value V) (P : StateAssertion V) :
  hoare_quadruple v P (fun v' => <[v' = v]> <*> P) (fun c => <[c = 0]> <*> P).
Proof.
  unfold hoare_quadruple, sa_star, sa_pure, sa_empty, disjoint_maps.
  eauto 20 with lamref.
Qed.

Theorem quad_value' (V : Set) (v : Value V) (P : StateAssertion V) :
  quadruple v P (fun v' => <[v' = v]> <*> P) (fun c => <[c = 0]> <*> P).
Proof.
  solve_simple_quad_30.
Qed.

Theorem hquad_value_untimed (V : Set) (v : Value V) (P : StateAssertion V) :
  hoare_quadruple v P (fun _ => P) (fun _ => P).
Proof.
  eapply hquad_weaken; eauto using hquad_value';
    unfold sa_implies, sa_star, sa_pure, sa_empty;
    try (intros v' m [m1 [m2 [[? ?] [? [? ?]]]]]; subst);
    eauto.
Qed.

Theorem quad_value_untimed (V : Set) (v : Value V) (P : StateAssertion V) :
  quadruple v P (fun _ => P) (fun _ => P).
Proof.
  eapply quad_weaken; eauto using quad_value';
    unfold sa_implies, sa_star, sa_pure, sa_empty;
    try (intros v' m [m1 [m2 [[? ?] [? [? ?]]]]]; subst);
    eauto.
Qed.

Theorem hquad_lam (V : Set) (e : Expr _) (v : Value V) P Q C :
  hoare_quadruple (subst_e e v) P Q (fun c => C (1+c)) ->
  hoare_quadruple ((-\e) <* v) P Q C.
Proof.
  unfold hoare_quadruple. intros.
  edestruct H as [? [? [? [? ?]]]]; eauto 10 with lamref.
Qed.

Theorem quad_lam (V : Set) (e : Expr _) (v : Value V) P Q C :
  quadruple (subst_e e v) P Q (fun c => C (1+c)) ->
  quadruple ((-\e) <* v) P Q C.
Proof.
  unfold_all. intros. edestruct_direct.
  edestruct H; edestruct_direct; repeat (eexists; eauto with lamref).
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

Ltac solve_hquad n H :=
  unfold_all;
  intros;
  edestruct_direct;
  edestruct_all;
  eauto n using H.

Ltac solve_hquad_15 := solve_hquad integer:(15).

Ltac normalize_star :=
  repeat match goal with
  | [H : ((_ <*> _) <*> _) ?m |- _] => apply star_assoc_r in H
  | [H : (<[_]> <*> _) ?m |- _] => apply star_pure_l in H as [? ?]
  | [H : ((<exists> _, _) <*> _) ?m |- _] => apply star_exists_l in H as [? ?]
  end.

Ltac solve_star :=
  repeat match goal with
  | [|- ((_ <*> _) <*> _) ?m ] => apply star_assoc_l; eauto
  | [|- (<[_]> <*> _) ?m ] => apply star_pure_l; split; auto
  | [|- ((<exists> _, _) <*> _) ?m ] => apply star_exists_l; eexists; eauto
  end.
(*
Ltac solve_assertion :=
  repeat match goal with
  | [|- (<exists> _, _) ?m ] => apply quad_exists
*)
Ltac esolve_star :=
  repeat match goal with
  | [|- ((_ <*> _) <*> _) ?m ] => apply star_assoc_l
  | [|- (<[_]> <*> _) ?m ] => apply star_pure_l; split; eauto
  end.

Ltac split_all :=
  repeat match goal with
  | [|- exists _, _ ] => eexists
  | [|- _ /\ _ ] => split
  end.

Ltac solve_quad n H :=
  unfold quadruple, hoare_quadruple;
  intros;
  edestruct_direct;
  repeat (edestruct_all; normalize_star);
  subst;
  split_all;
  eauto n using H;
  solve_star.

Ltac solve_quad_15 := solve_quad integer:(15).

Theorem hquad_app (V : Set) (e1 e2 : Expr V) e1' (v2 : Value V)
  P1 P2 P3 Q3 C1 C2 C3 :
  hoare_quadruple e1 P1 (fun v => <[v = (-\e1')]> <*> P2) C1 ->
  hoare_quadruple e2 P2 (fun v => <[v = v2]> <*> P3) C2 ->
  hoare_quadruple (subst_e e1' v2) P3 (fun v => Q3 v) C3 ->
  hoare_quadruple (App e1 e2) P1 Q3 C3.
Proof.
  solve_hquad integer:(10) big_red_app.
Qed.

Theorem triple_app (V : Set) (e1 e2 : Expr V) e1' (v2 : Value V)
  P1 P2 P3 Q3 c1 c2 :
  triple e1 P1 (fun v c => <[v = (-\e1') /\ c = c1]> <*> P2) ->
  triple e2 P2 (fun v c => <[v = v2 /\ c = c2]> <*> P3) ->
  triple (subst_e e1' v2) P3 (fun v c => Q3 v (c1 + c2 + 1 + c)) ->
  triple (App e1 e2) P1 Q3.
Proof.
  solve_triple integer:(10) big_red_app.
Qed.

(*
Theorem triple_app' (V : Set) (e1 e2 : Expr V) e1' (v2 : Value V)
  P1 Q1 Q2 Q3 Q4 :
  (forall e v v' m m' m'' c c' c'', Q1 e c m -> Q2 v c' m' -> Q3 v' c'' m'' -> Q4 v' (c+c'+c'') m'') ->
  triple e1 P1 (fun v c => <[v = (-\e1')]> <*> Q1 e1' c) ->
  triple e2 (<forall> e c, Q1 e c) (fun v c => <[v = v2]> <*> Q2 v2 c) ->
  triple (subst_e e1' v2) (<forall> v c, Q2 v c) Q3 ->
  triple (App e1 e2) P1 Q4.
Proof.
  solve_triple integer:(10) big_red_app.
Qed.
*)

Theorem htriple_bneg (V : Set) (e : Expr V) (b : bool) P Q :
  hoare_triple e P (fun v c => <[v = Bool b]> <*> Q (1+c)) ->
  hoare_triple ([~] e)
    P
    (fun v c => <[v = Bool (negb b)]> <*> Q c).
Proof.
  solve_htriple_15 big_red_bneg.
Qed.

Theorem triple_bneg (V : Set) (e : Expr V) (b : bool) P Q :
  triple e P (fun v c => <[v = Bool b]> <*> Q (1+c)) ->
  triple ([~] e)
    P
    (fun v c => <[v = Bool (negb b)]> <*> Q c).
Proof.
  solve_triple integer:(10) big_red_bneg.
Qed.

Theorem htriple_ineg (V : Set) (e : Expr V) (i : Z) P Q :
  hoare_triple e P (fun v c => <[v = Int i]> <*> Q (1+c)) ->
  hoare_triple ([--] e)
    P
    (fun v c => <[v = Int (- i)]> <*> Q c).
Proof.
  solve_htriple_15 big_red_ineg.
Qed.

Theorem triple_ineg (V : Set) (e : Expr V) (i : Z) P Q :
  triple e P (fun v c => <[v = Int i]> <*> Q (1+c)) ->
  triple ([--] e)
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
  solve_htriple_15 big_red_bor.
Qed.

Theorem triple_bor (V : Set) (e1 e2 : Expr V) (b1 b2 : bool)
  P1 P2 Q2 c1 :
  triple e1 P1 (fun v c => <[v = Bool b1 /\ c = c1]> <*> P2) ->
  triple e2 P2 (fun v c => <[v = Bool b2]> <*> Q2 (c1+c+1)) ->
  @triple V (e1 [||] e2)
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
  solve_htriple_15 big_red_band.
Qed.

Theorem triple_band (V : Set) (e1 e2 : Expr V) (b1 b2 : bool)
  P1 P2 Q2 c1 :
  triple e1 P1 (fun v c => <[v = Bool b1 /\ c = c1]> <*> P2) ->
  triple e2 P2 (fun v c => <[v = Bool b2]> <*> Q2 (c1+c+1)) ->
  @triple V (e1 [&&] e2)
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
  solve_htriple_15 big_red_iadd.
Qed.

Theorem triple_iadd (V : Set) (e1 e2 : Expr V) (i1 i2 : Z)
  P1 P2 Q2 c1 :
  triple e1 P1 (fun v c => <[v = Int i1 /\ c = c1]> <*> P2) ->
  triple e2 P2 (fun v c => <[v = Int i2]> <*> Q2 (c1+c+1)) ->
  @triple V (e1 [+] e2)
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
  solve_htriple_15 big_red_isub.
Qed.

Theorem triple_isub (V : Set) (e1 e2 : Expr V) (i1 i2 : Z)
  P1 P2 Q2 c1 :
  triple e1 P1 (fun v c => <[v = Int i1 /\ c = c1]> <*> P2) ->
  triple e2 P2 (fun v c => <[v = Int i2]> <*> Q2 (c1+c+1)) ->
  @triple V (e1 [-] e2)
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
  solve_htriple_15 big_red_imul.
Qed.

Theorem triple_imul (V : Set) (e1 e2 : Expr V) (i1 i2 : Z)
  P1 P2 Q2 c1 :
  triple e1 P1 (fun v c => <[v = Int i1 /\ c = c1]> <*> P2) ->
  triple e2 P2 (fun v c => <[v = Int i2]> <*> Q2 (c1+c+1)) ->
  @triple V (e1 [*] e2)
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
  solve_htriple_15 big_red_idiv.
Qed.


Theorem triple_idiv (V : Set) (e1 e2 : Expr V) (i1 i2 : Z)
  P1 P2 Q2 c1 :
  triple e1 P1 (fun v c => <[v = Int i1 /\ c = c1]> <*> P2) ->
  triple e2 P2 (fun v c => <[v = Int i2]> <*> Q2 (c1+c+1)) ->
  @triple V (e1 [/] e2)
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
  solve_htriple_15 big_red_clt.
Qed.

Theorem triple_clt (V : Set) (e1 e2 : Expr V) (i1 i2 : Z)
  P1 P2 Q2 c1 :
  triple e1 P1 (fun v c => <[v = Int i1 /\ c = c1]> <*> P2) ->
  triple e2 P2 (fun v c => <[v = Int i2]> <*> Q2 (c1+c+1)) ->
  @triple V (e1 [<] e2)
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
  solve_htriple_15 big_red_ceq.
Qed.

Theorem triple_ceq (V : Set) (e1 e2 : Expr V) (i1 i2 : Z)
  P1 P2 Q2 c1 :
  triple e1 P1 (fun v c => <[v = Int i1 /\ c = c1]> <*> P2) ->
  triple e2 P2 (fun v c => <[v = Int i2]> <*> Q2 (c1+c+1)) ->
  @triple V (e1 [=] e2)
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
  unfold hoare_triple.
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
    - edestruct H5 with (i := 0) as (v'&c'&m'&?&?);
        eauto_lr.
      normalize_star. edestruct_direct.
      edestruct IHn with (Ps := (s0::Ps)%list) as (ms&m''&?&?&?&?&?);
        simpl; eauto 10 with lamref.
      destruct ms; [discriminate|]. simpl in *. injection_on_all S.
      injection_on_all_Some. exists (m::m0::ms)%list.
      repeat eexists; simpl in *; eauto. intros.
      inversion_all_Nth_cons; eauto with lamref. }
  eauto 20 using big_red_rec with st_assertions lamref.
Qed.

Theorem triple_rec (V : Set) (es : list (Expr V)) (vs : list (Value V))
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
    triple e
      P
      (fun v' c' => <[v' = v /\ c' = c]> <*> Q)) ->
  triple (RecE es)
    P
    (fun v c => <[v = RecV vs /\ c = List.list_sum cs + 1]> <*> Q).
Proof.
  unfold triple, hoare_triple.
  intros.
  assert (exists ms m',
    1+n = List.length ms /\
    Some m = List.head ms /\
    Some m' = last_error ms /\
    (Q <*> H6) m' /\
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
    - exists [m]%list. split_all; simpl; eauto. intros. inversion_Nth_nil.
    - edestruct H5 with (i := 0) as (v'&c'&m'&?&?);
        eauto_lr.
      normalize_star. edestruct_direct.
      edestruct IHn with (Ps := (s0::Ps)%list) as (ms&m''&?&?&?&?&?);
        simpl; eauto 10 with lamref.
      destruct ms; [discriminate|]. simpl in *. injection_on_all S.
      injection_on_all_Some. exists (m::m0::ms)%list.
      split_all; simpl in *; eauto. intros.
      inversion_all_Nth_cons; eauto with lamref. }
  split_all; eauto using big_red_rec with lamref.
  solve_star.
Qed.

Theorem htriple_get (V : Set) n (e : Expr V) (vs : list (Value V)) v P Q :
  Nth n vs v ->
  hoare_triple e P (fun v' c => <[v' = RecV vs]> <*> Q (1+c)) ->
  hoare_triple (Get n e)
    P
    (fun v' c => <[v' = v]> <*> Q c).
Proof.
  solve_htriple_15 big_red_get.
Qed.

Theorem triple_get (V : Set) n (e : Expr V) (vs : list (Value V)) v P Q :
  Nth n vs v ->
  triple e P (fun v' c => <[v' = RecV vs]> <*> Q (1+c)) ->
  triple (Get n e)
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
  split_all; try (eapply big_red_ref; eauto); simpl; eauto.
  intros ? [? | []] ?. subst. eauto.
Qed.

Theorem triple_ref (V : Set) (e : Expr V) (v : Value V) P Q :
  triple e P (fun v' c => <[v' = v]> <*> Q (1+c)) ->
  triple (Ref e)
    P
    (fun v' c => <exists> l, <[v' = Lab l]> <*> <( l :== v )> <*> Q c).
Proof.
  pose proof new_label_is_fresh. unfold Is_fresh_label, not in *.
  unfold triple, hoare_triple. intros. edestruct_all. normalize_star. subst.
  split_all; try (eapply big_red_ref; eauto); simpl.
  solve_star. unfold sa_star in *. edestruct_direct.
  split_all; eauto with st_assertions. intros ? [? | []] ?. subst. eauto.
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

Theorem triple_deref (V : Set) (e : Expr V) (v : Value V) l P Q :
  triple e
    (<(l :== v)> <*> P)
    (fun v' c => <[v' = Lab l]> <*> <(l :== v)> <*> Q (1+c)) ->
  triple (Deref e)
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

Theorem triple_assign (V : Set) (e1 e2 : Expr V) (v v' : Value V) l P1 P2 Q2 c1 :
  triple e1
    (<(l :== v)> <*> P1)
    (fun v'' c => <[v'' = Lab l /\ c = c1]> <*> <(l :== v)> <*> P2) ->
  triple e2
    (<(l :== v)> <*> P2)
    (fun v'' c => <[v'' = v']> <*> <(l :== v)> <*> Q2 (c1+c+1)) ->
  triple (Assign e1 e2)
    (<(l :== v)> <*> P1)
    (fun v'' c => <[v'' = U_val]> <*> <(l :== v')> <*> Q2 c).
Proof.
  unfold triple, hoare_triple. intros. edestruct_all. normalize_star.
  edestruct H0; clear H0. { solve_star. } edestruct_direct. normalize_star. subst.
  unfold sa_star, sa_single in H5. edestruct_direct. simpl in *.
  split_all; try eapply big_red_assign; simpl in *; eauto with lamref;
    solve_star; auto with lamref.
  unfold_all. split_all; eauto.
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
  solve_htriple_15 big_red_seq.
Qed.

Theorem triple_seq (V : Set) (e1 e2 : Expr V) (v : Value V) P1 P2 Q2 c1 :
  triple e1
    P1
    (fun v' c => <[v' = U_val /\ c = c1]> <*> P2) ->
  triple e2
    P2
    (fun v' c => <[v' = v]> <*> Q2 (c1+1+c)) ->
  triple (Seq e1 e2)
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
  - solve_htriple_15 big_red_if_true.
  - solve_htriple_15 big_red_if_false.
Qed.

Theorem triple_if_simple (V : Set) (e1 e2 e3 : Expr V) b P1 P2 Q2 c1 :
  triple e1
    P1
    (fun v' c => <[v' = Bool b /\ c = c1]> <*> P2 b) ->
  triple e2
    (P2 true)
    (fun v c => Q2 v (c1+1+c)) ->
  triple e3
    (P2 false)
    (fun v c => Q2 v (c1+1+c)) ->
  triple (If e1 e2 e3) P1 Q2.
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
  - solve_htriple_15 big_red_if_true.
  - solve_htriple_15 big_red_if_false.
Qed.

Theorem triple_if (V : Set) (e1 e2 e3 : Expr V) P1 P2 Q2 c1 :
  triple e1
    P1
    (fun v' c => <exists> b, <[v' = Bool b /\ c = c1]> <*> P2 b) ->
  triple e2
    (P2 true)
    (fun v c => Q2 v (c1+1+c)) ->
  triple e3
    (P2 false)
    (fun v c => Q2 v (c1+1+c)) ->
  triple (If e1 e2 e3) P1 Q2.
Proof.
  unfold triple, hoare_triple. intros. edestruct_all. normalize_star.
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
  solve_htriple_15 big_red_while_true.
Qed.

Theorem triple_while_true (V : Set) (e1 e2 : Expr V) c1 c2 P P2 P3 Q :
  triple e1
    P
    (fun v c => <[v = Bool true /\ c = c1]> <*> P2) ->
  triple e2
    P2
    (fun v c => <[v = U_val /\ c = c2]> <*> P3) ->
  triple (While e1 e2)
    P3
    (fun v c => <[v = U_val]> <*> Q (1+(c1+1+(c2+1+c)))) ->
  triple (While e1 e2)
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
  solve_htriple_15 big_red_while_false.
Qed.

Theorem triple_while_false (V : Set) (e1 e2 : Expr V) P Q :
  triple e1
    P
    (fun v c => <[v = Bool false]> <*> Q (1+(c+1))) ->
  triple (While e1 e2)
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
  solve_htriple_15 big_red_while_false.
Qed.
*)