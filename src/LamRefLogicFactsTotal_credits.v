Require Arith.
Require List.
Import List.ListNotations.
Require Import String.
Require Import ZArith.

Require Import src.LambdaRef.
Require Import src.LamRefFacts.
Require Import src.LambdaTotalTriple_credits.
Require Import src.Tactics.

From Coq Require Import Lia.

Ltac unfold_all :=
  unfold triple, hoare_triple, sa_exists, sa_forall, sa_credits, sa_star,
    sa_single, sa_pure, sa_empty, sa_implies, disjoint_maps, labels.

Ltac unfold_all_in H :=
  unfold triple, hoare_triple, sa_exists, sa_forall, sa_credits, sa_star,
    sa_single, sa_pure, sa_empty, sa_implies, disjoint_maps, labels in H.

Ltac subst_case_or :=
  match goal with
  | [H : ?x = _ \/ ?x = _ |- _] => destruct H; subst x
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
  unfold_all. intros. edestruct_direct. eauto 15.
Qed.

Lemma star_implies_mono_post
  (V : Set) (P : V -> StateAssertion V) P' Q Q' :
  P -->> P' ->
  Q ->> Q' ->
  P <*>+ Q -->> P' <*>+ Q'.
Proof.
  intros. now apply star_implies_mono.
Qed.

Lemma star_pure_l (V : Set) P (Q : StateAssertion V) c m :
  (<[P]> <*> Q) c m <-> (P /\ Q c m).
Proof.
  unfold_all. split; intros; edestruct_direct; eauto 15.
Qed.

Lemma star_exists_l A (V : Set) (P : A -> StateAssertion V) Q c m :
  ((<exists> x, P x) <*> Q) c m <-> exists x, (P x <*> Q) c m.
Proof.
  unfold_all. split; intros H; edestruct_direct; eauto 10.
Qed.

Ltac edestruct_all_in n :=
  repeat match goal with
  | [p : ?P ?c ?m, H : forall _ _, ?P _ _ -> exists _, _ |- _] =>
    destruct H with c m; eauto n; clear H; edestruct_direct
  | [p : (?P <*> ?Q) ?c ?m, H : forall _ _ _, (?P <*> _) _ _ -> exists _, _ |- _] =>
    destruct H with Q c m; eauto n; clear H; edestruct_direct
  | [H : forall _ _, (exists _, _) -> exists _, _ |- _] =>
    edestruct H; eauto n; clear H; edestruct_direct
  | [H : forall _ _ _, (exists _, _) -> exists _, _ |- _] =>
    edestruct H; eauto n; clear H; edestruct_direct
  | [q : ?Q ?v ?c ?m, H : forall _ _ _, ?Q _ _ _ -> exists _, _ |- _] =>
    destruct H with v c m; eauto n; clear H; edestruct_direct
  | [q : (?Q ?v <*> ?R) ?c ?m, H : forall _ _ _ _, (?Q _ <*> _) _ _ -> exists _, _ |- _] =>
    destruct H with v R c m; eauto n; clear H; edestruct_direct
  end.

Ltac edestruct_all := edestruct_all_in integer:(5).

Theorem htriple_of_triple (V : Set) (e : Expr V) P Q :
  triple e P Q ->
  hoare_triple e P Q.
Proof.
  unfold triple. intros Htriple. specialize Htriple with <[]>. revert Htriple.
  unfold_all. intros. edestruct_all_in integer:(15).
  repeat rewrite List.app_nil_r in *.
  repeat eexists; eauto; lia.
Qed.

Theorem htriple_weaken (V : Set) (e : Expr V) P P' Q Q' :
  P' ->> P ->
  (Q -->> Q') ->
  hoare_triple e P Q ->
  hoare_triple e P' Q'.
Proof.
  unfold hoare_triple, sa_implies. intros ? ? H ? ? ?.
  edestruct H as (?&?&?&?&?&?&?); eauto 10.
Qed.

Theorem triple_weaken (V : Set) (e : Expr V) P P' Q Q' :
  P' ->> P ->
  (Q -->> Q') ->
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
  split; intros ? ? ? H; [destruct H|]; subst; auto.
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
  unfold hoare_triple, sa_exists. split; intros ? ? ? H; [destruct H|]; eauto.
Qed.

Theorem triple_exists A (V : Set) (e : Expr V) P Q :
  (forall x : A, triple e (P x) Q) <-> triple e (<exists> x, P x) Q.
Proof.
  unfold_all.
  split; intros Htriple; intros; edestruct_direct; edestruct Htriple; eauto;
    repeat eexists; eauto.
Qed.

Theorem htriple_pure_post (V : Set) (e : Expr V) P Q :
  ((forall c m, P c m -> Q) /\ hoare_triple e P (fun _ => <[]>)) <->
    hoare_triple e P (fun _ => <[Q]>).
Proof.
  unfold hoare_triple, sa_pure, sa_empty. split.
  - intros [? Hhoare] ? ? ?.
    edestruct Hhoare as (?&?&?&?&?&(->&->)&?); repeat eexists; eauto.
  - intros Hhoare.
    split; intros; edestruct Hhoare as (?&?&?&?&?&(?&->&->)&?); eauto 10.
Qed.

Ltac solve_assoc :=
  repeat eexists; eauto using List.app_assoc; rewrite List.map_app in *; intros;
    try match goal with
    | [H : List.In _ (_ ++ _)%list |- _] => apply List.in_app_or in H as [? | ?]
    end;
    eauto using List.in_or_app.

Ltac split_all :=
  repeat match goal with
  | [|- exists _, _ ] => eexists
  | [|- _ /\ _ ] => split
  end.

Ltac or_choose :=
  match goal with
  | [|- _ \/ _] => left + right
  | _ => idtac
  end.

Ltac prove_disjoint_map :=
  repeat match goal with
  | [H : forall p,
      List.In p (List.map fst ?m1) ->
      List.In p (List.map fst ?m2) -> False |- _] =>
      fold (labels m1) in H; fold (labels m2) in H;
      fold (disjoint_maps m1 m2) in H
  | [|- forall p,
      List.In p (List.map fst ?m1) ->
      List.In p (List.map fst ?m2) -> False] =>
      fold (labels m1); fold (labels m2);
      fold (disjoint_maps m1 m2)
  | [H : disjoint_maps _ _ |- disjoint_maps _ _] => apply H
  end.

Lemma star_assoc_l (V : Set) (P : StateAssertion V) Q R :
  P <*> (Q <*> R) ->> (P <*> Q) <*> R.
Proof.
  unfold_all. intros. edestruct_direct.
  solve_assoc. lia.
Qed.

Lemma star_assoc_r (V : Set) (P : StateAssertion V) Q R :
  (P <*> Q) <*> R ->> P <*> (Q <*> R).
Proof.
  unfold_all. intros. edestruct_direct.
  solve_assoc. lia.
Qed.

Lemma star_assoc (V : Set) (P : StateAssertion V) Q R :
  P <*> (Q <*> R) <<->> (P <*> Q) <*> R.
Proof.
  auto using star_assoc_l, star_assoc_r.
Qed.

Lemma star_assoc_post_l (V : Set) (P : V -> StateAssertion V) Q R :
  P <*>+ (Q <*> R) -->> (P <*>+ Q) <*>+ R.
Proof.
  simpl. auto using star_assoc_l.
Qed.

Lemma star_assoc_post_r (V : Set) (P : V -> StateAssertion V) Q R :
  (P <*>+ Q) <*>+ R -->> P <*>+ (Q <*> R).
Proof.
  simpl. auto using star_assoc_r.
Qed.

Lemma star_assoc_post (V : Set) (P : V -> StateAssertion V) Q R :
  P <*>+ (Q <*> R) <<-->> (P <*>+ Q) <*>+ R.
Proof.
  auto using star_assoc_post_l, star_assoc_post_r.
Qed.

(*
Lemma star_comm (V : Set) (P : StateAssertion V) Q :
  P <*> Q <<->> Q <*> P.
Proof.
  unfold_all.
  split; intros; edestruct_direct; do 4 eexists; split_all; eauto; try lia. (*TODO*)  apply List.app_comm.
   eauto 100 with lamref st_assertions.
  auto using star_assoc_l, star_assoc_r.
Qed.
*)

Lemma star_credits (V : Set) (k : nat) (P : StateAssertion V) c m :
  (sa_credits k <*> P) c m <->
    exists c', c = k + c' /\ P c' m.
Proof.
  unfold_all.
  split; intros; edestruct_direct; eauto 10 with lamref st_assertions.
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
  hoare_triple v <[]> (fun v' => <[v' = v]>).
Proof.
  unfold hoare_triple, sa_pure, sa_empty.
  intros m Hm. subst. eauto 10 with lamref.
Qed.

Ltac solve_simple_triple n :=
  unfold_all; intros; edestruct_direct; eauto n with lamref.
Ltac solve_simple_triple_30 :=
  solve_simple_triple integer:(30).

Theorem triple_value (V : Set) (v : Value V) :
  triple v <[]> (fun v' => <[v' = v]>).
Proof.
  solve_simple_triple integer:(20).
Qed.

Theorem htriple_value' (V : Set) (v : Value V) (P : StateAssertion V) :
  hoare_triple v P (fun v' => <[v' = v]> <*> P).
Proof.
  unfold hoare_triple, sa_star, sa_pure, sa_empty, disjoint_maps.
  eauto 20 with lamref.
Qed.

Theorem triple_value' (V : Set) (v : Value V) (P : StateAssertion V) :
  triple v P (fun v' => <[v' = v]> <*> P).
Proof.
  solve_simple_triple_30.
Qed.

Theorem htriple_value_untimed (V : Set) (v : Value V) (P : StateAssertion V) :
  hoare_triple v P (fun _ => P).
Proof.
  eapply htriple_weaken; eauto using htriple_value';
    unfold sa_implies, sa_star, sa_pure, sa_empty;
    [| intros v' c m (c1&m1&c2&m2&(?&?&?)&?&?&?&?); subst ];
    eauto.
Qed.

Theorem triple_value_untimed (V : Set) (v : Value V) (P : StateAssertion V) :
  triple v P (fun _ => P).
Proof.
  eapply triple_weaken; eauto using triple_value';
    unfold sa_implies, sa_star, sa_pure, sa_empty;
    [| intros v' c m (c1&m1&c2&m2&(?&?&?)&?&?&?&?); subst ];
    eauto.
Qed.

Ltac injection_on_all constr :=
  repeat match goal with
  | [H : constr _ = constr _ |- _] => injection H as H
  end.

Theorem htriple_lam (V : Set) (e : Expr _) (v : Value V) P Q :
  hoare_triple (subst_e e v) P Q ->
  hoare_triple ((-\e) <* v) (P <*> sa_credits 1) Q.
Proof.
  unfold hoare_triple, sa_credits, sa_star. intros. destruct c1.
  { edestruct_direct. lia. }
  specialize (H c1 m). edestruct_direct.
  rewrite List.app_nil_r in *. rewrite Nat.add_1_r in *. injection_on_all S.
  destruct H as (?&?&?&?&?&?&?); subst; eauto 10 with lamref.
Qed.

Theorem triple_lam (V : Set) (e : Expr _) (v : Value V) P Q :
  triple (subst_e e v) P Q ->
  triple ((-\e) <* v) (P <*> sa_credits 1) Q.
Proof.
  unfold_all. intros. destruct c1.
  { edestruct_direct. lia. }
  specialize (H H0 c1 m). edestruct_direct.
  rewrite List.app_nil_r in *. rewrite Nat.add_1_r in *. simpl in *.
  injection_on_all S.
  destruct H as (?&?&?&?&?&(?&?&?&?&?&?&?&?&?)&?); subst; eauto 10 with lamref.
  repeat eexists; eauto_lr. lia.
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

Ltac normalize_star :=
  repeat match goal with
  | [H : ((_ <*> _) <*> _) ?c ?m |- _] => apply star_assoc_r in H
  | [H : (<[_]> <*> _) ?c ?m |- _] => apply star_pure_l in H as [? ?]
  | [H : ((<exists> _, _) <*> _) ?c ?m |- _] => apply star_exists_l in H as [? ?]
  | [H : (<exists> _, _) ?c ?m |- _] => destruct H
  end.

Ltac solve_star :=
  repeat match goal with
  | [|- ((_ <*> _) <*> _) ?c ?m ] => apply star_assoc_l; eauto
  | [|- (<[_]> <*> _) ?c ?m ] => apply star_pure_l; split; auto
  | [|- ((<exists> _, _) <*> _) ?c ?m ] => apply star_exists_l; eexists; eauto
  | [|- (<exists> _, _) ?c ?m] => eexists
  end.
(*
Ltac solve_assertion :=
  repeat match goal with
  | [|- (<exists> _, _) ?m ] => apply triple_exists
*)
Ltac esolve_star :=
  repeat match goal with
  | [|- ((_ <*> _) <*> _) ?m ] => apply star_assoc_l
  | [|- (<[_]> <*> _) ?m ] => apply star_pure_l; split; eauto
  end.

Ltac discr_0_S_cred :=
  match goal with
  | [H : (sa_credits (S _)  <*> _) 0 _ |- _] =>
    revert H; unfold_all; intro; edestruct_direct; lia
  end.

Ltac make_cred_positive :=
  match goal with
  | [H : (sa_credits (S _) <*> _) ?c _ |- _] =>
    destruct c; [ discr_0_S_cred |]; unfold sa_star, sa_credits in H
  end.

Ltac solve_htriple n H :=
  unfold hoare_triple;
  intros;
  normalize_star;
  make_cred_positive;
  edestruct_direct;
  simpl in *;
  injection_on_all S; subst;
  repeat (edestruct_all; normalize_star);
  edestruct_direct;
  subst; simpl in *;
  split_all;
  eauto n using H;
  solve_star;
  eauto;
  try lia.

Ltac solve_htriple_15 := solve_htriple integer:(15).

Ltac fold_star :=
  match goal with
  | [Hp : ?P ?cp ?mp, Hq : ?Q ?cq ?mq, Hdis : disjoint_maps ?mp ?mq |- _] =>
    assert ((P <*> Q) (cp + cq) (mp ++ mq)%list);
      [eauto 10 with st_assertions|]
  end.

Ltac solve_triple n H :=
  unfold triple, hoare_triple;
  intros;
  normalize_star;
  make_cred_positive;
  edestruct_direct;
  simpl in *;
  injection_on_all S; subst; fold_star;
  repeat (edestruct_all; normalize_star);
  edestruct_direct;
  subst;
  split_all;
  eauto n using H;
  solve_star;
  eauto;
  try lia.

Ltac solve_triple_15 := solve_triple integer:(15).

Theorem htriple_app (V : Set) (e1 e2 : Expr V)
  P1 P2 Q2 Q3 :
  hoare_triple e1
    P1
    (fun v => <exists> e1',
      <[v = (-\e1') /\
        (forall v : Value V, hoare_triple (subst_e e1' v) (Q2 v) Q3)]> <*>
      P2) ->
  hoare_triple e2 P2 Q2 ->
  hoare_triple (App e1 e2) (sa_credits 1 <*> P1) Q3.
Proof.
  solve_htriple integer:(10) big_red_app.
Qed.

Theorem triple_app (V : Set) (e1 e2 : Expr V)
  P1 P2 Q2 Q3 :
  triple e1
    P1
    (fun v => <exists> e1',
      <[v = (-\e1') /\
        (forall v : Value V, triple (subst_e e1' v) (Q2 v) Q3)]> <*>
      P2) ->
  triple e2 P2 Q2 ->
  triple (App e1 e2) (sa_credits 1 <*> P1) Q3.
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

Theorem htriple_bneg (V : Set) (e : Expr V) P Q :
  hoare_triple e P (fun v => <exists> b : bool, <[v = Bool b]> <*> Q b) ->
  hoare_triple ([~] e)
    (sa_credits 1 <*> P)
    (fun v => <exists> b : bool, <[v = Bool (negb b)]> <*> Q b).
Proof.
  solve_htriple_15 big_red_bneg.
Qed.

Theorem triple_bneg (V : Set) (e : Expr V) P Q :
  triple e P (fun v => <exists> b : bool, <[v = Bool b]> <*> Q b) ->
  triple ([~] e)
    (sa_credits 1 <*> P)
    (fun v => <exists> b : bool, <[v = Bool (negb b)]> <*> Q b).
Proof.
  solve_triple integer:(10) big_red_bneg.
Qed.

Theorem htriple_ineg (V : Set) (e : Expr V) P Q :
  hoare_triple e P (fun v => <exists> i : Z, <[v = Int i]> <*> Q i) ->
  hoare_triple ([--] e)
    (sa_credits 1 <*> P)
    (fun v => <exists> i : Z, <[v = Int (- i)]> <*> Q i).
Proof.
  solve_htriple_15 big_red_ineg.
Qed.

Theorem triple_ineg (V : Set) (e : Expr V) P Q :
  triple e P (fun v => <exists> i : Z, <[v = Int i]> <*> Q i) ->
  triple ([--] e)
    (sa_credits 1 <*> P)
    (fun v => <exists> i : Z, <[v = Int (- i)]> <*> Q i).
Proof.
  solve_triple_15 big_red_ineg.
Qed.

Theorem htriple_bor (V : Set) (e1 e2 : Expr V)
  P1 Q1 Q2 :
  hoare_triple e1
    P1
    (fun v => <exists> b1 : bool, <[v = Bool b1]> <*> Q1 b1) ->
  (forall b1 : bool,
    hoare_triple e2
      (Q1 b1)
      (fun v => <exists> b2 : bool, <[v = Bool b2]> <*> Q2 b1 b2)) ->
  @hoare_triple V (e1 [||] e2)
    (sa_credits 1 <*> P1)
    (fun v => <exists> b1 b2 : bool, <[v = Bool (b1 || b2)]> <*> Q2 b1 b2).
Proof.
  solve_htriple_15 big_red_bor.
Qed.

Theorem triple_bor (V : Set) (e1 e2 : Expr V)
  P1 Q1 Q2 :
  triple e1 P1 (fun v => <exists> b1 : bool, <[v = Bool b1]> <*> Q1 b1) ->
  (forall b1 : bool,
    triple e2
      (Q1 b1)
      (fun v => <exists> b2 : bool, <[v = Bool b2]> <*> Q2 b1 b2)) ->
  @triple V (e1 [||] e2)
    (sa_credits 1 <*> P1)
    (fun v => <exists> b1 b2 : bool, <[v = Bool (b1 || b2)]> <*> Q2 b1 b2).
Proof.
  solve_triple_15 big_red_bor.
Qed.

Theorem htriple_band (V : Set) (e1 e2 : Expr V)
  P1 Q1 Q2 :
  hoare_triple e1
    P1
    (fun v => <exists> b1 : bool, <[v = Bool b1]> <*> Q1 b1) ->
  (forall b1 : bool,
    hoare_triple e2
      (Q1 b1)
      (fun v => <exists> b2 : bool, <[v = Bool b2]> <*> Q2 b1 b2)) ->
  @hoare_triple V (e1 [&&] e2)
    (sa_credits 1 <*> P1)
    (fun v => <exists> b1 b2 : bool, <[v = Bool (b1 && b2)]> <*> Q2 b1 b2).
Proof.
  solve_htriple_15 big_red_band.
Qed.

Theorem triple_band (V : Set) (e1 e2 : Expr V)
  P1 Q1 Q2 :
  triple e1
    P1
    (fun v => <exists> b1 : bool, <[v = Bool b1]> <*> Q1 b1) ->
  (forall b1 : bool,
    triple e2
      (Q1 b1)
      (fun v => <exists> b2 : bool, <[v = Bool b2]> <*> Q2 b1 b2)) ->
  @triple V (e1 [&&] e2)
    (sa_credits 1 <*> P1)
    (fun v => <exists> b1 b2 : bool, <[v = Bool (b1 && b2)]> <*> Q2 b1 b2).
Proof.
  solve_triple_15 big_red_band.
Qed.

Theorem htriple_iadd (V : Set) (e1 e2 : Expr V)
  P1 Q1 Q2 :
  hoare_triple e1
    P1
    (fun v => <exists> i1 : Z, <[v = Int i1]> <*> Q1 i1) ->
  (forall i1 : Z,
    hoare_triple e2
      (Q1 i1)
      (fun v => <exists> i2 : Z, <[v = Int i2]> <*> Q2 i1 i2)) ->
  @hoare_triple V (e1 [+] e2)
    (sa_credits 1 <*> P1)
    (fun v => <exists> i1 i2 : Z, <[v = Int (i1 + i2)]> <*> Q2 i1 i2).
Proof.
  solve_htriple_15 big_red_iadd.
Qed.

Theorem triple_iadd (V : Set) (e1 e2 : Expr V)
  P1 Q1 Q2 :
  triple e1
    P1
    (fun v => <exists> i1 : Z, <[v = Int i1]> <*> Q1 i1) ->
  (forall i1 : Z,
    triple e2
      (Q1 i1)
      (fun v => <exists> i2 : Z, <[v = Int i2]> <*> Q2 i1 i2)) ->
  @triple V (e1 [+] e2)
    (sa_credits 1 <*> P1)
    (fun v => <exists> i1 i2 : Z, <[v = Int (i1 + i2)]> <*> Q2 i1 i2).
Proof.
  solve_triple_15 big_red_iadd.
Qed.

Theorem htriple_isub (V : Set) (e1 e2 : Expr V)
  P1 Q1 Q2 :
  hoare_triple e1
    P1
    (fun v => <exists> i1 : Z, <[v = Int i1]> <*> Q1 i1) ->
  (forall i1 : Z,
    hoare_triple e2
      (Q1 i1)
      (fun v => <exists> i2 : Z, <[v = Int i2]> <*> Q2 i1 i2)) ->
  @hoare_triple V (e1 [-] e2)
    (sa_credits 1 <*> P1)
    (fun v => <exists> i1 i2 : Z, <[v = Int (i1 - i2)]> <*> Q2 i1 i2).
Proof.
  solve_htriple_15 big_red_isub.
Qed.

Theorem triple_isub (V : Set) (e1 e2 : Expr V)
  P1 Q1 Q2 :
  triple e1
    P1
    (fun v => <exists> i1 : Z, <[v = Int i1]> <*> Q1 i1) ->
  (forall i1 : Z,
    triple e2
      (Q1 i1)
      (fun v => <exists> i2 : Z, <[v = Int i2]> <*> Q2 i1 i2)) ->
  @triple V (e1 [-] e2)
    (sa_credits 1 <*> P1)
    (fun v => <exists> i1 i2 : Z, <[v = Int (i1 - i2)]> <*> Q2 i1 i2).
Proof.
  solve_triple_15 big_red_isub.
Qed.

Theorem htriple_imul (V : Set) (e1 e2 : Expr V)
  P1 Q1 Q2 :
  hoare_triple e1
    P1
    (fun v => <exists> i1 : Z, <[v = Int i1]> <*> Q1 i1) ->
  (forall i1 : Z,
    hoare_triple e2
      (Q1 i1)
      (fun v => <exists> i2 : Z, <[v = Int i2]> <*> Q2 i1 i2)) ->
  @hoare_triple V (e1 [*] e2)
    (sa_credits 1 <*> P1)
    (fun v => <exists> i1 i2 : Z, <[v = Int (i1 * i2)]> <*> Q2 i1 i2).
Proof.
  solve_htriple_15 big_red_imul.
Qed.

Theorem triple_imul (V : Set) (e1 e2 : Expr V)
  P1 Q1 Q2 :
  triple e1
    P1
    (fun v => <exists> i1 : Z, <[v = Int i1]> <*> Q1 i1) ->
  (forall i1 : Z,
    triple e2
      (Q1 i1)
      (fun v => <exists> i2 : Z, <[v = Int i2]> <*> Q2 i1 i2)) ->
  @triple V (e1 [*] e2)
    (sa_credits 1 <*> P1)
    (fun v => <exists> i1 i2 : Z, <[v = Int (i1 * i2)]> <*> Q2 i1 i2).
Proof.
  solve_triple_15 big_red_imul.
Qed.

Theorem htriple_idiv (V : Set) (e1 e2 : Expr V)
  P1 Q1 Q2 :
  hoare_triple e1
    P1
    (fun v => <exists> i1 : Z, <[v = Int i1]> <*> Q1 i1) ->
  (forall i1 : Z,
    hoare_triple e2
      (Q1 i1)
      (fun v => <exists> i2 : Z, <[v = Int i2]> <*> Q2 i1 i2)) ->
  @hoare_triple V (e1 [/] e2)
    (sa_credits 1 <*> P1)
    (fun v => <exists> i1 i2 : Z, <[v = Int (i1 / i2)]> <*> Q2 i1 i2).
Proof.
  solve_htriple_15 big_red_idiv.
Qed.


Theorem triple_idiv (V : Set) (e1 e2 : Expr V)
  P1 Q1 Q2 :
  triple e1
    P1
    (fun v => <exists> i1 : Z, <[v = Int i1]> <*> Q1 i1) ->
  (forall i1 : Z,
    triple e2
      (Q1 i1)
      (fun v => <exists> i2 : Z, <[v = Int i2]> <*> Q2 i1 i2)) ->
  @triple V (e1 [/] e2)
    (sa_credits 1 <*> P1)
    (fun v => <exists> i1 i2 : Z, <[v = Int (i1 / i2)]> <*> Q2 i1 i2).
Proof.
  solve_triple_15 big_red_idiv.
Qed.

Theorem htriple_clt (V : Set) (e1 e2 : Expr V)
  P1 Q1 Q2 :
  hoare_triple e1
    P1
    (fun v => <exists> i1 : Z, <[v = Int i1]> <*> Q1 i1) ->
  (forall i1 : Z,
    hoare_triple e2
      (Q1 i1)
      (fun v => <exists> i2 : Z, <[v = Int i2]> <*> Q2 i1 i2)) ->
  @hoare_triple V (e1 [<] e2)
    (sa_credits 1 <*> P1)
    (fun v => <exists> i1 i2 : Z, <[v = Bool (i1 <? i2)%Z]> <*> Q2 i1 i2).
Proof.
  solve_htriple_15 big_red_clt.
Qed.

Theorem triple_clt (V : Set) (e1 e2 : Expr V)
  P1 Q1 Q2 :
  triple e1
    P1
    (fun v => <exists> i1 : Z, <[v = Int i1]> <*> Q1 i1) ->
  (forall i1 : Z,
    triple e2
      (Q1 i1)
      (fun v => <exists> i2 : Z, <[v = Int i2]> <*> Q2 i1 i2)) ->
  @triple V (e1 [<] e2)
    (sa_credits 1 <*> P1)
    (fun v => <exists> i1 i2 : Z, <[v = Bool (i1 <? i2)%Z]> <*> Q2 i1 i2).
Proof.
  solve_triple_15 big_red_clt.
Qed.

Theorem htriple_ceq (V : Set) (e1 e2 : Expr V)
  P1 Q1 Q2 :
  hoare_triple e1
    P1
    (fun v => <exists> i1 : Z, <[v = Int i1]> <*> Q1 i1) ->
  (forall i1 : Z,
    hoare_triple e2
      (Q1 i1)
      (fun v => <exists> i2 : Z, <[v = Int i2]> <*> Q2 i1 i2)) ->
  @hoare_triple V (e1 [=] e2)
    (sa_credits 1 <*> P1)
    (fun v => <exists> i1 i2 : Z, <[v = Bool (i1 =? i2)%Z]> <*> Q2 i1 i2).
Proof.
  solve_htriple_15 big_red_ceq.
Qed.

Theorem triple_ceq (V : Set) (e1 e2 : Expr V)
  P1 Q1 Q2 :
  triple e1
    P1
    (fun v => <exists> i1 : Z, <[v = Int i1]> <*> Q1 i1) ->
  (forall i1 : Z,
    triple e2
      (Q1 i1)
      (fun v => <exists> i2 : Z, <[v = Int i2]> <*> Q2 i1 i2)) ->
  @triple V (e1 [=] e2)
    (sa_credits 1 <*> P1)
    (fun v => <exists> i1 i2 : Z, <[v = Bool (i1 =? i2)%Z]> <*> Q2 i1 i2).
Proof.
  solve_triple_15 big_red_ceq.
Qed.

Ltac revert_all_eq :=
  repeat match goal with
  | [H : _ = _ |- _] => revert H
  end.

Ltac clear_trivial :=
  repeat match goal with
  | [H : disjoint_maps []%list _ |- _] => clear H
  | [H : disjoint_maps _ []%list |- _] => clear H
  end.

Ltac match_lists_for_lengths :=
  repeat match goal with
  | [_ : 0 = List.length ?xs |- _] => destruct xs; [simpl in *|discriminate]
  | [_ : S _ = List.length ?xs |- _] =>
    destruct xs; [discriminate|simpl in *]; injection_on_all S
  | [_ : Some _ = List.head ?xs |- _] =>
    destruct xs; [discriminate|simpl in *]; injection_on_all_Some
  end.

Theorem htriple_rec (V : Set) (es : list (Expr V)) (vs : list (Value V))
  n Ps P Q :
  n = List.length es ->
  n = List.length vs ->
  1+n = List.length Ps ->
  Some P = List.head Ps ->
  Some Q = last_error Ps ->
  (forall i e v P Q,
    Nth i es e ->
    Nth i vs v ->
    Nth i Ps P ->
    Nth (1+i) Ps Q ->
    hoare_triple e
      P
      (fun v' => <[v' = v]> <*> Q)) ->
  hoare_triple (RecE es)
    (sa_credits 1 <*> P)
    (fun v => <[v = RecV vs]> <*> Q).
Proof.
  unfold hoare_triple.
  intros. remember m as m0. revert_all_eq. make_cred_positive.
  edestruct_direct. simpl in *. injection_on_all S. subst_with c1. intros.
  subst_with m. clear_trivial.
  assert (exists cs ms c2 m',
    1+n = List.length cs /\
    1+n = List.length ms /\
    Some c1 = List.head cs /\
    Some c2 = last_error cs /\
    Some m = List.head ms /\
    Some m' = last_error ms /\
    Q c2 m' /\
      forall i c2 c2',
      Nth i cs c2 ->
      Nth (1+i) cs c2' ->
      exists c, c2 = c + c2' /\
        forall e v m m',
        Nth i es e ->
        Nth i vs v ->
        Nth i ms m ->
        Nth (1+i) ms m' ->
        C[e,m ~~> v,m'|c])
    as (cs&ms&c2&m'&?&?&?&?&?&?&?&?).
  { generalize dependent c1. generalize dependent m.
    generalize dependent P. generalize dependent Ps.
    generalize dependent vs. generalize dependent es.
    induction n as [|n IHn]; intros; unfold last_error in *; match_lists_for_lengths;
      injection_on_all_Some; subst.
    - exists [c1]%list, [m]%list. split_all; simpl; auto. intros.
      inversion_Nth_cons_succ. inversion_Nth_nil.
    - match goal with
      | [H :
          forall _ _ _ _ _,
          Nth _ _ _ ->
          Nth _ _ _ ->
          Nth _ _ _ ->
          Nth _ _ _ ->
          forall _ _,
          _ ->
          exists _ _ _ _, _ /\ _ /\ _ |- _] =>
        edestruct H with (i := 0) as (v'&c'&c2&m'&?&?&?); eauto_lr
      end.
      normalize_star. subst. fold (List.last_error (s0::Ps)%list) in H6.
      match goal with
      | [sa : StateAssertion V |- _] =>
        edestruct IHn with (Ps := (sa::Ps)%list) as (cs&ms&c2'&m''&?&?&?&?&?&?&?&?);
          simpl; eauto 10 with lamref
      end.
      match_lists_for_lengths.
      simpl in *. injection_on_all_Some. subst_with c2.
      match goal with
      | [_ : cost_red _ _ _ ?mm ?cc |- _] =>
        exists (cc+c2::c2::cs)%list, (m::mm::ms)%list
      end.
      subst. split_all; simpl in *; eauto 3. intros.
      inversion_Nth_cons_succ.
      match goal with
      | [_ : cost_red _ _ _ _ ?cc |- _] => inversion_Nth_cons_2 (cc+c2) c2
      end.
      + inversion_Nth_cons. split_all; auto. intros. inversion_all_Nth_cons.
        auto.
      + match goal with
        | [H : forall _ _ _, Nth _ _ _ -> Nth _ _ _ -> exists _, _ /\ _ |- _] =>
          edestruct H as (?&?&?); eauto
        end.
        split_all; eauto. intros. repeat inversion_Nth_cons_succ. eauto_lr. }
  destruct cs; [discriminate|].
  assert (c2 <= c1).
  { simpl in *. injection_on_all_Some. subst.
    eapply mono_le_last with (ns := (n0::cs)%list); eauto_lr.
    unfold monotone. intros. edestruct H13 with (i := i) as (?&?&?); eauto.
    lia. }
  split_all; solve_star; simpl; eauto using big_red_rec_diff.
  lia.
Qed.
(*
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
*)
(* vvvv TODO vvvv *)
Theorem htriple_get (V : Set) n (e : Expr V) P Q :
  hoare_triple e
    P
    (fun v' =>
      <exists> vs, <[v' = RecV vs]> <*> <exists> v, <[Nth n vs v]> <*> Q v) ->
  hoare_triple (Get n e) (sa_credits 1 <*> P) Q.
Proof.
  solve_htriple_15 big_red_get.
Qed.

Theorem triple_get (V : Set) n (e : Expr V) P Q :
  triple e
    P
    (fun v' =>
      <exists> vs, <[v' = RecV vs]> <*> <exists> v, <[Nth n vs v]> <*> Q v) ->
  triple (Get n e) (sa_credits 1 <*> P) Q.
Proof.
  solve_triple_15 big_red_get.
Qed.

Theorem htriple_ref (V : Set) (e : Expr V) P Q :
  hoare_triple e P Q ->
  hoare_triple (Ref e)
    (sa_credits 1 <*> P)
    (fun v' => <exists> l v, <[v' = Lab l]> <*> <( l :== v )> <*> Q v).
Proof.
  pose proof new_label_is_fresh. unfold Is_fresh_label, not in *.
  unfold_all. intros. edestruct_direct. edestruct_all. simpl in *.
  split_all; try (eapply big_red_ref; eauto); simpl; eauto.
  intros ? [? | []] ?. subst. eauto.
Qed.

Theorem triple_ref (V : Set) (e : Expr V) (v : Value V) P Q :
  triple e P Q ->
  triple (Ref e)
    (sa_credits 1 <*> P)
    (fun v' => <exists> l v, <[v' = Lab l]> <*> <( l :== v )> <*> Q v).
Proof.
  pose proof new_label_is_fresh. unfold Is_fresh_label, not in *.
  unfold triple, hoare_triple. intros. normalize_star. make_cred_positive.
  edestruct_direct. simpl in *. injection_on_all S. fold_star. edestruct_all.
  normalize_star. subst.
  split_all; try (eapply big_red_ref; eauto); simpl; eauto.
  solve_star. unfold sa_star in *. edestruct_direct.
  split_all; eauto with st_assertions. intros ? [? | []] ?. subst. eauto.
Qed.

Ltac find_star_and_unfold_all :=
  match goal with
  | [H : (_ <*> _) _ _ |- _] => unfold_all_in H
  end.

Theorem htriple_deref (V : Set) (e : Expr V) (v : Value V) l P Q :
  hoare_triple e
    (<(l :== v)> <*> P)
    (fun v' => <[v' = Lab l]> <*> <(l :== v)> <*> Q) ->
  hoare_triple (Deref e)
    (sa_credits 1 <*> <(l :== v)> <*> P)
    (fun v' => <[v' = v]> <*> <(l :== v)> <*> Q).
Proof.
  unfold triple, hoare_triple. intros. normalize_star. make_cred_positive.
  edestruct_direct. fold_star. edestruct_all. simpl in *.
  injection_on_all S. unfold_all. find_star_and_unfold_all. edestruct_direct.
  repeat eexists; try eapply big_red_deref; simpl in *; eauto with lamref.
Qed.

Ltac conormalize_star :=
  repeat match goal with
  | [H : (_ <*> (_ <*> _)) ?c ?m |- _] => apply star_assoc_l in H
  end.

Theorem triple_deref (V : Set) (e : Expr V) (v : Value V) l P Q :
  triple e
    (<(l :== v)> <*> P)
    (fun v' => <[v' = Lab l]> <*> <(l :== v)> <*> Q) ->
  triple (Deref e)
    (sa_credits 1 <*> <(l :== v)> <*> P)
    (fun v' => <[v' = v]> <*> <(l :== v)> <*> Q).
Proof.
  unfold triple, hoare_triple. intros. normalize_star. make_cred_positive.
  edestruct_direct. fold_star. fold_star. conormalize_star. edestruct_all. simpl in *.
  injection_on_all S. unfold_all. find_star_and_unfold_all. edestruct_direct.
  repeat eexists; try eapply big_red_deref; simpl in *; eauto with lamref.
Qed.
(*
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
*)
Theorem htriple_seq (V : Set) (e1 e2 : Expr V) P1 Q1 Q2 :
  hoare_triple e1 P1 (fun v' => <[v' = U_val]> <*> Q1) ->
  hoare_triple e2 Q1 Q2 ->
  hoare_triple (Seq e1 e2) (sa_credits 1 <*> P1) Q2.
Proof.
  solve_htriple_15 big_red_seq.
Qed.

Theorem triple_seq (V : Set) (e1 e2 : Expr V) P1 Q1 Q2 :
  triple e1 P1 (fun v' => <[v' = U_val]> <*> Q1) ->
  triple e2 Q1 Q2 ->
  triple (Seq e1 e2) (sa_credits 1 <*> P1) Q2.
Proof.
  solve_triple_15 big_red_seq.
Qed.

Theorem htriple_if_simple (V : Set) (e1 e2 e3 : Expr V) b P1 Q1 Q2 :
  hoare_triple e1 P1 (fun v' => <[v' = Bool b]> <*> Q1 b) ->
  hoare_triple e2 (Q1 true) (fun v => Q2 v) ->
  hoare_triple e3 (Q1 false) (fun v => Q2 v) ->
  hoare_triple (If e1 e2 e3) (sa_credits 1 <*> P1) Q2.
Proof.
  destruct b.
  - solve_htriple_15 big_red_if_true.
  - solve_htriple_15 big_red_if_false.
Qed.

Theorem triple_if_simple (V : Set) (e1 e2 e3 : Expr V) b P1 Q1 Q2 :
  triple e1 P1 (fun v' => <[v' = Bool b]> <*> Q1 b) ->
  triple e2 (Q1 true) (fun v => Q2 v) ->
  triple e3 (Q1 false) (fun v => Q2 v) ->
  triple (If e1 e2 e3) (sa_credits 1 <*> P1) Q2.
Proof.
  destruct b.
  - solve_triple_15 big_red_if_true.
  - solve_triple_15 big_red_if_false.
Qed.

Theorem htriple_if (V : Set) (e1 e2 e3 : Expr V) P1 Q1 Q2 :
  hoare_triple e1 P1 (fun v' => <exists> b, <[v' = Bool b]> <*> Q1 b) ->
  hoare_triple e2 (Q1 true) (fun v => Q2 v) ->
  hoare_triple e3 (Q1 false) (fun v => Q2 v) ->
  hoare_triple (If e1 e2 e3) (sa_credits 1 <*> P1) Q2.
Proof.
  unfold hoare_triple. intros.
  make_cred_positive. edestruct_direct. simpl in *. injection_on_all S.
  subst_with c1. edestruct_all. normalize_star. subst.
  match goal with [b : bool |- _] => destruct b end;
    edestruct_all; split_all; eauto using big_red_if_true, big_red_if_false; lia.
Qed.

Theorem triple_if (V : Set) (e1 e2 e3 : Expr V) P1 Q1 Q2 :
  triple e1 P1 (fun v' => <exists> b, <[v' = Bool b]> <*> Q1 b) ->
  triple e2 (Q1 true) (fun v => Q2 v) ->
  triple e3 (Q1 false) (fun v => Q2 v) ->
  triple (If e1 e2 e3) (sa_credits 1 <*> P1) Q2.
Proof.
  unfold triple, hoare_triple. intros. normalize_star.
  make_cred_positive. edestruct_direct. simpl in *. injection_on_all S.
  fold_star. edestruct_all. normalize_star. subst.
  match goal with [b : bool |- _] => destruct b end;
    edestruct_all; split_all; eauto using big_red_if_true, big_red_if_false; lia.
Qed.

Theorem htriple_while_true (V : Set) (e1 e2 : Expr V) P Q1 Q2 Q :
  hoare_triple e1 P (fun v => <[v = Bool true]> <*> Q1) ->
  hoare_triple e2 Q1 (fun v => <[v = U_val]> <*> Q2) ->
  hoare_triple (While e1 e2) Q2 (fun v => <[v = U_val]> <*> Q) ->
  hoare_triple (While e1 e2)
    (sa_credits 3 <*> P)
    (fun v => <[v = U_val]> <*> Q).
Proof.
  solve_htriple_15 big_red_while_true.
Qed.

Theorem triple_while_true (V : Set) (e1 e2 : Expr V) P Q1 Q2 Q :
  triple e1 P (fun v => <[v = Bool true]> <*> Q1) ->
  triple e2 Q1 (fun v => <[v = U_val]> <*> Q2) ->
  triple (While e1 e2) Q2 (fun v => <[v = U_val]> <*> Q) ->
  triple (While e1 e2)
    (sa_credits 3 <*> P)
    (fun v => <[v = U_val]> <*> Q).
Proof.
  solve_triple_15 big_red_while_true.
Qed.

Theorem htriple_while_false (V : Set) (e1 e2 : Expr V) P Q :
  hoare_triple e1 P (fun v => <[v = Bool false]> <*> Q) ->
  hoare_triple (While e1 e2)
    (sa_credits 2 <*> P)
    (fun v => <[v = U_val]> <*> Q).
Proof.
  solve_htriple_15 big_red_while_false.
Qed.

Theorem triple_while_false (V : Set) (e1 e2 : Expr V) P Q :
  triple e1 P (fun v => <[v = Bool false]> <*> Q) ->
  triple (While e1 e2)
    (sa_credits 2 <*> P)
    (fun v => <[v = U_val]> <*> Q).
Proof.
  solve_triple_15 big_red_while_false.
Qed.

Theorem htriple_while (V : Set) (e1 e2 : Expr V) P Q :
  hoare_triple e1
    P
    (fun v => <exists> b, <[v = Bool b]> <*> Q b) ->
  hoare_triple e2
    (Q true)
    (fun v => <[v = U_val]> <*> sa_credits 3 <*> P) ->
  hoare_triple (While e1 e2)
    (sa_credits 2 <*> P)
    (fun v => <[v = U_val]> <*> Q false).
Proof.
  unfold hoare_triple. intros ? ?. induction c1 using (well_founded_ind lt_wf).
  intros. make_cred_positive. edestruct_direct. simpl in *.
  injection_on_all S. edestruct_all. normalize_star. destruct x1.
  2:{ subst. split_all. eapply big_red_while_false; eauto. solve_star; eauto. lia. }
  edestruct_all. normalize_star. destruct x6.
  { find_star_and_unfold_all. edestruct_direct. discriminate. }
  assert ((sa_credits 2 <*> P) x6 x7).
  { find_star_and_unfold_all. edestruct_direct. simpl in *. injection_on_all S. unfold_all. split_all; eauto. }
  assert (x6 < S (S (x0 + (x5 + S x6)))). { lia. }
  edestruct (H1 x6 H8 x7 H7). edestruct_direct. normalize_star. subst. split_all.
  - eapply big_red_while_true with (c1 := x0) (c2 := x5) (c3 := x3); eauto.
  - solve_star; eauto.
  - lia.
Qed.

Theorem triple_while (V : Set) (e1 e2 : Expr V) P Q :
  triple e1
    P
    (fun v => <exists> b, <[v = Bool b]> <*> Q b) ->
  triple e2
    (Q true)
    (fun v => <[v = U_val]> <*> sa_credits 3 <*> P) ->
  triple (While e1 e2)
    (sa_credits 2 <*> P)
    (fun v => <[v = U_val]> <*> Q false).
Proof.
  unfold triple, hoare_triple. intros ? ?. induction c1 using (well_founded_ind lt_wf).
  intros. normalize_star. make_cred_positive. edestruct_direct. fold_star. simpl in *.
  injection_on_all S. edestruct_all. normalize_star. destruct x7.
  2:{ subst. split_all. eapply big_red_while_false; eauto. solve_star; eauto. lia. }
  edestruct_all. normalize_star. destruct x9.
  { find_star_and_unfold_all. edestruct_direct. discriminate. }
  assert (((sa_credits 2 <*> P) <*> H1) x9 x10).
  { find_star_and_unfold_all. edestruct_direct. simpl in *. injection_on_all S. unfold_all. split_all; eauto. }
  assert (x9 < S (S (x3 + x5))). { lia. }
  edestruct (H2 x9 H13 x10 H12). edestruct_direct. normalize_star. subst. split_all.
  - eapply big_red_while_true; eauto.
  - solve_star; eauto.
  - lia.
Qed.
