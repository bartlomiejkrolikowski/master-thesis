Require Arith.
Require List.
Import List.ListNotations.
Require Import String.
Require Import ZArith.

Require Import src.LambdaRef.
Require Import src.LamRefFacts.
Require Import src.LambdaTotalTriple_credits_perm.
Require Import src.Tactics.

Require Import src.Interweave.

From Coq Require Import Lia.

Ltac unfold_all :=
  unfold triple, hoare_triple, sa_exists, sa_forall, sa_credits, sa_star,
    sa_single_any, sa_single, sa_single_decl, sa_array_decl, sa_pure, sa_empty,
    sa_implies, disjoint_maps, labels.

Ltac unfold_all_in H :=
  unfold triple, hoare_triple, sa_exists, sa_forall, sa_credits, sa_star,
    sa_single_any, sa_single, sa_single_decl, sa_array_decl, sa_pure, sa_empty,
    sa_implies, disjoint_maps, labels in H.

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

Lemma Interweave_valid V (m1 m2 m3 : Map V) :
  Is_Valid_Map m3 ->
  Interweave m1 m2 m3 ->
  Is_Valid_Map m1 /\ Is_Valid_Map m2.
Proof.
  unfold Is_Valid_Map, labels. intros Hvalid Hinter. induction Hinter; simpl.
  - auto.
  - inversion Hvalid. destruct IHHinter; auto. split; auto. constructor; auto.
    unfold not in *. eauto using in_or_Interweave, map_Interweave.
  - inversion Hvalid. destruct IHHinter; auto. split; auto. constructor; auto.
    unfold not in *. eauto using in_or_Interweave, map_Interweave.
Qed.

Lemma Interweave_valid_l V (m1 m2 m3 : Map V) :
  Is_Valid_Map m3 ->
  Interweave m1 m2 m3 ->
  Is_Valid_Map m1.
Proof.
  intros Hvalid Hinter. apply Interweave_valid in Hinter as (?&?); auto.
Qed.

Lemma Interweave_valid_r V (m1 m2 m3 : Map V) :
  Is_Valid_Map m3 ->
  Interweave m1 m2 m3 ->
  Is_Valid_Map m2.
Proof.
  intros Hvalid Hinter. apply Interweave_valid in Hinter as (?&?); auto.
Qed.

Lemma star_implies_mono_valid V (P : StateAssertion V) P' Q Q' :
  (forall c m, Is_Valid_Map m -> P c m -> P' c m) ->
  (forall c m, Is_Valid_Map m -> Q c m -> Q' c m) ->
  (forall c m, Is_Valid_Map m -> (P <*> Q) c m -> (P' <*> Q') c m).
Proof.
  unfold_all. intros. edestruct_direct.
  eauto 13 using Interweave_valid_l, Interweave_valid_r.
Qed.

Lemma star_implies_mono_post
  (V : Set) (P : V -> StateAssertion V) P' Q Q' :
  P -->> P' ->
  Q ->> Q' ->
  P <*>+ Q -->> P' <*>+ Q'.
Proof.
  intros. now apply star_implies_mono.
Qed.

Ltac split_all :=
  repeat match goal with
  | [|- exists _, _ ] => eexists
  | [|- _ /\ _ ] => split
  end.

Lemma star_pure_l (V : Set) P (Q : StateAssertion V) c m :
  (<[P]> <*> Q) c m <-> (P /\ Q c m).
Proof.
  unfold_all.
  split; intros; edestruct_direct; simpl; split_all; eauto using Interweave_nil_l.
  erewrite <- Interweave_nil_l_inv; eauto.
Qed.

Lemma star_exists_l A (V : Set) (P : A -> StateAssertion V) Q c m :
  ((<exists> x, P x) <*> Q) c m <-> exists x, (P x <*> Q) c m.
Proof.
  unfold_all. split; intros H; edestruct_direct; eauto 10.
Qed.

Lemma star_exists_l' V A P (Q : StateAssertion V) :
  (<exists> x : A, P x) <*> Q ->> <exists> x : A, P x <*> Q.
Proof.
  unfold sa_implies. intros. apply star_exists_l. assumption.
Qed.

Lemma star_exists_r A (V : Set) P (Q : A -> StateAssertion V) c m :
  (P <*> (<exists> x, Q x)) c m <-> exists x, (P <*> Q x) c m.
Proof.
  unfold_all; split; intros H; edestruct_direct; eauto 10.
Qed.

Lemma star_exists_r' V A (P : StateAssertion V) Q :
  (P <*> (<exists> x : A, Q x)) ->> <exists> x : A, (P <*> Q x).
Proof.
  unfold sa_implies. intros. apply star_exists_r. assumption.
Qed.

Lemma exists_implies A (V : Set) (P Q : A -> StateAssertion V) :
  (forall x, P x ->> Q x) ->
  (<exists> x, P x) ->> (<exists> x, Q x).
Proof.
  unfold_all. intros. edestruct_direct.
Qed.

Ltac edestruct_all_in n :=
  repeat match goal with
  | [ Hvalid : Is_Valid_Map ?m,
      p : ?P ?c ?m,
      H : forall _ _, Is_Valid_Map _ -> ?P _ _ -> exists _, _ |- _] =>
    destruct H with c m; eauto n; clear H; edestruct_direct
  | [ Hvalid : Is_Valid_Map ?m,
      p : (?P <*> ?Q) ?c ?m,
      H : forall _ _ _, Is_Valid_Map _ -> (?P <*> _) _ _ -> exists _, _ |- _] =>
    destruct H with Q c m; eauto n; clear H; edestruct_direct
  | [p : ?P ?c ?m, H : forall _ _, ?P _ _ -> exists _, _ |- _] =>
    destruct H with c m; eauto n; clear H; edestruct_direct
  | [p : (?P <*> ?Q) ?c ?m, H : forall _ _ _, (?P <*> _) _ _ -> exists _, _ |- _] =>
    destruct H with Q c m; eauto n; clear H; edestruct_direct
  | [ Hvalid : Is_Valid_Map ?m,
      H : forall _ _, Is_Valid_Map _ -> (exists _, _) -> exists _, _ |- _] =>
    edestruct H; eauto n; clear H; edestruct_direct
  | [ Hvalid : Is_Valid_Map ?m,
      H : forall _ _ _, Is_Valid_Map _ -> (exists _, _) -> exists _, _ |- _] =>
    edestruct H; eauto n; clear H; edestruct_direct
  | [H : forall _ _, (exists _, _) -> exists _, _ |- _] =>
    edestruct H; eauto n; clear H; edestruct_direct
  | [H : forall _ _ _, (exists _, _) -> exists _, _ |- _] =>
    edestruct H; eauto n; clear H; edestruct_direct
  | [ Hvalid : Is_Valid_Map ?m,
      q : ?Q ?v ?c ?m,
      H : forall _ _ _, Is_Valid_Map _ -> ?Q _ _ _ -> exists _, _ |- _] =>
    destruct H with v c m; eauto n; clear H; edestruct_direct
  | [ Hvalid : Is_Valid_Map ?m,
      q : (?Q ?v <*> ?R) ?c ?m,
      H : forall _ _ _ _, Is_Valid_Map _ -> (?Q _ <*> _) _ _ -> exists _, _ |- _] =>
    destruct H with v R c m; eauto n; clear H; edestruct_direct
  | [q : ?Q ?v ?c ?m, H : forall _ _ _, ?Q _ _ _ -> exists _, _ |- _] =>
    destruct H with v c m; eauto n; clear H; edestruct_direct
  | [q : (?Q ?v <*> ?R) ?c ?m, H : forall _ _ _ _, (?Q _ <*> _) _ _ -> exists _, _ |- _] =>
    destruct H with v R c m; eauto n; clear H; edestruct_direct
  end.

Ltac edestruct_all := edestruct_all_in integer:(5).

Ltac invert_Intwv_nil :=
  match goal with
  | [H : Interweave []%list _ _ |- _] => apply Interweave_nil_l_inv in H as ->
  | [H : Interweave []%list _ _ |- _] => apply Interweave_nil_l_inv in H as <-
  | [H : Interweave _ []%list _ |- _] => apply Interweave_nil_r_inv in H as ->
  | [H : Interweave _ []%list _ |- _] => apply Interweave_nil_r_inv in H as <-
  end.

Theorem htriple_of_triple (V : Set) (e : Expr V) P Q :
  triple e P Q ->
  hoare_triple e P Q.
Proof.
  unfold triple. intros Htriple. specialize Htriple with <[]>. revert Htriple.
  unfold_all. intros. edestruct_all_in integer:(5).
  { split_all; eauto using Interweave_nil_r. }
  invert_Intwv_nil.
  repeat eexists; eauto; try lia.
Qed.

Theorem htriple_weaken (V : Set) (e : Expr V) P P' Q Q' :
  P' ->> P ->
  (Q -->> Q') ->
  hoare_triple e P Q ->
  hoare_triple e P' Q'.
Proof.
  unfold hoare_triple, sa_implies. intros ? ? H. intros.
  edestruct H; eauto. edestruct_direct. eauto 10.
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

Theorem htriple_weaken_valid (V : Set) (e : Expr V) P P' Q Q' :
  (forall c m, Is_Valid_Map m -> P' c m -> P c m) ->
  (forall v c m, Is_Valid_Map m -> Q v c m -> Q' v c m) ->
  hoare_triple e P Q ->
  hoare_triple e P' Q'.
Proof.
  unfold hoare_triple, sa_implies. intros ? ? H. intros.
  edestruct H; eauto. edestruct_direct. eauto 10.
Qed.

Theorem triple_weaken_valid (V : Set) (e : Expr V) P P' Q Q' :
  (forall c m, Is_Valid_Map m -> P' c m -> P c m) ->
  (forall v c m, Is_Valid_Map m -> Q v c m -> Q' v c m) ->
  triple e P Q ->
  triple e P' Q'.
Proof.
  unfold triple. intros.
  eapply htriple_weaken_valid with (P <*> _) (Q <*>+ _);
    eauto 3 using star_implies_mono_valid.
Qed.

Theorem htriple_pure_post (V : Set) (e : Expr V) P Q :
  ((forall c m, Is_Valid_Map m -> P c m -> Q) /\
    hoare_triple e P (fun _ => <[]>)) <->
    hoare_triple e P (fun _ => <[Q]>).
Proof.
  unfold hoare_triple, sa_pure, sa_empty. split.
  - intros. edestruct_direct. edestruct_all. split_all; eauto.
  - intros. split; intros; edestruct_all. eauto 10.
Qed.

Ltac solve_assoc :=
  repeat eexists; eauto using List.app_assoc; rewrite List.map_app in *; intros;
    try match goal with
    | [H : List.In _ (_ ++ _)%list |- _] => apply List.in_app_or in H as [? | ?]
    end;
    eauto using List.in_or_app.

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
  destruct Interweave_assoc_r with (Label * option (Value V))%type x0 x4 x6 x2 m as (?&?&?);
    auto.
  repeat eexists; eauto; intros.
  { apply map_Interweave with (f := fst) in H4, H5, H6, H7.
    eapply in_or_Interweave in H4; eauto. }
  { lia. }
  { apply map_Interweave with (f := fst) in H4, H5, H6, H7.
    eapply in_or_Interweave in H4; eauto.
    eapply in_Interweave_or in H6 as [? | ?]; eauto.
  }
Qed.

Lemma star_assoc_r (V : Set) (P : StateAssertion V) Q R :
  (P <*> Q) <*> R ->> P <*> (Q <*> R).
Proof.
  unfold_all. intros. edestruct_direct.
  destruct Interweave_assoc_l with (Label * option (Value V))%type x4 x6 x2 x0 m as (?&?&?);
    auto.
  repeat eexists; eauto; intros.
  { apply map_Interweave with (f := fst) in H3, H5, H6, H7.
    eapply in_or_Interweave in H3; eauto. }
  { lia. }
  { apply map_Interweave with (f := fst) in H3, H5, H6, H7.
    eapply in_or_Interweave in H3; eauto.
    eapply in_Interweave_or in H6 as [? | ?]; eauto.
  }
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

Lemma star_comm (V : Set) (P : StateAssertion V) Q :
  P <*> Q ->> Q <*> P.
Proof.
  unfold_all. intros. edestruct_direct. split_all; eauto; try lia.
  apply Interweave_comm. assumption.
Qed.

Theorem htriple_pure (V : Set) (e : Expr V) P Q :
  (P -> hoare_triple e <[]> Q) <-> hoare_triple e <[P]> Q.
Proof.
  unfold hoare_triple, sa_pure, sa_empty.
  split; intros; edestruct_direct.
Qed.

Theorem triple_pure (V : Set) (e : Expr V) P Q :
  (P -> triple e <[]> Q) <-> triple e <[P]> Q.
Proof.
  unfold_all.
  split; intros Htriple; intros; edestruct_direct; edestruct Htriple; eauto;
    repeat eexists; eauto.
Qed.

Theorem htriple_pure_star (V : Set) (e : Expr V) P H Q :
  (P -> hoare_triple e H Q) <-> hoare_triple e (<[P]> <*> H) Q.
Proof.
  unfold hoare_triple, sa_pure, sa_star, sa_empty, disjoint_maps, labels.
  split; intros; edestruct_direct;
    try match goal with
    | [p : ?P, H : ?P -> _ |- _] => specialize (H p)
    end;
    repeat invert_Intwv_nil; simpl in *; edestruct_all.
  split_all; eauto. apply Interweave_nil_l.
Qed.

Theorem triple_pure_star (V : Set) (e : Expr V) P H Q :
  (P -> triple e H Q) <-> triple e (<[P]> <*> H) Q.
Proof.
  unfold_all.
  split; intros; edestruct_direct;
    try match goal with
    | [p : ?P, H : ?P -> _ |- _] => specialize (H p)
    end;
    repeat invert_Intwv_nil; simpl in *; edestruct_all;
    split_all; eauto. apply Interweave_nil_l.
Qed.

Theorem htriple_exists A (V : Set) (e : Expr V) P Q :
  (forall x : A, hoare_triple e (P x) Q) <->
    hoare_triple e (<exists> x, P x) Q.
Proof.
  unfold hoare_triple, sa_exists.
  split; intros; [edestruct_direct | edestruct_all].
Qed.

Theorem triple_exists A (V : Set) (e : Expr V) P Q :
  (forall x : A, triple e (P x) Q) <-> triple e (<exists> x, P x) Q.
Proof.
  unfold_all.
  split; intros Htriple; intros; edestruct_direct; edestruct Htriple; eauto;
    repeat eexists; eauto.
Qed.

Theorem htriple_exists_star A (V : Set) (e : Expr V) H P Q :
  (forall x : A, hoare_triple e (H <*> P x) Q) <->
    hoare_triple e (H <*> <exists> x, P x) Q.
Proof.
  unfold hoare_triple, sa_star, sa_exists, disjoint_maps, labels.
  split; intros; edestruct_direct; edestruct_all; split_all; eauto.
Qed.

Fact empty_spec (V : Set) c (m : Map V) :
  <[]> c m <-> c = 0 /\ m = []%list.
Proof.
  unfold_all. reflexivity.
Qed.

Fact pure_spec (V : Set) P c (m : Map V) :
  <[P]> c m <-> P /\ c = 0 /\ m = []%list.
Proof.
  unfold_all. reflexivity.
Qed.

Ltac normalize_star :=
  repeat match goal with
  | [H : <[]> ?c ?m |- _] => apply empty_spec in H as (?&?)
  | [H : <[_]> ?c ?m |- _] => apply pure_spec in H as (?&?&?)
  | [H : ((_ <*> _) <*> _) ?c ?m |- _] => apply star_assoc_r in H
  | [H : (<[_]> <*> _) ?c ?m |- _] => apply star_pure_l in H as [? ?]
  | [H : ((<exists> _, _) <*> _) ?c ?m |- _] => apply star_exists_l in H as [? ?]
  | [H : (<exists> _, _) ?c ?m |- _] => destruct H
  end.

Ltac solve_star :=
  repeat match goal with
  | [H : <[]> ?c ?m |- _] => apply empty_spec; eauto
  | [H : <[_]> ?c ?m |- _] => apply pure_spec; eauto
  | [|- ((_ <*> _) <*> _) ?c ?m ] => apply star_assoc_l; eauto
  | [|- (<[_]> <*> _) ?c ?m ] => apply star_pure_l; split; auto
  | [|- ((<exists> _, _) <*> _) ?c ?m ] => apply star_exists_l; eexists; eauto
  | [|- (<exists> _, _) ?c ?m] => eexists
  end.

Ltac swap_star :=
  match goal with
  | [|- (_ <*> _) ?c ?m] => apply star_comm
  end.

Ltac swap_star_ctx :=
  match goal with
  | [H : (_ <*> _) ?c ?m |- _] => apply star_comm in H
  end.

Theorem triple_exists_star A (V : Set) (e : Expr V) H P Q :
  (forall x : A, triple e (H <*> P x) Q) <->
    triple e (H <*> <exists> x, P x) Q.
Proof.
  unfold triple, hoare_triple.
  split; intros.
  - normalize_star. swap_star_ctx. normalize_star. swap_star_ctx.
    normalize_star. swap_star_ctx. edestruct H0; eauto.
  - edestruct H0; eauto. solve_star. swap_star. solve_star. swap_star.
    solve_star. swap_star. eassumption.
Qed.

Lemma star_credits (V : Set) (k : nat) (P : StateAssertion V) c m :
  (sa_credits k <*> P) c m <->
    exists c', c = k + c' /\ P c' m.
Proof.
  unfold_all. split; intros; edestruct_direct.
  - invert_Intwv_nil. eauto.
  - split_all; eauto using Interweave_nil_l.
Qed.

Fact implies_trans (V : Set) (P Q R : StateAssertion V) :
  P ->> Q ->
  Q ->> R ->
  P ->> R.
Proof.
  unfold_all. auto.
Qed.

Fact implies_spec (V : Set) (P Q : StateAssertion V) :
  (P ->> Q) <-> forall c m, P c m -> Q c m.
Proof.
  unfold_all. reflexivity.
Qed.

Fact implies_post_spec (V : Set) (P Q : Value V -> StateAssertion V) :
  (P -->> Q) <-> forall v c m, P v c m -> Q v c m.
Proof.
  unfold_all. reflexivity.
Qed.

Fact wand_star (V : Set) (P Q : StateAssertion V) :
  ((P <-*> Q) <*> P) ->> Q.
Proof.
  unfold sa_wand, sa_implies. intros. normalize_star. swap_star_ctx. auto.
Qed.

Fact wand_star_r (V : Set) (P Q : StateAssertion V) :
  (P <*> (P <-*> Q)) ->> Q.
Proof.
  eauto using star_comm, wand_star, implies_trans.
Qed.

Fact wand_wand (V : Set) (P Q R : StateAssertion V) :
  (P <-*> Q) <*> (Q <-*> R) ->> (P <-*> R).
Proof.
  unfold sa_wand, sa_implies. intros. normalize_star. swap_star_ctx.
  normalize_star. solve_star; eauto. intros ? ? H_sa.
  eapply star_implies_mono in H_sa; [|apply implies_refl|apply star_comm].
  apply star_assoc_l in H_sa.
  eapply star_implies_mono in H_sa; eauto using implies_refl.
Qed.

Fact wand_wand_r (V : Set) (P Q R : StateAssertion V) :
  (Q <-*> R) <*> (P <-*> Q) ->> (P <-*> R).
Proof.
  eauto using star_comm, wand_wand, implies_trans.
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

(** facts about StateAssertion *)

Fact credits_star_l (V : Set) c1 c2 c :
  c = c1 + c2 ->
  sa_credits c1 <*> sa_credits c2 ->> sa_credits (V := V) c.
Proof.
  unfold_all. intros. edestruct_direct. invert_Intwv_nil. auto.
Qed.

Fact credits_star_r (V : Set) c1 c2 c :
  c = c1 + c2 ->
  sa_credits (V := V) c ->> sa_credits c1 <*> sa_credits c2.
Proof.
  unfold_all. intros. edestruct_direct. split_all; auto using Interweave_nil.
Qed.

Fact empty_star_l_intro (V : Set) (P : StateAssertion V) :
  P ->> <[]> <*> P.
Proof.
  unfold_all. intros. split_all; eauto using Interweave_nil_l.
Qed.

Fact empty_star_r_intro (V : Set) (P : StateAssertion V) :
  P ->> P <*> <[]>.
Proof.
  unfold_all. intros. split_all; eauto using Interweave_nil_r.
Qed.

Fact empty_star_l_cancel (V : Set) (P : StateAssertion V) :
  <[]> <*> P ->> P.
Proof.
  unfold_all. intros. edestruct_direct. invert_Intwv_nil. auto.
Qed.

Fact empty_star_r_cancel (V : Set) (P : StateAssertion V) :
  P <*> <[]> ->> P.
Proof.
  unfold_all. intros. edestruct_direct. rewrite Nat.add_0_r.
  invert_Intwv_nil. auto.
Qed.

Fact disjoint_maps_nil_l V m :
  @disjoint_maps V nil m.
Proof.
  unfold disjoint_maps. simpl. auto.
Qed.

Fact disjoint_maps_nil_r V m :
  @disjoint_maps V m nil.
Proof.
  unfold disjoint_maps. simpl. auto.
Qed.

Fact equiv_sa_equiv V (P Q : StateAssertion V) :
  P <<->> Q <-> forall c m, P c m <-> Q c m.
Proof.
  unfold sa_implies. split.
  - intuition.
  - intros Hequiv. split; intros; apply Hequiv; assumption.
Qed.

Lemma star_equiv_l V (P P' Q : StateAssertion V) :
  P <<->> P' ->
  (P <*> Q) <<->> (P' <*> Q).
Proof.
  repeat rewrite -> equiv_sa_equiv. intros Hequiv ? ?.
  split; now (apply star_implies_mono; unfold sa_implies; intros;
    [apply Hequiv|apply implies_refl]).
Qed.

Lemma star_equiv_r V (P Q Q' : StateAssertion V) :
  Q <<->> Q' ->
  (P <*> Q) <<->> (P <*> Q').
Proof.
  repeat rewrite -> equiv_sa_equiv. intros Hequiv ? ?.
  split; now (apply star_implies_mono; unfold sa_implies; intros;
    [apply implies_refl|apply Hequiv]).
Qed.

Lemma exists_equiv A P P' :
  (forall x : A, P x <-> P' x) ->
  (exists x, P x) <-> (exists x, P' x).
Proof.
  intros Hequiv. split; intros (?&?%Hequiv); eauto.
Qed.

Lemma sa_exists_equiv A V (P P' : A -> StateAssertion V) :
  (forall x, P x <<->> P' x) ->
  (<exists> x, P x) <<->> (<exists> x, P' x).
Proof.
  intros Hequiv. apply equiv_sa_equiv. intros. unfold sa_exists.
  apply exists_equiv. intros. apply equiv_sa_equiv. auto.
Qed.

Lemma star_exists_equiv_l A V (P : A -> StateAssertion V) Q :
  (<exists> x, P x) <*> Q <<->> (<exists> x, P x <*> Q).
Proof.
  rewrite equiv_sa_equiv. intros. apply star_exists_l.
Qed.

Lemma empty_star_l V (P : StateAssertion V) :
  <[]> <*> P <<->> P.
Proof.
  apply equiv_sa_equiv. intros.
  split; [apply empty_star_l_cancel|apply empty_star_l_intro].
Qed.

Lemma empty_star_r V (P : StateAssertion V) :
  P <*> <[]> <<->> P.
Proof.
  apply equiv_sa_equiv. intros.
  split; [apply empty_star_r_cancel|apply empty_star_r_intro].
Qed.

Fact sa_equiv_symm V (P Q : StateAssertion V) :
  P <<->> Q ->
  Q <<->> P.
Proof.
  repeat rewrite equiv_sa_equiv. intros. symmetry. eauto.
Qed.

Fact sa_equiv_trans V (P Q R : StateAssertion V) :
  P <<->> Q ->
  Q <<->> R ->
  P <<->> R.
Proof.
  repeat rewrite equiv_sa_equiv. intros. etransitivity; eauto.
Qed.

Lemma length_n_new_cells V l n :
  List.length (@n_new_cells_from V l n) = n.
Proof.
  destruct l as [k]. revert k. induction n; simpl; auto.
Qed.

Lemma NoDup_insert A (x : A) (l1 l2 : list A) :
  ~ List.In x (l1 ++ l2) ->
  List.NoDup (l1 ++ l2) ->
  List.NoDup (l1 ++ x::l2).
Proof.
  induction l1; simpl; intros Hnin Hnodup.
  - auto using List.NoDup.
  - inversion Hnodup. unfold not in *. constructor.
    + unfold not. intros [-> | Hin]%List.in_elt_inv; auto.
    + auto.
Qed.

Lemma array_content_label_le V A n n' c m :
  @array_content V A (Lab (OfNat n)) c m ->
  List.In (OfNat n') (labels m) ->
  n <= n'.
Proof.
  unfold labels. intros Harray. remember (Lab (OfNat n)) as l eqn:Hl.
  generalize dependent n. induction Harray; simpl.
  - contradiction.
  - intros ? [=->] **.
    match goal with
    | [Hinter : Interweave [_] _ _, Hin : List.In _ _ |- _ ] =>
      apply Interweave_single_l in Hinter as (?&?&->&->);
      simpl in *; rewrite List.map_app in Hin; simpl in Hin;
      apply List.in_elt_inv in Hin as [[=->] | Hin']
    end.
    + constructor.
    + rewrite <- List.map_app in Hin'. apply Le.le_Sn_le_stt.
      apply IHHarray; auto.
Qed.

Lemma valid_array_content V A v c m :
  @array_content V A v c m -> Is_Valid_Map m.
Proof.
  unfold Is_Valid_Map, labels. intros Harray. induction Harray; simpl.
  - constructor.
  - match goal with
    | [H : Interweave [_] _ _ |- _ ] =>
      apply Interweave_single_l in H as (?&?&->&->)
    end.
    rewrite List.map_app in *. simpl. apply NoDup_insert; auto. intros Hin.
    eapply Nat.nle_succ_diag_l. eapply array_content_label_le; [eassumption|].
    unfold labels. rewrite List.map_app. assumption.
Qed.

Lemma array_decl_empty_content V n l c m :
  <(l :\ n \= )> c m -> @array_content V (List.repeat None n) (Lab l) c m.
Proof.
  unfold sa_array_decl.
  destruct l as [nl]. intros (->&->). revert nl.
  induction n; intros; simpl; econstructor; auto.
  constructor. apply Interweave_nil_l.
Qed.

Lemma array_content_nil V v c m :
  @array_content V nil v c m <-> (<exists> l, <[v = Lab l]>) c m.
Proof.
  unfold sa_exists, sa_pure, sa_empty.
  split.
  - intros Harray. inversion Harray. eauto.
  - intros (?&->&->&->). constructor.
Qed.

Lemma array_content_cons V x A v c m :
  @array_content V (x::A) v c m <->
    (<exists> n, <[v = Lab (OfNat n)]> <*> <(OfNat n :?= x)> <*>
     array_content A (Lab (OfNat (S n)))) c m.
Proof.
  unfold sa_exists, sa_single_any, sa_star, sa_pure, sa_empty.
  split.
  - intros Harray. inversion Harray. subst. do 5 eexists.
    repeat split; eauto 15 using disjoint_maps_nil_l, Interweave_nil_l.
    unfold disjoint_maps. simpl.
    eintros ? [<-|[]] ?%array_content_label_le; eauto. lia.
  - intros
      (?&?&?&?&?&
        (?&?&?&?&(->&->&->)&(->&->)&->&?&<-%Interweave_nil_l_inv)&
        ?&->&?&?).
    simpl. econstructor; eauto.
Qed.

Lemma array_content_app V A A' n c m :
  @array_content V (A ++ A') (Lab (OfNat n)) c m <->
    (array_content A (Lab (OfNat n)) <*>
     array_content A' (Lab (OfNat (n + List.length A)))) c m.
Proof.
  revert n c m. induction A; intros n; simpl.
  - rewrite Nat.add_0_r. apply equiv_sa_equiv. eapply sa_equiv_trans.
    + apply sa_equiv_symm, empty_star_l.
    + apply star_equiv_l, sa_equiv_symm.
      eapply sa_equiv_trans; apply equiv_sa_equiv.
      * apply array_content_nil.
      * unfold sa_empty. split.
        -- intros. normalize_star. subst. auto.
        -- intros (->&->). solve_star. rewrite pure_spec. eauto.
  - rewrite Nat.add_succ_r. intros. rewrite array_content_cons.
    apply equiv_sa_equiv. eapply sa_equiv_symm, sa_equiv_trans.
    + eapply star_equiv_l, equiv_sa_equiv, array_content_cons.
    + eapply sa_equiv_trans.
      * apply star_exists_equiv_l.
      * apply sa_exists_equiv. intros. eapply sa_equiv_trans.
        -- apply sa_equiv_symm, star_assoc.
        -- eapply sa_equiv_symm, sa_equiv_trans.
          ++ apply star_equiv_r, equiv_sa_equiv. intros. apply IHA.
          ++ simpl. apply equiv_sa_equiv. intros.
            split; intros; normalize_star;
            match goal with
            | [H : ?f _ = ?f _ |- _] => injection H as ->
            end;
            solve_star.
Qed.

Fact single_single_any (V : Set) l (v : Value V) :
  sa_single l v <<->> sa_single_any l (Some v).
Proof.
  unfold_all. auto.
Qed.

Fact single_single_any_l (V : Set) l (v : Value V) :
  sa_single_any l (Some v) ->> sa_single l v.
Proof.
  apply single_single_any.
Qed.

Fact single_single_any_r (V : Set) l (v : Value V) :
  sa_single l v ->> sa_single_any l (Some v).
Proof.
  apply single_single_any.
Qed.

Ltac solve_simple_triple n :=
  unfold_all; intros; edestruct_direct; eauto n using Interweave_nil_l with lamref.
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
  eauto 20 using Interweave_nil_l with lamref.
Qed.

Theorem triple_value' (V : Set) (v : Value V) (P : StateAssertion V) :
  triple v P (fun v' => <[v' = v]> <*> P).
Proof.
  solve_simple_triple_30.
Qed.

Theorem triple_value_implies (V : Set) (v : Value V) (P : StateAssertion V) Q :
  P ->> Q v ->
  triple v P Q.
Proof.
  intros H. eapply triple_weaken, triple_frame, triple_value.
  - apply empty_star_l_intro.
  - apply implies_post_spec. intros. normalize_star. subst. apply H.
    assumption.
Qed.

Theorem htriple_value_untimed (V : Set) (v : Value V) (P : StateAssertion V) :
  hoare_triple v P (fun _ => P).
Proof.
  eapply htriple_weaken; eauto using htriple_value';
    unfold sa_implies, sa_star, sa_pure, sa_empty;
    [| intros v' c m (c1&m1&c2&m2&(?&?&?)&?&?&?&?); subst ]; simpl;
    eauto.
  invert_Intwv_nil. assumption.
Qed.

Theorem triple_value_untimed (V : Set) (v : Value V) (P : StateAssertion V) :
  triple v P (fun _ => P).
Proof.
  eapply triple_weaken; eauto using triple_value';
    unfold sa_implies, sa_star, sa_pure, sa_empty;
    [| intros v' c m (c1&m1&c2&m2&(?&?&?)&?&?&?&?); subst ];
    eauto.
  invert_Intwv_nil. assumption.
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
  invert_Intwv_nil. rewrite Nat.add_1_r in *. injection_on_all S.
  destruct H; edestruct_direct; subst; eauto 10 with lamref.
Qed.

Theorem triple_lam (V : Set) (e : Expr _) (v : Value V) P Q :
  triple (subst_e e v) P Q ->
  triple ((-\e) <* v) (P <*> sa_credits 1) Q.
Proof.
  unfold_all. intros. destruct c1.
  { edestruct_direct. lia. }
  specialize (H H0 c1 m). edestruct_direct.
  invert_Intwv_nil. rewrite Nat.add_1_r in *. simpl in *. injection_on_all S.
  destruct H; edestruct_direct; subst; eauto 10 with lamref.
  repeat eexists; eauto_lr. lia.
Qed.

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
  invert_Intwv_nil;
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
  | [ Hp : ?P ?cp ?mp,
      Hq : ?Q ?cq ?mq,
      Hdis : disjoint_maps ?mp ?mq,
      Hiw : Interweave ?mp ?mq ?mpq |- _] =>
    assert ((P <*> Q) (cp + cq) mpq); [eauto 10 with st_assertions|]
  end.

Ltac fold_star_with P :=
  match goal with
  | [ Hp : P ?cp ?mp,
      Hq : ?Q ?cq ?mq,
      Hdis : disjoint_maps ?mp ?mq,
      Hiw : Interweave ?mp ?mq ?mpq |- _] =>
    assert ((P <*> Q) (cp + cq) mpq); [eauto 10 with st_assertions|]
  end.

Ltac solve_triple n H :=
  unfold triple, hoare_triple;
  intros;
  normalize_star;
  make_cred_positive;
  edestruct_direct;
  simpl in *;
  injection_on_all S; subst; fold_star;
  invert_Intwv_nil;
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
  edestruct_direct. invert_Intwv_nil. simpl in *. injection_on_all S.
  subst_with c1. intros. subst_with m. clear_trivial.
  assert (exists cs ms c2 m',
    Is_Valid_Map m' /\
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
    as (cs&ms&c2&m'&?&?&?&?&?&?&?&?&?).
  { generalize dependent c1. generalize dependent m.
    generalize dependent P. generalize dependent Ps.
    generalize dependent vs. generalize dependent es.
    induction n as [|n IHn]; intros; unfold last_error in *; match_lists_for_lengths;
      injection_on_all_Some; subst.
    - exists [c1]%list, [m]%list. split_all; simpl; eauto.
      intros. inversion_Nth_cons_succ. inversion_Nth_nil.
    - match goal with
      | [H :
          forall _ _ _ _ _,
          Nth _ _ _ ->
          Nth _ _ _ ->
          Nth _ _ _ ->
          Nth _ _ _ ->
          forall _ _,
          _ ->
          _ ->
          exists _ _ _ _, _ /\ _ /\ _ |- _] =>
        edestruct H with (i := 0) as (v'&c'&c2&m'&?&?&?&?); eauto_lr
      end.
      normalize_star. subst. (* fold (List.last_error (s0::Ps)%list) in H6. *)
      match goal with
      | [sa : StateAssertion V |- _] =>
        edestruct IHn with (Ps := (sa::Ps)%list) as (cs&ms&c2'&m''&?&?&?&?&?&?&?&?&?);
          simpl; eauto 10 using Interweave_nil_l with lamref
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
    unfold monotone. intros. edestruct H15 with (i := i) as (?&?&?); eauto.
    lia. }
  split_all; solve_star; simpl; eauto using big_red_rec_diff.
  lia.
Qed.

Ltac find_star_and_unfold_all :=
  match goal with
  | [H : (_ <*> _) _ _ |- _] => unfold_all_in H
  end.

Ltac fold_disjoint_maps :=
  match goal with
  | [H :
    forall _,
      List.In _ (List.map _ ?m1) ->
      List.In _ (List.map _ ?m2) -> False |- _] =>
    fold (labels m1) in H; fold (labels m2) in H; fold (disjoint_maps m1 m2) in H
  end.

Theorem triple_rec (V : Set) (es : list (Expr V)) (vs : list (Value V))
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
    triple e
      P
      (fun v' => <[v' = v]> <*> Q)) ->
  triple (RecE es)
    (sa_credits 1 <*> P)
    (fun v => <[v = RecV vs]> <*> Q).
Proof.
  unfold triple, hoare_triple.
  intros. remember m as m0. revert_all_eq. normalize_star. make_cred_positive.
  edestruct_direct. invert_Intwv_nil. simpl in *. injection_on_all S. intros.
  clear_trivial. fold_star.
  rewrite_with_and_clear c1. rewrite_with_and_clear m.
  clear H1 H0 H3 H7 x3 x4 x5 x6.
  assert (exists cs ms c2 m',
    Is_Valid_Map m' /\
    1+n = List.length cs /\
    1+n = List.length ms /\
    Some c1 = List.head cs /\
    Some c2 = last_error cs /\
    Some m = List.head ms /\
    Some m' = last_error ms /\
    (Q <*> H5) c2 m' /\
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
    as (cs&ms&c2&m'&?&?&?&?&?&?&?&?&?).
  { generalize dependent c1. generalize dependent m.
    generalize dependent P. generalize dependent Ps.
    generalize dependent vs. generalize dependent es.
    induction n as [|n IHn]; intros; normalize_star; unfold last_error in *;
      match_lists_for_lengths; injection_on_all_Some; subst.
    - eexists [c1]%list, [m]%list. split_all; simpl; eauto. intros.
      inversion_Nth_cons_succ. inversion_Nth_nil.
    - match goal with
      | [H :
          forall _ _ _ _ _,
          Nth _ _ _ ->
          Nth _ _ _ ->
          Nth _ _ _ ->
          Nth _ _ _ ->
          forall _ _ _,
          _ ->
          _ ->
          exists _ _ _ _, _ /\ _ /\ _ |- _] =>
        edestruct H with (i := 0) as (v'&c'&c2&m'&?&?&?&?); eauto_lr
      end.
      normalize_star. find_star_and_unfold_all. edestruct_direct.
      fold_disjoint_maps. fold_star_with s0. subst.
      match goal with
      | [sa : StateAssertion V |- _] =>
        edestruct IHn with (Ps := (sa::Ps)%list) as (cs&ms&c2'&m''&?&?&?&?&?&?&?&?&?);
          simpl; eauto 10 with lamref
      end.
      match_lists_for_lengths.
      simpl in *. injection_on_all_Some. rewrite_with_and_clear n.
      match goal with
      | [_ : cost_red _ _ _ ?mm ?cc |- _] =>
        exists (cc+n::n::cs)%list, (m::mm::ms)%list
      end.
      subst. split_all; simpl in *; eauto 3. intros.
      inversion_Nth_cons_succ.
      match goal with
      | [_ : cost_red _ _ _ _ ?cc |- _] => inversion_Nth_cons_2 (cc+n) n
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
    unfold monotone. intros. edestruct H16 with (i := i) as (?&?&?); eauto.
    lia. }
  split_all; solve_star; simpl; eauto using big_red_rec_diff.
  lia.
Qed.

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

Lemma valid_map_Interweave (V : Set) (m1 m2 m3 : Map V) :
  Is_Valid_Map m1 ->
  Is_Valid_Map m2 ->
  disjoint_maps m1 m2 ->
  Interweave m1 m2 m3 ->
  Is_Valid_Map m3.
Proof.
  unfold Is_Valid_Map, disjoint_maps, labels.
  intros Hvalid1 Hvalid2 Hdisjoint Hinter.
  induction Hinter; simpl in *; constructor;
    match goal with
    | [H : List.NoDup (_ :: _) |- _] => inversion H
    end;
    eauto; intro; unfold not in *;
    match goal with
    | [Hin : List.In (?g _) _ |- _] =>
      eapply in_Interweave_or in Hin as [? | ?];
      try (apply map_Interweave with (f := g); eassumption)
    end;
    eauto.
Qed.

Lemma valid_map_app (V : Set) (m1 m2 : Map V) :
  Is_Valid_Map m1 ->
  Is_Valid_Map m2 ->
  disjoint_maps m1 m2 ->
  Is_Valid_Map (m1 ++ m2)%list.
Proof.
  eauto using valid_map_Interweave, Interweave_app.
Qed.

Lemma n_new_cells_from_mono (V : Set) n k n' :
  List.In (OfNat n') (labels (n_new_cells_from (V := V) (OfNat n) k)) ->
  n <= n'.
Proof.
  unfold labels. revert n. induction k; intros n []; subst; simpl in *.
  - injection H. lia.
  - eauto using le_S_n, le_S, IHk.
Qed.

Lemma valid_n_new_cells_from (V : Set) l k :
  Is_Valid_Map (n_new_cells_from (V := V) l k).
Proof.
  unfold Is_Valid_Map. destruct l as [n]. revert n.
  induction k; simpl; constructor; auto.
  intros Hin. apply n_new_cells_from_mono in Hin. lia.
Qed.

Lemma disjoint_maps_n_new_cells_from (V : Set) n (m : Map V) :
  disjoint_maps (n_new_cells_from (new_label m) n) m.
Proof.
  unfold disjoint_maps, new_label. intros [n'] Hin_new Hin_m1.
  apply n_new_cells_from_mono in Hin_new. pose proof max_list_max.
  eapply List.Forall_forall in H; eauto using (List.in_map of_label).
  simpl in *. lia.
Qed.

Lemma valid_map_alloc_array (V : Set) n l (m1 m2 : Map V) :
  Is_Valid_Map m1 ->
  (m2,l) = alloc_array n m1 ->
  Is_Valid_Map m2.
Proof.
  unfold alloc_array. intros Hvalid Halloc. injection Halloc as -> _.
  apply valid_map_app;
    auto using valid_n_new_cells_from, disjoint_maps_n_new_cells_from.
Qed.

Lemma labels_Assignment (V : Set) l v (m1 m2 : Map V) :
  Assignment l v m1 m2 ->
  labels m1 = labels m2.
Proof.
  unfold labels. intros Hassign. induction Hassign; simpl; f_equal.
  assumption.
Qed.

Lemma valid_map_Assignment_is_valid (V : Set) l v (m1 m2 : Map V) :
  Is_Valid_Map m1 ->
  Assignment l v m1 m2 ->
  Is_Valid_Map m2.
Proof.
  unfold Is_Valid_Map. intros Hvalid Hassign.
  erewrite <- labels_Assignment; eauto.
Qed.

Lemma labels_Dealloc (V : Set) l (m1 m2 : Map V) :
  Dealloc l m1 m2 ->
  List.incl (labels m2) (labels m1).
Proof.
  unfold List.incl, labels. intros Hdealloc.
  induction Hdealloc; simpl; intros l' Hin; auto. destruct Hin; auto.
Qed.

Lemma valid_map_Dealloc (V : Set) l (m1 m2 : Map V) :
  Is_Valid_Map m1 ->
  Dealloc l m1 m2 ->
  Is_Valid_Map m2.
Proof.
  unfold Is_Valid_Map. intros Hvalid Hdealloc.
  induction Hdealloc; simpl in *; inversion Hvalid; auto.
  constructor; auto. unfold not in *. pose proof labels_Dealloc.
  unfold List.incl in *. eauto.
Qed.

Lemma valid_map_cost_red (V : Set) e (v : Value V) m1 m2 c :
  Is_Valid_Map m1 ->
  C[e,m1 ~~> v,m2|c] ->
  Is_Valid_Map m2.
Proof.
  intros Hvalid Hred. induction Hred; auto.
  apply IHHred. clear Hred IHHred.
  induction H; subst;
    eauto 2 using
      Is_Valid_Map_cons_new,
      valid_map_alloc_array,
      valid_map_Assignment_is_valid,
      valid_map_Dealloc.
Qed.

Theorem htriple_ref (V : Set) (e : Expr V) P Q :
  hoare_triple e P Q ->
  hoare_triple (Ref e)
    (sa_credits 1 <*> P)
    (fun v' => <exists> l v, <[v' = Lab l]> <*> <( l :== v )> <*> Q v).
Proof.
  pose proof new_label_is_fresh. unfold Is_fresh_label, not in *.
  unfold_all. intros. edestruct_direct. invert_Intwv_nil. edestruct_all.
  simpl in *.
  split_all; try (eapply big_red_ref; eauto); simpl;
    eauto using Interweave_cons_l, Interweave_nil_l, Is_Valid_Map_cons_new.
  intros ? [? | []] ?. subst. eauto.
Qed.

Theorem triple_ref (V : Set) (e : Expr V) P Q :
  triple e P Q ->
  triple (Ref e)
    (sa_credits 1 <*> P)
    (fun v' => <exists> l v, <[v' = Lab l]> <*> <( l :== v )> <*> Q v).
Proof.
  pose proof new_label_is_fresh. unfold Is_fresh_label, not in *.
  unfold triple, hoare_triple. intros. normalize_star. make_cred_positive.
  edestruct_direct. invert_Intwv_nil. simpl in *. injection_on_all S.
  fold_star. edestruct_all. normalize_star. subst.
  split_all; try (eapply big_red_ref; eauto); simpl;
    eauto using Is_Valid_Map_cons_new.
  solve_star. unfold sa_star in *. edestruct_direct.
  split_all;
    eauto using Interweave_cons_l, Interweave_nil_l with st_assertions.
  intros ? [? | []] ?. subst. eauto.
Qed.

Theorem htriple_new_array (V : Set) (e : Expr V) P Q :
  hoare_triple e
    P
    (fun v => <exists> i, <[v = Int i]> <*> <[(i >= 0)%Z]> <*> Q i) ->
  hoare_triple (NewArray e)
    (sa_credits 1 <*> P)
    (fun v =>
      <exists> i l, <[v = Lab l]> <*> sa_array_decl l (Z.to_nat i) <*> Q i).
Proof.
  unfold hoare_triple. intros. make_cred_positive. edestruct_direct.
  invert_Intwv_nil. edestruct_all. normalize_star. subst. split_all.
  - eapply big_red_new_array; eauto. unfold alloc_array. auto.
  - solve_star. unfold sa_star, sa_array_decl.
    split_all; eauto using Interweave_app, disjoint_maps_n_new_cells_from.
  - eapply valid_map_alloc_array in H5; unfold alloc_array; eauto.
  - assumption.
Qed.

Theorem htriple_new_array_content (V : Set) (e : Expr V) P Q :
  hoare_triple e
    P
    (fun v => <exists> i, <[v = Int i]> <*> <[(i >= 0)%Z]> <*> Q i) ->
  hoare_triple (NewArray e)
    (sa_credits 1 <*> P)
    (fun v =>
      <exists> i, array_content (List.repeat None (Z.to_nat i)) v <*> Q i).
Proof.
  intros. eapply htriple_weaken, htriple_new_array; eauto using implies_refl.
  apply implies_post_spec. intros. normalize_star. subst. solve_star.
  eapply star_implies_mono; try eassumption.
  { apply implies_spec, array_decl_empty_content. }
  { apply implies_refl. }
Qed.

Theorem triple_new_array (V : Set) (e : Expr V) P Q :
  triple e
    P
    (fun v => <exists> i, <[v = Int i]> <*> <[(i >= 0)%Z]> <*> Q i) ->
  triple (NewArray e)
    (sa_credits 1 <*> P)
    (fun v =>
      <exists> i l, <[v = Lab l]> <*> sa_array_decl l (Z.to_nat i) <*> Q i).
Proof.
  unfold triple, hoare_triple. intros. normalize_star. make_cred_positive.
  edestruct_direct. invert_Intwv_nil. fold_star. edestruct_all. normalize_star.
  subst. unfold sa_star in H13. edestruct_direct. split_all.
  - eapply big_red_new_array; eauto. unfold alloc_array. auto.
  - solve_star. unfold sa_star, sa_array_decl.
    split_all; eauto using Interweave_app, disjoint_maps_n_new_cells_from.
  - eapply valid_map_alloc_array in H10; unfold alloc_array; eauto.
  - lia.
Qed.

Theorem triple_new_array_content (V : Set) (e : Expr V) P Q :
  triple e
    P
    (fun v => <exists> i, <[v = Int i]> <*> <[(i >= 0)%Z]> <*> Q i) ->
  triple (NewArray e)
    (sa_credits 1 <*> P)
    (fun v =>
      <exists> i, array_content (List.repeat None (Z.to_nat i)) v <*> Q i).
Proof.
  intros. eapply triple_weaken, triple_new_array; eauto using implies_refl.
  apply implies_post_spec. intros. normalize_star. subst. solve_star.
  eapply star_implies_mono; try eassumption.
  { apply implies_spec, array_decl_empty_content. }
  { apply implies_refl. }
Qed.

Lemma valid_map_Lookup (V : Set) l v (m : Map V) :
  List.In (l, Some v) m ->
  Lookup l m v.
Proof.
  unfold Is_Valid_Map. unfold_all. revert l v. induction m; simpl; intros.
  - contradiction.
  - destruct H as [-> | ?]; eauto_lr.
Qed.

Theorem htriple_deref (V : Set) (e : Expr V) (v : Value V) l P Q :
  hoare_triple e
    (<(l :== v)> <*> P)
    (fun v' => <[v' = Lab l]> <*> <(l :== v)> <*> Q) ->
  hoare_triple (Deref e)
    (sa_credits 1 <*> <(l :== v)> <*> P)
    (fun v' => <[v' = v']> <*> <(l :== v)> <*> Q).
Proof.
  unfold hoare_triple. intros. normalize_star. make_cred_positive.
  edestruct_direct. fold_star. repeat invert_Intwv_nil. edestruct_all.
  simpl in *. injection_on_all S. normalize_star. subst.
  split_all; try eapply big_red_deref; simpl in *;
    eauto using valid_map_Lookup with lamref; solve_star.
  unfold_all_in H10. edestruct_direct.
  eapply valid_map_Lookup, in_or_Interweave; eauto. simpl. auto.
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
  edestruct_direct. fold_star. fold_star. conormalize_star.
  repeat invert_Intwv_nil. edestruct_all. simpl in *. injection_on_all S.
  normalize_star. subst.
  split_all; solve_star; try eapply big_red_deref; simpl in *;
    eauto using valid_map_Lookup with lamref.
  unfold_all_in H15. edestruct_direct.
  eapply valid_map_Lookup, in_or_Interweave; eauto. simpl. auto.
Qed.

Theorem htriple_shift (V : Set) (e1 e2 : Expr V) P Q1 Q2 :
  hoare_triple e1
    P
    (fun v => <exists> n, <[v = Lab (OfNat n)]> <*> Q1 n) ->
  (forall n, hoare_triple e2
    (Q1 n)
    (fun v => <exists> i, <[v = Int i]> <*> <[(i >= 0)%Z]> <*> Q2 n i)) ->
  hoare_triple (Shift e1 e2)
    (sa_credits 1 <*> P)
    (fun v => <exists> n i, <[v = Lab (OfNat (n + Z.to_nat i))]> <*> Q2 n i).
Proof.
  solve_htriple_15 big_red_shift.
Qed.

Theorem triple_shift (V : Set) (e1 e2 : Expr V) P Q1 Q2 :
  triple e1
    P
    (fun v => <exists> n, <[v = Lab (OfNat n)]> <*> Q1 n) ->
  (forall n, triple e2
    (Q1 n)
    (fun v => <exists> i, <[v = Int i]> <*> <[(i >= 0)%Z]> <*> Q2 n i)) ->
  triple (Shift e1 e2)
    (sa_credits 1 <*> P)
    (fun v => <exists> n i, <[v = Lab (OfNat (n + Z.to_nat i))]> <*> Q2 n i).
Proof.
  solve_triple_15 big_red_shift.
Qed.

Lemma valid_map_Assignment (V : Set) l v v' (m : Map V) :
  List.In (l,v) m ->
  Assignment l v' m (update l v' m).
Proof.
  unfold Is_Valid_Map. unfold_all. revert l v. induction m; simpl; intros.
  - contradiction.
  - destruct l as (n). destruct H as [-> | ?].
    + unfold_all_lab. rewrite Nat.eqb_refl. constructor.
    + destruct a as ((n')&?). unfold_all_lab. destruct Nat.eqb_spec with n n'.
      * subst. constructor.
      * eauto_lr.
Qed.

Lemma Interweave_update_l (V : Set) l v v' (m1 m2 m : Map V) :
  List.In (l,v) m1 ->
  (forall v'', ~ List.In (l,v'') m2) ->
  Interweave m1 m2 m ->
  Interweave (update l v' m1) m2 (update l v' m).
Proof.
  unfold not. intros Hin Hnin Hinter. induction Hinter; simpl in *.
  - contradiction.
  - destruct l as (n). destruct Hin.
    + subst. unfold_all_lab. rewrite Nat.eqb_refl. constructor. assumption.
    + destruct x as ((n')&?). unfold_all_lab. destruct Nat.eqb.
      * constructor. assumption.
      * constructor. auto.
  - destruct l as (n), y as ((n')&?). unfold_all_lab.
    destruct Nat.eqb_spec with n n'.
      * subst. exfalso. eauto.
      * constructor. eauto.
Qed.

Lemma labels_update (V : Set) l v' (m : Map V) :
  List.In l (labels m) ->
  labels (update l v' m) = labels m.
Proof.
  unfold labels. intros Hin. induction m; simpl in *.
  - contradiction.
  - destruct l as (n), a as ((n')&?); simpl in *.
    destruct Hin as [-> | ?]; unfold_all_lab.
    + rewrite Nat.eqb_refl. simpl. reflexivity.
    + destruct Nat.eqb_spec with n n'; simpl.
      * subst. reflexivity.
      * f_equal. auto.
Qed.

Lemma valid_map_update (V : Set) l v' (m : Map V) :
  List.In l (labels m) ->
  Is_Valid_Map m ->
  Is_Valid_Map (update l v' m).
Proof.
  unfold Is_Valid_Map. intros Hin Hvalid. remember (labels m) as ls eqn:Hls.
  generalize dependent m.
  induction Hvalid; intros; destruct m; cbn in *; try discriminate.
  - repeat constructor; simpl; auto.
  - destruct l as (n), p as ((n')&?). simpl in *. unfold_all_lab.
    injection Hls as -> ->. destruct Nat.eqb_spec with n n'; simpl.
    + constructor; auto.
    + unfold labels in *. unfold not in *.
      destruct Hin as [Hin | Hin]; [injection Hin as ->; exfalso; auto|].
      constructor; auto. fold (labels (update (OfNat n) v' m)).
      rewrite labels_update; unfold labels; auto.
Qed.

Theorem htriple_assign (V : Set) (e1 e2 : Expr V) (v : option (Value V)) l P1 P2 Q2 :
  hoare_triple e1
    (<(l :?= v)> <*> P1)
    (fun v'' => <[v'' = Lab l]> <*> <(l :?= v)> <*> P2) ->
  hoare_triple e2
    (<(l :?= v)> <*> P2)
    (fun v' => <(l :?= v)> <*> Q2 v') ->
  hoare_triple (Assign e1 e2)
    (sa_credits 1 <*> <(l :?= v)> <*> P1)
    (fun v'' => <[v'' = U_val]> <*> <exists> v', <(l :== v')> <*> Q2 v').
Proof.
  unfold hoare_triple. intros. normalize_star. make_cred_positive.
  edestruct_direct. fold_star. repeat invert_Intwv_nil.
  edestruct_all. normalize_star. edestruct_all_in integer:(10).
  normalize_star. subst. find_star_and_unfold_all. edestruct_direct.
  eapply in_or_Interweave in H16 as ?; simpl; auto.
  eapply valid_map_update in H14 as ?.
  2:{ eauto using List.in_map. }
  split_all; solve_star; [eapply big_red_assign| | |]; eauto using valid_map_Assignment.
  { unfold_all. split_all; eauto; simpl; eauto.
  eapply Interweave_update_l with (l := l) in H16; simpl in *; eauto.
  { destruct l. unfold_all_lab. rewrite Nat.eqb_refl in H16. eassumption. }
  { unfold not. intros. apply List.in_map with (f := fst) in H18. eauto. } }
  lia.
Qed.

Theorem triple_assign (V : Set) (e1 e2 : Expr V) (v : option (Value V)) l P1 P2 Q2 :
  triple e1
    (<(l :?= v)> <*> P1)
    (fun v'' => <[v'' = Lab l]> <*> <(l :?= v)> <*> P2) ->
  triple e2
    (<(l :?= v)> <*> P2)
    (fun v' => <(l :?= v)> <*> Q2 v') ->
  triple (Assign e1 e2)
    (sa_credits 1 <*> <(l :?= v)> <*> P1)
    (fun v'' => <[v'' = U_val]> <*> <exists> v', <(l :== v')> <*> Q2 v').
Proof.
  unfold triple, hoare_triple. intros. normalize_star. make_cred_positive.
  edestruct_direct. fold_star. fold_star. repeat invert_Intwv_nil.
  conormalize_star. edestruct_all. normalize_star. subst.
  conormalize_star. edestruct_all. normalize_star. subst.
  find_star_and_unfold_all. edestruct_direct.
  eapply in_or_Interweave in H24 as ?; simpl; auto.
  eapply valid_map_update in H18 as ?.
  2:{ eauto using List.in_map. }
  split_all; solve_star; [eapply big_red_assign| | |]; eauto using valid_map_Assignment.
  { unfold_all. split_all; eauto; simpl; eauto.
  eapply Interweave_update_l with (l := l) in H24; simpl in *; eauto.
  { destruct l. unfold_all_lab. rewrite Nat.eqb_refl in H24. eassumption. }
  { unfold not. intros. apply List.in_map with (f := fst) in H26. eauto. } }
  lia.
Qed.

Lemma dealloc_Interweave (V : Set) l ov (m1 m2 : Map V) :
  Interweave [(l,ov)]%list m1 m2 ->
  Dealloc l m2 m1.
Proof.
  remember [(l,ov)]%list as m0 eqn:Hm0. intros Hinter. induction Hinter.
  - discriminate.
  - injection Hm0 as -> ->. invert_Intwv_nil. constructor.
  - subst. constructor. auto.
Qed.

Theorem htriple_free (V : Set) (e : Expr V) l ov P Q :
  hoare_triple e
    (sa_single_any l ov <*> P)
    (fun v => <[v = Lab l]> <*> sa_single_any l ov <*> Q) ->
  hoare_triple (Free e)
    (sa_credits 1 <*> sa_single_any l ov <*> P)
    (fun v => <[v = U_val]> <*> Q).
Proof.
  unfold hoare_triple. intros. normalize_star. make_cred_positive.
  edestruct_direct. invert_Intwv_nil. fold_star. edestruct_all. normalize_star.
  subst. find_star_and_unfold_all. edestruct_direct.
  split_all;
    eauto using big_red_free, Interweave_valid_r, dealloc_Interweave with lamref.
  - solve_star. eassumption.
  - lia.
Qed.

Theorem triple_free (V : Set) (e : Expr V) l ov P Q :
  triple e
    (sa_single_any l ov <*> P)
    (fun v => <[v = Lab l]> <*> sa_single_any l ov <*> Q) ->
  triple (Free e)
    (sa_credits 1 <*> sa_single_any l ov <*> P)
    (fun v => <[v = U_val]> <*> Q).
Proof.
  unfold triple, hoare_triple. intros. normalize_star. make_cred_positive.
  edestruct_direct. invert_Intwv_nil. fold_star. fold_star. conormalize_star.
  edestruct_all. normalize_star. subst. find_star_and_unfold_all.
  edestruct_direct. fold_disjoint_maps. fold_disjoint_maps. fold_star_with Q.
  split_all;
    eauto using big_red_free, Interweave_valid_r, dealloc_Interweave with lamref.
  - solve_star. eassumption.
  - lia.
Qed.

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
  subst_with c1. invert_Intwv_nil. edestruct_all. normalize_star. subst.
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
  fold_star. invert_Intwv_nil. edestruct_all. normalize_star. subst.
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
  injection_on_all S. invert_Intwv_nil. edestruct_all. normalize_star.
  destruct x1.
  2:{ subst. split_all. eapply big_red_while_false; eauto. solve_star; eauto.
    assumption. lia. }
  edestruct_all. normalize_star. destruct x5.
  { find_star_and_unfold_all. edestruct_direct. discriminate. }
  assert ((sa_credits 2 <*> P) x5 x6).
  { find_star_and_unfold_all. edestruct_direct. simpl in *. injection_on_all S.
    unfold_all. split_all; eauto. }
  assert (x5 < S (S (x0 + (x4 + S x5)))). { lia. }
  edestruct (H1 x5 H11 x6 H9 H10). edestruct_direct. normalize_star. subst. split_all.
  - eapply big_red_while_true with (c1 := x0) (c2 := x4) (c3 := x2); eauto.
  - solve_star; eauto.
  - assumption.
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
  injection_on_all S. invert_Intwv_nil. edestruct_all. normalize_star. destruct x7.
  2:{ subst. split_all. eapply big_red_while_false; eauto. solve_star; eauto.
    assumption. lia. }
  edestruct_all. normalize_star. destruct x9.
  { find_star_and_unfold_all. edestruct_direct. discriminate. }
  assert (((sa_credits 2 <*> P) <*> H1) x9 x10).
  { find_star_and_unfold_all. edestruct_direct. simpl in *. injection_on_all S.
    unfold_all. invert_Intwv_nil. split_all; eauto using Interweave_nil_l. }
  assert (x9 < S (S (x3 + x5))). { lia. }
  edestruct (H2 x9 H17 x10 H15 H16). edestruct_direct. normalize_star. subst.
  split_all.
  - eapply big_red_while_true; eauto.
  - solve_star; eauto.
  - assumption.
  - lia.
Qed.

(* other facts *)

Theorem htriple_fun_app (V : Set) (v : Value V) e P Q1 Q2 :
  triple_fun v Q1 Q2 ->
  hoare_triple e P Q1 ->
  hoare_triple (v <* e) P Q2.
Proof.
  unfold triple_fun. intros.
  assert (forall v' : Value V, hoare_triple (v <* v') (Q1 v') Q2).
  { auto using htriple_of_triple. }
  unfold hoare_triple in *. intros. edestruct_all.
  split_all; eauto using cost_red_comp, cost_red_app2, big_red_app. lia.
Qed.

Theorem triple_fun_app (V : Set) (v : Value V) e P Q1 Q2 :
  triple_fun v Q1 Q2 ->
  triple e P Q1 ->
  triple (v <* e) P Q2.
Proof.
  unfold triple_fun. intros.
  unfold triple, hoare_triple in *. intros. edestruct_all.
  split_all; eauto using cost_red_comp, cost_red_app2, big_red_app. lia.
Qed.

Theorem triple_fun_app2 (V : Set) (e1 e2 : Expr V) P1 P2 Q1 Q2 :
  triple e1 P1 (fun v => <[triple_fun v Q1 Q2]> <*> P2) ->
  triple e2 P2 Q1 ->
  triple (e1 <* e2) P1 Q2.
Proof.
  unfold triple_fun. intros.
  unfold triple, hoare_triple in *. intros. edestruct_all. normalize_star.
  edestruct_all.
  split_all;
    eauto using cost_red_comp, cost_red_app1, cost_red_app2, big_red_app.
  lia.
Qed.

Theorem triple_fun_frame (V : Set) (v : Value V) P Q H :
  triple_fun v P Q ->
  triple_fun v (P <*>+ H) (Q <*>+ H).
Proof.
  unfold triple_fun. auto using triple_frame.
Qed.

Theorem triple_fun_weaken (V : Set) (v : Value V) P' P Q Q' :
  P' -->> P ->
  Q -->> Q' ->
  triple_fun v P Q ->
  triple_fun v P' Q'.
Proof.
  unfold triple_fun. eauto using triple_weaken.
Qed.

Lemma triple_value_inv (V : Set) (v : Value V) P Q c m :
  triple v P Q ->
  Is_Valid_Map m ->
  P c m -> Q v c m.
Proof.
  unfold triple, hoare_triple. intros Htriple Hvalid HP.
  specialize Htriple
    with <[]> c m
    as (v'&c'&c2&m'
      &([=->]&->&->)%cost_red_value
      &HQ%empty_star_r_cancel
      &Hvalid'
      &->);
    auto.
  apply empty_star_r_intro. assumption.
Qed.

Fixpoint triple_list_curry {V : Set} (es : list (Expr V)) (P : StateAssertion V) :
  n_ary_fun_type (List.length es) (Value V) (StateAssertion V) ->
  (Value V -> n_ary_fun_type (List.length es) (Value V) (StateAssertion V)) ->
  ((Value V -> StateAssertion V) -> Prop) ->
    Prop :=
  match es with
  | [] => fun Q Qlast f => P ->> $1 <*> Q -> f Qlast
  | (e::es') => fun Q Qlast f =>
    forall Qmid x, triple e P (fun v => <[v = x]> <*> Qmid x) ->
      triple_list_curry es' (Qmid x) (Q x) (Qlast x) f
  end%list.

Lemma triple_list_curry_weaken_pre (V : Set) (e : Expr V) es
  (P1 P1' P2 : StateAssertion V) Q1 Q2 :
  P1 ->> P1' ->
  triple_list_curry es P2 Q1 Q2 (triple e P1') ->
  triple_list_curry es P2 Q1 Q2 (triple e P1).
Proof.
  revert P2 Q1 Q2. induction es; simpl; intros P2 Q1 Q2.
  - intros Himpl1 Htriple Himpl2.
    eapply triple_weaken; eauto using implies_refl.
  - intros Himpl1 Htriple_list Qmid x Htriple. eapply IHes; auto.
Qed.

Theorem triple_fun_n_ary_app_general (V : Set) (e e' : Expr V) es
  (P1 P2 : StateAssertion V) Q1 Q2 :
  triple e P1 (fun v => <[triple_fun_n_ary (List.length es) v Q1 Q2]> <*> P2) ->
  triple_list_curry (e'::es) P2 Q1 Q2
    (triple (n_ary_app e (e'::es)) ($(List.length es) <*> P1)).
Proof.
  revert e e' P1 P2. induction es (*using List.rev_ind*).
  - simpl. intros. eapply triple_fun_app2; eauto.
    eapply triple_weaken; [apply empty_star_l_cancel| |];
      eauto using implies_refl.
    intros. simpl. apply implies_spec. intros. normalize_star. solve_star.
    eapply triple_fun_weaken; eauto using implies_refl.
    intros. simpl.
    eauto using
      implies_trans, star_assoc_l, star_implies_mono, implies_refl, star_comm.
  - intros. hnf. intros. simpl List.length in *.
    apply triple_list_curry_weaken_pre with
      (P1' := $(List.length es) <*> ($1 <*> P1)).
    { eapply implies_trans; [|apply star_assoc].
      apply star_implies_mono; auto using implies_refl.
      apply credits_star_r. lia. }
    apply IHes.
    eapply triple_weaken, triple_app; [|
      lazymatch goal with
      | [|- forall x, ?Q x ->> @?Q' x] => unify Q Q'
      end
    | |]; eauto using implies_refl.
    simpl in H. eapply triple_weaken; eauto using implies_refl.
    apply implies_post_spec. intros. normalize_star. unfold triple_fun in *.
    specialize H1 with x x. apply htriple_of_triple in H1. unfold hoare_triple in H1.
    destruct (H1 1 []%list)
      as (?&?&?&?&
        (?&?&?&?&?&?&?&
          ([=<-]&->&->)%cost_red_value&
          ([=<-]&->&->)%cost_red_value&
          Hred&?)%big_red_app_inv&
        ?&?&?).
    + unfold Is_Valid_Map, labels. simpl. constructor.
    + swap_star. solve_star. unfold sa_credits. auto.
    + assert (x1=1/\x2=0/\x10=0) as (->&->&->) by lia.
      apply cost_red_0 in Hred as (Hsubst_e&<-); [|reflexivity].
      normalize_star. solve_star. split; auto. intros. apply triple_frame.
      apply triple_pure. intros ->. rewrite Hsubst_e.
      apply triple_value_implies, implies_spec. intros.
      normalize_star. subst. apply pure_spec. auto.
Qed.

Theorem triple_fun_n_ary_app (V : Set) (v : Value V) e es
  (P : StateAssertion V) Q1 Q2 :
  triple_fun_n_ary (List.length es) v Q1 Q2 ->
  triple_list_curry (e::es) P Q1 Q2
    (triple (n_ary_app v (e::es)) ($(List.length es) <*> P)).
Proof.
  intros. apply triple_fun_n_ary_app_general.
  eapply triple_weaken, triple_frame; [|
    lazymatch goal with
    | [|- forall x, ?Q x ->> @?Q' x] => unify Q Q'
    end
  |]; eauto using empty_star_l_intro, implies_refl.
  apply triple_value_implies. apply implies_spec. intros. normalize_star. subst.
  apply pure_spec. auto.
Qed.

Fixpoint sa_star_n_ary {V} n :
  n_ary_fun_type n (Value V) (StateAssertion V) ->
  n_ary_fun_type n (Value V) (StateAssertion V) ->
  n_ary_fun_type n (Value V) (StateAssertion V) :=
  match n with
  | 0 => fun P Q => P <*> Q
  | S n' => fun P Q => fun x => sa_star_n_ary n' (P x) (Q x)
  end.

Fixpoint sa_star_n_ary_post {V} n :
  n_ary_fun_type (S n) (Value V) (StateAssertion V) ->
  n_ary_fun_type n (Value V) (StateAssertion V) ->
  n_ary_fun_type (S n) (Value V) (StateAssertion V) :=
  match n with
  | 0 => fun P Q => P <*>+ Q
  | S n' => fun P Q => fun x => sa_star_n_ary_post n' (P x) (Q x)
  end.

Theorem triple_fun_n_ary_frame (V : Set) (v : Value V) n Q1 Q2 H :
  triple_fun_n_ary n v Q1 Q2 ->
  triple_fun_n_ary n v
    (sa_star_n_ary (S n) Q1 H) (sa_star_n_ary_post (S n) Q2 H).
Proof.
  revert v. induction n; simpl.
  - intros. eapply triple_fun_weaken; intros.
    { apply star_assoc_l. }
    { apply implies_refl. }
    auto using triple_fun_frame.
  - intros. simpl in IHn. eapply triple_fun_weaken; auto.
    { intros. apply implies_refl. }
    { apply implies_post_spec. intros. normalize_star. subst.
      apply pure_spec. auto. }
Qed.

Fixpoint sa_implies_n_ary {V} n :
  n_ary_fun_type n (Value V) (StateAssertion V) ->
  n_ary_fun_type n (Value V) (StateAssertion V) ->
    Prop :=
  match n with
  | 0 => fun P Q => P ->> Q
  | S n' => fun P Q => forall x, sa_implies_n_ary n' (P x) (Q x)
  end.

Theorem triple_fun_n_ary_weaken (V : Set) (v : Value V) n Q1' Q1 Q2 Q2' :
  sa_implies_n_ary (S n) Q1' Q1 ->
  sa_implies_n_ary (S (S n)) Q2 Q2' ->
  triple_fun_n_ary n v Q1 Q2 ->
  triple_fun_n_ary n v Q1' Q2'.
Proof.
  revert v Q1 Q2. induction n; simpl.
  - intros. eapply triple_fun_weaken; intros; auto. apply star_implies_mono.
    { apply implies_refl. }
    { auto. }
  - intros. simpl in IHn. eapply triple_fun_weaken; auto.
    { intros. simpl. apply implies_refl. }
    { apply implies_post_spec. intros. normalize_star. subst.
      apply pure_spec. eauto. }
Qed.
