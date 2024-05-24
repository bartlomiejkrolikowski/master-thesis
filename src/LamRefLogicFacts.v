Require List.
Import List.ListNotations.
Require Import String.
Require Import ZArith.

Require Import src.LambdaRef.
Require Import src.LamRefFacts.
Require Import src.LambdaAssertions.

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
