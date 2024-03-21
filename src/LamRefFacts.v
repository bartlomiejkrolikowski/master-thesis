Require List.
Import List.ListNotations.
Require Import String.
Require Import ZArith.

Require Import src.LambdaRef.

Theorem cost_red_comp :
  forall V (e : _ V) m e' m' c e'' m'' c',
    C[e, m ~~> e', m' | c] ->
    C[e', m' ~~> e'', m'' | c'] ->
    C[e, m ~~> e'', m'' | c + c'].
Proof.
  intros V e m e' m' c e'' m'' c' Hred1 Hred2.
  induction Hred1 as [| ? ? ? ? e''' ? m''' HR ? ? ].
  - easy.
  - simpl. eapply S_red.
    + exact HR.
    + apply IHHred1. assumption.
Qed.

Theorem cost_red_app1 :
  forall V (m : _ V) m' e1 e1' e2 c,
    C[e1, m ~~> e1', m' | c] ->
    C[App e1 e2, m ~~> App e1' e2, m' | c].
Proof.
  intros V m m' e1 e1' e2 c Hred.
  induction Hred as [| ? ? ? ? ? ? ? HR ? ? ].
  - constructor.
  - econstructor.
    + constructor. exact HR.
    + assumption.
Qed.

Theorem cost_red_app2 :
  forall V (m : _ V) m' (v : Value _) e e' c,
    C[e, m ~~> e', m' | c] ->
    C[App v e, m ~~> App v e', m' | c].
Proof.
  intros V m m' v e e' c Hred.
  induction Hred as [| ? ? ? ? ? ? ? HR ? ? ].
  - constructor.
  - econstructor.
    + apply red_app2. exact HR.
    + assumption.
Qed.
