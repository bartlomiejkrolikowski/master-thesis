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


Theorem triple_weaken (V : Set) (e : Expr V) P P' Q Q' :
  P' ->> P ->
  (forall v c, (Q v c) ->> (Q' v c)) ->
  hoare_triple e P Q ->
  hoare_triple e P' Q'.
Proof.
  unfold hoare_triple, sa_implies. intros ? ? H ? ?.
  edestruct H as [? [? [? [? ?]]]]; eauto 10.
Qed.

Theorem triple_value (V : Set) (v : Value V) :
  hoare_triple v <[]> (fun v' c => <[v' = v /\ c = 0]>).
Proof.
  unfold hoare_triple, sa_pure, sa_empty.
  intros m Hm. subst. eauto 10 with lamref.
Qed.

Theorem triple_value' (V : Set) (v : Value V) (P : StateAssertion V) :
  hoare_triple v P (fun v' c => <[v' = v /\ c = 0]> <*> P).
Proof.
  unfold hoare_triple, sa_star, sa_pure, sa_empty, disjoint_maps.
  eauto 15 with lamref.
Qed.

Theorem triple_value_untimed (V : Set) (v : Value V) (P : StateAssertion V) :
  hoare_triple v P (fun _ _ => P).
Proof.
  eapply triple_weaken; eauto using triple_value';
    unfold sa_implies, sa_star, sa_pure, sa_empty;
    [| intros v' c m [m1 [m2 [[? ?] [? [? ?]]]]]; subst ];
    eauto.
Qed.

Theorem triple_lam (V : Set) (e : Expr _) (v : Value V) P Q :
  hoare_triple (subst_e e v) P (fun v c => Q v (1+c)) ->
  hoare_triple ((-\e) <* v) P Q.
Proof.
  unfold hoare_triple. intros.
  edestruct H as [? [? [? [? ?]]]]; eauto 10 with lamref.
Qed.

(*Theorem triple_seq (V : Set) (e1 e2 : Expr V) P1 P2 Q1 Q2 :
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

Ltac unfold_all :=
  unfold hoare_triple, sa_exists, sa_star, sa_single, sa_pure, sa_empty,
    sa_implies, disjoint_maps, labels.

Ltac edestruct_direct :=
  repeat match goal with
  | [H : exists _, _ |- _] => edestruct H; eauto; clear H
  | [H : _ /\ _ |- _] => edestruct H; eauto; subst; clear H
  end.

Ltac edestruct_all :=
  repeat match goal with
  | [p : ?P ?m, H : forall _, ?P _ -> exists _, _ |- _] =>
    destruct H with m; eauto; clear H; edestruct_direct
  end.

Ltac solve_triple n H :=
  unfold_all;
  intros;
  edestruct_all;
  eauto n using H.

Ltac solve_triple_15 := solve_triple integer:(15).

Theorem triple_app (V : Set) (e1 e2 : Expr V) e1' (v2 : Value V)
  P1 P2 P3 Q3 c1 c2 :
  hoare_triple e1 P1 (fun v c => <[v = (-\e1') /\ c = c1]> <*> P2) ->
  hoare_triple e2 P2 (fun v c => <[v = v2 /\ c = c2]> <*> P3) ->
  hoare_triple (subst_e e1' v2) P3 (fun v c => Q3 v (c1 + c2 + 1 + c)) ->
  hoare_triple (App e1 e2) P1 Q3.
Proof.
  solve_triple integer:(10) big_red_app.
Qed.

Theorem triple_bneg (V : Set) (e : Expr V) (b : bool) P Q :
  hoare_triple e P (fun v c => <[v = Bool b]> <*> Q (1+c)) ->
  hoare_triple ([~] e)
    P
    (fun v c => <[v = Bool (negb b)]> <*> Q c).
Proof.
  solve_triple_15 big_red_bneg.
Qed.

Theorem triple_ineg (V : Set) (e : Expr V) (i : Z) P Q :
  hoare_triple e P (fun v c => <[v = Int i]> <*> Q (1+c)) ->
  hoare_triple ([--] e)
    P
    (fun v c => <[v = Int (- i)]> <*> Q c).
Proof.
  solve_triple_15 big_red_ineg.
Qed.

Theorem triple_bor (V : Set) (e1 e2 : Expr V) (b1 b2 : bool)
  P1 P2 Q2 c1 :
  hoare_triple e1 P1 (fun v c => <[v = Bool b1 /\ c = c1]> <*> P2) ->
  hoare_triple e2 P2 (fun v c => <[v = Bool b2]> <*> Q2 (c1+c+1)) ->
  @hoare_triple V (e1 [||] e2)
    P1
    (fun v c => <[v = Bool (b1 || b2)]> <*> Q2 c).
Proof.
  solve_triple_15 big_red_bor.
Qed.

Theorem triple_band (V : Set) (e1 e2 : Expr V) (b1 b2 : bool)
  P1 P2 Q2 c1 :
  hoare_triple e1 P1 (fun v c => <[v = Bool b1 /\ c = c1]> <*> P2) ->
  hoare_triple e2 P2 (fun v c => <[v = Bool b2]> <*> Q2 (c1+c+1)) ->
  @hoare_triple V (e1 [&&] e2)
    P1
    (fun v c => <[v = Bool (b1 && b2)]> <*> Q2 c).
Proof.
  solve_triple_15 big_red_band.
Qed.

Theorem triple_iadd (V : Set) (e1 e2 : Expr V) (i1 i2 : Z)
  P1 P2 Q2 c1 :
  hoare_triple e1 P1 (fun v c => <[v = Int i1 /\ c = c1]> <*> P2) ->
  hoare_triple e2 P2 (fun v c => <[v = Int i2]> <*> Q2 (c1+c+1)) ->
  @hoare_triple V (e1 [+] e2)
    P1
    (fun v c => <[v = Int (i1 + i2)]> <*> Q2 c).
Proof.
  solve_triple_15 big_red_iadd.
Qed.

Theorem triple_isub (V : Set) (e1 e2 : Expr V) (i1 i2 : Z)
  P1 P2 Q2 c1 :
  hoare_triple e1 P1 (fun v c => <[v = Int i1 /\ c = c1]> <*> P2) ->
  hoare_triple e2 P2 (fun v c => <[v = Int i2]> <*> Q2 (c1+c+1)) ->
  @hoare_triple V (e1 [-] e2)
    P1
    (fun v c => <[v = Int (i1 - i2)]> <*> Q2 c).
Proof.
  solve_triple_15 big_red_isub.
Qed.

Theorem triple_imul (V : Set) (e1 e2 : Expr V) (i1 i2 : Z)
  P1 P2 Q2 c1 :
  hoare_triple e1 P1 (fun v c => <[v = Int i1 /\ c = c1]> <*> P2) ->
  hoare_triple e2 P2 (fun v c => <[v = Int i2]> <*> Q2 (c1+c+1)) ->
  @hoare_triple V (e1 [*] e2)
    P1
    (fun v c => <[v = Int (i1 * i2)]> <*> Q2 c).
Proof.
  solve_triple_15 big_red_imul.
Qed.

Theorem triple_idiv (V : Set) (e1 e2 : Expr V) (i1 i2 : Z)
  P1 P2 Q2 c1 :
  hoare_triple e1 P1 (fun v c => <[v = Int i1 /\ c = c1]> <*> P2) ->
  hoare_triple e2 P2 (fun v c => <[v = Int i2]> <*> Q2 (c1+c+1)) ->
  @hoare_triple V (e1 [/] e2)
    P1
    (fun v c => <[v = Int (i1 / i2)]> <*> Q2 c).
Proof.
  solve_triple_15 big_red_idiv.
Qed.

Theorem triple_clt (V : Set) (e1 e2 : Expr V) (i1 i2 : Z)
  P1 P2 Q2 c1 :
  hoare_triple e1 P1 (fun v c => <[v = Int i1 /\ c = c1]> <*> P2) ->
  hoare_triple e2 P2 (fun v c => <[v = Int i2]> <*> Q2 (c1+c+1)) ->
  @hoare_triple V (e1 [<] e2)
    P1
    (fun v c => <[v = Bool (i1 <? i2)%Z]> <*> Q2 c).
Proof.
  solve_triple_15 big_red_clt.
Qed.

Theorem triple_ceq (V : Set) (e1 e2 : Expr V) (i1 i2 : Z)
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
    hoare_triple e
      P
      (fun v' c' => <[v' = v /\ c' = c]> <*> Q)) ->
  hoare_triple (RecE (vals2exprs vs))
    P
    (fun v c => <[v = RecV vs /\ c = List.list_sum cs + 1]> <*> Q).
Proof.
  unfold_all.
  intros.
  specialize (big_red_rec V n) as Hbig.
Admitted.

Theorem triple_get (V : Set) n (e : Expr V) (vs : list (Value V)) v P Q :
  Nth n vs v ->
  hoare_triple e P (fun v' c => <[v' = RecV vs]> <*> Q (1+c)) ->
  hoare_triple (Get n e)
    P
    (fun v' c => <[v' = v]> <*> Q c).
Proof.
  solve_triple_15 big_red_get.
Qed.

Theorem triple_ref (V : Set) (e : Expr V) (v : Value V) P Q :
  hoare_triple e P (fun v' c => <[v' = v]> <*> Q (1+c)) ->
  hoare_triple (Ref e)
    P
    (fun v' c => <exists> l, <[v' = Lab l]> <*> <( l :== v )> <*> Q c).
Proof.
  unfold_all.
  intros.
  edestruct_all.
  repeat eexists. eapply big_red_ref; eauto.
  eauto. eauto. simpl. unfold new_label, list_max, of_label, labels. eauto 100.
Admitted.

Theorem triple_deref (V : Set) (e : Expr V) (v : Value V) l P Q :
  hoare_triple e
    (<(l :== v)> <*> P)
    (fun v' c => <[v' = Lab l]> <*> <(l :== v)> <*> Q (1+c)) ->
  hoare_triple (Deref e)
    (<(l :== v)> <*> P)
    (fun v' c => <[v' = v]> <*> <(l :== v)> <*> Q c).
Proof.
  (*solve_triple integer:(100) big_red_deref.*)
Admitted.

Theorem triple_assign (V : Set) (e1 e2 : Expr V) (v v' : Value V) l P1 P2 Q2 c1 :
  hoare_triple e1
    (<(l :== v)> <*> P1)
    (fun v'' c => <[v'' = Lab l /\ c = c1]> <*> P2) ->
  hoare_triple e2
    (<(l :== v)> <*> P2)
    (fun v'' c => <[v'' = v']> <*> Q2 (c1+c+1)) ->
  hoare_triple (Assign e1 e2)
    (<(l :== v)> <*> P1)
    (fun v'' c => <[v'' = U_val]> <*> <(l :== v')> <*> Q2 c).
Proof.
  (*solve_triple integer:(100) big_red_assign.*)
Admitted.

Theorem triple_seq (V : Set) (e1 e2 : Expr V) (v : Value V) P1 P2 Q2 c1 :
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

Theorem triple_if_true (V : Set) (e1 e2 e3 : Expr V) v P1 P2 Q2 c1 :
  hoare_triple e1
    P1
    (fun v' c => <[v' = Bool true /\ c = c1]> <*> P2) ->
  hoare_triple e2
    P2
    (fun v' c => <[v' = v]> <*> Q2 (c1+1+c)) ->
  hoare_triple (If e1 e2 e3)
    P1
    (fun v' c => <[v' = v]> <*> Q2 c).
Proof.
  solve_triple_15 big_red_if_true.
Qed.

Theorem triple_if_false (V : Set) (e1 e2 e3 : Expr V) v P1 P2 Q2 c1 :
  hoare_triple e1
    P1
    (fun v' c => <[v' = Bool false /\ c = c1]> <*> P2) ->
  hoare_triple e3
    P2
    (fun v' c => <[v' = v]> <*> Q2 (c1+1+c)) ->
  hoare_triple (If e1 e2 e3)
    P1
    (fun v' c => <[v' = v]> <*> Q2 c).
Proof.
  solve_triple_15 big_red_if_false.
Qed.

(*
Theorem triple_while_true (V : Set) (e1 e2 : Expr V) P Q :
  hoare_triple e1
    P
    (fun v c => <[v = Bool true]> <*> Q (1+(c+1))) ->
  hoare_triple e
    P
    (fun v c => <[v = Bool true]> <*> Q (1+(c+1))) ->
  hoare_triple (While e1 e2)
    P
    (fun v c => <[v = U_val]> <*> Q c).
Proof.
  solve_triple_15 big_red_while_true.
Qed.
*)
Theorem triple_while_false (V : Set) (e1 e2 : Expr V) P Q :
  hoare_triple e1
    P
    (fun v c => <[v = Bool false]> <*> Q (1+(c+1))) ->
  hoare_triple (While e1 e2)
    P
    (fun v c => <[v = U_val]> <*> Q c).
Proof.
  solve_triple_15 big_red_while_false.
Qed.
