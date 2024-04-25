Require List.
Import List.ListNotations.
Require Import String.
Require Import ZArith.

Require Import src.LambdaRef3.

Lemma SplitAt_spec_eq :
  forall A xs ys (y : A) zs,
    L[xs ~~> ys | y | zs] ->
    xs = (ys ++ [y] ++ zs)%list.
Proof.
  intros A xs ys y zs Hsplit.
  induction Hsplit.
  - reflexivity.
  - simpl. f_equal. assumption.
Qed.

Lemma SplitAt_spec :
  forall A ys (y : A) zs,
    L[ys ++ [y] ++ zs ~~> ys | y | zs].
Proof.
  intros A ys y zs. induction ys; simpl.
  - constructor.
  - now constructor.
Qed.

Lemma Nth_spec (A : Set) n l (a : A) :
  Nth n l a -> List.nth_error l n = Some a.
Proof.
  now induction 1.
Qed.

Lemma list_map_inj (A B : Type) (f : A -> B) (xs ys : list A) :
  (forall x y, f x = f y -> x = y) ->
  List.map f xs = List.map f ys ->
  xs = ys.
Proof.
  intros Hinj Heq. generalize dependent ys.
  induction xs as [| x xs' IH ]; intros;
    destruct ys as [| y ys' ]; simpl in *; try discriminate.
  - reflexivity.
  - injection Heq; intros. f_equal; auto.
Qed.

Lemma vals2exprs_inj (V : Set) (vs vs' : list (Value V)) :
  vals2exprs vs = vals2exprs vs' -> vs = vs'.
Proof.
  apply list_map_inj. intros x y Heq. injection Heq. easy.
Qed.

(* uniqueness of reduction results *)
Lemma uniqueness (V : Set)
  (e e' e'' : Expr V) (m m' m'' : Map V) :
  red e m e' m' ->
  red e m e'' m'' ->
  e' = e'' /\ m' = m''.
Proof.
  intro H'. revert e'' m''. induction H'; intros e'' m'' H'';
  try now (inversion H''; try easy;
    match goal with
    | [ H : red (Val _) _ _ _ |- _ ] => inversion H
    end).
  - inversion H'';
      match goal with
      | [ H : vals2exprs _ = vals2exprs _ |- _ ] =>
        apply vals2exprs_inj in H; subst; easy
      | [ H  : L[ vals2exprs _ ~~> vals2exprs _ | ?e | _ ],
          HR : R[ ?e, _ ~~> _, _] |- _ ] =>
        unfold vals2exprs in H; apply SplitAt_spec_eq in H;
        apply List.map_eq_app in H; destruct H as [? [? [_ [_ H]]]];
        simpl in H; apply List.map_eq_cons in H;
        destruct H as [? [? [_ [H _]]]];
        subst; inversion HR
      end.
  - inversion H''.
    repeat match goal with
    | [ H : Nth _ _ _ |- _ ] => apply Nth_spec in H; try rewrite H in *
    end.
    split; congruence.
  - inversion H''.
Admitted.

(*
Lemma uniqueness_full (V : Set)
  (e e' e'' : Expr V) (m m' m'' : Map V) (c' c'' : nat) :
  cost_red e m e' m' c' ->
  cost_red e m e'' m'' c'' ->
  e' = e'' /\ m' = m'' /\ c' = c''.
Proof.
  intros H' H''.
Admitted.
*)

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
  forall V m m' (v : Value V) e e' c,
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

Theorem cost_red_unop :
  forall V k (m : _ V) m' e e' c,
    C[e, m ~~> e', m' | c] ->
    C[UnOp k e, m ~~> UnOp k e', m' | c].
Proof.
  intros V k m m' e e' c Hred.
  induction Hred as [| ? ? ? ? ? ? ? HR ? ? ].
  - constructor.
  - econstructor.
    + constructor. exact HR.
    + assumption.
Qed.

Theorem cost_red_binop1 :
  forall V k (m : _ V) m' e1 e1' e2 c,
    C[e1, m ~~> e1', m' | c] ->
    C[BinOp k e1 e2, m ~~> BinOp k e1' e2, m' | c].
Proof.
  intros V k m m' e1 e1' e2 c Hred.
  induction Hred as [| ? ? ? ? ? ? ? HR ? ? ].
  - constructor.
  - econstructor.
    + constructor. exact HR.
    + assumption.
Qed.

Theorem cost_red_binop2 :
  forall V k m m' (v : Value V) e e' c,
    C[e, m ~~> e', m' | c] ->
    C[BinOp k v e, m ~~> BinOp k v e', m' | c].
Proof.
  intros V k m m' v e e' c Hred.
  induction Hred as [| ? ? ? ? ? ? ? HR ? ? ].
  - constructor.
  - econstructor.
    + apply red_binop2. exact HR.
    + assumption.
Qed.

Theorem cost_red_rec_split :
  forall V (m : _ V) m' es es' vs0 e e' es0 c,
    L[es  ~~> vals2exprs vs0 | e | es0] ->
    L[es' ~~> vals2exprs vs0 | e' | es0] ->
    C[e, m ~~> e', m' | c] ->
    C[RecE es, m ~~> RecE es', m' | c].
Proof.
  intros V m m' es es' vs0 e e' es0 c Hsplit1 Hsplit2 Hred.
  generalize dependent es.
  induction Hred as [| ? ? ? ? ? ? ? HR ? ? ]; intros.
  - apply SplitAt_spec_eq in Hsplit1, Hsplit2. subst. constructor.
  - econstructor.
    + eapply red_rec_split.
      * eassumption.
      * apply SplitAt_spec.
      * exact HR.
    + apply IHHred.
      * assumption.
      * apply SplitAt_spec.
Qed.

Theorem cost_red_ref_e :
  forall V (m : _ V) m' e e' c,
    C[e, m ~~> e', m' | c] ->
    C[Ref e, m ~~> Ref e', m' | c].
Proof.
  intros V m m' e e' c Hred.
  induction Hred as [| ? ? ? ? ? ? ? HR ? ? ].
  - constructor.
  - econstructor.
    + constructor. exact HR.
    + assumption.
Qed.

Theorem cost_red_deref_e :
  forall V (m : _ V) m' e e' c,
    C[e, m ~~> e', m' | c] ->
    C[Deref e, m ~~> Deref e', m' | c].
Proof.
  intros V m m' e e' c Hred.
  induction Hred as [| ? ? ? ? ? ? ? HR ? ? ].
  - constructor.
  - econstructor.
    + constructor. exact HR.
    + assumption.
Qed.

Theorem cost_red_assign1 :
  forall V (m : _ V) m' e1 e1' e2 c,
    C[e1, m ~~> e1', m' | c] ->
    C[Assign e1 e2, m ~~> Assign e1' e2, m' | c].
Proof.
  intros V m m' e1 e1' e2 c Hred.
  induction Hred as [| ? ? ? ? ? ? ? HR ? ? ].
  - constructor.
  - econstructor.
    + constructor. exact HR.
    + assumption.
Qed.

Theorem cost_red_assign2 :
  forall V m m' (v : Value V) e e' c,
    C[e, m ~~> e', m' | c] ->
    C[Assign v e, m ~~> Assign v e', m' | c].
Proof.
  intros V m m' v e e' c Hred.
  induction Hred as [| ? ? ? ? ? ? ? HR ? ? ].
  - constructor.
  - econstructor.
    + apply red_assign2. exact HR.
    + assumption.
Qed.

Theorem cost_red_seq1 :
  forall V (m : _ V) m' e1 e1' e2 c,
    C[e1, m ~~> e1', m' | c] ->
    C[Seq e1 e2, m ~~> Seq e1' e2, m' | c].
Proof.
  intros V m m' e1 e1' e2 c Hred.
  induction Hred as [| ? ? ? ? ? ? ? HR ? ? ].
  - constructor.
  - econstructor.
    + constructor. exact HR.
    + assumption.
Qed.

Theorem cost_red_cond_if :
  forall V (m : _ V) m' e1 e1' e2 e3 c,
    C[e1, m ~~> e1', m' | c] ->
    C[If e1 e2 e3, m ~~> If e1' e2 e3, m' | c].
Proof.
  intros V m m' e1 e1' e2 e3 c Hred.
  induction Hred as [| ? ? ? ? ? ? ? HR ? ? ].
  - constructor.
  - econstructor.
    + constructor. exact HR.
    + assumption.
Qed.

(* values can't be reduced *)
Fact red_value :
  forall V m m' (v : Value V) e,
    ~ R[v, m ~~> e, m'].
Proof.
  intros V m m' v e Hred. inversion Hred.
Qed.

Fact cost_red_value :
  forall V m m' (v : Value V) (e : Expr V) c,
    C[v, m ~~> e, m' | c] ->
    e = v /\ m' = m /\ c = 0.
Proof.
  intros V m m' v e c Hred.
  destruct Hred as [| ? ? ? ? ? HR ? ].
  - easy.
  - apply red_value in HR. destruct HR.
Qed.

Fact is_value_or_not :
  forall V (e : Expr V),
    (exists v : Value V, e = v) \/
    (forall v : Value V, e <> v).
Proof.
  destruct e.
  1:{ left. eexists. reflexivity. }
  all: right; discriminate.
Qed.

(* inversions of lemmas above *)
Lemma cost_red_split1 :
  forall V (e : _ V) m e' m' c e'' m'' c',
    R[e, m ~~> e', m'] ->
    C[e, m ~~> e'', m'' | c + c'] ->
    C[e', m' ~~> e'', m'' | c'].
Proof.
  intros V e m e' m' c e'' m'' c' Hred. (* TODO *)
Abort.

Theorem cost_red_split :
  forall V (e : _ V) m e' m' c e'' m'' c',
    C[e, m ~~> e', m' | c] ->
    C[e, m ~~> e'', m'' | c + c'] ->
    C[e', m' ~~> e'', m'' | c'].
Proof.
  intros V e m e' m' c e'' m'' c' Hred1.
  induction Hred1 as [| ? ? ? ? e''' ? m''' HR ? ? ].
  - easy.
  - simpl. intro HredComp. apply IHHred1. (* TODO *)
Abort.

Theorem cost_red_app1_inv :
  forall V (m : _ V) m' e1 e1' e2 c,
    C[App e1 e2, m ~~> App e1' e2, m' | c] ->
    (forall v : Value V, e1 <> Val v) ->
    C[e1, m ~~> e1', m' | c].
Proof.
  intros V m m' e1 e1' e2 c Hred Hnvalue.
  inversion Hred.
  - constructor.
  - subst. inversion H.
    + subst. specialize Hnvalue with (-\ e). contradiction.
    + subst. (* TODO *)
Abort.

Theorem cost_red_app2_inv :
  forall V m m' (v : Value V) e e' c,
    C[App v e, m ~~> App v e', m' | c] ->
    (forall v : Value V, e <> Val v) ->
    C[e, m ~~> e', m' | c].
Proof.
  intros V m m' v e e' c Hred.
  remember (App v e) as eApp.
  remember (App v e') as eApp'.
  generalize dependent v.
  generalize dependent e. generalize dependent e'.
  induction Hred as [| ? ? ? ? ? ? ? HR ? ? ];
    intros e''' e'''' v HeqeApp HeqeApp' Hnvalue;
    subst.
  - injection HeqeApp' as He''''. subst. constructor.
  - inversion HR.
    + subst. specialize Hnvalue with v0. contradiction.
    + subst. apply red_value in H4. contradiction.
    + subst. econstructor.
      * eassumption.
      * eapply IHHred.
        -- reflexivity.
        -- reflexivity.
        -- (* TODO *)
Admitted.

(*
Theorem cost_red_unop :
  forall V k (m : _ V) m' e e' c,
    C[e, m ~~> e', m' | c] ->
    C[UnOp k e, m ~~> UnOp k e', m' | c].
Proof.
  intros V k m m' e e' c Hred.
  induction Hred as [| ? ? ? ? ? ? ? HR ? ? ].
  - constructor.
  - econstructor.
    + constructor. exact HR.
    + assumption.
Qed.

Theorem cost_red_binop1 :
  forall V k (m : _ V) m' e1 e1' e2 c,
    C[e1, m ~~> e1', m' | c] ->
    C[BinOp k e1 e2, m ~~> BinOp k e1' e2, m' | c].
Proof.
  intros V k m m' e1 e1' e2 c Hred.
  induction Hred as [| ? ? ? ? ? ? ? HR ? ? ].
  - constructor.
  - econstructor.
    + constructor. exact HR.
    + assumption.
Qed.

Theorem cost_red_binop2 :
  forall V k m m' (v : Value V) e e' c,
    C[e, m ~~> e', m' | c] ->
    C[BinOp k v e, m ~~> BinOp k v e', m' | c].
Proof.
  intros V k m m' v e e' c Hred.
  induction Hred as [| ? ? ? ? ? ? ? HR ? ? ].
  - constructor.
  - econstructor.
    + apply red_binop2. exact HR.
    + assumption.
Qed.

Lemma SplitAt_spec_eq :
  forall A xs ys (y : A) zs,
    L[xs ~~> ys | y | zs] ->
    xs = (ys ++ [y] ++ zs)%list.
Proof.
  intros A xs ys y zs Hsplit.
  induction Hsplit.
  - reflexivity.
  - simpl. f_equal. assumption.
Qed.

Lemma SplitAt_spec :
  forall A ys (y : A) zs,
    L[ys ++ [y] ++ zs ~~> ys | y | zs].
Proof.
  intros A ys y zs. induction ys; simpl.
  - constructor.
  - now constructor.
Qed.
*)

Fact vals2exprs_are_vals :
  forall V (vs : list (Value V)),
    List.Forall (fun e => exists v : Value V, e = Val v) (vals2exprs vs).
Proof.
  intros. apply List.Forall_map. apply List.Forall_forall.
  intros. eexists. reflexivity.
Qed.

Fact decidable_In :
  forall A,
    (forall x y : A, x = y \/ x <> y) ->
    forall (x : A) (xs : list A), List.In x xs \/ ~ List.In x xs.
Proof.
  intros A Hdecidable x xs. induction xs as [| y ? ? ]; simpl.
  - auto.
  - destruct Hdecidable with y x as [Hx | Hx], IHxs as [HIn | HIn];
    intuition.
Qed.

Theorem cost_red_rec_split_inv :
  forall V m m' es es' vs0 e (v : Value V) es0 c,
    L[es  ~~> vals2exprs vs0 | e | es0] ->
    L[es' ~~> vals2exprs vs0 | v | es0] ->
    (forall v : Value V, e <> Val v) ->
    C[RecE es, m ~~> RecE es', m' | c] ->
    C[e, m ~~> v, m' | c].
Proof.
  intros V m m' es es' vs0 e v es0 c Hsplit1 Hsplit2 Hnval HCRed.
  remember (RecE es) as eREes eqn:HeqeREes.
  remember (RecE es') as eREes' eqn:HeqeREes'.
  generalize dependent e.
  generalize dependent es.
  generalize dependent es'.
  induction HCRed as [ e' | e' ? ? ? ? ? ? HR ? ? ]; intros.
  - subst. injection HeqeREes as Hes.
    apply SplitAt_spec_eq in Hsplit1, Hsplit2.
    rewrite Hsplit1, Hsplit2 in Hes.
    apply List.app_inv_head in Hes. injection Hes as He. subst.
    constructor.
  - subst. inversion HR.
    + subst. apply SplitAt_spec_eq in Hsplit1.
      specialize vals2exprs_are_vals with (vs := vs) as Hvs.
      rewrite Hsplit1 in Hvs. apply List.Forall_elt in Hvs.
      destruct Hvs as [v' He]. now destruct Hnval with v'.
    + subst. apply SplitAt_spec_eq in Hsplit1, H0.
      rewrite H0 in Hsplit1. clear H0.
      assert (~ List.In e (vals2exprs vs1)) as HnIn1.
      {
        admit. (*TODO*)
      }
Admitted.
(*
Theorem cost_red_ref_e :
  forall V (m : _ V) m' e e' c,
    C[e, m ~~> e', m' | c] ->
    C[Ref e, m ~~> Ref e', m' | c].
Proof.
  intros V m m' e e' c Hred.
  induction Hred as [| ? ? ? ? ? ? ? HR ? ? ].
  - constructor.
  - econstructor.
    + constructor. exact HR.
    + assumption.
Qed.

Theorem cost_red_deref_e :
  forall V (m : _ V) m' e e' c,
    C[e, m ~~> e', m' | c] ->
    C[Deref e, m ~~> Deref e', m' | c].
Proof.
  intros V m m' e e' c Hred.
  induction Hred as [| ? ? ? ? ? ? ? HR ? ? ].
  - constructor.
  - econstructor.
    + constructor. exact HR.
    + assumption.
Qed.

Theorem cost_red_assign1 :
  forall V (m : _ V) m' e1 e1' e2 c,
    C[e1, m ~~> e1', m' | c] ->
    C[Assign e1 e2, m ~~> Assign e1' e2, m' | c].
Proof.
  intros V m m' e1 e1' e2 c Hred.
  induction Hred as [| ? ? ? ? ? ? ? HR ? ? ].
  - constructor.
  - econstructor.
    + constructor. exact HR.
    + assumption.
Qed.

Theorem cost_red_assign2 :
  forall V m m' (v : Value V) e e' c,
    C[e, m ~~> e', m' | c] ->
    C[Assign v e, m ~~> Assign v e', m' | c].
Proof.
  intros V m m' v e e' c Hred.
  induction Hred as [| ? ? ? ? ? ? ? HR ? ? ].
  - constructor.
  - econstructor.
    + apply red_assign2. exact HR.
    + assumption.
Qed.

Theorem cost_red_seq1 :
  forall V (m : _ V) m' e1 e1' e2 c,
    C[e1, m ~~> e1', m' | c] ->
    C[Seq e1 e2, m ~~> Seq e1' e2, m' | c].
Proof.
  intros V m m' e1 e1' e2 c Hred.
  induction Hred as [| ? ? ? ? ? ? ? HR ? ? ].
  - constructor.
  - econstructor.
    + constructor. exact HR.
    + assumption.
Qed.

Theorem cost_red_cond_if :
  forall V (m : _ V) m' e1 e1' e2 e3 c,
    C[e1, m ~~> e1', m' | c] ->
    C[If e1 e2 e3, m ~~> If e1' e2 e3, m' | c].
Proof.
  intros V m m' e1 e1' e2 e3 c Hred.
  induction Hred as [| ? ? ? ? ? ? ? HR ? ? ].
  - constructor.
  - econstructor.
    + constructor. exact HR.
    + assumption.
Qed.
*)