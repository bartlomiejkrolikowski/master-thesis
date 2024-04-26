Require List.
Import List.ListNotations.
Require Import String.
Require Import ZArith.

Require Import src.LambdaRef.
Require Import Lia.

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

Lemma SplitAt_2ways :
  forall A xs ys (y : A) zs ys' (y' : A) zs',
    L[xs ~~> ys | y | zs] ->
    L[xs ~~> ys' | y' | zs'] ->
    List.In y ys'
    \/ (ys = ys' /\ y = y' /\ zs = zs')
    \/ List.In y' ys.
Proof.
  intros ? ? ? ? ? ? ? ? Hsplit1 Hsplit2.
  revert ys' y' zs' Hsplit2.
  induction Hsplit1 as [| x xs ys y zs Hsplit1' IH1 ]; intros.
  - remember (x :: xs)%list as xs' eqn:Hxs'.
    revert x xs Hxs'.
    induction Hsplit2 as [| x' xs' ys' y' zs' Hsplit2' IH2 ];
      intros; injection Hxs' as [] [].
    + auto.
    + destruct Hsplit2'; simpl; auto.
  - inversion Hsplit2; subst; simpl.
    + auto.
    + edestruct IH1 as [Hin | [[Hys [Hy Hzs]] | Hin]]; eauto.
      subst. auto.
Qed.

Lemma SplitAt_deterministic :
  forall A xs ys (y : A) zs ys' (y' : A) zs',
    L[xs ~~> ys | y | zs] ->
    L[xs ~~> ys' | y' | zs'] ->
    ~ List.In y ys' ->
    ~ List.In y' ys ->
    (ys = ys' /\ y = y' /\ zs = zs').
Proof.
  intros ? ? ? ? ? ? ? ? Hsplit1 Hsplit2 Hin Hin'.
  edestruct SplitAt_2ways as [? | [? | ?]];
    [| | | eassumption |]; eauto; contradiction.
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

Lemma Is_Valid_Map_cons_fresh (V : Set) (l : Label) v (m : Map V) :
  Is_fresh_label l m ->
  Is_Valid_Map m ->
  Is_Valid_Map ((l, v) :: m)%list.
Proof.
  unfold Is_fresh_label, Is_Valid_Map. intros. now constructor.
Qed.

Lemma max_list_max ns :
  List.Forall (fun n => n <= list_max ns) ns.
Proof.
  induction ns as [| n ns' IH ]; constructor;
  try eapply List.Forall_impl; try eassumption; simpl; lia.
Qed.

Section label_section.
Open Scope label_scope.
Lemma new_label_spec_lt (V : Set) (m : Map V) :
  List.Forall (fun l => l < new_label m) (labels m).
Proof.
  specialize (max_list_max (List.map (fun '(OfNat n) => n) (labels m))) as H.
  eapply List.Forall_map, List.Forall_impl in H.
  - eassumption.
  - destruct a. simpl. lia.
Qed.
End label_section.

Lemma new_label_is_fresh (V : Set) (m : Map V) :
  Is_fresh_label (new_label m) m.
Proof.
  intro Hin. specialize new_label_spec_lt with V m as H.
  eapply List.Forall_forall in H; [| eassumption ].
  destruct new_label. simpl in *. lia.
Qed.

Lemma Is_Valid_Map_cons_new (V : Set) v (m : Map V) :
  Is_Valid_Map m ->
  Is_Valid_Map ((new_label m, v) :: m)%list.
Proof.
  auto using Is_Valid_Map_cons_fresh, new_label_is_fresh.
Qed.

Lemma Lookup_success (V : Set) (l : Label) (m : Map V) v :
  Lookup l m v -> List.In l (labels m).
Proof.
  induction 1 as [| [l' v'] m' v Hlookup' IH]; simpl; auto.
Qed.

Lemma Lookup_spec (V : Set) (l : Label) (m : Map V) v :
  Is_Valid_Map m ->
  Lookup l m v ->
  lookup l m = Some v.
Proof.
  destruct l as [n]. intros Hvalid Hlookup.
  induction Hlookup as [| [[n'] v'] m' v Hlookup' IH ]; simpl.
  - now rewrite Nat.eqb_refl.
  - inversion Hvalid. destruct Nat.eqb_spec with n n'.
    + subst. apply Lookup_success in Hlookup'.
      contradiction.
    + auto.
Qed.

Lemma Assignment_success (V : Set) (l : Label) v (m m' : Map V) :
  Assignment l v m m' -> List.In l (labels m).
Proof.
  induction 1 as [| [l' v'] m m' Hlookup' IH]; simpl; auto.
Qed.

Lemma update_in (V : Set) (l : Label) v (m : Map V) :
  List.In l (labels m) ->
  labels (update l v m) = labels m.
Proof.
  destruct l as [n]. intros Hin. induction m as [| [[n'] v'] m' IH]; simpl.
  - contradiction.
  - destruct Nat.eqb_spec with n n'; simpl in *.
    + reflexivity.
    + f_equal. destruct Hin as [Heq | Hin].
      * congruence.
      * auto.
Qed.

Lemma valid_labels (V : Set) (m m' : Map V) :
  labels m = labels m' ->
  Is_Valid_Map m ->
  Is_Valid_Map m'.
Proof.
  unfold Is_Valid_Map. revert m'.
  induction m as [| [l v] m IH]; destruct m' as [| [l' v'] m'];
    simpl; intros Heq Hvalid; try discriminate; try injection Heq as [] [];
    assumption.
Qed.

Lemma Assignment_spec (V : Set) (l : Label) v (m m' : Map V) :
  Is_Valid_Map m ->
  Assignment l v m m' ->
  m' = update l v m /\ Is_Valid_Map m'.
Proof.
  destruct l as [n]. intros Hvalid Hassign.
  induction Hassign as [| [[n'] v'] m m' Hassign IH]; simpl.
  - now rewrite Nat.eqb_refl.
  - inversion Hvalid. destruct Nat.eqb_spec with n n'.
    + subst. apply Assignment_success in Hassign.
      contradiction.
    + destruct IH as [Hupdate Hvalid']; [| subst; split]; auto.
      eapply valid_labels with ((_, _) :: m)%list.
      * simpl. f_equal. symmetry. apply update_in.
        eapply Assignment_success. eassumption.
      * eassumption.
Qed.

(*
Fixpoint value_eq_dec (V : Set) (v v' : Value V) {struct v} :
  (forall x x' : V, x = x' \/ x <> x') ->
  v = v' \/ v <> v'
with expr_eq_dec (V : Set) (e e' : Expr V) {struct e} :
  (forall x x' : V, x = x' \/ x <> x') ->
  e = e' \/ e <> e'.
Proof.
  - intro Hdec. destruct v, v'; try (right; discriminate).
    + left. reflexivity.
    + destruct Hdec with v v0.
  - destruct e, e'; auto.
Qed.
*)

Lemma in_vals2expr (V : Set) (e : Expr V) vs :
  List.In e (vals2exprs vs) ->
  exists v : Value V, e = v.
Proof.
  induction vs; simpl; intros H; destruct H; eauto.
Qed.

(* uniqueness of reduction results *)
Theorem uniqueness (V : Set)
  (e e' e'' : Expr V) (m m' m'' : Map V) :
  Is_Valid_Map m ->
  red e m e' m' ->
  red e m e'' m'' ->
  e' = e'' /\ m' = m'' /\ Is_Valid_Map m'.
Proof.
  intros H H'. revert e'' m''. induction H'; intros e'' m'' H'';
  try (inversion H''; subst;
    try apply Is_Valid_Map_cons_new with (v := v) in H as Hmap;
    try easy;
    match goal with
    | [ H : red (Val _) _ _ _ |- _ ] => inversion H
    | [ H : Assignment _ _ _ _,
        H' : Assignment _ _ _ _ |- _ ] =>
        apply Assignment_spec in H as [? ?]; [|assumption];
        apply Assignment_spec in H' as [? ?]; [|assumption];
        repeat split; congruence
    end);
    try (inversion H''; subst;
      try match goal with
      | [ H : red (Val _) _ _ _ |- _ ] => inversion H
      end;
      edestruct IHH' as [He1 [Hm' Hvalid]]; eauto;
      subst; easy).
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
    repeat split; congruence.
  - inversion H''; subst.
    + repeat match goal with
      | [ H : Lookup _ _ _ |- _ ] =>
        apply Lookup_spec in H; try assumption
      end.
      repeat split; congruence.
    + match goal with
      | [ H : red (Val _) _ _ _ |- _ ] => inversion H
      end.
  - inversion H''; subst.
    + match goal with
      | [ H  : L[ vals2exprs _ ~~> vals2exprs _ | ?e | _ ],
          HR : R[ ?e, _ ~~> _, _] |- _ ] =>
        unfold vals2exprs in H; apply SplitAt_spec_eq in H;
        apply List.map_eq_app in H; destruct H as [? [? [_ [_ H]]]];
        simpl in H; apply List.map_eq_cons in H;
        destruct H as [? [? [_ [H _]]]];
        subst; inversion HR
      end.
    + edestruct SplitAt_deterministic with (y := e) (y' := e0) as [? [? ?]];
        eauto;
        try match goal with
        | [|- ~ List.In _ _] =>
          intros Hin; apply in_vals2expr in Hin as [? ?]; subst
        end;
        try match goal with
        | [ H : red (Val _) _ _ _ |- _ ] => inversion H
        end.
      subst.
      match goal with
      | [H : vals2exprs _ = vals2exprs _ |- _] =>
        rewrite H2 in *
      end.
      match goal with
      | [ Hvalid : Is_Valid_Map _,
          Hred : red _ _ _ _
          |- _] =>
        destruct (IHH' Hvalid _ _ Hred) as [? [? ?]]
      end.
      repeat match goal with
      | [H : SplitAt ?es1 _ _ _ |- _ ] => apply SplitAt_spec_eq in H
      end.
      subst. auto.
Qed.

Lemma no_red_val (V : Set) (e e' : Expr V) (m m' : Map V) :
  C[e, m ~~> e', m' | 0] ->
  e = e' /\ m = m'.
Proof.
  inversion 1. auto.
Qed.

(* TODO *)
Fixpoint uniqueness_full (V : Set)
  (e : Expr V) (v1 v2 : Value V) (m m1 m2 : Map V) (c1 c2 : nat)
  (Hvalid : Is_Valid_Map m)
  (Hred1 : C[e, m ~~> v1, m1 | c1])
  (Hred2 : C[e, m ~~> v2, m2 | c2])
  : v1 = v2 /\ m1 = m2 /\ Is_Valid_Map m1.
Proof.
  inversion Hred1.
  - clear uniqueness_full. inversion Hred2; subst.
    + injection H2. auto.
    + inversion H2.
  - inversion Hred2; subst.
    + inversion H.
    + destruct (uniqueness _ _ _ _ _ _ _ Hvalid H H4) as [He' [Hm' Hvalid']].
      subst. apply (uniqueness_full _ _ _ _ _ _ _ _ _ Hvalid' H0 H5).
Qed.

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