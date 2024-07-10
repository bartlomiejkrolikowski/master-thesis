Require Arith.
Require Import Lia.
Require List.
Import List.ListNotations.
Require Import String.
Require Import ZArith.

Require Import src_arrays.LambdaRef.
Require Import src_arrays.Tactics.

Fact liftS_inc (V V' : Set) (f : V -> Value V') x v' :
  liftS (inc_fun f v') (option_map Some x) = liftS f x.
Proof.
  destruct x; reflexivity.
Qed.

Fact liftS_ext (V V' : Set) (f g : V -> Value V') x :
  (forall x, f x = g x) ->
  liftS f x = liftS g x.
Proof.
  destruct x; simpl; intro Hext; [f_equal|]; auto.
Qed.

Fact liftS_Var V (x : inc_set V) :
  liftS Var x = Var x.
Proof.
  destruct x; reflexivity.
Qed.

Fixpoint bind_v_ext (V V' : Set) (f g : V -> Value V') v {struct v} :
  (forall x, f x = g x) ->
  bind_v f v = bind_v g v
with bind_e_ext (V V' : Set) (f g : V -> Value V') e {struct e} :
  (forall x, f x = g x) ->
  bind_e f e = bind_e g e.
Proof.
  - destruct v; simpl; trivial; intro Hext; f_equal.
    + revert l. fix Hind 1. destruct l; simpl; f_equal; auto.
    + auto using liftS_ext.
  - destruct e; simpl; intro; f_equal; auto.
    revert l. fix Hind 1. destruct l; simpl; f_equal; auto.
Qed.

Fixpoint bind_v_map_v (V V' V'' : Set) (f : V' -> Value V'') (g : V -> V') v {struct v} :
  bind_v f (map_v g v) = bind_v (fun x => f (g x)) v
with bind_e_map_e (V V' V'' : Set) (f : V' -> Value V'') (g : V -> V') e {struct e} :
  bind_e f (map_e g e) = bind_e (fun x => f (g x)) e.
Proof.
  - destruct v; simpl; trivial; f_equal.
    + revert l. fix Hind 1. destruct l; simpl; f_equal; auto.
    + erewrite bind_e_ext with (f := liftS (fun x => f (g x)));
        [|destruct x]; eauto.
  - destruct e; simpl; f_equal; eauto.
    revert l. fix Hind 1. destruct l; simpl; f_equal; auto.
Qed.

Fixpoint bind_v_shift (V V' : Set) (f : V -> Value V') v v' {struct v} :
  bind_v (inc_fun f v') (shift_v v) = bind_v f v
with bind_e_shift (V V' : Set) (f : V -> Value V') e v' {struct e} :
  bind_e (inc_fun f v') (shift_e e) = bind_e f e.
Proof.
  - destruct v; simpl; trivial; f_equal.
    + unfold shift_v in *.
      revert l. fix Hind 1. destruct l; simpl; f_equal; auto.
    + erewrite bind_e_ext with (f := liftS f).
      * apply bind_e_map_e.
      * destruct x; reflexivity.
  - destruct e; simpl; f_equal; eauto. unfold shift_e in *.
    revert l. fix Hind 1. destruct l; simpl; f_equal; auto.
Qed.

Fixpoint bind_v_id (V : Set) (v : Value V) {struct v} :
  bind_v Var v = v
with bind_e_id (V : Set) (e : Expr V) {struct e} :
  bind_e Var e = e.
Proof.
  - destruct v; simpl; trivial; f_equal.
    + revert l. fix Hind 1. destruct l; simpl; f_equal; auto.
    + erewrite bind_e_ext; auto using liftS_Var.
  - destruct e; simpl; f_equal; auto.
    revert l. fix Hind 1. destruct l; simpl; f_equal; auto.
Qed.

(** OTHER LEMMAS *)

Fact lift_inj A (f : nat -> A) l l' :
  (forall n n', f n = f n' -> n = n') ->
  lift f l = lift f l' ->
  l = l'.
Proof.
  destruct l as [n], l' as [l']. auto.
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

Lemma SplitAt_map A B (f : A -> B) xs ys y zs :
  L[xs ~~> ys | y | zs] ->
  L[List.map f xs ~~> List.map f ys | f y | List.map f zs].
Proof.
  intros Hsplit. induction Hsplit; simpl; constructor. assumption.
Qed.

Lemma Nth_spec (A : Set) n l (a : A) :
  Nth n l a -> List.nth_error l n = Some a.
Proof.
  now induction 1.
Qed.

Lemma Nth_map (A B : Set) (f : A -> B) n l a :
  Nth n l a -> Nth n (List.map f l) (f a).
Proof.
  intros Hnth. induction Hnth; constructor; auto.
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

Lemma list_max_plus n n' l :
  list_max (List.map (plus n) (n'::l)%list) = n + list_max (n'::l)%list.
Proof.
  induction l; simpl in *; try lia.
Qed.

Lemma list_max_app n l l' :
  n = list_max l' ->
  list_max ((List.map (plus n) l) ++ l') = n + list_max l.
Proof.
  intro. subst. induction l; simpl in *; try lia.
Qed.

(*Lemma S_list_max_app n l l' :
  n = S (list_max l') ->
  (list_max ((List.map (plus n) l) ++ l')) = n + list_max l.
Proof.
  intro. subst. induction l; simpl in *; try lia.
Qed.*)

Ltac unfold_all_lab :=
  unfold label_lt, label_ltb, label_eqb, lift2, lift, of_label in *.

Section label_section.
Open Scope label_scope.
Lemma new_label_spec_lt (V : Set) (m : Map V) :
  List.Forall (fun l => l < new_label m) (labels m).
Proof.
  specialize (max_list_max (List.map (fun '(OfNat n) => n) (labels m))) as H.
  eapply List.Forall_map, List.Forall_impl in H.
  - eassumption.
  - destruct a. unfold_all_lab.
    unfold new_label, labels, of_label in *.
    simpl. lia.
Qed.
End label_section.

Lemma new_label_is_fresh (V : Set) (m : Map V) :
  Is_fresh_label (new_label m) m.
Proof.
  intro Hin. specialize new_label_spec_lt with V m as H.
  eapply List.Forall_forall in H; [| eassumption ].
  destruct new_label. unfold_all_lab. simpl in *. lia.
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
  - unfold_all_lab. now rewrite Nat.eqb_refl.
  - inversion Hvalid. unfold_all_lab.
    destruct Nat.eqb_spec with n n'.
    + subst. apply Lookup_success in Hlookup'.
      contradiction.
    + auto.
Qed.

Lemma Lookup_spec_eq (V : Set) (l : Label) (m : Map V) v :
  lookup l m = Some v ->
  Lookup l m v.
Proof.
  destruct l as [n]. intros Hlookup.
  induction m as [| [[n'] v'] m' IH].
  - discriminate.
  - simpl in *. unfold_all_lab.
    destruct Nat.eqb_spec with n n'.
    + destruct v' as [v'|].
      * injection Hlookup as []. subst. constructor 1.
      * discriminate.
    + constructor 2. auto.
Qed.

Lemma Lookup_map (V V' : Set)
  f (g : Value V -> Value V') (l : Label) (m : Map V) m' v :
  Lookup l m v ->
  Lookup (f l)
    (List.map (fun '(l', v') => (f l', option_map g v')) m ++ m')%list (g v).
Proof.
  intro Hlookup. induction Hlookup; simpl; constructor. assumption.
Qed.

Lemma Lookup_map_nat (V V' : Set)
  f (g : Value V -> Value V') (l : Label) (m : Map V) m' v :
  Lookup l m v ->
  Lookup (lift f l)
    (List.map (fun '(OfNat n', v') => (f n', option_map g v')) m ++ m')%list
    (g v).
Proof.
  destruct l as [n]. intro Hlookup.
  induction Hlookup; simpl; constructor. assumption.
Qed.

Lemma Assignment_success (V : Set) (l : Label) v (m m' : Map V) :
  Assignment l v m m' -> List.In l (labels m).
Proof.
  induction 1 as [| [l' v'] m m' Hassign' IH]; simpl; auto.
Qed.

Lemma Assignment_map_nat (V V' : Set)
  f (g : Value V -> Value V') (l : Label) (m : Map V) m' m'' v :
  Assignment l v m m' ->
  Assignment (lift f l) (g v)
    (List.map (fun '(OfNat n', v') => (f n', option_map g v')) m ++ m'')%list
    (List.map (fun '(OfNat n', v') => (f n', option_map g v')) m' ++ m'')%list.
Proof.
  destruct l as [n]. intro Hassign.
  induction Hassign; simpl; constructor. assumption.
Qed.

Lemma update_in (V : Set) (l : Label) v (m : Map V) :
  List.In l (labels m) ->
  labels (update l v m) = labels m.
Proof.
  destruct l as [n]. intros Hin. induction m as [| [[n'] v'] m' IH]; simpl.
  - contradiction.
  - unfold_all_lab.
    destruct Nat.eqb_spec with n n'; simpl in *.
    + reflexivity.
    + f_equal. destruct Hin as [Heq | Hin].
      * congruence.
      * auto.
Qed.

Lemma lookup_same (V : Set) (l : Label) v (m : Map V) :
  lookup l (update l v m) = Some v.
Proof.
  destruct l as [n].
  induction m as [| [[n'] v'] m' IH]; simpl; unfold_all_lab.
  - now rewrite Nat.eqb_refl.
  - destruct Nat.eqb_spec with n n'; simpl; unfold_all_lab.
    + apply Nat.eqb_eq in e. now rewrite e.
    + apply Nat.eqb_neq in n0. now rewrite n0.
Qed.

Lemma Lookup_update (V : Set) (l l' : Label) v v' (m : Map V) :
  l <> l' ->
  Lookup l m v ->
  Lookup l (update l' v' m) v.
Proof.
  destruct l as [n], l' as [n']. intros Hneq Hlookup.
  induction Hlookup as [| [[n''] v''] m' v Hlookup' IH ];
    simpl; unfold_all_lab.
  - destruct Nat.eqb_spec with n' n.
    + congruence.
    + constructor.
  - destruct Nat.eqb; constructor; auto.
Qed.

Lemma lookup_fresh (V : Set) (l : Label) (m : Map V) :
  Is_fresh_label l m ->
  lookup l m = None.
Proof.
  unfold Is_fresh_label. destruct l as [n].
  induction m as [| [[n'] v] m' IHm']; simpl.
  - reflexivity.
  - intros Hfresh. unfold_all_lab.
    destruct Nat.eqb_spec with n n'; subst.
    + exfalso. auto.
    + auto.
Qed.

(*
Lemma lookup_None (V : Set) (l : Label) (m : Map V) :
  lookup l m = None ->
  Is_fresh_label l m.
Proof.
  unfold Is_fresh_label, not. destruct l as [n].
  induction m as [| [[n'] v] m' IHm']; simpl.
  - auto.
  - intros HNone. unfold_all_lab.
    destruct Nat.eqb_spec with n n'; subst.
    + discriminate.
    + intros [Heq | Hin]; [injection Heq |]; auto.
Qed.

Lemma lookup_fresh_equiv (V : Set) (l : Label) (m : Map V) :
  Is_fresh_label l m <-> lookup l m = None.
Proof. split; auto using lookup_fresh, lookup_None. Qed.

Lemma lookup_not_fresh (V : Set) (l : Label) (m : Map V) :
  ~ Is_fresh_label l m ->
  exists v : Value V, lookup l m = Some v.
Proof.
  rewrite lookup_fresh_equiv. destruct lookup.
  - eauto.
  - contradiction.
Qed.
*)

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
  induction Hassign as [| [[n'] v'] m m' Hassign IH]; simpl; unfold_all_lab.
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

Fixpoint map_v_shift_labels (V V' : Set) f (g : V -> V') (v : Value V) :
  map_labels_v f (map_v g v) = map_v g (map_labels_v f v)
with map_e_shift_labels (V V' : Set) f (g : V -> V') (e : Expr V) :
  map_labels_e f (map_e g e) = map_e g (map_labels_e f e).
Proof.
  - destruct v; simpl; eauto using f_equal.
    destruct l; cbn; repeat f_equal; eauto.
    revert l. fix Hall 1.
    destruct l; cbn; repeat f_equal; eauto.
  - destruct e; simpl; f_equal; eauto.
    revert l. fix Hall 1.
    destruct l; cbn; repeat f_equal; eauto.
Qed.

Fixpoint shift_v_shift_labels (V : Set) f (v : Value V) :
  map_labels_v f (shift_v v) = shift_v (map_labels_v f v)
with shift_e_shift_labels (V : Set) f (e : Expr V) :
  map_labels_e f (shift_e e) = shift_e (map_labels_e f e).
Proof.
  - destruct v; cbn; eauto using f_equal, map_e_shift_labels.
    destruct l; cbn; repeat f_equal; auto.
    revert l. fix Hall 1.
    destruct l; cbn; repeat f_equal; auto.
  - destruct e; cbn; f_equal; eauto.
    revert l. fix Hall 1.
    destruct l; cbn; repeat f_equal; auto.
Qed.

Fixpoint bind_v_shift_labels (V V' : Set) f (g : V -> Value V') (v : Value V) :
  map_labels_v f (bind_v g v) =
    bind_v (fun x => map_labels_v f (g x)) (map_labels_v f v)
with bind_e_shift_labels (V V' : Set) f (g : V -> Value V') (e : Expr V) :
  map_labels_e f (bind_e g e) =
    bind_e (fun x => map_labels_v f (g x)) (map_labels_e f e).
Proof.
  - destruct v; simpl; auto.
    + f_equal. revert l. fix Hall 1.
      destruct l; simpl; f_equal; auto.
    + f_equal.
      rewrite bind_e_ext with
        (f := liftS (fun x => map_labels_v f (g x)))
        (g := fun x => map_labels_v f (liftS g x));
        [|destruct x]; eauto using shift_v_shift_labels.
  - destruct e; simpl; f_equal; auto.
    revert l. fix Hall 1.
    destruct l; cbn; repeat f_equal; auto.
Qed.

Fixpoint subst_v_shift_labels (V : Set) f (v : Value (inc_set V)) v' :
  map_labels_v f (subst_v v v') = subst_v (map_labels_v f v) (map_labels_v f v')
with subst_e_shift_labels (V : Set) f (e : Expr (inc_set V)) v' :
  map_labels_e f (subst_e e v') = subst_e (map_labels_e f e) (map_labels_v f v').
Proof.
  - destruct v; cbn; auto.
    + destruct i; simpl; reflexivity.
    + f_equal. revert l. fix Hall 1.
      destruct l; simpl; f_equal; eauto.
    + f_equal. rewrite bind_e_shift_labels. apply bind_e_ext.
      destruct x; simpl; trivial.
      destruct i; simpl; auto using shift_v_shift_labels.
  - destruct e; cbn; f_equal; eauto.
    revert l. fix Hall 1.
    destruct l; cbn; repeat f_equal; eauto using bind_e_shift_labels.
Qed.

Fixpoint shift_inj_v (V : Set) f (v v' : Value V) :
  (forall l l', f l = f l' -> l = l') ->
  map_labels_v f v = map_labels_v f v' ->
  v = v'
with shift_inj_e (V : Set) f (e e' : Expr V) :
  (forall l l', f l = f l' -> l = l') ->
  map_labels_e f e = map_labels_e f e' ->
  e = e'.
Proof.
  all: intros Hinj Heq.
  - destruct v, v'; simpl in *; trivial; try discriminate;
      injection Heq as Heq; f_equal; eauto.
    generalize dependent l. revert l0. fix Hall 1.
    destruct l; simpl; destruct l0; simpl; intro; f_equal; try discriminate;
      injection Heq; eauto.
  - destruct e, e'; simpl in *; trivial; try discriminate;
      injection Heq as Heq; f_equal; eauto.
    generalize dependent l. revert l0. fix Hall 1.
    destruct l; simpl; destruct l0; simpl; intro; f_equal; try discriminate;
      injection Heq; eauto.
Qed.

Lemma vals2expr_shift (V : Set) f (vs : list (Value V)) :
  vals2exprs (List.map (map_labels_v f) vs) =
    List.map (map_labels_e f) (vals2exprs vs).
Proof.
  induction vs; simpl; f_equal. assumption.
Qed.

(*
Lemma new_label_plus V n (m : Map V) m' m2 :
  n = of_label (new_label m') ->
  m2 = List.map (fun '(OfNat n', v) => (OfNat (n + n'), v)) m ->
  new_label (m2 ++ m')%list = OfNat (lift2 plus (new_label m) (new_label m')).
Proof.
  intros. subst. unfold_all_lab. unfold new_label. induction m; simpl; try lia.
Qed.
*)

Lemma map_fst_map_pair A' B B' (f : nat -> A') (g : B -> B') l :
  List.map fst (List.map (fun '(OfNat a,b) => (f a,g b)) l) =
    List.map f (List.map of_label (List.map fst l)).
Proof.
  unfold_all_lab.
  induction l; simpl; f_equal; destruct a as [[]]; auto.
Qed.

Fact f_if A B (f : A -> B) (b : bool) x y :
  f (if b then x else y) = if b then f x else f y.
Proof.
  now destruct b.
Qed.

(* TODO *)
Theorem red_shift (V : Set) n m m' m'' m2 m2' (e e' e2 e2' : Expr V) :
  S n = of_label (new_label m'') ->
  m2 = List.map (fun '(OfNat n', v) => (OfNat (n + n'), option_map (map_labels_v (lift (fun n' => OfNat (plus n n')))) v)) m ->
  m2' = List.map (fun '(OfNat n', v) => (OfNat (n + n'), option_map (map_labels_v (lift (fun n' => OfNat (plus n n')))) v)) m' ->
  e2 = map_labels_e (lift (fun n' => OfNat (plus n n'))) e ->
  e2' = map_labels_e (lift (fun n' => OfNat (plus n n'))) e' ->
  R[e, m ~~> e', m'] ->
  R[e2, m2 ++ m'' ~~> e2', m2' ++ m'']%list.
Proof.
  unfold new_label, of_label.
  intros Hn Hm2 Hm2' He2 He2' Hred. injection Hn as Hn. subst.
  induction Hred; simpl; try now econstructor.
  - rewrite subst_e_shift_labels. econstructor.
  - rewrite <- vals2expr_shift. eapply red_rec_e2v.
  - apply red_rec_get. apply Nth_map. assumption.
  - subst. apply red_ref. unfold new_label. simpl.
    rewrite Nat.add_succ_r.
    erewrite <- list_max_app; auto.
    repeat f_equal. unfold labels.
    repeat rewrite List.map_app. f_equal.
    repeat rewrite List.map_map. apply List.map_ext.
    intros [[n] v']. simpl. reflexivity.
  - apply red_new_array; try assumption. admit.
  - apply red_deref. apply Lookup_map_nat. assumption.
  - admit.
  - apply red_assign. apply Assignment_map_nat. assumption.
  - apply red_free. admit.
  - rewrite f_if. apply red_if.
  - eapply red_rec_split; try (rewrite vals2expr_shift; apply SplitAt_map);
      eassumption.
Admitted.

Theorem cost_red_shift (V : Set) n m m' m'' m2 m2' (e e' e2 e2' : Expr V) c :
  S n = of_label (new_label m'') ->
  m2 = List.map (fun '(OfNat n', v) => (OfNat (n + n'), option_map (map_labels_v (lift (fun n' => OfNat (plus n n')))) v)) m ->
  m2' = List.map (fun '(OfNat n', v) => (OfNat (n + n'), option_map (map_labels_v (lift (fun n' => OfNat (plus n n')))) v)) m' ->
  e2 = map_labels_e (lift (fun n' => OfNat (plus n n'))) e ->
  e2' = map_labels_e (lift (fun n' => OfNat (plus n n'))) e' ->
  C[e, m ~~> e', m' | c] ->
  C[e2, m2 ++ m'' ~~> e2', m2' ++ m'' | c]%list.
Proof.
  intros Hn Hm2 Hm2' He2 He2' Hred. subst.
  induction Hred; econstructor; eauto using red_shift.
Qed.

(*
Inductive equiv_v :
  forall {V : Set}, Map V -> Map V -> Value V -> Value V -> Prop :=
| equiv_U_val V m m'  : @equiv_v V m m' U_val U_val
| equiv_Var V m m' v  : @equiv_v V m m' (Var v) (Var v)
| equiv_Int V m m' i  : @equiv_v V m m' (Int i) (Int i)
| equiv_Bool V m m' b : @equiv_v V m m' (Bool b) (Bool b)
| equiv_LabNone V m m' l l' :
  Is_fresh_label l m ->
  Is_fresh_label l' m' ->
  @equiv_v V m m' (Lab l) (Lab l')
| equiv_LabSome V m m' l l' v v' :
  Lookup l m v ->
  Lookup l' m' v' ->
  @equiv_v V m m' v v' ->
  @equiv_v V m m' (Lab l) (Lab l')
| equiv_RecV V m m' vs vs' :
  List.Forall2 (@equiv_v V m m') vs vs' ->
  @equiv_v V m m' (RecV vs) (RecV vs')
| equiv_Lam V m m' e e' :
  @equiv_e (inc_set V)
    (List.map (fun '(l, v) => (l, shift_v v)) m)
    (List.map (fun '(l, v) => (l, shift_v v)) m')
    e e' ->
  @equiv_v V m m' (Lam e) (Lam e')
with equiv_e :
  forall {V : Set}, Map V -> Map V -> Expr V -> Expr V -> Prop :=
| equiv_Val V m m' v v' :
  @equiv_v V m m' v v' ->
  @equiv_e V m m' (Val v) (Val v')
| equiv_App V m m' e1 e2 e1' e2' :
  @equiv_e V m m' e1 e1' ->
  @equiv_e V m m' e2 e2' ->
  @equiv_e V m m' (App e1 e2) (App e1' e2')
| equiv_UnOp V m m' k e e' :
  @equiv_e V m m' e e' ->
  @equiv_e V m m' (UnOp k e) (UnOp k e')
| equiv_BinOp V m m' k e1 e2 e1' e2' :
  @equiv_e V m m' e1 e1' ->
  @equiv_e V m m' e2 e2' ->
  @equiv_e V m m' (BinOp k e1 e2) (BinOp k e1' e2')
| equiv_RecE V m m' es es' :
  List.Forall2 (@equiv_e V m m') es es' ->
  @equiv_e V m m' (RecE es) (RecE es')
| equiv_Get V m m' n e e' :
  @equiv_e V m m' e e' ->
  @equiv_e V m m' (Get n e) (Get n e')
| equiv_Ref V m m' e e' :
  @equiv_e V m m' e e' ->
  @equiv_e V m m' (Ref e) (Ref e')
| equiv_Deref V m m' e e' :
  @equiv_e V m m' e e' ->
  @equiv_e V m m' (Deref e) (Deref e')
| equiv_Assign V m m' e1 e2 e1' e2' :
  @equiv_e V m m' e1 e1' ->
  @equiv_e V m m' e2 e2' ->
  @equiv_e V m m' (Assign e1 e2) (Assign e1' e2')
| equiv_Seq V m m' e1 e2 e1' e2' :
  @equiv_e V m m' e1 e1' ->
  @equiv_e V m m' e2 e2' ->
  @equiv_e V m m' (Seq e1 e2) (Seq e1' e2')
| equiv_If V m m' e1 e2 e3 e1' e2' e3' :
  @equiv_e V m m' e1 e1' ->
  @equiv_e V m m' e2 e2' ->
  @equiv_e V m m' e3 e3' ->
  @equiv_e V m m' (If e1 e2 e3) (If e1' e2' e3')
| equiv_While V m m' e1 e2 e1' e2' :
  @equiv_e V m m' e1 e1' ->
  @equiv_e V m m' e2 e2' ->
  @equiv_e V m m' (While e1 e2) (While e1' e2')
.

Lemma is_fresh_label_decidable (V : Set) (l : Label) (m : Map V) :
  Is_fresh_label l m \/ ~ Is_fresh_label l m.
Proof.
  unfold Is_fresh_label, not. destruct l as [n].
  induction m as [| [[n'] v'] m' [IHm' | IHm']]; simpl; auto.
  destruct Nat.eq_dec with n n'; subst; auto.
  left. intuition.
  match goal with [H:OfNat _ = OfNat _ |- _] => injection H end.
  auto.
Qed.

Fixpoint equiv_v_refl_empty {V : Set} (v : Value V) {struct v} :
  equiv_v nil nil v v
with equiv_e_refl_empty {V : Set} (e : Expr V) {struct e} :
  equiv_e nil nil e e.
Proof.
  - destruct v; constructor; unfold Is_fresh_label; simpl; auto.
    revert l. fix Hall 1.
    destruct l; constructor; auto.
  - destruct e; constructor; unfold Is_fresh_label; simpl; auto.
    revert l. fix Hall 1.
    destruct l; constructor; auto.
Qed.

Fixpoint equiv_v_refl_cons {V : Set}
  (p : Label * Value V) (m : Map V) (v : Value V)
  (Hequiv : equiv_v m m v v) {struct Hequiv} :
  equiv_v (p::m)%list (p::m)%list v v
with equiv_e_refl_cons {V : Set}
  (p : Label * Value V) (m : Map V) (e : Expr V)
  (Hequiv : equiv_e m m e e) {struct Hequiv} :
  equiv_e (p::m)%list (p::m)%list e e.
Proof.
  - destruct p as [[n''] v''].
    destruct Hequiv.
    + constructor.
    + constructor.
    + constructor.
    + constructor.
    + destruct l as [n], l' as [n'].
      destruct Nat.eq_dec with n n'', Nat.eq_dec with n' n''; subst.
      * (*TODO*) constructor.
     destruct is_fresh_label_decidable with V l (m). constructor.
    ; constructor; unfold Is_fresh_label in *; simpl; auto.
    revert l. fix Hall 1.
    destruct l; constructor; auto.
  - destruct e; constructor; unfold Is_fresh_label; simpl; auto.
    revert l. fix Hall 1.
    destruct l; constructor; auto.
Qed.

Theorem equiv_v_refl {V : Set} (m : Map V) :
  (forall (v : Value V), equiv_v m m v v)
  /\ (forall (e : Expr V), equiv_e m m e e).
Proof.
  induction m as [| ? ? [IHm_v IHm_e]].
  - split.
    + apply equiv_v_refl_empty.
    + apply equiv_e_refl_empty.
  - split.
    + destruct v.
  5:{ destruct is_fresh_label_decidable with (l := l) (m := (a::m)%list).
    - apply equiv_LabNone; auto.
    - apply lookup_not_fresh in H as [v H].
      eapply equiv_LabSome; eauto using Lookup_spec_eq.
  }
    + apply equiv_e_refl_empty.
Qed.

(*
Fixpoint equiv_v_refl_in {V : Set}
  (l : Label) (m : Map V) (v : Value V) {struct v} :
  Lookup l m v ->
  equiv_v m m v v.
Proof.
  destruct v.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - admit.
  - constructor.
    generalize dependent l0. fix Hall 1.
    destruct l0; constructor.
    + inversion H; subst. eapply equiv_v_refl_in. auto.
*)
Fixpoint equiv_v_refl {V : Set} (m : Map V) (v : Value V) {struct v} :
  equiv_v m m v v
with equiv_e_refl {V : Set} (m : Map V) (e : Expr V) {struct e} :
  equiv_e m m e e.
Proof.
  - destruct v.
  5:{ destruct is_fresh_label_decidable with (l := l) (m := m).
    - apply equiv_LabNone; auto.
    - apply lookup_not_fresh in H as [v H].
      eapply equiv_LabSome; eauto using Lookup_spec_eq.
  }
  all: constructor; auto.
    revert l. fix Hall 1.
    destruct l; constructor; auto.
  - destruct e; try constructor; auto.
    revert l. fix Hall 1.
    destruct l; constructor; auto.
Qed.

Theorem extend_state (V : Set)
  (e e' : Expr V) (m m' : Map V) :
  red e nil e' m' ->
  red e m e' (m' ++ m)%list.
Proof.
  intros Hred. remember []%list as m0 eqn:Hm0.
  induction Hred; simpl; subst; try constructor; eauto; try now inversion H.
  2:{ eapply red_rec_split; eauto. }
Admitted.
*)

Ltac discriminate_red_Val :=
  match goal with
  | [ H : red (Val _) _ _ _ |- _ ] => inversion H
  end.

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
    inversion H''; subst;
    try (try discriminate_red_Val;
      edestruct IHH' as [He1 [Hm' Hvalid]]; eauto;
      subst; easy);
    try match goal with
    | [ H : vals2exprs _ = vals2exprs _ |- _ ] =>
      apply vals2exprs_inj in H; subst; easy
    | [ H  : L[ vals2exprs _ ~~> vals2exprs _ | ?e | _ ],
        HR : R[ ?e, _ ~~> _, _] |- _ ] =>
      unfold vals2exprs in H; apply SplitAt_spec_eq in H;
      apply List.map_eq_app in H; destruct H as [? [? [_ [_ H]]]];
      simpl in H; apply List.map_eq_cons in H;
      destruct H as [? [? [_ [H _]]]];
      subst; inversion HR
    end;
    repeat match goal with
    | [ H : Nth _ _ _ |- _ ] => apply Nth_spec in H; try rewrite H in *
    | [ H : Lookup _ _ _ |- _ ] =>
      apply Lookup_spec in H; try assumption
    end;
    try (repeat split; congruence).
  - admit.
  - admit.
  - admit.
  - edestruct SplitAt_deterministic with (y := e) (y' := e0) as [? [? ?]];
      eauto;
      try match goal with
      | [|- ~ List.In _ _] =>
        intros Hin; apply in_vals2expr in Hin as [? ?]; subst
      end;
      try discriminate_red_Val.
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
Admitted.

Lemma no_red_val (V : Set) (e e' : Expr V) (m m' : Map V) :
  C[e, m ~~> e', m' | 0] ->
  e = e' /\ m = m'.
Proof.
  inversion 1. auto.
Qed.

Fixpoint uniqueness_full (V : Set)
  (e : Expr V) (v1 v2 : Value V) (m m1 m2 : Map V) (c1 c2 : nat)
  (Hvalid : Is_Valid_Map m)
  (Hred1 : C[e, m ~~> v1, m1 | c1])
  (Hred2 : C[e, m ~~> v2, m2 | c2])
  : v1 = v2 /\ m1 = m2 /\ c1 = c2 /\ Is_Valid_Map m1.
Proof.
  remember (Val v1) as e1 eqn:He1. destruct Hred1.
  - clear uniqueness_full. inversion Hred2; subst.
    + injection H. auto.
    + inversion H.
  - inversion Hred2; subst.
    + inversion H.
    + destruct (uniqueness _ _ _ _ _ _ _ Hvalid H H0) as [He' [Hm' Hvalid']].
      subst.
      destruct (uniqueness_full _ _ _ _ _ _ _ _ _ Hvalid' Hred1 H1)
        as [? [? [? ?]]].
      auto.
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

(* reductions from last to first *)
Lemma cost_red_last :
  forall V (e : _ V) m e' m' e'' m'' c,
    C[e, m ~~> e', m' | c] ->
    R[e', m' ~~> e'', m''] ->
    C[e, m ~~> e'', m'' | S c].
Proof with eauto.
  intros V e m e' m' e'' m'' c Hcost_red Hred. induction Hcost_red.
  - repeat econstructor...
  - econstructor...
Qed.

(* inversions of lemmas above *)
Lemma cost_red_split1 :
  forall V (e : _ V) m e' m' e'' m'' c,
    Is_Valid_Map m ->
    R[e, m ~~> e', m'] ->
    C[e, m ~~> e'', m'' | S c] ->
    C[e', m' ~~> e'', m'' | c].
Proof.
  intros V e m e' m' e'' m'' c Hvalid Hred Hcost_red.
  inversion Hcost_red.
  match goal with
  | [ Hred1 : red _ _ _ _,
      Hred2 : red _ _ _ _
      |- _ ] =>
    destruct (uniqueness _ _ _ _ _ _ _ Hvalid Hred1 Hred2) as [He' [Hm' Hvalid']]
  end.
  subst. auto.
Qed.

Lemma cost_red_split1_exists :
  forall V (e : _ V) m e' m' (v : Value V) m'' c,
    Is_Valid_Map m ->
    R[e, m ~~> e', m'] ->
    C[e, m ~~> v, m'' | c] ->
    exists c', C[e', m' ~~> v, m'' | c'].
Proof.
  intros V e m e' m' v m'' c Hvalid Hred Hcost_red.
  inversion Hcost_red; subst; try discriminate_red_Val.
  match goal with
  | [ Hred1 : red _ _ _ _,
      Hred2 : red _ _ _ _
      |- _ ] =>
    destruct (uniqueness _ _ _ _ _ _ _ Hvalid Hred1 Hred2) as [He' [Hm' Hvalid']]
  end.
  subst. eauto.
Qed.

Theorem cost_red_split :
  forall V (e : _ V) m e' m' c e'' m'' c',
    Is_Valid_Map m ->
    C[e, m ~~> e', m' | c] ->
    C[e, m ~~> e'', m'' | c + c'] ->
    C[e', m' ~~> e'', m'' | c'].
Proof.
  intros V e m e' m' c e'' m'' c' Hvalid Hred1.
  induction Hred1 as [| ? ? ? ? e''' ? m''' HR ? ? ].
  - easy.
  - simpl. intro HredComp. apply IHHred1. eapply uniqueness; eauto.
    eapply cost_red_split1; eauto.
Qed.

Theorem cost_red_split_exists :
  forall V (e : _ V) m e' m' c (v : Value V) m'' c',
    Is_Valid_Map m ->
    C[e, m ~~> e', m' | c] ->
    C[e, m ~~> v, m'' | c'] ->
    exists c'', C[e', m' ~~> v, m'' | c''].
Proof.
  intros V e m e' m' c v m'' c' Hvalid Hred1.
  generalize dependent c'.
  induction Hred1 as [| ? ? ? ? e''' ? m''' HR ? ? ].
  - eauto.
  - simpl. intros c' HredComp. inversion HredComp; subst.
    + discriminate_red_Val.
    + eapply IHHred1. eapply uniqueness; eauto.
      eapply cost_red_split1; eauto.
Qed.

Ltac cut_values H :=
  exfalso; eapply H; [apply Nat.lt_0_succ| |]; auto with lamref.

Ltac finish_inversion_proof IH H :=
  econstructor; eauto; eapply IH; auto; unfold not; intros;
  match goal with
  | [Hlt : _ < _ |- _] =>
    eapply H; [apply -> Nat.succ_lt_mono; apply Hlt| |]
  end; eauto with lamref.

Theorem cost_red_app1_inv :
  forall V (m : _ V) m' e1 e1' e2 c,
    C[App e1 e2, m ~~> App e1' e2, m' | c] ->
    (forall e1'' m'' c'' (v : Value V),
      c'' < c ->
      C[e1, m ~~> e1'', m'' | c''] ->
      e1'' <> Val v) ->
    C[e1, m ~~> e1', m' | c].
Proof.
  intros V m m' e1 e1' e2 c Hred Hnvalue.
  remember (e1 <* e2) as e eqn:He. remember (e1' <* e2) as e' eqn:He'.
  generalize dependent e2. generalize dependent e1'.
  generalize dependent e1.
  induction Hred; intros; subst.
  - injection He'. intros. subst. constructor.
  - inversion H; subst; try now (cut_values Hnvalue).
    finish_inversion_proof IHHred Hnvalue.
Qed.

Theorem cost_red_app2_inv :
  forall V m m' (v : Value V) e e' c,
    C[App v e, m ~~> App v e', m' | c] ->
    (forall e'' m'' c'' (v : Value V),
      c'' < c ->
      C[e, m ~~> e'', m'' | c''] ->
      e'' <> Val v) ->
    C[e, m ~~> e', m' | c].
Proof.
  intros V m m' v e e' c Hred.
  remember (App v e) as eApp eqn:HeApp.
  remember (App v e') as eApp' eqn:HeApp'.
  generalize dependent v.
  generalize dependent e. generalize dependent e'.
  induction Hred as [| ? ? ? ? ? ? ? HR ? ? ];
    intros e''' e'''' v ? ? Hnvalue;
    subst.
  - injection HeApp'. intros. subst. constructor.
  - inversion HR; subst;
      try now (discriminate_red_Val || cut_values Hnvalue).
    finish_inversion_proof IHHred Hnvalue.
Qed.

Theorem cost_red_unop_inv :
  forall V k (m : _ V) m' e e' c,
    C[UnOp k e, m ~~> UnOp k e', m' | c] ->
    (forall e'' m'' c'' (v : Value V),
      c'' < c ->
      C[e, m ~~> e'', m'' | c''] ->
      e'' <> Val v) ->
    C[e, m ~~> e', m' | c].
Proof.
  intros V k m m' e e' c Hred Hnvalue.
  remember (UnOp k e) as e1 eqn:He1. remember (UnOp k e') as e1' eqn:He1'.
  generalize dependent e'. generalize dependent e.
  induction Hred as [| ? ? ? ? ? ? ? HR ? ? ]; intros; subst.
  - injection He1'. intros. subst. constructor.
  - inversion HR; subst; try now (cut_values Hnvalue).
    finish_inversion_proof IHHred Hnvalue.
Qed.

(*
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

(* big step semantics *)

Ltac eauto_lr := eauto with lamref.
Ltac induction_on_cost_red v H :=
  remember (Val v); induction H; subst; simpl; eauto_lr.
Ltac solve_by_induction :=
  intros;
  match goal with
  | [H1 : cost_red _ _ (Val ?v1) _ _,
     H2 : cost_red _ _ (Val ?v2) _ _,
     H3 : cost_red _ _ (Val ?v3) _ _
     |- _] =>
    induction_on_cost_red v1 H1;
    induction_on_cost_red v2 H2;
    induction_on_cost_red v3 H3
  | [H1 : cost_red _ _ (Val ?v1) _ _,
     H2 : cost_red _ _ (Val ?v2) _ _
     |- _] =>
    induction_on_cost_red v1 H1;
    induction_on_cost_red v2 H2
  | [H1 : cost_red _ _ (Val ?v1) _ _ |- _] =>
    induction_on_cost_red v1 H1
  end.

Theorem big_red_app (V : Set) m1 m2 m3 m4 c1 c2 c3
  (e1 e2 : Expr V) e1' (v2 v3 : Value V) :
  C[e1,m1 ~~> -\ e1',m2|c1] ->
  C[e2,m2 ~~>     v2,m3|c2] ->
  C[subst_e e1' v2,m3 ~~> v3,m4|c3] ->
  C[e1 <* e2,m1 ~~> v3,m4|c1+c2+1+c3].
Proof.
  solve_by_induction.
Qed.

Theorem big_red_bneg (V : Set) m1 m2 c
  (e : Expr V) b :
  C[e,m1 ~~> Bool b,m2|c] ->
  C[[~] e,m1 ~~> Bool (negb b),m2|1+c].
Proof.
  solve_by_induction.
Qed.

Theorem big_red_ineg (V : Set) m1 m2 c
  (e : Expr V) i :
  C[e,m1 ~~> Int i,m2|c] ->
  C[[--] e,m1 ~~> Int (-i),m2|1+c].
Proof.
  solve_by_induction.
Qed.

Theorem big_red_bor (V : Set) m1 m2 m3 c1 c2
  (e1 e2 : Expr V) b1 b2 :
  C[e1,m1 ~~> Bool b1,m2|c1] ->
  C[e2,m2 ~~> Bool b2,m3|c2] ->
  C[e1 [||] e2,m1 ~~> Bool (b1 || b2),m3|c1+c2+1].
Proof.
  solve_by_induction.
Qed.

Theorem big_red_band (V : Set) m1 m2 m3 c1 c2
  (e1 e2 : Expr V) b1 b2 :
  C[e1,m1 ~~> Bool b1,m2|c1] ->
  C[e2,m2 ~~> Bool b2,m3|c2] ->
  C[e1 [&&] e2,m1 ~~> Bool (b1 && b2),m3|c1+c2+1].
Proof.
  solve_by_induction.
Qed.

Theorem big_red_iadd (V : Set) m1 m2 m3 c1 c2
  (e1 e2 : Expr V) i1 i2 :
  C[e1,m1 ~~> Int i1,m2|c1] ->
  C[e2,m2 ~~> Int i2,m3|c2] ->
  C[e1 [+] e2,m1 ~~> Int (i1 + i2),m3|c1+c2+1].
Proof.
  solve_by_induction.
Qed.

Theorem big_red_isub (V : Set) m1 m2 m3 c1 c2
  (e1 e2 : Expr V) i1 i2 :
  C[e1,m1 ~~> Int i1,m2|c1] ->
  C[e2,m2 ~~> Int i2,m3|c2] ->
  C[e1 [-] e2,m1 ~~> Int (i1 - i2),m3|c1+c2+1].
Proof.
  solve_by_induction.
Qed.

Theorem big_red_imul (V : Set) m1 m2 m3 c1 c2
  (e1 e2 : Expr V) i1 i2 :
  C[e1,m1 ~~> Int i1,m2|c1] ->
  C[e2,m2 ~~> Int i2,m3|c2] ->
  C[e1 [*] e2,m1 ~~> Int (i1 * i2),m3|c1+c2+1].
Proof.
  solve_by_induction.
Qed.

Theorem big_red_idiv (V : Set) m1 m2 m3 c1 c2
  (e1 e2 : Expr V) i1 i2 :
  C[e1,m1 ~~> Int i1,m2|c1] ->
  C[e2,m2 ~~> Int i2,m3|c2] ->
  C[e1 [/] e2,m1 ~~> Int (i1 / i2),m3|c1+c2+1].
Proof.
  solve_by_induction.
Qed.

Theorem big_red_clt (V : Set) m1 m2 m3 c1 c2
  (e1 e2 : Expr V) i1 i2 :
  C[e1,m1 ~~> Int i1,m2|c1] ->
  C[e2,m2 ~~> Int i2,m3|c2] ->
  C[e1 [<] e2,m1 ~~> Bool (i1 <? i2)%Z,m3|c1+c2+1].
Proof.
  solve_by_induction.
Qed.

Theorem big_red_ceq (V : Set) m1 m2 m3 c1 c2
  (e1 e2 : Expr V) i1 i2 :
  C[e1,m1 ~~> Int i1,m2|c1] ->
  C[e2,m2 ~~> Int i2,m3|c2] ->
  C[e1 [=] e2,m1 ~~> Bool (i1 =? i2)%Z,m3|c1+c2+1].
Proof.
  solve_by_induction.
Qed.

Notation "List.last_error xs" :=
  (List.last (List.map Some xs) None)
  (at level 50).

Lemma red_rec_cons_value (V : Set) m m' c
  (es : list (Expr V)) v (vs : list (Value V)) :
  C[RecE es,m ~~> RecV vs,m'|c] ->
  C[RecE (Val v::es)%list,m ~~> RecV (v::vs)%list,m'|c].
Proof.
  intros Hr. remember (RecE es) as e. remember (Val (RecV vs)) as ev.
  generalize dependent es. induction Hr; intros; subst; try discriminate.
  inversion H; subst.
  - inversion Hr; subst; try discriminate_red_Val.
    unfold vals2exprs.
    change
      (C[ RecE (List.map Val (v::vs))%list,m'' ~~> RecV (v::vs)%list,m'' | 1]).
    fold (@vals2exprs V). eauto_lr.
  - econstructor.
    + eapply red_rec_split with (vs0 := (v::vs0)%list); simpl;
        eauto using SplitAt_tl.
    + auto.
Qed.

Lemma red_rec_cons (V : Set) m1 m2 m3 c1 c2
  (e : Expr V) es (v : Value V) vs :
  C[e,m1 ~~> v,m2|c1] ->
  C[RecE es,m2 ~~> RecV vs,m3|c2] ->
  C[RecE (e::es),m1 ~~> RecV (v::vs),m3|c1+c2].
Proof.
  intros Hr1 Hr2. eapply cost_red_comp.
  - eapply cost_red_rec_split with (vs0 := []%list); eauto; simpl;
      apply SplitAt_hd.
  - now apply red_rec_cons_value.
Qed.

Theorem big_red_rec (V : Set) n ms m m' cs
  (es : list (Expr V)) (vs : list (Value V)) :
  Some m = List.head ms ->
  Some m' = List.last_error ms ->
  n = List.length es ->
  n = List.length vs ->
  1+n = List.length ms ->
  n = List.length cs ->
  (forall i e v m m' c,
    Nth i es e ->
    Nth i vs v ->
    Nth i ms m ->
    Nth (1+i) ms m' ->
    Nth i cs c ->
    C[e,m ~~> v,m'|c]) ->
  C[RecE es,m ~~> RecV vs,m'|List.list_sum cs + 1].
Proof.
  intros. subst.
  generalize dependent ms.
  generalize dependent m. generalize dependent m'.
  generalize dependent cs. generalize dependent vs.
  induction es; intros; destruct vs; destruct ms; destruct cs;
    simpl in *; try discriminate.
  - econstructor.
    + fold (List.map (@Val V) []). fold (@vals2exprs V []).
      eauto_lr.
    + destruct ms; simpl in *; try discriminate.
      injection H as ?. injection H0 as ?. subst. eauto_lr.
  - destruct ms; simpl in *; try discriminate. injection H as ?. subst.
    rewrite <- Nat.add_assoc. eapply red_rec_cons.
    + eapply H5; try constructor. constructor.
    + injection H2 as ?. injection H3 as ?. injection H4 as ?.
      eapply IHes with (ms := (m1::ms)%list); simpl; auto.
      intros. eauto 10 with lamref.
Qed.

Definition sums (l : list nat) : nat * list nat :=
  (List.fold_right
    (fun n '(s, ls) => let s' := n+s in (s', s::ls)) (0, []) l)%list.

Fixpoint diffs (n : nat) (l : list nat) : list nat :=
  match l with
  | [] => []
  | (n'::l') => n-n' :: diffs n' l'
  end%list.

Lemma diffs_sums l :
  let '(s, ls) := (sums l) in diffs s ls = l.
Proof.
  induction l; simpl; auto.
  destruct sums. simpl. f_equal; auto. lia.
Qed.

Definition last_error {A} (xs : list A) := List.last (List.map Some xs) None.

Definition monotone (ns : list nat) :=
  forall i n n',
    Nth i ns n ->
    Nth (1+i) ns n' ->
    n' <= n.

Lemma mono_le_last i n ns n' :
  monotone ns ->
  Some n' = last_error ns ->
  Nth i ns n ->
  n' <= n.
Proof.
  unfold monotone, last_error.
  intros Hmono Hlast Hnth. generalize dependent n. generalize dependent i.
  induction ns; simpl in *; intros.
  - inversion Hnth.
  - destruct ns.
    + inversion Hnth; subst; simpl in *.
      * injection Hlast as []. auto.
      * inversion H3.
    + inversion Hnth; subst; simpl in *; [transitivity n0|]; eauto_lr.
Qed.

Lemma sum_diffs n n' l :
  monotone (n::l) ->
  Some n' = last_error (n::l) ->
  List.list_sum (diffs n l) = n-n'.
Proof.
  unfold monotone, last_error. revert n.
  induction l; simpl in *; intros n Hmono Hlast.
  - injection Hlast as []. lia.
  - erewrite IHl; eauto_lr.
    + rewrite Nat.add_sub_assoc.
      * f_equal. apply Nat.sub_add. eauto_lr.
      * eapply mono_le_last; eauto_lr.
Qed.

Lemma length_diffs n l :
  List.length (diffs n l) = List.length l.
Proof.
  generalize n.
  induction l; simpl; auto.
Qed.

Lemma Nth_lt_length A i (l : list A) :
  i < List.length l <-> exists x, Nth i l x.
Proof.
  split.
  - revert i. induction l; simpl; intros i Hlt; [lia|].
    destruct i; eauto_lr.
    edestruct IHl; eauto_lr. lia.
  - intros (x&Hnth). induction Hnth; simpl; lia.
Qed.

Corollary Nth_eq_length A B i (l : list A) (l' : list B) :
  List.length l = List.length l' ->
  (exists x, Nth i l x) <-> (exists x, Nth i l' x).
Proof.
  intros. erewrite <- Nth_lt_length. rewrite H. apply Nth_lt_length.
Qed.

Lemma Nth_diffs i n l m :
  monotone (n::l) ->
  Nth i (diffs n l) m <->
    (exists m1 m2, m1 = m + m2 /\ Nth i (n::l) m1 /\ Nth (1+i) (n::l) m2).
Proof.
  unfold monotone. revert i n m. induction l; simpl.
  - split; intros; edestruct_direct; try inversion_Nth_cons_succ; inversion_Nth_nil.
  - split; intros.
    + inversion_Nth_cons.
      * repeat econstructor. rewrite Nat.sub_add; eauto_lr.
      * match goal with
        | [H : Nth _ (diffs _ l) _ |- _] => eapply IHl in H as (?&?&?&?&?)
        end; eauto_lr.
        subst. simpl in *. inversion_Nth_cons_succ. eauto 10 with lamref.
    + edestruct_direct. inversion_Nth_cons_succ. inversion_Nth_cons_2 n a.
      * inversion_Nth_cons. rewrite Nat.add_sub. eauto_lr.
      * econstructor. eapply IHl; eauto_lr.
Qed.

Lemma le_add k l m :
  k = l + m -> m <= k.
Proof.
  lia.
Qed.

Theorem big_red_rec_diff (V : Set) n ms m m' cs c c'
  (es : list (Expr V)) (vs : list (Value V)) :
  Some c = List.head cs ->
  Some m = List.head ms ->
  Some c' = List.last_error cs ->
  Some m' = List.last_error ms ->
  n = List.length es ->
  n = List.length vs ->
  1+n = List.length ms ->
  1+n = List.length cs ->
  (forall i c2 c2',
    Nth i cs c2 ->
    Nth (1+i) cs c2' ->
    exists c, c2 = c + c2' /\
      forall e v m m',
      Nth i es e ->
      Nth i vs v ->
      Nth i ms m ->
      Nth (1+i) ms m' ->
      C[e,m ~~> v,m'|c]) ->
  C[RecE es,m ~~> RecV vs,m'|(c - c') + 1].
Proof.
  intros.
  assert (monotone cs).
  { unfold monotone. intros. edestruct H7 with (i := i) as (?&?&?); eauto_lr; try lia. }
  destruct cs; try discriminate.
  match goal with
  | [H : _ = List.length (_ :: cs) |- _] => simpl in H; injection H as ->
  end.
  simpl in *. injection_on_all_Some. subst_with c.
  rewrite <- sum_diffs with (n := c) (l := cs); auto.
  eapply big_red_rec with (cs := diffs c cs); eauto using length_diffs. intros.
  match goal with
  | [H : Nth _ (diffs _ _) _ |- _] => eapply Nth_diffs in H as (?&?&?&?&?)
  end; auto.
  edestruct H7 with (i := i) as (?&?&?); eauto 10 with lamref.
  match goal with
  | [_ : ?x = ?c1 + ?y, _ : ?x = ?c2 + ?y |- _] =>
    assert (c1 = c2) as ->; [lia|]
  end.
  auto.
Qed.

(*
  intros. subst.
  generalize dependent ms.
  generalize dependent m. generalize dependent m'.
  generalize dependent cs.
  generalize dependent c. generalize dependent c'.
  generalize dependent vs.
  induction es; intros; destruct vs; destruct ms; destruct cs;
    simpl in *; try discriminate.
  - rewrite Nat.add_1_r. econstructor.
    + fold (List.map (@Val V) []). fold (@vals2exprs V []).
      eauto_lr.
    + destruct ms, cs; simpl in *; try discriminate.
      injection H as ?. injection H1 as ?. injection H0 as ?. injection H2 as ?.
      subst. rewrite Nat.sub_diag. eauto_lr.
  - destruct ms, cs; simpl in *; try discriminate.
    injection H as ?. injection H0 as ?. subst.
    edestruct H7 with (i := 0) as (?&?&?); eauto_lr. subst.
    rewrite <- Nat.add_sub_assoc.
    + rewrite <- Nat.add_assoc. eapply red_rec_cons.
      * eauto_lr.
      * injection H4 as ?. injection H6 as ?. injection H5 as ?.
        eapply IHes with (cs := (n0::cs)%list) (ms := (m1::ms)%list); simpl;
          auto.
        intros. edestruct H7 with (i := S i) as (?&?&?); eauto 10 with lamref.
    + eapply mono_le_last; unfold monotone, last_error; eauto_lr; simpl;
        eauto_lr.
      intros. edestruct H7 with (i := 1+i) as (?&?&?); eauto_lr; try lia.
Qed.*)

Theorem big_red_get (V : Set) n m1 m2 c
  (e : Expr V) (vs : list (Value V)) v :
  Nth n vs v ->
  C[e,m1 ~~> RecV vs,m2|c] ->
  C[Get n e,m1 ~~> v,m2|1+c].
Proof.
  solve_by_induction.
Qed.

Theorem big_red_ref (V : Set) l m1 m2 c
  (e : Expr V) (v : Value V) :
  l = new_label m2 ->
  C[e,m1 ~~> v,m2|c] ->
  C[Ref e,m1 ~~> Lab l,(l, Some v)::m2|1+c]%list.
Proof.
  solve_by_induction.
Qed.

Theorem big_red_deref (V : Set) l m1 m2 c
  (e : Expr V) (v : Value V) :
  Lookup l m2 v ->
  C[e,m1 ~~> Lab l,m2|c] ->
  C[Deref e,m1 ~~> v,m2|1+c].
Proof.
  solve_by_induction.
Qed.

Theorem big_red_assign (V : Set) l m1 m2 m3 m4 c1 c2
  (e1 e2 : Expr V) (v : Value V) :
  Assignment l v m3 m4 ->
  C[e1,m1 ~~> Lab l,m2|c1] ->
  C[e2,m2 ~~> v,m3|c2] ->
  C[e1 <- e2,m1 ~~> U_val,m4|c1+c2+1].
Proof.
  solve_by_induction.
Qed.

Theorem big_red_seq (V : Set) m1 m2 m3 c1 c2
  (e1 e2 : Expr V) (v : Value V) :
  C[e1,m1 ~~> U_val,m2|c1] ->
  C[e2,m2 ~~> v,m3|c2] ->
  C[e1 ;; e2,m1 ~~> v,m3|c1+1+c2].
Proof.
  solve_by_induction.
Qed.

Theorem big_red_if_true (V : Set) m1 m2 m3 c1 c2
  (e1 e2 e3 : Expr V) (v : Value V) :
  C[e1,m1 ~~> Bool true,m2|c1] ->
  C[e2,m2 ~~> v,m3|c2] ->
  C[[if]e1[then]e2[else]e3[end],m1 ~~> v,m3|c1+1+c2].
Proof.
  solve_by_induction.
Qed.

Theorem big_red_if_false (V : Set) m1 m2 m3 c1 c2
  (e1 e2 e3 : Expr V) (v : Value V) :
  C[e1,m1 ~~> Bool false,m2|c1] ->
  C[e3,m2 ~~> v,m3|c2] ->
  C[[if]e1[then]e2[else]e3[end],m1 ~~> v,m3|c1+1+c2].
Proof.
  solve_by_induction.
Qed.

Theorem big_red_while_true (V : Set) m1 m2 m3 m4 c1 c2 c3
  (e1 e2 : Expr V) :
  C[e1,m1 ~~> Bool true,m2|c1] ->
  C[e2,m2 ~~> U_val,m3|c2] ->
  C[[while]e1[do]e2[end],m3 ~~> U_val,m4|c3] ->
  C[[while]e1[do]e2[end],m1 ~~> U_val,m4|1+(c1+1+(c2+1+c3))].
Proof.
  eauto using big_red_if_true, big_red_seq with lamref.
Qed.

Theorem big_red_while_false (V : Set) m1 m2 c
  (e1 e2 : Expr V) :
  C[e1,m1 ~~> Bool false,m2|c] ->
  C[[while]e1[do]e2[end],m1 ~~> U_val,m2|1+(c+1)].
Proof.
  rewrite <- Nat.add_0_r with (c+1).
  eauto using big_red_if_false with lamref.
Qed.

(* big step inversions *)
(*
Ltac eauto_lr := eauto with lamref.
Ltac induction_on_cost_red v H :=
  remember (Val v); induction H; subst; simpl; eauto_lr.
Ltac solve_by_induction :=
  intros;
  match goal with
  | [H1 : cost_red _ _ (Val ?v1) _ _,
     H2 : cost_red _ _ (Val ?v2) _ _,
     H3 : cost_red _ _ (Val ?v3) _ _
     |- _] =>
    induction_on_cost_red v1 H1;
    induction_on_cost_red v2 H2;
    induction_on_cost_red v3 H3
  | [H1 : cost_red _ _ (Val ?v1) _ _,
     H2 : cost_red _ _ (Val ?v2) _ _
     |- _] =>
    induction_on_cost_red v1 H1;
    induction_on_cost_red v2 H2
  | [H1 : cost_red _ _ (Val ?v1) _ _ |- _] =>
    induction_on_cost_red v1 H1
  end.
*)(*
Theorem big_red_bneg_inv (V : Set) m1 m2 c
  (e : Expr V) b :
  C[[~] e,m1 ~~> Bool (negb b),m2|1+c] ->
  C[e,m1 ~~> Bool b,m2|c].
Proof.
  intros Hr. remember ([~]e) as e'. remember (1+c) as c'.
  generalize dependent e. generalize dependent c.
  induction_on_cost_red (@Bool V (negb b)) Hr; try discriminate.
  intros. injection Heqc' as ?. subst. inversion H; subst.
  eapply IHHr; auto.
  solve_by_induction.
Qed.
*)