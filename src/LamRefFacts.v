Require Arith.
Require Import Lia.
Require List.
Import List.ListNotations.
Require Import String.
Require Import ZArith.

Require Import src.LambdaRef.
Require Import src.Tactics.

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

Fixpoint map_v_ext (V V' : Set) (f g : V -> V') v {struct v} :
  (forall x, f x = g x) ->
  map_v f v = map_v g v
with map_e_ext (V V' : Set) (f g : V -> V') e {struct e} :
  (forall x, f x = g x) ->
  map_e f e = map_e g e.
Proof.
  - destruct v; simpl; trivial; intro Hext; f_equal; auto.
    + revert l. fix Hind 1. destruct l; simpl; f_equal; auto.
    + apply map_e_ext. intros. destruct x; simpl; f_equal. auto.
  - destruct e; simpl; intro; f_equal; auto.
    revert l. fix Hind 1. destruct l; simpl; f_equal; auto.
Qed.

Fixpoint map_v_map_v (V V' V'' : Set) (f : V' -> V'') (g : V -> V') v {struct v} :
  map_v f (map_v g v) = map_v (fun x => f (g x)) v
with map_e_map_e (V V' V'' : Set) (f : V' -> V'') (g : V -> V') e {struct e} :
  map_e f (map_e g e) = map_e (fun x => f (g x)) e.
Proof.
  - destruct v; simpl; trivial; f_equal.
    + revert l. fix Hind 1. destruct l; simpl; f_equal; auto.
    + erewrite map_e_ext with (f := option_map (fun x => f (g x)));
        [|destruct x]; auto.
  - destruct e; simpl; f_equal; auto.
    + revert l. fix Hind 1. destruct l; simpl; f_equal; auto.
Qed.

Lemma map_v_closed_value (V V' : Set) (f : V -> V') v :
  is_closed_value v ->
  is_closed_value (map_v f v).
Proof.
  unfold is_closed_value, is_limited_value.
  intros [v' ->]. exists v'. rewrite map_v_map_v.
  apply map_v_ext. intros [].
Qed.

Lemma map_e_closed_expr (V V' : Set) (f : V -> V') e :
  is_closed_expr e ->
  is_closed_expr (map_e f e).
Proof.
  unfold is_closed_expr, is_limited_expr.
  intros [e' ->]. exists e'. rewrite map_e_map_e.
  apply map_e_ext. intros [].
Qed.

Lemma map_v_same_on_closed (V V' : Set) (f g : V -> V') v :
  is_closed_value v ->
  map_v f v = map_v g v.
Proof.
  unfold is_closed_value, is_limited_expr.
  intros [v' ->]. repeat rewrite map_v_map_v.
  apply map_v_ext. intros [].
Qed.

Lemma map_e_same_on_closed (V V' : Set) (f g : V -> V') e :
  is_closed_expr e ->
  map_e f e = map_e g e.
Proof.
  unfold is_closed_value, is_limited_expr.
  intros [e' ->]. repeat rewrite map_e_map_e.
  apply map_e_ext. intros [].
Qed.

Corollary map_v_shift_closed (V : Set) (f : V -> option V) v :
  is_closed_value v ->
  map_v f v = shift_v v.
Proof.
  unfold shift_v. apply map_v_same_on_closed.
Qed.

Corollary map_e_shift_closed (V : Set) (f : V -> option V) e :
  is_closed_expr e ->
  map_e f e = shift_e e.
Proof.
  unfold shift_e. apply map_e_same_on_closed.
Qed.

Definition in_range [A B] (f : A -> B) (y : B) :=
  exists x, y = f x.

Ltac prove_is_limited :=
  unfold is_limited_value, is_limited_expr, in_range; repeat intros (?&->);
  unshelve eexists; [econstructor|simpl; reflexivity]; eassumption.

Fact is_limited_U_val V A f :
  is_limited_value A f (@U_val V).
Proof.
  prove_is_limited.
Qed.
Global Hint Resolve is_limited_U_val : is_closed_db.

Fact is_limited_Int V i A f :
  is_limited_value A f (@Int V i).
Proof.
  prove_is_limited.
Qed.
Global Hint Resolve is_limited_Int : is_closed_db.

Fact is_limited_Bool V b A f :
  is_limited_value A f (@Bool V b).
Proof.
  prove_is_limited.
Qed.
Global Hint Resolve is_limited_Bool : is_closed_db.

Fact is_limited_Lab V l A f :
  is_limited_value A f (@Lab V l).
Proof.
  prove_is_limited.
Qed.
Global Hint Resolve is_limited_Lab : is_closed_db.

Fact is_limited_RecV V (vs : list (Value V)) A f :
  List.Forall (is_limited_value A f) vs ->
  is_limited_value A f (RecV vs).
Proof.
  unfold is_limited_value. intros Hlimited. induction Hlimited.
  - now exists (RecV []).
  - destruct H as (v'&->). destruct IHHlimited as (vs'&Hvs').
    destruct vs'; try discriminate. simpl in Hvs'. injection Hvs' as ->.
    eexists (RecV (v'::_)). simpl. reflexivity.
Qed.
Global Hint Resolve is_limited_RecV : is_closed_db.

Fact is_limited_Lam V A f (e1 : Expr (inc_set V)) :
  is_limited_expr (inc_set A) (option_map f) e1 ->
  is_limited_value A f (Lam e1).
Proof.
  prove_is_limited.
Qed.
Global Hint Resolve is_limited_Lam : is_closed_db.

Fact is_limited_Val V (v : Value V) A f :
  is_limited_value A f v ->
  is_limited_expr A f (Val v).
Proof.
  prove_is_limited.
Qed.
Global Hint Resolve is_limited_Val : is_closed_db.

Fact is_limited_App V (e1 e2 : Expr V) A f :
  is_limited_expr A f e1 ->
  is_limited_expr A f e2 ->
  is_limited_expr A f (e1 <* e2).
Proof.
  prove_is_limited.
Qed.
Global Hint Resolve is_limited_App : is_closed_db.

Fact is_limited_UnOp V k (e1 : Expr V) A f :
  is_limited_expr A f e1 ->
  is_limited_expr A f (UnOp k e1).
Proof.
  prove_is_limited.
Qed.
Global Hint Resolve is_limited_UnOp : is_closed_db.

Fact is_limited_BinOp V k (e1 e2 : Expr V) A f :
  is_limited_expr A f e1 ->
  is_limited_expr A f e2 ->
  is_limited_expr A f (BinOp k e1 e2).
Proof.
  prove_is_limited.
Qed.
Global Hint Resolve is_limited_BinOp : is_closed_db.

Fact is_limited_RecE V (es : list (Expr V)) A f :
  List.Forall (is_limited_expr A f) es ->
  is_limited_expr A f (RecE es).
Proof.
  unfold is_limited_expr. intros Hlimited. induction Hlimited.
  - now exists (RecE []).
  - destruct H as (e'&->). destruct IHHlimited as (es'&Hes').
    destruct es'; try discriminate. simpl in Hes'. injection Hes' as ->.
    eexists (RecE (e'::_)). simpl. reflexivity.
Qed.
Global Hint Resolve is_limited_RecE : is_closed_db.

Fact is_limited_Get V n (e1 : Expr V) A f :
  is_limited_expr A f e1 ->
  is_limited_expr A f (Get n e1).
Proof.
  prove_is_limited.
Qed.
Global Hint Resolve is_limited_Get : is_closed_db.

Fact is_limited_Ref V (e1 : Expr V) A f :
  is_limited_expr A f e1 ->
  is_limited_expr A f (Ref e1).
Proof.
  prove_is_limited.
Qed.
Global Hint Resolve is_limited_Ref : is_closed_db.

Fact is_limited_NewArray V (e1 : Expr V) A f :
  is_limited_expr A f e1 ->
  is_limited_expr A f (NewArray e1).
Proof.
  prove_is_limited.
Qed.
Global Hint Resolve is_limited_NewArray : is_closed_db.

Fact is_limited_Deref V (e1 : Expr V) A f :
  is_limited_expr A f e1 ->
  is_limited_expr A f (Deref e1).
Proof.
  prove_is_limited.
Qed.
Global Hint Resolve is_limited_Deref : is_closed_db.

Fact is_limited_Shift V (e1 e2 : Expr V) A f :
  is_limited_expr A f e1 ->
  is_limited_expr A f e2 ->
  is_limited_expr A f (Shift e1 e2).
Proof.
  prove_is_limited.
Qed.
Global Hint Resolve is_limited_Shift : is_closed_db.

Fact is_limited_Assign V (e1 e2 : Expr V) A f :
  is_limited_expr A f e1 ->
  is_limited_expr A f e2 ->
  is_limited_expr A f (Assign e1 e2).
Proof.
  prove_is_limited.
Qed.
Global Hint Resolve is_limited_Assign : is_closed_db.

Fact is_limited_Free V (e1 : Expr V) A f :
  is_limited_expr A f e1 ->
  is_limited_expr A f (Free e1).
Proof.
  prove_is_limited.
Qed.
Global Hint Resolve is_limited_Free : is_closed_db.

Fact is_limited_Seq V (e1 e2 : Expr V) A f :
  is_limited_expr A f e1 ->
  is_limited_expr A f e2 ->
  is_limited_expr A f (Seq e1 e2).
Proof.
  prove_is_limited.
Qed.
Global Hint Resolve is_limited_Seq : is_closed_db.

Fact is_limited_If V (e1 e2 e3 : Expr V) A f :
  is_limited_expr A f e1 ->
  is_limited_expr A f e2 ->
  is_limited_expr A f e3 ->
  is_limited_expr A f (If e1 e2 e3).
Proof.
  prove_is_limited.
Qed.
Global Hint Resolve is_limited_If : is_closed_db.

Fact is_limited_While V (e1 e2 : Expr V) A f :
  is_limited_expr A f e1 ->
  is_limited_expr A f e2 ->
  is_limited_expr A f (While e1 e2).
Proof.
  prove_is_limited.
Qed.
Global Hint Resolve is_limited_While : is_closed_db.

Fact is_limited_Var V A f x :
  in_range f x ->
  is_limited_value A f (@Var V x).
Proof.
  prove_is_limited.
Qed.
Global Hint Resolve is_limited_Var : is_closed_db.

Ltac prove_in_range := prove_is_limited.

Fact in_range_None A B f :
  @in_range (inc_set A) (inc_set B) (option_map f) None.
Proof.
  prove_in_range.
Qed.
Global Hint Resolve in_range_None : is_closed_db.

Fact in_range_Some A B f x :
  in_range f x ->
  @in_range (inc_set A) (inc_set B) (option_map f) (Some x).
Proof.
  prove_in_range.
Qed.
Global Hint Resolve in_range_Some : is_closed_db.

Fact is_limited_shift_v A B f v :
  is_limited_value A f v ->
  @is_limited_value (inc_set A) (inc_set B) (option_map f) (shift_v v).
Proof.
  unfold is_limited_value. intros (x&->). exists (shift_v x).
  unfold shift_v, option_map. repeat rewrite -> map_v_map_v.
  reflexivity.
Qed.
Global Hint Resolve is_limited_shift_v : is_closed_db.

Fact is_limited_shift_e A B f e :
  is_limited_expr A f e ->
  @is_limited_expr (inc_set A) (inc_set B) (option_map f) (shift_e e).
Proof.
  unfold is_limited_expr. intros (x&->). exists (shift_e x).
  unfold shift_e, option_map. repeat rewrite -> map_e_map_e.
  reflexivity.
Qed.
Global Hint Resolve is_limited_shift_e : is_closed_db.

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

Fixpoint bind_v_map_v_l (V V' V'' : Set) (f : V' -> V'') (g : V -> Value V') v {struct v} :
  map_v f (bind_v g v) = bind_v (fun x => map_v f (g x)) v
with bind_e_map_e_l (V V' V'' : Set) (f : V' -> V'') (g : V -> Value V') e {struct e} :
  map_e f (bind_e g e) = bind_e (fun x => map_v f (g x)) e.
Proof.
  - destruct v; simpl; trivial; f_equal.
    + revert l. fix Hind 1. destruct l; simpl; f_equal; auto.
    + erewrite bind_e_ext with (f := liftS (fun x => map_v f (g x)));
        [|destruct x]; eauto.
      simpl. unfold shift_v. do 2 rewrite map_v_map_v. auto.
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

Fixpoint bind_v_liftS_shift (A B : Set) (f : A -> Value B) (v : Value A) {struct v} :
  bind_v (liftS f) (shift_v v) = bind_v (fun x => shift_v (f x)) v
with bind_e_liftS_shift (A B : Set) (f : A -> Value B) (e : Expr A) {struct e} :
  bind_e (liftS f) (shift_e e) = bind_e (fun x => shift_v (f x)) e.
Proof.
  - destruct v; cbn; trivial; f_equal.
    + revert l. fix Hind 1. destruct l; simpl; f_equal; auto.
    + erewrite bind_e_ext with (f := liftS (fun x => shift_v (f x))).
      * apply bind_e_map_e.
      * destruct x; reflexivity.
  - destruct e; cbn; f_equal; eauto.
    revert l. fix Hind 1. destruct l; simpl; f_equal; auto.
Qed.

Theorem bind_v_liftS_shift_swap (A B : Set) (f : A -> Value B) (v : Value A) :
  bind_v (liftS f) (shift_v v) = shift_v (bind_v f v).
Proof.
  unfold shift_v. rewrite bind_v_map_v, bind_v_map_v_l. auto using bind_v_ext.
Qed.

Theorem bind_e_liftS_shift_swap (A B : Set) (f : A -> Value B) (e : Expr A) :
  bind_e (liftS f) (shift_e e) = shift_e (bind_e f e).
Proof.
  unfold shift_e. rewrite bind_e_map_e, bind_e_map_e_l. auto using bind_e_ext.
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

Ltac discriminate_red_Val :=
  match goal with
  | [ H : red (Val _) _ _ _ |- _ ] => inversion H
  end.

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

Fact cost_red_0 :
  forall V m m' (e e' : Expr V) c,
    c = 0 ->
    C[e, m ~~> e', m' | c] ->
    e = e' /\ m = m'.
Proof.
  intros. destruct H0; try discriminate. auto.
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

Theorem big_red_new_array (V : Set) l m1 m2 m3 c
  (e : Expr V) i :
  (i >= 0)%Z ->
  (m3, l) = alloc_array (Z.to_nat i) m2 ->
  C[e,m1 ~~> Int i,m2|c] ->
  C[NewArray e,m1 ~~> Lab l,m3|1+c].
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

Theorem big_red_shift (V : Set) m1 m2 m3 c1 c2
  (e1 e2 : Expr V) n i :
  (i >= 0)%Z ->
  C[e1,m1 ~~> Lab (OfNat n),m2|c1] ->
  C[e2,m2 ~~> Int i,m3|c2] ->
  C[Shift e1 e2,m1 ~~> Lab (OfNat (n + Z.to_nat i)),m3|1+c1+c2].
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

Theorem big_red_free (V : Set) l m1 m2 m3 c
  (e : Expr V) :
  Dealloc l m2 m3 ->
  C[e,m1 ~~> Lab l,m2|c] ->
  C[Free e,m1 ~~> U_val,m3|1+c].
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

Theorem big_red_app_inv (V : Set) m1 m4 c
  (e1 e2 : Expr V) (v : Value V) :
  C[e1 <* e2,m1 ~~> v,m4|c] ->
  exists c1 e1' m2 c2 (v2 : Value V) m3 c3,
  C[e1,m1 ~~> -\ e1',m2|c1] /\
  C[e2,m2 ~~>     v2,m3|c2] /\
  C[subst_e e1' v2,m3 ~~> v,m4|c3] /\
  c = c1 + c2 + 1 + c3.
Proof.
  remember (e1 <* e2) as e eqn:He. remember (Val v) as ev eqn:Hev. intros Hred.
  revert e1 e2 v He Hev. induction Hred; intros ? ? ? ->; try discriminate.
  intros ->. inversion H; subst.
  - eauto 11 with lamref.
  - destruct (IHHred _ _ _ eq_refl eq_refl) as (?&?&?&?&?&?&?&?&?&?&->).
    eauto 12 with lamref.
  - destruct (IHHred _ _ _ eq_refl eq_refl)
      as (?&?&?&?&?&?&?&(<-&->&->)%cost_red_value&?&?&->).
    eauto 12 with lamref.
Qed.
