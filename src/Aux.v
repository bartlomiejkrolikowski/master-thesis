Require List.
Import List.ListNotations.
Require Import String.
Require Import ZArith.

Require Import src.LambdaRef.

Definition list_max (l : list nat) : nat :=
  List.fold_right max 0 l.

Lemma list_le_list_max :
  forall l : list nat, List.Forall (fun x => x <= list_max l) l.
Proof.
  intro l. remember (list_max l) as M. generalize dependent M.
  induction l; simpl.
  - constructor.
  - constructor; subst.
    + apply Nat.le_max_l.
    + apply List.Forall_impl with (fun x => x <= list_max l).
      * intros n Hle. apply Nat.max_le_iff. now right.
      * now apply IHl.
Qed.

Definition get_fresh (m : Map) : Label :=
  OfNat (1 + list_max (List.map (fun '(OfNat n) => n) (labels m))).

Lemma map_lt_get_fresh :
  forall (m : Map) (M : nat),
    OfNat M = get_fresh m ->
    List.Forall (fun '(OfNat x) => x < M) (labels m).
Proof.
  intros ? ? HM. unfold get_fresh in HM. simpl in HM.
  injection HM as HM.
  match goal with
  | [H : M = S (list_max ?l) |- _] =>
    assert (HForall : List.Forall (fun n => n <= pred M) l)
  end.
  { rewrite HM. simpl. apply list_le_list_max. }
  apply List.Forall_map in HForall.
  match goal with
  | [H : List.Forall ?f _ |- _] => apply List.Forall_impl with (P := f)
  end.
  - intros [n]. rewrite HM. simpl. apply le_n_S.
  - assumption.
Qed.

Lemma map_neq_get_fresh :
  forall (m : Map),
    List.Forall (fun l => l <> get_fresh m) (labels m).
Proof.
  intros. destruct (get_fresh m) as [M] eqn:Hfresh.
  apply List.Forall_impl with (fun '(OfNat x) => x < M).
  - intros [n] Hlt Heq. injection Heq as Heq. subst.
    now apply Nat.lt_irrefl in Hlt.
  - now apply map_lt_get_fresh.
Qed.

Lemma has_fresh : forall (m : Map), Is_fresh_label (get_fresh m) m.
Proof.
  unfold Is_fresh_label. intros ? HIn.
  apply -> List.Forall_forall in HIn.
  2: apply map_neq_get_fresh.
  now simpl in HIn.
Qed.
