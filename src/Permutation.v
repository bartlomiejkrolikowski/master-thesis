Require Import List.
Import ListNotations.

Definition permutation {A : Type} (l l' : list A) : Prop :=
  forall x : A, In x l <-> In x l'.

Inductive Permutation {A : Type} : list A -> list A -> Prop :=
| Perm_nil : Permutation nil nil
| Perm_cons (x : A) (l l' : list A) :
    Permutation l l' -> Permutation (cons x l) (cons x l')
| Perm_swap (x y : A) (l l' : list A) :
    Permutation l l' -> Permutation (x::y::l)%list (y::x::l')%list
| Perm_trans (l l' l'' : list A) :
    Permutation l l' -> Permutation l' l'' -> Permutation l l''.

Lemma Permutaiton_length A (l l' : list A) :
  Permutation l l' -> length l = length l'.
Proof.
  induction 1; simpl in *; auto. eapply eq_trans; eassumption.
Qed.

Lemma Permutation_refl A (l : list A) : Permutation l l.
Proof.
  induction l; now constructor.
Qed.

Lemma Permutation_symm A (l l' : list A) :
  Permutation l l' -> Permutation l' l.
Proof.
  induction 1; econstructor; eauto.
Qed.
(*
Theorem Permutation_spec A (l l' : list A) :
  length l = length l' ->
  Permutation l l' <-> permutation l l'.

Lemma Permutation_NoDup A (l l' : list A) :
  NoDup l ->
  Permutation l l' ->
  NoDup l'.
Proof.
  intros Hnodup Hperm. generalize dependent l'. induction Hnodup; intros.
  - apply Permutaiton_length in Hperm. destruct l'.
    + constructor.
    + discriminate.
  - inversion Hperm; subst.
    + constructor. apply

Theorem Permutation_spec_nodup A (l l' : list A) :
  NoDup l ->
  NoDup l' ->
  Permutation l l' <-> permutation l l'.
Proof.
  unfold permutation. split.
  - intro Hperm. induction Hperm; simpl.
    + reflexivity.
    + repeat match goal with
      | [H : NoDup (_ :: _) |- _] => inversion H; clear H
      end.
      intro. rewrite IHHperm; auto. reflexivity.
    + repeat match goal with
      | [H : NoDup (_ :: _) |- _] => inversion H; clear H
      end.
      intro. rewrite IHHperm; auto. do 2 rewrite <- or_assoc.
      erewrite (or_comm (_ = _) (_ = _)). reflexivity.
    + intro. etransitivity.
     rewrite IHHperm; auto. do 2 rewrite <- or_assoc.
  - generalize dependent l'. induction l.
    + destruct l'.
      * constructor.
      * unfold permutation. simpl. intros. exfalso. eapply H1. eauto.
    + destruct l'.
      * unfold permutation. simpl. intros. exfalso. eapply H1. eauto.
      * unfold permutation. simpl.
Qed.
*)