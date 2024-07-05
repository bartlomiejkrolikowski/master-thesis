Require Import List.
Import ListNotations.

Require Import Lia.

Inductive Interweave {A} : list A -> list A -> list A -> Prop :=
| Interweave_nil : Interweave [] [] []
| Interweave_cons_l x xs ys zs :
  Interweave xs ys zs -> Interweave (x::xs) ys (x::zs)
| Interweave_cons_r y xs ys zs :
  Interweave xs ys zs -> Interweave xs (y::ys) (y::zs).

Fact Interweave_nil_l A (l : list A) : Interweave [] l l.
Proof.
  induction l; constructor. auto.
Qed.

Fact Interweave_symm A (xs ys zs : list A) :
  Interweave ys xs zs -> Interweave xs ys zs.
Proof.
  intros Hinter. induction Hinter; constructor; auto.
Qed.

Fact Interweave_nil_r A (l : list A) : Interweave l [] l.
Proof.
  auto using Interweave_symm, Interweave_nil_l.
Qed.

Lemma Interweave_nil_l_inv A (ys zs : list A) :
  Interweave [] ys zs -> ys = zs.
Proof.
  intros Hinter. remember [] as xs eqn:Hxs. induction Hinter; f_equal; auto.
  discriminate.
Qed.

Lemma Interweave_nil_r_inv A (xs zs : list A) :
  Interweave xs [] zs -> xs = zs.
Proof.
  intros. auto using Interweave_nil_l_inv, Interweave_symm.
Qed.

Lemma Interweave_nil_inv A (xs ys : list A) :
  Interweave xs ys [] -> xs = [] /\ ys = [].
Proof.
  inversion 1. auto.
Qed.

Fact Interweave_assoc_l A (xs ys zs xys xyzs : list A) :
  Interweave xs ys xys ->
  Interweave xys zs xyzs ->
  exists yzs, Interweave ys zs yzs /\
    Interweave xs yzs xyzs.
Proof.
  intros Hxy Hxyz. generalize dependent ys. generalize dependent xs.
  induction Hxyz; intros.
  - apply Interweave_nil_inv in Hxy as [-> ->]. eexists. split; constructor.
  - inversion Hxy; subst.
    + edestruct IHHxyz as (?&?&?).
      * eassumption.
      * eexists. split; [|constructor]; eassumption.
    + edestruct IHHxyz as (?&?&?).
      * eassumption.
      * eexists. split; constructor; eassumption.
  - edestruct IHHxyz as (?&?&?).
    + eassumption.
    + eexists. split; constructor; eassumption.
Qed.

Fact Interweave_assoc_r A (xs ys zs yzs xyzs : list A) :
  Interweave ys zs yzs ->
  Interweave xs yzs xyzs ->
  exists xys, Interweave xs ys xys /\
    Interweave xys zs xyzs.
Proof.
  intros Hyz Hxyz. apply Interweave_symm in Hyz, Hxyz.
  destruct Interweave_assoc_l with A zs ys xs yzs xyzs as (yxs&Hys&Hzyx);
    eauto using Interweave_symm.
Qed.

Fact Interweave_length A (xs ys zs : list A) :
  Interweave xs ys zs ->
  length zs = length xs + length ys.
Proof.
  intros Hinter. induction Hinter; simpl; try lia.
Qed.
