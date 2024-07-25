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

Fact Interweave_comm A (xs ys zs : list A) :
  Interweave ys xs zs -> Interweave xs ys zs.
Proof.
  intros Hinter. induction Hinter; constructor; auto.
Qed.

Fact Interweave_nil_r A (l : list A) : Interweave l [] l.
Proof.
  auto using Interweave_comm, Interweave_nil_l.
Qed.

Fact Interweave_app A (xs ys : list A) : Interweave xs ys (xs ++ ys).
Proof.
  induction xs; simpl.
  - apply Interweave_nil_l.
  - constructor. assumption.
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
  intros. auto using Interweave_nil_l_inv, Interweave_comm.
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
  intros Hyz Hxyz. apply Interweave_comm in Hyz, Hxyz.
  destruct Interweave_assoc_l with A zs ys xs yzs xyzs as (yxs&Hys&Hzyx);
    eauto using Interweave_comm.
Qed.

Fact Interweave_length A (xs ys zs : list A) :
  Interweave xs ys zs ->
  length zs = length xs + length ys.
Proof.
  intros Hinter. induction Hinter; simpl; try lia.
Qed.

Lemma in_Interweave_or A x (xs ys zs : list A) :
  Interweave xs ys zs ->
  In x zs -> In x xs \/ In x ys.
Proof.
  intros Hinter Hin. induction Hinter; simpl in *.
  - auto.
  - destruct Hin; auto. destruct IHHinter; auto.
  - destruct Hin; auto. destruct IHHinter; auto.
Qed.

Lemma in_or_Interweave A x (xs ys zs : list A) :
  Interweave xs ys zs ->
  In x xs \/ In x ys -> In x zs.
Proof.
  intros Hinter Hor. induction Hinter; simpl in *.
  - destruct Hor; auto.
  - destruct Hor as [[? | ?] | ?]; auto.
  - destruct Hor as [? | [? | ?]]; auto.
Qed.

Lemma in_Interweave_iff A x (xs ys zs : list A) :
  Interweave xs ys zs ->
  In x zs <-> In x xs \/ In x ys.
Proof.
  intros. split; eauto using in_Interweave_or, in_or_Interweave.
Qed.

Lemma map_Interweave A B (f : A -> B) (xs ys zs : list A) :
  Interweave xs ys zs ->
  Interweave (map f xs) (map f ys) (map f zs).
Proof.
  intros Hinter. induction Hinter; simpl; constructor; assumption.
Qed.

Lemma map_eq_Interweave_l A B (f : A -> B) (zs : list A) (xs' ys' : list B) :
  Interweave xs' ys' (map f zs) ->
  exists xs ys,
    xs' = map f xs /\ ys' = map f ys /\ Interweave xs ys zs.
Proof.
  intros Hinter. remember (map f zs) as zs' eqn:Hzs'. generalize dependent zs.
  induction Hinter; intros; symmetry in Hzs'.
  - apply map_eq_nil in Hzs' as ->. exists [], []. simpl. repeat constructor.
  - apply map_eq_cons in Hzs' as (?&?&->&<-&<-).
    edestruct IHHinter as (?&?&->&->&?); auto.
    eexists (_ :: _), _. simpl. repeat constructor. assumption.
  - apply map_eq_cons in Hzs' as (?&?&->&<-&<-).
    edestruct IHHinter as (?&?&->&->&?); auto.
    eexists _, (_ :: _). simpl. repeat constructor. assumption.
Qed.

Lemma map_eq_Interweave_r A B (f : A -> B) (xs ys : list A) (zs' : list B) :
  Interweave (map f xs) (map f ys) zs' ->
  exists zs,
    zs' = map f zs /\ Interweave xs ys zs.
Proof.
  intros Hinter.
  remember (map f xs) as xs' eqn:Hxs'. remember (map f ys) as ys' eqn:Hys'.
  generalize dependent ys. generalize dependent xs.
  induction Hinter; intros.
  - symmetry in Hxs', Hys'. apply map_eq_nil in Hxs' as ->, Hys' as ->.
    exists []. simpl. repeat constructor.
  - symmetry in Hxs'. subst ys. apply map_eq_cons in Hxs' as (?&?&->&<-&<-).
    edestruct IHHinter as (?&->&?); auto.
    eexists (_ :: _). simpl. repeat constructor. assumption.
  - subst xs. symmetry in Hys'. apply map_eq_cons in Hys' as (?&?&->&<-&<-).
    edestruct IHHinter as (?&->&?); auto.
    eexists (_ :: _). simpl. repeat constructor. assumption.
Qed.
