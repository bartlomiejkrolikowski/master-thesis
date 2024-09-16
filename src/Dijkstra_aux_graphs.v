Require List.
Import List.ListNotations.
Require Import String.
Require Import ZArith.

Require Import src.LambdaRef.
Require Import src.LamRefFacts.
Require Import src.LambdaAssertions_credits_perm.
Require Import src.LambdaTotalTriple_credits_perm.
Require Import src.LamRefLogicFactsTotal_credits_perm.
Require Import Lia.
Require Import src.Tactics.
Require Import src.SA_Tactics.
Require Import src.Interweave.

Require Import graphs.Graphs.

Definition is_elem_list {A} (P : A -> Prop) (L : list A) :=
  forall x, List.In x L <-> P x.

Definition is_elem_weighted_list {A B} (P : A -> Prop) (W : A -> B) (L : list (A * B)) :=
  forall x w, List.In (x,w) L <-> (P x /\ w = W x).

Definition is_elem_unique_list {A} (P : A -> Prop) (L : list A) :=
  is_elem_list P L /\ List.NoDup L.

Definition is_elem_weighted_unique_list {A B} (P : A -> Prop) (W : A -> B) (L : list (A * B)) :=
  is_elem_weighted_list P W L /\ List.NoDup (List.map fst L).

Definition is_set_size {A} (P : A -> Prop) (n : nat) : Prop :=
  exists l, is_elem_unique_list P l /\ List.length l = n.

Fact empty_set_size A :
  @is_set_size A empty 0.
Proof.
  unfold is_set_size, is_elem_unique_list, is_elem_list, empty.
  exists nil. simpl. intuition constructor.
Qed.

Fact single_set_size A x :
  @is_set_size A (single x) 1.
Proof.
  unfold is_set_size, is_elem_unique_list, is_elem_list, single.
  exists [x]%list. simpl. intuition (repeat econstructor); tauto.
Qed.

Fact equiv_elem_list A P Q L :
  @set_equiv A P Q ->
  is_elem_list P L ->
  is_elem_list Q L.
Proof.
  unfold set_equiv, is_elem_list.
  intros Hequiv Hlist x. rewrite <- Hequiv, Hlist. reflexivity.
Qed.

Fact equiv_elem_unique_list A P Q L :
  @set_equiv A P Q ->
  is_elem_unique_list P L ->
  is_elem_unique_list Q L.
Proof.
  unfold is_elem_unique_list. intros Hequiv (Hlist&Hnodup).
  split; eauto using equiv_elem_list.
Qed.

Fact equiv_set_size A P Q n :
  @set_equiv A P Q ->
  is_set_size P n ->
  is_set_size Q n.
Proof.
  unfold is_set_size. intros ? (?&?&?). eauto using equiv_elem_unique_list.
Qed.

Lemma is_elem_unique_list_unique_length A (P : A -> Prop) L1 L2 :
  is_elem_unique_list P L1 ->
  is_elem_unique_list P L2 ->
  List.length L1 = List.length L2.
Proof.
  unfold is_elem_unique_list, is_elem_list. revert P L2.
  induction L1; simpl; intros P L2 (Helem1&Hnodup1) (Helem2&Hnodup2).
  - destruct L2; simpl; auto. exfalso. eapply Helem1, Helem2. simpl. auto.
  - assert (List.In a L2) as Hin.
    { apply Helem2, Helem1. auto. }
    apply List.in_split in Hin as (?&?&->). rewrite List.app_length. simpl.
    rewrite Nat.add_succ_r, <- List.app_length. f_equal.
    apply IHL1 with (P := fun x => x <> a /\ P x).
    + inversion Hnodup1. unfold not in *. split; auto. intros.
      rewrite <- Helem1. split.
      * intros. split; auto. intros ->. auto.
      * intros (?&[-> | ?]); [exfalso|]; auto.
    + apply List.NoDup_remove in Hnodup2 as (?&?). unfold not in *. split; auto.
      intros. rewrite <- Helem2. repeat rewrite -> List.in_app_iff in *. simpl.
      intuition; subst; exfalso; eauto.
Qed.

Corollary is_set_size_unique A (P : A -> Prop) (n m : nat) :
  is_set_size P n ->
  is_set_size P m ->
  n = m.
Proof.
  unfold is_set_size. intros (?&?&<-) (?&?&<-).
  eapply is_elem_unique_list_unique_length; eauto.
Qed.

Definition nat2value {V} (n : nat) : Value V := Int (Z.of_nat n).
Definition pair2Value {A B V} (f : A -> Value V) (g : B -> Value V) '(x,y) : Value V :=
  RecV [f x; g y].

Definition nats2values {V} (L : list nat) : list (Value V) :=
  List.map (fun t => Int (Z.of_nat t)) L.
Definition nat_pairs2values {V} (L : list (nat * nat)) : list (Value V) :=
  List.map (fun '(x,w) => RecV [Int (Z.of_nat x); Int (Z.of_nat w)]) L.

Definition is_max_label {A} (g : wgraph A) (C : nat) :=
  max_cost (uncurry (E g)) (uncurry (W g)) C.

Definition is_nat_function {V} (f : nat -> option nat) '(OfNat n0) : StateAssertion V :=
  fun c m =>
    forall n n', f n = Some n' <-> Lookup (OfNat (n0+n)) m (Int (Z.of_nat n')).

Definition is_nil_b {A} (L : list A) : bool :=
  match L with
  | nil => true
  | _ => false
  end.

Definition is_init_range (P : nat -> Prop) : Prop :=
  forall x, P x -> forall y, y < x -> P y.

Definition init_range (x : nat) : nat -> Prop := gt x.

Fact init_range_is_init x :
  is_init_range (init_range x).
Proof.
  unfold is_init_range, init_range. lia.
Qed.

Fact init_range_seq n x :
  init_range n x <-> List.In x (List.seq 0 n).
Proof.
  unfold init_range. rewrite List.in_seq. lia.
Qed.

Fact init_range_size n :
  is_set_size (init_range n) n.
Proof.
  unfold is_set_size, is_init_range, is_elem_unique_list, is_elem_list.
  exists (List.seq 0 n). rewrite List.seq_length.
  split_all; auto using List.seq_NoDup. intros. symmetry. apply init_range_seq.
Qed.

Fact init_range_subrange P x :
  is_init_range P ->
  P x ->
  is_subset (init_range (S x)) P.
Proof.
  unfold is_subset, is_init_range, init_range. intros His_init HP y Hgt.
  assert (y < x \/ y = x) as [Hlt | ->] by lia; try assumption.
  eapply His_init; eassumption.
Qed.

Inductive is_filtered_list {A} (P : A -> Prop) : list A -> list A -> Prop :=
| is_filtered_nil : is_filtered_list P [] []
| is_filtered_cons_true x L L' :
  P x ->
  is_filtered_list P L L' ->
  is_filtered_list P (x::L) (x::L')
| is_filtered_cons_false x L L' :
  ~ P x ->
  is_filtered_list P L L' ->
  is_filtered_list P (x::L) L'.

Fact exists_filtered A P L :
  (forall x, Decidable.decidable (P x)) ->
  exists L', @is_filtered_list A P L L'.
Proof.
  unfold Decidable.decidable. intros Hdec. induction L.
  - eexists. econstructor.
  - destruct IHL as (L'&?). edestruct Hdec; eexists; econstructor; eassumption.
Qed.

Fact filtered_in A P L L' x :
  @is_filtered_list A P L L' ->
  (List.In x L' <-> P x /\ List.In x L).
Proof.
  intros Hfiltered. induction Hfiltered; simpl; intuition; subst; tauto.
Qed.

Fact filtered_nodup A P L L' :
  @is_filtered_list A P L L' ->
  List.NoDup L ->
  List.NoDup L'.
Proof.
  intros Hfiltered Hnodup. induction Hfiltered.
  - assumption.
  - inversion Hnodup. constructor; auto. rewrite filtered_in; eauto. tauto.
  - inversion Hnodup. auto.
Qed.

Fact filtered_length A P L L' :
  @is_filtered_list A P L L' ->
  List.length L' <= List.length L.
Proof.
  intros Hfiltered. induction Hfiltered; simpl; lia.
Qed.

Fact subset_elem_list A P P' L L' :
  is_filtered_list P' L L' ->
  is_elem_list P L ->
  @is_subset A P' P ->
  is_elem_list P' L'.
Proof.
  unfold is_elem_list, is_subset. intros Hfiltered Hlist Hsubset x.
  rewrite filtered_in; eauto. rewrite Hlist. intuition.
Qed.

Fact subset_elem_unique_list A P P' L L' :
  is_filtered_list P' L L' ->
  is_elem_unique_list P L ->
  @is_subset A P' P ->
  is_elem_unique_list P' L'.
Proof.
  unfold is_elem_unique_list. intros ? (?&?) ?.
  eauto using subset_elem_list, filtered_nodup.
Qed.

Fact subset_size A P P' n :
  (forall x, Decidable.decidable (P' x)) ->
  is_set_size P n ->
  @is_subset A P' P ->
  exists n', n' <= n /\ is_set_size P' n'.
Proof.
  unfold is_set_size. intros Hdec (L&Hunique&<-) Hsubset.
  specialize exists_filtered with A P' L as (L'&Hfiltered);
    eauto 7 using filtered_length, subset_elem_unique_list.
Qed.

Fact subset_size_le A P P' n n' :
  (forall x, Decidable.decidable (P' x)) ->
  is_set_size P n ->
  is_set_size P' n' ->
  @is_subset A P' P ->
  n' <= n.
Proof.
  eintros Hdec Hsize1 Hsize2 (n''&Hle&Hsize3)%subset_size; eauto.
  rewrite (is_set_size_unique _ _ _ _ Hsize2 Hsize3). assumption.
Qed.

Fact init_range_lt_size P n x :
  is_init_range P ->
  is_set_size P n ->
  P x ->
  x < n.
Proof.
  eintros Hrng Hsize Hsubset%init_range_subrange%subset_size_le;
    eauto using init_range_size.
  unfold Decidable.decidable, init_range. lia.
Qed.

Fact max_label_unique A g C C' :
  @is_max_label A g C ->
  is_max_label g C' ->
  C = C'.
Proof.
  unfold is_max_label. apply max_cost_unique.
Qed.

Definition fun_of_list {A} (L : list (option A)) : nat -> option A :=
  fun i => List.nth i L None.

Definition list_of_f {A B} (f : A -> B) (L : list B) : Prop :=
  exists L', L = List.map f L'.

Definition is_nat_fun_of_val_list {V}
  (L : list (option (Value V))) (f : nat -> option nat) : Prop :=
  list_of_f (fun x => Some (Int x)) L /\
  forall i n, fun_of_list L i = Some (Int (Z.of_nat n)) <-> f i = Some n.

Lemma decidable_in A L x :
  (forall x y, Decidable.decidable (x = y :> A)) ->
  Decidable.decidable (@List.In A x L).
Proof.
  unfold Decidable.decidable. induction L; firstorder.
Qed.

Lemma decidable_if_elem_list A (P : A -> Prop) L x :
  (forall x y, Decidable.decidable (x = y :> A)) ->
  is_elem_list P L ->
  Decidable.decidable (P x).
Proof.
  unfold Decidable.decidable, is_elem_list. intros Hdec_eq <-.
  apply decidable_in. unfold Decidable.decidable. assumption.
Qed.

Lemma decidable_if_finite A (P : A -> Prop) n x :
  (forall x y, Decidable.decidable (x = y :> A)) ->
  is_set_size P n ->
  Decidable.decidable (P x).
Proof.
  unfold is_set_size, is_elem_unique_list. intros Hdec_eq (?&(?&?)&?).
  eapply decidable_if_elem_list; eassumption.
Qed.

Lemma decidable_exists_in A L :
  Decidable.decidable (exists x, @List.In A x L).
Proof.
  unfold Decidable.decidable. destruct L as [|x L]; simpl.
  - firstorder.
  - eauto.
Qed.

Lemma decidable_exists_if_elem_list A (P : A -> Prop) L :
  is_elem_list P L ->
  Decidable.decidable (exists x, P x).
Proof.
  unfold Decidable.decidable, is_elem_list. intros Hlist.
  destruct decidable_exists_in with A L as [(?&?) | ?].
  - rewrite Hlist in *. eauto.
  - right. intros (?&?). rewrite <- Hlist in *. eauto.
Qed.

Lemma decidable_neighbourhood A (g : graph A) P L v :
  (forall x y, Decidable.decidable (x = y :> A)) ->
  (forall v, Decidable.decidable (V g v)) ->
  (forall u v, Decidable.decidable (E g u v)) ->
  is_elem_list P L ->
  Decidable.decidable (neighbourhood g P v).
Proof.
  intros Heq_dec HVdec HEdec HPlist.
  assert (forall x, Decidable.decidable (P x)) as HPdec by
    eauto using decidable_if_elem_list.
  unfold Decidable.decidable, neighbourhood in *.
  destruct HPdec with v as [HP | HnP].
  - tauto.
  - destruct exists_filtered with A (fun x => P x /\ E g x v) L as (?&Hlist).
    { unfold Decidable.decidable. firstorder. }
    eapply subset_elem_list in Hlist.
    + apply decidable_exists_if_elem_list in Hlist as [? | ?]; tauto.
    + eassumption.
    + unfold is_subset. tauto.
Qed.

Fact decidable_uncurry A B p q :
  (forall x y, Decidable.decidable (x = y :> A)) ->
  (forall x y, Decidable.decidable (x = y :> B)) ->
  Decidable.decidable (p = q :> A * B).
Proof.
  unfold Decidable.decidable. destruct p as (p1&p2), q as (q1&q2).
  intros HA HB. destruct HA with p1 q1, HB with p2 q2.
  - left. f_equal; assumption.
  - right. intros [= ]. tauto.
  - right. intros [= ]. tauto.
  - right. intros [= ]. tauto.
Qed.

(*
Definition is_nonempty_set {A} (P : A -> Prop) : Prop :=
  exists x, P x.

Fact size_lt_0_nonempty A P s :
  @is_set_size A P s ->
  (is_nonempty_set P <-> s > 0).
Proof.
  unfold is_set_size, is_elem_unique_list, is_elem_list, is_nonempty_set.
  intros ([|]&(Hlist&?)&<-); simpl in *.
  - split.
    + intros (?&[]%Hlist).
    + lia.
  - split.
    + lia.
    + intros. eexists. apply Hlist. auto.
Qed.

Lemma nonempty_has_min_cost_elem_option_nat
  (P : nat -> Prop) (W : nat -> option nat) :
  is_nonempty_set P ->
  exists x, min_cost_elem P W x.
Proof.
  unfold is_nonempty_set, min_cost_elem. simpl. intros (x&?).
  remember (W x) as n eqn:Hn. destruct n.
  2:{ exists x. rewrite <- Hn. simpl. }
  induction n.
  -
  intros (L&(Hlist&Hnodup)&<-) ?. induction L; simpl in *; [lia|].
  inversion Hnodup. subst.
   eexists. rewrite
Qed.
*)
Lemma nonempty_has_min_cost_elem_option_nat {A}
  (P : A -> Prop) s (W : A -> option nat) :
  (forall x y, Decidable.decidable (x = y :> A)) ->
  is_set_size P s ->
  s > 0 ->
  exists x, min_cost_elem P W x.
Proof.
  unfold is_set_size, is_elem_unique_list, is_elem_list, min_cost_elem.
  intros Hdec_eq (L&(?&Hnodup)&<-) ?. generalize dependent P.
  induction L as [|x L IHL]; simpl in *; [lia|].
  intros P Hlist. destruct L as [|y L]; simpl in *.
  - exists x. split; [apply Hlist; auto|]. intros ? [->|[]]%Hlist.
    destruct W; lia.
  - destruct IHL with (P := fun z => z <> x /\ P z) as (x'&(?&?)&Hmin).
    + inversion Hnodup. assumption.
    + lia.
    + intros. rewrite <- Hlist. inversion Hnodup. simpl in *.
      intuition; subst; tauto.
    + assert (le (W x) (W x') \/ (le (W x') (W x) /\ W x <> W x'))
        as [Hle|[Hle Hneq]].
      { destruct W as [n|], W as [n'|]; simpl.
        { assert (n' <= n \/ n < n') as [|] by lia; auto.
          right. split; [lia|]. intros [=->]. lia. }
        { right. split; auto. discriminate. }
        { auto. }
        { auto. } }
      * exists x. rewrite <- Hlist. split; auto. simpl in Hle.
        intros y' [->|[->|]]%Hlist.
        { destruct (W y') as [k|]; lia. }
        { specialize Hmin with y'. rewrite <- Hlist in Hmin. inversion Hnodup.
          simpl in *.
          destruct (W x) as [k|], (W x') as [k'|], (W y') as [k''|]; try lia.
          { transitivity k'; try assumption. intuition. }
          { intuition. }
          { intuition. } }
        { specialize Hmin with y'. rewrite <- Hlist in Hmin. inversion Hnodup.
          simpl in *.
          destruct (W x) as [k|], (W x') as [k'|], (W y') as [k''|]; try lia.
          { transitivity k'; try assumption. apply Hmin. intuition. subst.
            tauto. }
          { exfalso. apply Hmin. intuition. subst. tauto. }
          { apply Hmin. intuition. subst. tauto. } }
      * exists x'. split; auto. intros y' HP.
        assert (le (W x) (W y') \/ le (W y') (W x)) as [Hle'|Hle'].
        { destruct (W x) as [n|], (W y') as [n'|]; simpl; lia. }
        -- destruct (W x), (W x'), (W y'); simpl in *; lia.
        -- specialize Hmin with y'. destruct Hdec_eq with y' x as [->|].
          { apply Hle. }
          { apply Hmin. auto. }
Qed.
(*
Fact sa_and_if_implies V (P Q : StateAssertion V) c m :
  P ->> Q ->
  P c m ->
  (P </\> Q) c m.
Proof.
  unfold sa_implies, sa_and. auto.
Qed.

Fact sa_implies_and_if_implies V (P Q : StateAssertion V) :
  P ->> Q ->
  P ->> (P </\> Q).
Proof.
  unfold sa_implies, sa_and. auto.
Qed.
*)
Lemma nonempty_has_min_cost_elem_nat A P s (W : A -> nat) :
  is_set_size P s ->
  s > 0 ->
  exists x, min_cost_elem P W x.
Proof.
  unfold is_set_size, is_elem_unique_list, is_elem_list, min_cost_elem.
  simpl. intros (L&(Hlist&Hnodup)&<-) Hle. generalize dependent P.
  induction L as [|x L IHL]; simpl in *; [lia|]; intros. inversion Hnodup.
  subst. destruct L as [|y L]; simpl in *.
  - exists x. rewrite <- Hlist. split; auto. intros ? [->|[]]%Hlist. lia.
  - destruct IHL with (P := fun z => z <> x /\ P z) as (x'&(?&?)&Hmin).
    + assumption.
    + lia.
    + intros. rewrite <- Hlist. intuition; subst; tauto.
    + assert (W x < W x' \/ W x' <= W x) as [Hlt|Hle'] by lia.
      * exists x. rewrite <- Hlist. split; auto.
        intros y' [->|[->|]]%Hlist.
        { lia. }
        { specialize Hmin with y'. rewrite <- Hlist in Hmin. inversion Hnodup.
          simpl in *.
          transitivity (W x'); try lia; intuition. }
        { specialize Hmin with y'. rewrite <- Hlist in Hmin. inversion Hnodup.
          simpl in *.
          transitivity (W x'); try lia. apply Hmin. intuition. subst. tauto. }
      * exists x'. split; auto. intros y' [->|[->|]]%Hlist.
        { auto. }
        { apply Hmin. rewrite <- Hlist. auto. }
        { apply Hmin. rewrite <- Hlist. split; auto. intros ->. auto. }
Qed.

Lemma decidable_list_disjointness A (L1 L2 : list A) :
  (forall x y, Decidable.decidable (x = y :> A)) ->
  Decidable.decidable (exists x, List.In x L1 /\ List.In x L2).
Proof.
  unfold Decidable.decidable. intros Hdec_eq.
  induction L1 as [|x L1 IHL1]; simpl.
  - firstorder.
  - destruct IHL1 as [(?&?&?)|?].
    + eauto.
    + destruct (decidable_in _ L2 x).
      { assumption. }
      * eauto.
      * right. intros (?&[->|]&?); eauto.
Qed.

Lemma neighbour_list_in_finite_decidable_graph A (g : graph A) Lv x :
  (forall x y, Decidable.decidable (x = y :> A)) ->
  is_elem_list (V g) Lv ->
  (forall x y, Decidable.decidable (E g x y)) ->
  exists Ln, is_elem_list (neighbours g x) Ln.
Proof.
  unfold is_elem_list, Decidable.decidable, neighbours. intros Hdec_eq Hlist Hdec.
  generalize dependent g. induction Lv as [|y Lv IHLv]; simpl; intros.
  - exists nil. simpl. intros y. split; [intros []|]. intros []%E_closed1%Hlist.
  - destruct IHLv with (g := induced_subgraph (fun x => List.In x Lv) g)
      as (Ln&HLn).
    { intros x'. simpl. unfold intersect. rewrite <- Hlist. tauto. }
    { intros x' y'. simpl. destruct (decidable_in _ Lv x'); try tauto.
      destruct (decidable_in _ Lv y'); try tauto.
      destruct Hdec with x' y'; tauto. }
    simpl in *. destruct decidable_in with A Lv y as [|Hnin]; auto.
    + destruct Hdec_eq with x y as [->|].
      * exists Ln. intros x'. rewrite HLn. split; [tauto|]. intros HE.
        split_all; try assumption.
        apply E_closed2 in HE as [->|]%Hlist; assumption.
      * exists Ln. intros x'. rewrite HLn. destruct Hdec_eq with y x' as [->|].
        -- split; [tauto|]. intros HE. split_all; try assumption.
          apply E_closed1 in HE as [->|]%Hlist; assumption.
        -- split; [tauto|]. intros HE.
          split_all; try assumption;
            [apply E_closed1 in HE as [->|]%Hlist|
             apply E_closed2 in HE as [->|]%Hlist];
            assumption.
    + destruct Hdec_eq with x y as [->|].
      * revert Hdec_eq Hdec Hlist Hnin. clear. revert g.
        induction Lv as [|x Lv IHLv]; simpl; intros.
        -- destruct Hdec with y y.
          ++ exists [y]%list. simpl. intros x. split.
            ** intros [->|[]]. assumption.
            ** intros ?%E_closed2. apply Hlist. assumption.
          ++ exists nil. simpl. intros x. split.
            ** intros [].
            ** intros HE. apply E_closed2 in HE as HV.
              apply Hlist in HV as [->|[]]. auto.
        -- destruct IHLv
            with (g := induced_subgraph (fun x => y = x \/ List.In x Lv) g)
            as (Ln&HLn).
          { assumption. }
          { intros x' y'. simpl. destruct Hdec_eq with y x' as [->|].
            { destruct Hdec_eq with x' y' as [->|].
              { destruct Hdec with y' y'; tauto. }
              { destruct (decidable_in _ Lv y'); try tauto.
                destruct Hdec with x' y'; tauto. } }
            { destruct Hdec_eq with y y' as [->|].
              { destruct (decidable_in _ Lv x'); try tauto.
                destruct Hdec with x' y'; tauto. }
              { destruct (decidable_in _ Lv x'); try tauto.
                destruct (decidable_in _ Lv y'); try tauto.
                destruct Hdec with x' y'; tauto. } } }
          { simpl. unfold intersect. intros. rewrite <- Hlist. tauto. }
          { auto. }
          simpl in *. destruct Hdec with y x.
          ++ exists (x::Ln)%list. simpl. intros x'. rewrite HLn.
            destruct Hdec_eq with x x' as [->|]; [tauto|].
            split; [tauto|]. intros HE. apply E_closed2 in HE as HVx'.
            apply Hlist in HVx'. tauto.
          ++ exists Ln. intros x'. rewrite HLn. split; [tauto|]. intros HE.
            apply E_closed2 in HE as HVx'.
            apply Hlist in HVx' as [->|[->|]]; tauto.
      * destruct decidable_in with A Lv x; auto.
        -- destruct Hdec with x y.
          ++ exists (y::Ln)%list. simpl. intros x'. rewrite HLn.
            destruct Hdec_eq with y x' as [->|]; try tauto.
            split; [tauto|]. intros HE. apply E_closed1 in HE as HVx.
            apply E_closed2 in HE as HVx'. apply Hlist in HVx, HVx'; tauto.
          ++ exists Ln. intros x'. rewrite HLn.
            destruct Hdec_eq with x x' as [->|]; try tauto.
            destruct Hdec_eq with y x' as [->|]; try tauto.
            split; [tauto|]. intros HE. apply E_closed1 in HE as HVx.
            apply E_closed2 in HE as HVx'. apply Hlist in HVx, HVx'; tauto.
        -- exists nil. simpl. intros. split; [tauto|].
          intros [->|]%E_closed1%Hlist; tauto.
Qed.

Definition neighbour_of {A} (g : graph A) (v : A) : A -> Prop :=
  fun u => E g u v.

Lemma neighbour_of_list_in_finite_decidable_graph A (g : graph A) Lv x :
  (forall x y, Decidable.decidable (x = y :> A)) ->
  is_elem_list (V g) Lv ->
  (forall x y, Decidable.decidable (E g x y)) ->
  exists Ln, is_elem_list (neighbour_of g x) Ln.
Proof.
  unfold is_elem_list, Decidable.decidable, neighbour_of. intros Hdec_eq Hlist Hdec.
  generalize dependent g. induction Lv as [|y Lv IHLv]; simpl; intros.
  - exists nil. simpl. intros y. split; [intros []|]. intros []%E_closed1%Hlist.
  - destruct IHLv with (g := induced_subgraph (fun x => List.In x Lv) g)
      as (Ln&HLn).
    { intros x'. simpl. unfold intersect. rewrite <- Hlist. tauto. }
    { intros x' y'. simpl. destruct (decidable_in _ Lv x'); try tauto.
      destruct (decidable_in _ Lv y'); try tauto.
      destruct Hdec with x' y'; tauto. }
    simpl in *. destruct decidable_in with A Lv y as [|Hnin]; auto.
    + destruct Hdec_eq with x y as [->|].
      * exists Ln. intros x'. rewrite HLn. split; [tauto|]. intros HE.
        split_all; try assumption.
        apply E_closed1 in HE as [->|]%Hlist; assumption.
      * exists Ln. intros x'. rewrite HLn. destruct Hdec_eq with y x' as [->|].
        -- split; [tauto|]. intros HE. split_all; try assumption.
          apply E_closed2 in HE as [->|]%Hlist; assumption.
        -- split; [tauto|]. intros HE.
          split_all; try assumption;
            [apply E_closed1 in HE as [->|]%Hlist|
             apply E_closed2 in HE as [->|]%Hlist];
            assumption.
    + destruct Hdec_eq with x y as [->|].
      * revert Hdec_eq Hdec Hlist Hnin. clear. revert g.
        induction Lv as [|x Lv IHLv]; simpl; intros.
        -- destruct Hdec with y y.
          ++ exists [y]%list. simpl. intros x. split.
            ** intros [->|[]]. assumption.
            ** intros ?%E_closed1. apply Hlist. assumption.
          ++ exists nil. simpl. intros x. split.
            ** intros [].
            ** intros HE. apply E_closed1 in HE as HV.
              apply Hlist in HV as [->|[]]. auto.
        -- destruct IHLv
            with (g := induced_subgraph (fun x => y = x \/ List.In x Lv) g)
            as (Ln&HLn).
          { assumption. }
          { intros x' y'. simpl. destruct Hdec_eq with y x' as [->|].
            { destruct Hdec_eq with x' y' as [->|].
              { destruct Hdec with y' y'; tauto. }
              { destruct (decidable_in _ Lv y'); try tauto.
                destruct Hdec with x' y'; tauto. } }
            { destruct Hdec_eq with y y' as [->|].
              { destruct (decidable_in _ Lv x'); try tauto.
                destruct Hdec with x' y'; tauto. }
              { destruct (decidable_in _ Lv x'); try tauto.
                destruct (decidable_in _ Lv y'); try tauto.
                destruct Hdec with x' y'; tauto. } } }
          { simpl. unfold intersect. intros. rewrite <- Hlist. tauto. }
          { auto. }
          simpl in *. destruct Hdec with x y.
          ++ exists (x::Ln)%list. simpl. intros x'. rewrite HLn.
            destruct Hdec_eq with x x' as [->|]; [tauto|].
            split; [tauto|]. intros HE. apply E_closed1 in HE as HVx'.
            apply Hlist in HVx'. tauto.
          ++ exists Ln. intros x'. rewrite HLn. split; [tauto|]. intros HE.
            apply E_closed1 in HE as HVx'.
            apply Hlist in HVx' as [->|[->|]]; tauto.
      * destruct decidable_in with A Lv x; auto.
        -- destruct Hdec with y x.
          ++ exists (y::Ln)%list. simpl. intros x'. rewrite HLn.
            destruct Hdec_eq with y x' as [->|]; try tauto.
            split; [tauto|]. intros HE. apply E_closed1 in HE as HVx.
            apply E_closed2 in HE as HVx'. apply Hlist in HVx, HVx'; tauto.
          ++ exists Ln. intros x'. rewrite HLn.
            destruct Hdec_eq with x x' as [->|]; try tauto.
            destruct Hdec_eq with y x' as [->|]; try tauto.
            split; [tauto|]. intros HE. apply E_closed1 in HE as HVx.
            apply E_closed2 in HE as HVx'. apply Hlist in HVx, HVx'; tauto.
        -- exists nil. simpl. intros. split; [tauto|].
          intros [->|]%E_closed2%Hlist; tauto.
Qed.

Lemma path_list_in_finite_decidable_graph A (g : graph A) Lv Le u v :
  is_elem_list (V g) Lv ->
  is_elem_list (uncurry (E g)) Le ->
  (*(forall x y, Decidable.decidable (E g x y)) ->*)
  exists Lp, is_elem_list (is_path g u v) Lp.
Proof.
  unfold is_elem_list, is_path, uncurry. (*remember (List.length Lv) as l eqn:Hl.*)
  revert g u v (*Lv Hl*). induction Lv as [|x Lv IHLv]; simpl; intros ? ? ? (*? ?*) Hlist HElist.
  - exists nil. intros. simpl. split.
    + intros [].
    + intros ([]&?); erewrite Hlist; eauto using E_closed1.
  - (*specialize (decidable_if_elem_list _ Le (uncurry (E g))). specialize IHLv with (g := induced_subgraph (fun y => y <> x) g).*)
Admitted.

Lemma shortest_path_if_path A (g : wgraph A) u v p Lv Le :
  is_elem_list (V g) Lv ->
  is_elem_list (uncurry (E g)) Le ->
  is_path g u v p ->
  exists sp, is_shortest_path g u v sp.
Proof.
  unfold is_shortest_path. intros. eapply nonempty_has_min_cost_elem_nat.
Admitted.

Lemma shortest_path_if_walk A (g : wgraph A) u v p Lv Le :
  is_elem_list (V g) Lv ->
  is_elem_list (uncurry (E g)) Le ->
  is_walk g u v p ->
  exists sp, is_shortest_path g u v sp.
Proof.
Admitted.

Lemma invariant_D_is_some_for_subset A
  (D : A -> option nat) (pred : A -> option A) (P : A -> Prop) (s : A)
  (g : wgraph A) x Lv Le :
  is_elem_list (V g) Lv ->
  is_elem_list (uncurry (E g)) Le ->
  Dijkstra_invariant D pred P s g ->
  V g x ->
  P x ->
  exists y, D x = Some y.
Proof.
  unfold Dijkstra_invariant, Dijkstra_connectedness_invariant,
    Dijkstra_distance_invariant, Dijkstra_predecessors_invariant,
    are_valid_distances, are_valid_predecessors, are_maximal_predecessors,
    is_shortest_paths_tree, is_root.
  intros ? ? (Hconnected&?&?) ? ?. edestruct Hconnected; eauto.
  { simpl. unfold set_sum, intersect, single. eauto. }
  edestruct shortest_path_if_walk.
  3,4:eauto; simpl; eauto.
  { simpl. admit. }
Admitted.

Lemma invariant_D_is_some_for_neighbours A
  (D : A -> option nat) (pred : A -> option A) (P : A -> Prop) (s : A)
  (g : wgraph A) x Lv Le :
  is_elem_list (V g) Lv ->
  is_elem_list (uncurry (E g)) Le ->
  Dijkstra_invariant D pred P s g ->
  V g x ->
  neighbourhood g P x ->
  exists y, D x = Some y.
Proof.
  unfold Dijkstra_invariant, Dijkstra_connectedness_invariant,
    Dijkstra_distance_invariant, Dijkstra_predecessors_invariant,
    are_valid_distances, are_valid_predecessors, are_maximal_predecessors,
    is_shortest_paths_tree, is_root.
  intros ? ? (Hconnected&?&?) ? ?. edestruct Hconnected; eauto.
  { simpl. unfold set_sum, intersect, single. eauto. }
  edestruct shortest_path_if_walk.
  3,4:eauto; simpl; eauto.
  { simpl. admit. }
Admitted.

(*
Definition is_vertex_potential A (g : graph A) (P : A -> Prop) p : Prop :=
  forall s x,
  is_set_size (V g) s ->
  is_set_size (V (induced_subgraph P g)) x ->
  p = s - x.

Definition is_edge_potential A (g : graph A) (P : A -> Prop) p : Prop :=
  forall s x,
  is_set_size (uncurry (E g)) s ->
  is_set_size (uncurry (E (induced_subgraph P g))) x ->
  p = s - x.
*)

Lemma elem_weighted_unique_list_to_size A B P W L :
  @is_elem_weighted_unique_list A B P W L ->
  is_set_size P (List.length L).
Proof.
  unfold is_elem_weighted_unique_list, is_elem_weighted_list, is_set_size,
    is_elem_unique_list, is_elem_list.
  intros (Hin&?). exists (List.map fst L). split_all.
  - intros x. rewrite List.in_map_iff. split.
    + intros ((?&?)&<-&(?&?)%Hin). simpl. assumption.
    + intros. exists (x,W x). simpl. rewrite Hin. auto.
  - assumption.
  - apply List.map_length.
Qed.

Definition are_disjoint_sets {A} (P Q : A -> Prop) : Prop :=
  forall x, ~ (P x /\ Q x).

Definition set_remove {A} (P : A -> Prop) (x y : A) : Prop :=
  P y /\ y <> x.

Lemma sum_elem_list A (P Q : A -> Prop) Lp Lq :
  is_elem_list P Lp ->
  is_elem_list Q Lq ->
  is_elem_list (set_sum P Q) (Lp ++ Lq)%list.
Proof.
  unfold is_elem_list, is_elem_list, set_sum.
  intros HinLp HinLq x. rewrite <- HinLp, <- HinLq.
  apply List.in_app_iff.
Qed.

Lemma sum2_elem_list A (P Q : A -> A -> Prop) Lp Lq :
  is_elem_list (uncurry P) Lp ->
  is_elem_list (uncurry Q) Lq ->
  is_elem_list (uncurry (set_sum2 P Q)) (Lp ++ Lq)%list.
Proof.
  unfold is_elem_list, is_elem_list, set_sum2, uncurry.
  intros HinLp HinLq (x&y).
  rewrite List.in_app_iff, HinLp, HinLq. reflexivity.
Qed.

Lemma disjoint_list_nodup A (L1 L2 : list A) :
  List.NoDup L1 ->
  List.NoDup L2 ->
  (forall x, ~ (List.In x L1 /\ List.In x L2)) ->
  List.NoDup (L1 ++ L2)%list.
Proof.
  intros Hnodup1 Hnodup2 Hdisjoint. induction Hnodup1; simpl in *; eauto.
  constructor.
  - rewrite List.in_app_iff. firstorder.
  - apply IHHnodup1. firstorder.
Qed.

Lemma disjoint_elem_list A (P Q : A -> Prop) Lp Lq :
  are_disjoint_sets P Q ->
  is_elem_list P Lp ->
  is_elem_list Q Lq ->
  (forall x, ~ (List.In x Lp /\ List.In x Lq)).
Proof.
  unfold are_disjoint_sets, is_elem_list.
  intros Hdisjoint Hnodup1 Hnodup2 x. rewrite Hnodup1, Hnodup2. auto.
Qed.

Lemma disjoint_sum_elem_unique_list A (P Q : A -> Prop) Lp Lq :
  are_disjoint_sets P Q ->
  is_elem_unique_list P Lp ->
  is_elem_unique_list Q Lq ->
  is_elem_unique_list (set_sum P Q) (Lp ++ Lq)%list.
Proof.
  unfold is_elem_unique_list, is_elem_unique_list.
  intros Hdisjoint (?&HnodupP) (?&HnodupQ).
  eauto using sum_elem_list, disjoint_list_nodup, disjoint_elem_list.
Qed.

Lemma disjoint_sum2_elem_unique_list A (P Q : A -> A -> Prop) Lp Lq :
  are_disjoint_sets (uncurry P) (uncurry Q) ->
  is_elem_unique_list (uncurry P) Lp ->
  is_elem_unique_list (uncurry Q) Lq ->
  is_elem_unique_list (uncurry (set_sum2 P Q)) (Lp ++ Lq)%list.
Proof.
  unfold is_elem_unique_list, is_elem_unique_list.
  intros Hdisjoint (?&HnodupP) (?&HnodupQ).
  eauto using sum2_elem_list, disjoint_list_nodup, disjoint_elem_list.
Qed.

Lemma disjoint_sum_size A (P Q : A -> Prop) p q :
  are_disjoint_sets P Q ->
  is_set_size P p ->
  is_set_size Q q ->
  is_set_size (set_sum P Q) (p + q).
Proof.
  unfold is_set_size. intros ? (Lp&?&?) (Lq&?&?). exists (Lp ++ Lq)%list.
  subst. auto using disjoint_sum_elem_unique_list, List.app_length.
Qed.

Lemma disjoint_sum_size2 A (P Q : A -> A -> Prop) p q :
  are_disjoint_sets (uncurry P) (uncurry Q) ->
  is_set_size (uncurry P) p ->
  is_set_size (uncurry Q) q ->
  is_set_size (uncurry (set_sum2 P Q)) (p + q).
Proof.
  unfold is_set_size. intros ? (Lp&?&?) (Lq&?&?). exists (Lp ++ Lq)%list.
  subst. auto using disjoint_sum2_elem_unique_list, List.app_length.
Qed.

Definition cross {A B} (P : A -> Prop) (Q : B -> Prop) : A * B -> Prop :=
  fun '(a, b) => P a /\ Q b.

Definition list_cross {A B} (L1 : list A) (L2 : list B) : list (A * B) :=
  List.concat (List.map (fun x => List.map (fun y => (x,y)) L2) L1).

Lemma cross_elem_list A B P Q Lp Lq :
  is_elem_list P Lp ->
  is_elem_list Q Lq ->
  is_elem_list (@cross A B P Q) (list_cross Lp Lq).
Proof.
  unfold is_elem_list, cross, list_cross. intros HinP HinQ (a&b).
  rewrite List.in_concat, <- HinP, <- HinQ. split.
  - intros (?&(?&<-&?)%List.in_map_iff&(?&[= -> ->]&?)%List.in_map_iff). auto.
  - intros (HinA&HinB). clear P Q HinP HinQ.
    induction Lp as [|x Lp IHLp]; simpl in *.
    + contradiction.
    + destruct HinA as [-> | HinA].
      * eauto using List.in_map.
      * destruct IHLp as (L&?&?); eauto.
Qed.

Lemma nodup_list_cross A B L1 L2 :
  @List.NoDup A L1 ->
  @List.NoDup B L2 ->
  List.NoDup (list_cross L1 L2).
Proof.
  intros Hnodup1 Hnodup2. unfold list_cross. induction Hnodup1; simpl.
  - constructor.
  - apply disjoint_list_nodup; auto.
    + clear IHHnodup1. induction Hnodup2; simpl in *; constructor; auto.
      rewrite List.in_map_iff. intros (?&[=->]&?). auto.
    + intros (a&b)
        ((?&[= -> ->]&?)%List.in_map_iff
        &(?&(?&<-&?)%List.in_map_iff
          &(?&[= -> ->]&?)%List.in_map_iff)%List.in_concat).
      auto.
Qed.

Lemma cross_elem_unique_list A B P Q Lp Lq :
  is_elem_unique_list P Lp ->
  is_elem_unique_list Q Lq ->
  is_elem_unique_list (@cross A B P Q) (list_cross Lp Lq).
Proof.
  unfold is_elem_unique_list. intros (?&?) (?&?).
  auto using cross_elem_list, nodup_list_cross.
Qed.

Lemma list_cross_length A B L1 L2 :
  List.length (@list_cross A B L1 L2) = List.length L1 * List.length L2.
Proof.
  unfold list_cross. induction L1 as [|x L1 IHL1]; simpl in *; auto.
  rewrite List.app_length, IHL1, List.map_length. reflexivity.
Qed.

Lemma cross_size A B P Q p q :
  is_set_size P p ->
  is_set_size Q q ->
  is_set_size (@cross A B P Q) (p * q).
Proof.
  unfold is_set_size. intros (L1&?&<-) (L2&?&<-).
  exists (list_cross L1 L2).
  auto using cross_elem_unique_list, list_cross_length.
Qed.

Definition update_nat_function_at {A} (f : nat -> A) x y : nat -> A :=
  fun n => if n =? x then y else f n.

Lemma nat_function_update V f x y L1 t L2 :
  is_nat_fun_of_val_list (L1 ++ t::L2)%list f ->
  @is_nat_fun_of_val_list V
    (L1 ++ Some (Int (Z.of_nat y))::L2)%list
    (update_nat_function_at f x (Some y)).
Proof.
  unfold is_nat_fun_of_val_list.
Admitted.

Lemma array_content_to_is_nat_function V L f l :
  @is_nat_fun_of_val_list V L f ->
  array_content L (Lab l) ->> is_nat_function f l.
Proof.
Admitted.

Fixpoint nat_decrease_distance
  (v : nat) (NW : list (nat*nat)) (D pred : nat -> option nat) :
  nat -> option nat * option nat :=
  fun u =>
    match D v with
    | None => (D u, pred u)
    | Some dv =>
      match NW with
      | (n,w)::NW' =>
        if u =? n then
          match D u with
          | None => (Some (dv + w), Some v)
          | Some du =>
            if dv + w <? du then
              (Some (dv + w), Some v)
            else
              (D u, pred u)
          end
        else
          nat_decrease_distance v NW' D pred u
      | nil => (D u, pred u)
      end
    end%list.

Definition fun2pair {A B C} (f : A -> B*C) : (A -> B) * (A -> C) :=
  (fun x => fst (f x), fun x => snd (f x)).

Definition edge_remove {A} (u v : A) (g : graph A) : graph A := {|
  V := V g;
  E u' v' := E g u' v' /\ (u <> u' \/ v <> v');
  E_closed1 v _ HE := let '(conj HE _) := HE in E_closed1 g _ _ HE;
  E_closed2 _ _ HE := let '(conj HE _) := HE in E_closed2 g _ _ HE
|}.

Lemma distance_decrease_nat_decrease_distance g v dv NW D D' pred pred' :
  D v = Some dv ->
  is_elem_weighted_unique_list (neighbours (G g) v) (W g v) NW ->
  (D', pred') = fun2pair (nat_decrease_distance v NW D pred) ->
  distance_decrease g v D D' pred pred'.
Proof.
  unfold is_elem_weighted_unique_list, is_elem_weighted_list, neighbours,
    fun2pair, distance_decrease.
  intros Hdv (Hlist&Hnodup) [= -> ->]. exists dv. split; auto. intros u.
  generalize dependent g. induction NW as [|(n&w) NW' IHNW]; simpl in *; intros.
  - split; intros HE.
    + exfalso. eapply Hlist. eauto.
    + rewrite Hdv. simpl. auto.
  - rewrite Hdv. split; intros HE.
    + split; intros Hdu.
      * destruct Nat.eqb_spec with u n as [-> | Hneq].
        -- rewrite Hdu. simpl. destruct Hlist with n w as ((_&->)&_); auto.
        -- destruct Hlist with u (W g v u) as (_&[[= -> ->]|Hin]); auto.
          ++ tauto.
          ++ (*destruct IHNW with g as (HEvu&HnEvu).
            { inversion Hnodup. auto. }
            { intros. rewrite <- Hlist. split.
              { auto. }
              { intros [[= -> ]] } }*)
(*
            destruct IHNW with (wg_lift (edge_remove v u) g) as (HEvu&HnEvu).
            { inversion Hnodup. auto. }
            { intros x w'. simpl.
             split.
              { inversion Hnodup. intros Hin'.
                destruct Hlist with x w as ((?&?)&_).
                { auto. }
                repeat split; auto. right. intros ->.
                apply List.in_map with (f := fst) in Hin. simpl in Hin. auto. }
              { intros ((HE'&[?|Hneq])&HW).
                { tauto. }
                { destruct Hlist with x w as (_&[[= ]|Hin]); tauto. } } }
            simpl in *.
          ++

  destruct decidable_in with (L := NW) (x := (u, W g v u)) as [(?&?)%Hlist|?].
  { intros. apply decidable_uncurry; unfold Decidable.decidable; lia. }
  - split.
    +*) admit.
Admitted.

Lemma update_nat_function_at_preserves_le P Q f i (ov : option nat) x y :
  P x ->
  Q y ->
  le (f x) (f y) ->
  (forall x, P x -> le (f x) ov) ->
  (forall y, Q y -> le ov (f y)) ->
  le (update_nat_function_at f i ov x) (update_nat_function_at f i ov y).
Proof.
Admitted.

(* other properties *)

Lemma is_set_size_with_neighbours A B (P P' : A -> Prop) s g n x f L1 L2 :
  is_irreflexive g ->
  is_set_size (V g) n ->
  is_set_size P s ->
  P x ->
  are_disjoint_sets P P' ->
  @is_elem_weighted_unique_list A B (neighbours g x) f (L1 ++ L2)%list ->
  exists s', s' < n /\ is_set_size
    (set_sum (set_remove P x) (fun y => ~ P' y /\ List.In y (List.map fst L1))) s'.
Proof.
Admitted.

Lemma Dijkstra_invariant_nonnone A
  (D : A -> option nat) (pred : A -> option A) (P : A -> Prop)
  (s : A) (g : wgraph A) x :
  Dijkstra_invariant D pred P s g ->
  (x = s \/ neighbourhood g P x) ->
  ~ D x = None.
Proof.
Admitted.

Lemma Dijkstra_invariant_D_some A
  (D : A -> option nat) (pred : A -> option A) (P : A -> Prop)
  (s : A) (g : wgraph A) x n :
  Dijkstra_invariant D pred P s g ->
  D x = Some n ->
  x = s \/ P x \/ neighbourhood g P x.
Proof.
Admitted.

Lemma Dijkstra_invariant_if_D_some A
  (D : A -> option nat) (pred : A -> option A) (P : A -> Prop)
  (s : A) (g : wgraph A) x n (*n1*) n2 (*pr1*) pr2 :
  Dijkstra_invariant D pred P s g ->
  D x = Some n ->
  (*pred x = Some pr1 ->*)
  E g pr2 x ->
  (*D pr1 = Some n1 ->*)
  D pr2 = Some n2 ->
  (*n = n1 + W g pr1 x ->*)
  n2 + W g pr2 x < n ->
  (P = empty /\ x = s) \/ (P s /\ neighbourhood g P x).
Proof.
Admitted.

Lemma Dijkstra_invariant_if_D_some_neighbour_le_W A
  (D : A -> option nat) (pred : A -> option A) (P : A -> Prop)
  (s : A) (g : wgraph A) u v du dv :
  Dijkstra_invariant D pred P s g ->
  closest_neighbour g P D u ->
  neighbours g u v ->
  D u = Some du ->
  D v = Some dv ->
  dv <= du + W g u v ->
  P v.
Proof.
Admitted.

Lemma Dijkstra_invariant_D_is_some_in_set A
  (D : A -> option nat) (pred : A -> option A) (P : A -> Prop)
  (s : A) (g : wgraph A) v :
  Dijkstra_invariant D pred P s g ->
  P v ->
  exists d, D v = Some d.
Proof.
Admitted.

(* distance labels are greater or equal in the neighbourhood of P *)
Lemma Dijkstra_invariant_D_ge_in_neighbourhood A
  (D : A -> option nat) (pred : A -> option A) (P : A -> Prop)
  (s : A) (g : wgraph A) u v :
  Dijkstra_invariant D pred P s g ->
  P u ->
  (neighbourhood g P v) ->
  (*(exists d, D u = Some d) /\*) le (D u) (D v).
Proof.
Admitted.

Lemma Dijkstra_invariant_distance_decrease_in_P A
  (D D' : A -> option nat) (pred pred' : A -> option A) (P : A -> Prop)
  (s : A) (g : wgraph A) u v :
  Dijkstra_invariant D pred P s g ->
  distance_decrease g u D D' pred pred' ->
  P v ->
  D' v = D v.
Proof.
Admitted.

Lemma elem_unique_list_of_weighted_unique A B P (W : A -> B) LW :
  is_elem_weighted_unique_list P W LW ->
  is_elem_unique_list P (List.map fst LW).
Proof.
Admitted.

Lemma neighbourhood_add_new_single_size A g P v ns N N' :
  @is_set_size A (neighbourhood g P) ns ->
  is_elem_unique_list (neighbours g v) N ->
  is_filtered_list (fun x => ~ P x) N N' ->
  neighbourhood g P v ->
  is_set_size (neighbourhood g (add_single P v)) (ns + List.length N' - 1).
Proof.
Admitted.

Lemma edges_add_single_size A g P x es n n' :
  @is_irreflexive A g ->
  is_set_size (uncurry (set_sum2 (fun u v => P u /\ P v /\ E g u v)
    (fun u v => P u /\ ~ P v /\ E g u v))) es ->
  is_set_size (neighbours g x) n ->
  is_set_size (neighbour_of g x) n' ->
  is_set_size
    (uncurry (set_sum2
      (fun u v => add_single P x u /\ add_single P x v /\ E g u v)
      (fun u v => add_single P x u /\ ~ add_single P x v /\ E g u v)))
    (es + n + n').
Proof.
Admitted.

Lemma elem_list_to_unique A P L :
  (forall x y, Decidable.decidable (x = y :> A)) ->
  @is_elem_list A P L ->
  exists L', is_elem_unique_list P L'.
Proof.
  intros Hdec_eq Hlist. assert (forall x, Decidable.decidable (P x)) as Hdec.
  { intros. eapply decidable_if_elem_list; eassumption. }
  assert (forall x L, Decidable.decidable (@List.In A x L)) as HdecL.
  { intros. apply decidable_in. assumption. }
  unfold is_elem_unique_list, is_elem_list in *. generalize dependent P.
  induction L as [|x L IHL]; simpl in *; intros.
  - exists nil. simpl. auto using List.NoDup.
  - destruct HdecL with x L.
    + apply IHL; auto. intros. rewrite <- Hlist. intuition (subst;assumption).
    + edestruct IHL with (P := fun x => P x /\ List.In x L) as (L'&Hin&?).
      { intros. rewrite <- Hlist. tauto. }
      { intros. apply Decidable.dec_and; auto. }
      destruct Hdec with x.
        * exists (x::L')%list. simpl. split.
          -- intros. rewrite Hin, <- Hlist. tauto.
          -- constructor; auto. rewrite Hin. tauto.
        * exists L'. split; auto. intros. rewrite Hin.
          rewrite <- Hlist in *. tauto.
Qed.

Lemma elem_list_intersect_filtered A P Q L L' :
  @is_elem_list A P L ->
  is_filtered_list Q L L' ->
  is_elem_list (intersect P Q) L'.
Proof.
Admitted.

Lemma neighbourhood_add_single A g P u v :
  @neighbourhood A g (add_single P u) v <->
    (neighbourhood g P v) \/ (~ P v /\ neighbours g u v).
Proof.
Admitted.

Lemma set_remove_size_decr A (P : A -> Prop) x s :
  (forall x y, Decidable.decidable (x = y :> A)) ->
  is_set_size P s ->
  P x ->
  is_set_size (set_remove P x) (s-1).
Proof.
Admitted.

Lemma sum_size_le A (P Q : A -> Prop) sP sQ sPQ :
  is_set_size P sP ->
  is_set_size Q sQ ->
  is_set_size (set_sum P Q) sPQ ->
  sPQ <= sP + sQ.
Proof.
Admitted.

Lemma is_filtered_again A P L L' :
  @is_filtered_list A P L L' ->
  is_filtered_list (fun x => P x /\ List.In x L) L L'.
Proof.
Admitted.

Lemma Dijkstra_invariant_D_src A
  (D : A -> option nat) (pred : A -> option A) (P : A -> Prop)
  (s : A) (g : wgraph A) :
  Dijkstra_invariant D pred P s g ->
  D s = Some 0.
Proof.
Admitted.

Lemma distance_decrease_min A g v D D' pred pred' :
  @distance_decrease A g v D D' pred pred' ->
  D' v = D v.
Proof.
Admitted.

(*Lemma Dijkstra_invariant_all_le_C A
  (D : A -> option nat) (pred : A -> option A) (P : A -> Prop)
  (s : A) (g : wgraph A) n C u d :
  Dijkstra_invariant D pred P s g ->
  is_set_size P n ->
  is_max_label g C ->
  P u ->
  D u = Some d ->
  d <= n*C.
Proof.
Admitted.*)

Lemma Dijkstra_invariant_closest_neighbour_le_C A
  (D : A -> option nat) (pred : A -> option A) (P : A -> Prop)
  (s : A) (g : wgraph A) n C u d :
  Dijkstra_invariant D pred P s g ->
  is_set_size P n ->
  is_max_label g C ->
  closest_neighbour g P D u ->
  D u = Some d ->
  d <= (n+1)*C.
Proof.
Admitted.
