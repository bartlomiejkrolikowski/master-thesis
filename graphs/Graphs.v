Require Import List.
Import ListNotations.

(* directed graphs *)
Record graph A : Type := {
  V : A -> Prop;
  E : A -> A -> Prop;
  E_closed1 : forall u v, E u v -> V u;
  E_closed2 : forall u v, E u v -> V v
}.

Arguments V [A].
Arguments E [A].
Arguments E_closed1 [A].
Arguments E_closed2 [A].

Definition g_full {A} E : graph A := {|
  V x := True;
  E := E;
  E_closed1 _ _ _ := I;
  E_closed2 _ _ _ := I
|}.

Definition g_total {A} V : graph A := {|
  V := V;
  E u v := V u /\ V v;
  E_closed1 u v HE :=
    let '(conj HV _) := HE in HV;
  E_closed2 u v HE :=
    let '(conj _ HV) := HE in HV
|}.

Definition empty {A} (x : A) : Prop := False.
Definition single {A} (x y : A) : Prop := x = y.
Definition total {A} (x : A) : Prop := True.

Definition g_empty {A} : graph A := {|
  V x := False;
  E u v := False;
  E_closed1 _ _ HE := match HE with end;
  E_closed2 _ _ HE := match HE with end
|}.

Definition g_single {A} (v : A) : graph A := {|
  V x := x = v;
  E u v := False;
  E_closed1 _ _ HE := match HE with end;
  E_closed2 _ _ HE := match HE with end
|}.

Definition intersect {A} (P Q : A -> Prop) (x : A) : Prop := P x /\ Q x.
Definition intersect2 {A} (P Q : A -> A -> Prop) (x y : A) : Prop :=
  P x y /\ Q x y.

Definition induced_subgraph {A} (P : A -> Prop) (g : graph A) : graph A := {|
  V := intersect P (V g);
  E u v := P u /\ P v /\ E g u v;
  E_closed1 u v HE :=
    let '(conj HP (conj _ HEg)) := HE in conj HP (E_closed1 g u v HEg);
  E_closed2 u v HE :=
    let '(conj _ (conj HP HEg)) := HE in conj HP (E_closed2 g u v HEg)
|}.

Definition set_sum {A} (P Q : A -> Prop) (x : A) : Prop := P x \/ Q x.
Definition set_sum2 {A} (P Q : A -> A -> Prop) (x y : A) : Prop :=
  P x y \/ Q x y.

Definition neighbours {A} (g : graph A) (x : A) := E g x.

Definition neighbourhood {A} (g : graph A) (P : A -> Prop) (v : A) :=
  ~ P v /\ exists u : A, P u /\ E g u v.

(* the edge of a set of vertices *)
Definition vx_edge {A} (g : graph A) (P : A -> Prop) (v : A) :=
  P v /\ exists u, ~ P u /\ E g v u.

Definition induced_subgraph_edge {A}
  (P : A -> Prop) (g : graph A) : graph A := {|
  V := set_sum (vx_edge g P) (neighbourhood g P);
  E u v := P u /\ ~ P v /\ E g u v;
  E_closed1 u v HE :=
    let '(conj Hu (conj Hv HEg)) := HE in
      or_introl (conj Hu (ex_intro _ v (conj Hv HEg)));
  E_closed2 u v HE :=
    let '(conj Hu (conj Hv HEg)) := HE in
      or_intror (conj Hv (ex_intro _ u (conj Hu HEg)))
|}.

Definition g_intersect {A} (g1 g2 : graph A) : graph A := {|
  V := intersect (V g1) (V g2);
  E := intersect2 (E g1) (E g2);
  E_closed1 u v HE :=
    let '(conj HEg1 HEg2) := HE in conj (E_closed1 g1 u v HEg1) (E_closed1 g2 u v HEg2);
  E_closed2 u v HE :=
    let '(conj HEg1 HEg2) := HE in conj (E_closed2 g1 u v HEg1) (E_closed2 g2 u v HEg2);
|}.

Definition g_sum {A} (g1 g2 : graph A) : graph A := {|
  V := set_sum (V g1) (V g2);
  E := set_sum2 (E g1) (E g2);
  E_closed1 u v HE :=
    match HE with
    | or_introl HEg1 => or_introl (E_closed1 g1 u v HEg1)
    | or_intror HEg2 => or_intror (E_closed1 g2 u v HEg2)
    end;
  E_closed2 u v HE :=
    match HE with
    | or_introl HEg1 => or_introl (E_closed2 g1 u v HEg1)
    | or_intror HEg2 => or_intror (E_closed2 g2 u v HEg2)
    end;
|}.

Notation "g1 &&& g2" := (g_intersect g1 g2) (at level 50).
Notation "g1 ||| g2" := (g_sum g1 g2) (at level 50).

Definition induced_subgraph_with_edge {A}
  (P : A -> Prop) (g : graph A) : graph A :=
  induced_subgraph P g ||| induced_subgraph_edge P g.

Definition induced_subgraph_with_edge_and_vx {A}
  (P : A -> Prop) (v : A) (g : graph A) : graph A :=
  induced_subgraph (set_sum P (single v)) g ||| induced_subgraph_edge P g.

Definition is_total {A} (g : graph A) :=
  forall u v, E g u v.

Definition is_irreflexive {A} (g : graph A) :=
  forall u, ~ E g u u.

Definition is_subset {A} (P Q : A -> Prop) := forall x, P x -> Q x.

Definition is_subset2 {A} (P Q : A -> A -> Prop) := forall x y, P x y -> Q x y.

Definition is_subgraph {A} (g1 g2 : graph A) :=
  is_subset (V g1) (V g2) /\ is_subset2 (E g1) (E g2).

Definition is_finite {A} (P : A -> Prop) :=
  exists l : list A, forall x, P x -> In x l.

Definition is_finite_graph {A} (g : graph A) := is_finite (V g).

Inductive is_a_walk {A} (g : graph A) : list A -> Prop :=
  | is_a_walk_nil : is_a_walk g []
  | is_a_walk_single x : V g x -> is_a_walk g [x]
  | is_a_walk_cons u v p : E g u v -> is_a_walk g (v::p) -> is_a_walk g (u::v::p).

Inductive is_an_undir_walk {A} (g : graph A) : list A -> Prop :=
  | is_an_undir_walk_nil : is_an_undir_walk g []
  | is_an_undir_walk_single x : V g x -> is_an_undir_walk g [x]
  | is_an_undir_walk_cons u v p :
    E g u v -> is_an_undir_walk g (v::p) -> is_an_undir_walk g (u::v::p)
  | is_an_undir_walk_cons_rev u v p :
    E g v u -> is_an_undir_walk g (v::p) -> is_an_undir_walk g (u::v::p).

Inductive is_walk {A} (g : graph A) (u : A) : A -> list A -> Prop :=
  | is_walk_single : V g u -> is_walk g u u [u]
  | is_walk_cons v w p : E g u v -> is_walk g v w p -> is_walk g u w (u::p).

Inductive is_undir_walk {A} (g : graph A) (u : A) : A -> list A -> Prop :=
  | is_undir_walk_single : V g u -> is_undir_walk g u u [u]
  | is_undir_walk_cons v w p :
    E g u v -> is_undir_walk g v w p -> is_undir_walk g u w (u::p)
  | is_undir_walk_cons_rev v w p :
    E g v u -> is_undir_walk g v w p -> is_undir_walk g u w (u::p).

(*
Fact is_walk_spec A (g : graph A) (p : list A) :
  is_walk g p <->
    (forall x, In x p -> V g x) /\
    (forall u v, In u p -> In v p -> E g u v).
Proof.
  split.
  - intro Hwalk. induction Hwalk; simpl in *.
    + intuition.
    + intuition; subst.

Fact nil_walk A (g : graph A) : is_walk g [].
Proof.
  unfold is_walk. simpl. intuition.
Qed.

Fact single_walk A (g : graph A) x :
  V g x -> is_walk g [x].
Proof.
  unfold is_walk. simpl. intuition; subst. auto.
Qed.
*)

Definition is_a_path {A} (g : graph A) (p : list A) :=
  is_a_walk g p /\ NoDup p.

Definition is_an_undir_path {A} (g : graph A) (p : list A) :=
  is_an_undir_walk g p /\ NoDup p.

Definition is_path {A} (g : graph A) (u v : A) (p : list A) :=
  is_walk g u v p /\ NoDup p.

Definition is_undir_path {A} (g : graph A) (u v : A) (p : list A) :=
  is_undir_walk g u v p /\ NoDup p.

(* weighted directed graphs *)
Record wgraph A : Type := {
  G :> graph A;
  W : A -> A -> nat
}.

Arguments G [A].
Arguments W [A].

Definition wg_lift {A}
  (f : graph A -> graph A) (g : wgraph A) : wgraph A := {|
  G := f g;
  W := W g
|}.

Fixpoint walk_cost {A} (W : A -> A -> nat) (p : list A) : nat :=
  match p with
  | [] => 0
  | [x] => 0
  | u::(v::_) as p' => W u v + walk_cost W p'
  end.

Class Ordered A := {
  le : A -> A -> Prop;
  (*le_refl : forall x, le x x;*)
  le_antisym : forall x y, le x y -> le y x -> x = y
}.

Instance Ordered_nat : Ordered nat := {|
  le := Peano.le;
  le_antisym := PeanoNat.Nat.le_antisymm
|}.

#[refine]
Instance Ordered_option A `(Ordered A) : Ordered (option A) := {|
  le x y := match x, y with
  | Some x, Some y => le x y
  | Some x, None => True
  | None, Some y => False
  | None, None => True
  end
|}.
Proof.
  intros [x|] [y|]; try contradiction; try reflexivity.
  intros. f_equal. apply le_antisym; assumption.
Qed.

Definition min_cost_elem {A B} `{Ordered B} (P : A -> Prop) (cost : A -> B) (x : A) :=
  P x /\ forall (y : A), P y -> le (cost x) (cost y).

Definition max_cost_elem {A B} `{Ordered B} (P : A -> Prop) (cost : A -> B) (x : A) :=
  P x /\ forall (y : A), P y -> le (cost y) (cost x).

Definition max_cost {A B} `{Ordered B} (P : A -> Prop) (cost : A -> B) (y : B) :=
  exists x, P x /\ y = cost x /\ forall (x' : A), P x' -> le (cost x') y.

Definition is_shortest_walk {A} (g : wgraph A) (u v : A) (p : list A) :=
  min_cost_elem (is_walk g u v) (walk_cost (W g)) p.

Definition is_shortest_undir_walk {A} (g : wgraph A) (u v : A) (p : list A) :=
  min_cost_elem (is_undir_walk g u v) (walk_cost (W g)) p.

Definition is_shortest_path {A} (g : wgraph A) (u v : A) (p : list A) :=
  min_cost_elem (is_path g u v) (walk_cost (W g)) p.

Definition is_shortest_undir_path {A} (g : wgraph A) (u v : A) (p : list A) :=
  min_cost_elem (is_undir_path g u v) (walk_cost (W g)) p.

(* directed cycles *)
Definition is_dicycle {A} (g : graph A) (p : list A) :=
  exists (u v : A) (p' : list A), is_path g u v p' /\ E g v u /\ p = v::p'.

(* undirected cycles *)
Definition is_cycle {A} (g : graph A) (p : list A) :=
  exists (u v : A) (p' : list A), is_undir_path g u v p' /\ E g v u /\ p = v::p'.

Definition is_acyclic {A} (g : graph A) :=
  forall p : list A, ~ is_cycle g p.

Definition is_conected {A} (g : graph A) :=
  forall u v : A, exists p, is_undir_walk g u v p.

Definition is_tree {A} (g : graph A) (p : list A) :=
  is_conected g /\ is_acyclic g.

Definition is_root {A} (g : graph A) (r : A) :=
  forall v : A, V g v -> exists p, is_walk g r v p.

Definition is_rooted_tree {A} (r : A) (g : graph A) :=
  is_root g r /\ is_acyclic g.

Definition is_shortest_paths_tree {A} (s : A) (t : graph A) (g : wgraph A) :=
  is_rooted_tree s t /\
    forall v p, is_path t s v p -> is_shortest_path g s v p.

Definition are_valid_distances {A} (D : A -> option nat) (s : A) (g : wgraph A) :=
  forall v p, is_shortest_path g s v p -> D v = Some (walk_cost (W g) p).

Definition pred2graph {A} (root : A) (pred : A -> option A) : graph A := {|
  V x := x = root \/ (exists y, Some y = pred x) \/ exists y, Some x = pred y;
  E u v := Some u = pred v;
  E_closed1 u v HE := or_intror (or_intror (ex_intro _ v HE));
  E_closed2 u v HE := or_intror (or_introl (ex_intro _ u HE));
|}.

Definition are_valid_predecessors {A}
  (pred : A -> option A) (s : A) (g : wgraph A) :=
  is_shortest_paths_tree s (pred2graph s pred) g.

Definition are_maximal_predecessors {A}
  (pred : A -> option A) (s : A) (g : graph A) :=
  forall v p, is_walk g s v p -> exists p', is_walk (pred2graph s pred) s v p'.

Definition Dijkstra_distance_invariant {A}
  (D : A -> option nat) (P : A -> Prop) (s : A) (g : wgraph A) :=
  are_valid_distances D s (wg_lift (induced_subgraph_with_edge_and_vx P s) g).

Definition Dijkstra_predecessors_invariant {A}
  (pred : A -> option A) (P : A -> Prop) (s : A) (g : wgraph A) :=
  forall g', g' = (wg_lift (induced_subgraph_with_edge_and_vx P s) g) ->
    are_valid_predecessors pred s g' /\ are_maximal_predecessors pred s g'.

Definition Dijkstra_invariant {A}
  (D : A -> option nat) (pred : A -> option A) (P : A -> Prop) (s : A) (g : wgraph A) :=
  Dijkstra_distance_invariant D P s g /\
  Dijkstra_predecessors_invariant pred P s g.

Definition Dijkstra_final {A}
  (D : A -> option nat) (pred : A -> option A) (s : A) (g : wgraph A) :=
  are_valid_distances D s g /\
  are_valid_predecessors pred s g /\
  are_maximal_predecessors pred s g.

Definition Dijkstra_initial {A}
  (D : A -> option nat) (pred : A -> option A) (s : A) :=
  D s = Some 0 /\ (forall v, v <> s -> D v = None) /\ (forall v, pred v = None).

Definition add_single {A} (P : A -> Prop) (x : A) := set_sum P (single x).

Definition distance_decrease {A}
  (g : wgraph A) (v : A) (D D' : A -> option nat) (pred pred' : A -> option A) :=
  exists dv, D v = Some dv /\
  forall u,
    (E g v u ->
      (D u = None -> D' u = Some (dv + W g v u) /\ pred' u = Some v) /\
      (forall du, D u = Some du ->
        (dv + W g v u < du -> D' u = Some (dv + W g v u) /\ pred' u = Some v) /\
        (dv + W g v u >= du -> D' u = D u /\ pred' u = pred u))) /\
    (~ E g v u -> D' u = D u /\ pred' u = pred u).

Definition closest_neighbour {A}
  (g : wgraph A) (P : A -> Prop) (D : A -> option nat) (v : A) :=
  min_cost_elem (neighbourhood g P) D v.

Definition set_equiv {A} (P Q : A -> Prop) : Prop :=
  forall x, P x <-> Q x.

Definition set_equiv2 {A} (P Q : A -> A -> Prop) : Prop :=
  forall x y, P x y <-> Q x y.

Definition gr_equiv {A} (g1 g2 : graph A) : Prop :=
  set_equiv (V g1) (V g2) /\ set_equiv2 (E g1) (E g2).

Notation "g1 ~= g2" := (gr_equiv g1 g2) (at level 60).

Definition is_empty {A} (g : wgraph A) : Prop :=
  g ~= g_empty.

(* proofs of properties *)

Fact intersect_empty_l A (P : A -> Prop) x :
  intersect empty P x <-> empty x.
Proof.
  unfold intersect, empty. intuition.
Qed.

Fact intersect_empty_r A (P : A -> Prop) x :
  intersect P empty x <-> empty x.
Proof.
  unfold intersect, empty. intuition.
Qed.

Fact set_sum_empty_l A (P : A -> Prop) x :
  set_sum empty P x <-> P x.
Proof.
  unfold set_sum, empty. intuition.
Qed.

Fact set_sum_empty_r A (P : A -> Prop) x :
  set_sum P empty x <-> P x.
Proof.
  unfold set_sum, empty. intuition.
Qed.

Fact intersect_single_l A (P : A -> Prop) x y :
  P y ->
  (intersect (single y) P x <-> single y x).
Proof.
  unfold intersect, empty, single. intuition. now subst.
Qed.

Fact intersect_single_r A (P : A -> Prop) x y :
  P y ->
  (intersect P (single y) x <-> single y x).
Proof.
  unfold intersect, empty, single. intuition. now subst.
Qed.

Fact intersect_equiv_l A (P P' Q : A -> Prop) x :
  set_equiv P P' ->
  intersect P Q x <-> intersect P' Q x.
Proof.
  unfold set_equiv, intersect. intros Hequiv. rewrite Hequiv. reflexivity.
Qed.

Fact intersect_equiv_r A (P Q Q' : A -> Prop) x :
  set_equiv Q Q' ->
  intersect P Q x <-> intersect P Q' x.
Proof.
  unfold set_equiv, intersect. intros Hequiv. rewrite Hequiv. reflexivity.
Qed.

Fact neighbourhood_empty A (g : graph A) x :
  neighbourhood g empty x <-> empty x.
Proof.
  unfold neighbourhood, empty. split.
  - intros (_&?&?&_). assumption.
  - intros [].
Qed.

Fact set_equiv_spec A (P Q : A -> Prop) :
  set_equiv P Q <-> forall x, P x <-> Q x.
Proof.
  reflexivity.
Qed.

Fact set_equiv_spec_r A (P Q : A -> Prop) :
  set_equiv P Q -> forall x, P x <-> Q x.
Proof.
  apply set_equiv_spec.
Qed.

Fact set_equiv_spec_l A (P Q : A -> Prop) :
  (forall x, P x <-> Q x) -> set_equiv P Q.
Proof.
  apply set_equiv_spec.
Qed.

Fact vx_edge_empty A (g : graph A) x :
  vx_edge g empty x <-> empty x.
Proof.
  unfold vx_edge, empty. intuition.
Qed.

Fact max_cost_unique A B `(Ordered B) (P : A -> Prop) (cost : A -> B) y1 y2 :
  max_cost P cost y1 ->
  max_cost P cost y2 ->
  y1 = y2.
Proof.
  unfold max_cost. intros (?&?&->&?) (?&?&->&?). auto using le_antisym.
Qed.

Lemma induced_subgraph_empty A (g : graph A) :
  induced_subgraph empty g ~= g_empty.
Proof.
  unfold gr_equiv. simpl.
  unfold set_equiv, set_equiv2. split; intros.
  - rewrite intersect_empty_l. unfold empty. reflexivity.
  - unfold empty. intuition.
Qed.

Lemma induced_subgraph_single A (P : A -> Prop) (v : A) (g : graph A) :
  V g v ->
  ~ E g v v ->
  set_equiv P (single v) ->
  induced_subgraph P g ~= g_single v.
Proof.
  unfold gr_equiv. simpl. intros Hv Hvv Hequiv.
  unfold set_equiv, set_equiv2. split; intros.
  - rewrite intersect_equiv_l; eauto. rewrite intersect_single_l.
    + unfold single. intuition.
    + assumption.
  - unfold set_equiv, single in Hequiv. repeat rewrite Hequiv. intuition.
    subst. auto.
Qed.

Lemma induced_subgraph_edge_empty A (g : graph A) :
  induced_subgraph_edge empty g ~= g_empty.
Proof.
  unfold gr_equiv. simpl.
  unfold set_equiv, set_equiv2, set_sum. split; intros.
  - rewrite vx_edge_empty, neighbourhood_empty. unfold empty. intuition.
  - unfold empty. intuition.
Qed.

Fact set_sum_equiv A (P P' Q Q' : A -> Prop) :
  set_equiv P P' -> set_equiv Q Q' -> set_equiv (set_sum P Q) (set_sum P' Q').
Proof.
  unfold set_equiv, set_sum. intros HP HQ x. rewrite HP, HQ. reflexivity.
Qed.

Fact set_sum2_equiv A (P P' Q Q' : A -> A -> Prop) :
  set_equiv2 P P' -> set_equiv2 Q Q' -> set_equiv2 (set_sum2 P Q) (set_sum2 P' Q').
Proof.
  unfold set_equiv2, set_sum2. intros HP HQ x y. rewrite HP, HQ. reflexivity.
Qed.

Lemma g_sum_equiv A (g1 g1' g2 g2' : graph A) :
  g1 ~= g1' -> g2 ~= g2' -> (g1 ||| g2) ~= (g1' ||| g2').
Proof.
  unfold gr_equiv. simpl. intros (HV1&HE1) (HV2&HE2).
  auto using set_sum_equiv, set_sum2_equiv.
Qed.

Fact gr_equiv_trans A (g1 g2 g3 : graph A) :
  g1 ~= g2 -> g2 ~= g3 -> g1 ~= g3.
Proof.
  unfold gr_equiv, set_equiv, set_equiv2. intros (HV1&HE1) (HV2&HE2).
  split; etransitivity; eauto.
Qed.

Fact g_sum_empty_l A (g : graph A) :
  g_empty ||| g ~= g.
Proof.
  unfold gr_equiv. simpl. unfold set_sum, set_sum2, set_equiv, set_equiv2.
  intuition.
Qed.

Fact g_sum_empty_r A (g : graph A) :
  g ||| g_empty ~= g.
Proof.
  unfold gr_equiv. simpl. unfold set_sum, set_sum2, set_equiv, set_equiv2.
  intuition.
Qed.

Lemma induced_subgraph_with_edge_empty A (g : graph A) :
  induced_subgraph_with_edge empty g ~= g_empty.
Proof.
  unfold induced_subgraph_with_edge. eapply gr_equiv_trans.
  - auto using g_sum_equiv, induced_subgraph_empty, induced_subgraph_edge_empty.
  - apply g_sum_empty_l.
Qed.

Lemma induced_subgraph_with_edge_and_vx_empty A (s : A) (g : graph A) :
  V g s ->
  ~ E g s s ->
  induced_subgraph_with_edge_and_vx empty s g ~= g_single s.
Proof.
  unfold induced_subgraph_with_edge_and_vx. intros. eapply gr_equiv_trans.
  - eauto using
      g_sum_equiv, induced_subgraph_single, set_equiv_spec_l, set_sum_empty_l,
      induced_subgraph_edge_empty.
  - apply g_sum_empty_r.
Qed.

Lemma no_walk_empty A (g : graph A) (s v : A) :
  g ~= g_empty ->
  set_equiv (is_walk g s v) empty.
Proof.
  unfold gr_equiv, set_equiv, set_equiv2, empty. simpl. intros (HV&HE) p. split.
  - inversion 1.
    + now rewrite HV in *.
    + now rewrite HE in *.
  - intros [].
Qed.

Lemma no_path_empty A (g : graph A) (s v : A) :
  g ~= g_empty ->
  set_equiv (is_path g s v) empty.
Proof.
  unfold set_equiv, empty, is_path. intros Hg p.
  eapply no_walk_empty in Hg as Hnowalk. unfold set_equiv in Hnowalk.
  rewrite Hnowalk. unfold empty. intuition.
Qed.

Lemma no_min_cost_elem_empty A B `(Ordered B) (P : A -> Prop) (C : A -> B) (x : A) :
  set_equiv P empty ->
  ~ min_cost_elem P C x.
Proof.
  unfold set_equiv, min_cost_elem, empty, not. intros Hempty (HP&_).
  now rewrite Hempty in HP.
Qed.

Lemma no_shortest_path_empty A
  (g : wgraph A) (s v : A) (p : list A) :
  g ~= g_empty ->
  ~ is_shortest_path g s v p.
Proof.
  unfold is_shortest_path. intros.
  auto using no_min_cost_elem_empty, no_path_empty.
Qed.

Lemma pred2graph_all_None_empty A
  (pred : A -> option A) (s : A) :
  (forall v : A, pred v = None) ->
  pred2graph s pred ~= g_single s.
Proof.
  unfold gr_equiv, set_equiv, set_equiv2. simpl. intros Hnone.
  split; intros; split.
  - intros [Heq | [(y&Hpred) | (y&Hpred)]];
      auto; try rewrite Hnone in Hpred; discriminate.
  - auto.
  - rewrite Hnone. discriminate.
  - contradiction.
Qed.

Lemma is_root_single A (s : A) (g : graph A) :
  g ~= g_single s -> is_root g s.
Proof.
  unfold gr_equiv, set_equiv, set_equiv2, is_root. simpl. intros (HV&HE) v Hv.
  apply HV in Hv as ->. exists [s]. constructor. apply HV. reflexivity.
Qed.

Lemma all_walks_trivial_single A (s : A) (g : graph A) (u v : A) (p : list A) :
  g ~= g_single s ->
  is_walk g u v p ->
  u = s /\ v = s /\ p = [s].
Proof.
  unfold gr_equiv, set_equiv, set_equiv2. simpl. intros (HV&HE) Hwalk.
  destruct Hwalk.
  - rewrite HV in *. repeat split; f_equal; assumption.
  - rewrite HE in *. contradiction.
Qed.

Lemma all_paths_trivial_single A (s : A) (g : graph A) (u v : A) (p : list A) :
  g ~= g_single s ->
  is_path g u v p ->
  u = s /\ v = s /\ p = [s].
Proof.
  unfold is_path. intros Hequiv (Hwalk&_).
  eapply all_walks_trivial_single; eassumption.
Qed.

Lemma all_undir_walks_trivial_single A (s : A) (g : graph A) (u v : A) (p : list A) :
  g ~= g_single s ->
  is_undir_walk g u v p ->
  u = s /\ v = s /\ p = [s].
Proof.
  unfold gr_equiv, set_equiv, set_equiv2. simpl. intros (HV&HE) Hwalk.
  destruct Hwalk.
  - rewrite HV in *. repeat split; f_equal; assumption.
  - rewrite HE in *. contradiction.
  - rewrite HE in *. contradiction.
Qed.

Lemma all_undir_paths_trivial_single A (s : A) (g : graph A) (u v : A) (p : list A) :
  g ~= g_single s ->
  is_undir_path g u v p ->
  u = s /\ v = s /\ p = [s].
Proof.
  unfold is_undir_path. intros Hequiv (Hwalk&_).
  eapply all_undir_walks_trivial_single; eassumption.
Qed.

Lemma valid_initial_distance A
  (D : A -> option nat) (pred : A -> option A) (s : A) (g : wgraph A) :
  V g s ->
  ~ E g s s ->
  Dijkstra_initial D pred s ->
  Dijkstra_distance_invariant D empty s g.
Proof.
  unfold Dijkstra_initial, Dijkstra_distance_invariant.
  intros HVs HEs (HDs&HD&Hpred).
  unfold wg_lift, are_valid_distances, is_shortest_path, min_cost_elem.
  simpl. intros v p (Hpath&_). eapply all_paths_trivial_single in Hpath as (_&->&->).
  - simpl. eassumption.
  - apply induced_subgraph_with_edge_and_vx_empty; eassumption.
Qed.

Lemma no_cycle_single A (s : A) (g : graph A) (p : list A) :
  g ~= g_single s -> ~ is_cycle g p.
Proof.
  unfold gr_equiv, set_equiv, set_equiv2, is_cycle, not. simpl.
  intros (HV&HE) (u&v&p'&Hpath&Hvu&Hp). rewrite HE in Hvu. assumption.
Qed.

Lemma is_acyclic_single A (s : A) (g : graph A) :
  g ~= g_single s -> is_acyclic g.
Proof.
  unfold is_acyclic. intros Hequiv p. eapply no_cycle_single. eassumption.
Qed.

Lemma is_rooted_tree_single A (s : A) (g : graph A) :
  g ~= g_single s ->
  is_rooted_tree s g.
Proof.
  unfold is_rooted_tree. eauto using is_root_single, is_acyclic_single.
Qed.

Lemma trivial_path_is_path A (v : A) (g : graph A) :
  V g v -> is_path g v v [v].
Proof.
  unfold is_path. intros Hv. split; repeat constructor; simpl; auto.
Qed.

Lemma trivial_path_is_shortest A (v : A) (g : wgraph A) :
  V g v -> is_shortest_path g v v [v].
Proof.
  unfold is_shortest_path, min_cost_elem. intros Hv. split.
  - apply trivial_path_is_path. assumption.
  - intros p Hpath. simpl. apply le_0_n.
Qed.

Lemma is_shortest_paths_tree_single A (s : A) (g : graph A) (wg : wgraph A) :
  g ~= g_single s ->
  V wg s ->
  is_shortest_paths_tree s g wg.
Proof.
  unfold is_shortest_paths_tree. intros Hequv Hs. split.
  - apply is_rooted_tree_single. assumption.
  - intros v p Hpath.
    eapply all_paths_trivial_single in Hpath as (_&->&->); [|eassumption].
    apply trivial_path_is_shortest. assumption.
Qed.

Lemma are_valid_predecessors_all_None A
  (pred : A -> option A) (s : A) (g : wgraph A) :
  V g s ->
  (forall v : A, pred v = None) ->
  are_valid_predecessors pred s g.
Proof.
  unfold are_valid_predecessors. intros Hs Hpred.
  apply is_shortest_paths_tree_single.
  - apply pred2graph_all_None_empty. assumption.
  - assumption.
Qed.

Lemma are_maximal_predecessors_all_None A
  (pred : A -> option A) (s : A) (g : graph A) :
  g ~= g_single s ->
  (forall v : A, pred v = None) ->
  are_maximal_predecessors pred s g.
Proof.
  unfold are_maximal_predecessors. intros Hsingle Hpred v p Hwalk.
  eapply all_walks_trivial_single in Hwalk as (_&->&_); eauto.
  exists [s]. constructor. simpl. auto.
Qed.

Lemma valid_initial_predecessors A
  (D : A -> option nat) (pred : A -> option A) (s : A) (g : wgraph A) :
  V g s ->
  ~ E g s s ->
  Dijkstra_initial D pred s ->
  Dijkstra_predecessors_invariant pred empty s g.
Proof.
  unfold Dijkstra_initial, Dijkstra_predecessors_invariant.
  intros HVs HEs (HDs&HD&Hpred) g' Hg'. subst. split.
  - apply are_valid_predecessors_all_None.
    + simpl. unfold set_sum, intersect, single. auto.
    + assumption.
  - simpl.
    apply are_maximal_predecessors_all_None;
      auto using induced_subgraph_with_edge_and_vx_empty.
Qed.

Theorem valid_initial A
  (D : A -> option nat) (pred : A -> option A) (s : A) (g : wgraph A) :
  V g s ->
  ~ E g s s ->
  Dijkstra_initial D pred s ->
  Dijkstra_invariant D pred empty s g.
Proof.
  unfold Dijkstra_invariant. intros.
  eauto using valid_initial_distance, valid_initial_predecessors.
Qed.

Theorem valid_invariant A
  (D D' : A -> option nat) (pred pred' : A -> option A) (P : A -> Prop)
  (s : A) (g : wgraph A) (v : A) :
  Dijkstra_invariant D pred P s g ->
  closest_neighbour g P D v ->
  distance_decrease g v D D' pred pred' ->
  Dijkstra_invariant D' pred' (add_single P v) s g.
Proof.
Admitted.

Theorem valid_final A
  (D : A -> option nat) (pred : A -> option A) (s : A) (g : wgraph A) :
  Dijkstra_invariant D pred total s g ->
  Dijkstra_final D pred s g.
Proof.
Admitted.
