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

Definition is_total {A} (g : graph A) :=
  forall u v, E g u v.

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

Definition min_cost_elem {A} (P : A -> Prop) (cost : A -> nat) (x : A) :=
  P x /\ forall (y : A), P y -> cost x <= cost y.

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
  exists (u v : A) (p' : list A), is_path g u v p' /\ p = v::p'.

(* undirected cycles *)
Definition is_cycle {A} (g : graph A) (p : list A) :=
  exists (u v : A) (p' : list A), is_undir_path g u v p' /\ p = v::p'.

Definition is_acyclic {A} (g : graph A) :=
  forall p : list A, ~ is_cycle g p.

Definition is_conected {A} (g : graph A) :=
  forall u v : A, exists p, is_undir_walk g u v p.

Definition is_tree {A} (g : graph A) (p : list A) :=
  is_conected g /\ is_acyclic g.

Definition is_root {A} (g : graph A) (r : A) :=
  forall v : A, exists p, is_walk g r v p.

Definition is_rooted_tree {A} (r : A) (g : graph A) :=
  is_root g r /\ is_acyclic g.

Definition is_shortest_paths_tree {A} (s : A) (t : graph A) (g : wgraph A) :=
  is_rooted_tree s t /\
    forall v p, is_path t s v p -> is_shortest_path g s v p.

Definition are_valid_distances {A} (D : A -> nat) (s : A) (g : wgraph A) :=
  forall v p, is_shortest_path g s v p -> D v = walk_cost (W g) p.

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
  (D : A -> nat) (P : A -> Prop) (s : A) (g : wgraph A) :=
  are_valid_distances D s (wg_lift (induced_subgraph_with_edge P) g).

Definition Dijkstra_predecessors_invariant {A}
  (pred : A -> option A) (P : A -> Prop) (s : A) (g : wgraph A) :=
  forall g', g' = (wg_lift (induced_subgraph_with_edge P) g) ->
    are_valid_predecessors pred s g' /\ are_maximal_predecessors pred s g'.

Definition Dijkstra_invariant {A}
  (D : A -> nat) (pred : A -> option A) (P : A -> Prop) (s : A) (g : wgraph A) :=
  Dijkstra_distance_invariant D P s g /\
  Dijkstra_predecessors_invariant pred P s g.
