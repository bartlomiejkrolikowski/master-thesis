Require List.
Import List.ListNotations.
Require Import String.
Require Import ZArith.

Require Import src_arrays.LambdaRef.
Require Import src_arrays.LamRefFacts.
Require Import src_arrays.LambdaAssertions_credits_perm.
Require Import src_arrays.LambdaTotalTriple_credits_perm.
Require Import src_arrays.LamRefLogicFactsTotal_credits_perm.
Require Import Lia.
Require Import src_arrays.Tactics.
Require Import src_arrays.SA_Tactics.
Require Import src_arrays.Interweave.

Require Import graphs.Graphs.

Definition init_array : Value string :=
  [-\] "array", [-\] "size", [-\] "value",
    [let "i"] Ref (Int 0) [in]
      [while] ! Var "i" [<] Var "size" [do]
        (Var "array" >> ! Var "i") <- Var "value";;
        Var "i" <- ! Var "i" [+] Int 1
      [end];;
      Free (Var "i")
    [end]%string.

Definition free_array : Value string :=
  [-\] "array", [-\] "size",
    [let "i"] Ref (Int 0) [in]
      [while] ! Var "i" [<] Var "size" [do]
        Free (Var "array" >> ! Var "i");;
        Var "i" <- ! Var "i" [+] Int 1
      [end];;
      Free (Var "i")
    [end]%string.

Definition generic_dijkstra (get_size get_max_label get_neighbours mkheap h_insert h_empty h_extract_min h_decrease_key h_free l_is_nil l_head l_tail : Value string) : Value string :=
  [-\] "g", [-\] "src", (*[-\] "dst",*)
    [let "n"] get_size <* Var "g" [in]
    [let "C"] get_max_label <* Var "g" [in]
    [let "h"] mkheap <* Var "n" <* Var "C" [in]
    [let "dist"] NewArray (Var "n") [in]
    [let "pred"] NewArray (Var "n") [in]
      init_array <* (Var "dist") <* (Var "n") <* (Int (-1));;
      init_array <* (Var "pred") <* (Var "n") <* (Int (-1));;
      (Var "dist" >> ! Var "i") <- Int 0;;
      h_insert <* Var "h" <* Var "src" <* Int 0;;
      [while] [~] (h_empty <* Var "h") [do]
        [let "rec_current"] h_extract_min <* (Var "h") [in]
        [let "current"] Get 0 (Var "rec_current") [in]
        [let "dist_current"] Get 1 (Var "rec_current") [in]
        [let "neighs"] Ref (get_neighbours <* Var "g" <* Var "current") [in]
        (* neighs : a reference to a list *)
          [while] [~] (l_is_nil <* Var "neighs") [do]
            [let "rec_neigh"] l_head <* Var "neighs" [in]
            [let "neigh"] Get 0 (Var "rec_neigh") [in]
            [let "length"] Get 1 (Var "rec_neigh") [in]
            [let "dist_neigh"] ! (Var "dist" >> Var "neigh") [in]
            [let "new_dist"] Var "dist_current" [+] Var "length" [in]
              [if] (Var "dist_neigh" [<] Int 0) [then]
                (Var "dist" >> Var "neigh") <- Var "new_dist";;
                (Var "pred" >> Var "neigh") <- Var "current";;
                h_insert <* Var "h" <* Var "neigh" <* Var "new_dist"
              [else] [if] (Var "new_dist" [<] Var "dist_neigh") [then]
                (Var "dist" >> Var "neigh") <- Var "new_dist";;
                (Var "pred" >> Var "neigh") <- Var "current";;
                h_decrease_key <* Var "h" <* Var "neigh" <* Var "new_dist"
              [else]
                U_val (* Nothing happens. *)
              [end]
            [end]
            [end]
            [end]
            [end]
            [end];;
            Var "neighs" <- l_tail <* Var "neighs"
          [end];;
          Free (Var "neighs")
        [end]
        [end]
        [end]
        [end]
      [end];;
      h_free <* (Var "h");;
      RecV [Var "dist"; Var "pred"]
      (*
      [let "x"] ! (Var "dist" >> Var "dst") [in]
        free_array <* (Var "dist");;
        Var "x"
      [end]
      *)
    [end]
    [end]
    [end]
    [end]
    [end]
    [end]%string.

Definition is_elem_list {A} (P : A -> Prop) (L : list A) :=
  forall x, List.In x L <-> P x.

Definition is_elem_weighted_list {A B} (P : A -> Prop) (W : A -> B) (L : list (A * B)) :=
  forall x w, List.In (x,w) L <-> (P x /\ w = W x).

Definition is_elem_unique_list {A} (P : A -> Prop) (L : list A) :=
  is_elem_list P L /\ List.NoDup L.

Definition is_elem_weighted_unique_list {A B} (P : A -> Prop) (W : A -> B) (L : list (A * B)) :=
  is_elem_weighted_list P W L /\ List.NoDup L.

Definition is_set_size {A} (P : A -> Prop) (n : nat) : Prop :=
  exists l, is_elem_unique_list P l /\ List.length l = n.

Parameter is_list : forall {V}, list (Value V) -> Value V -> StateAssertion V.

Definition nat2value {V} (n : nat) : Value V := Int (Z.of_nat n).
Definition pair2Value {A B V} (f : A -> Value V) (g : B -> Value V) '(x,y) : Value V :=
  RecV [f x; g y].

Definition nats2values {V} (L : list nat) : list (Value V) :=
  List.map (fun t => Int (Z.of_nat t)) L.
Definition nat_pairs2values {V} (L : list (nat * nat)) : list (Value V) :=
  List.map (fun '(x,w) => RecV [Int (Z.of_nat x); Int (Z.of_nat w)]) L.

Inductive is_graph {A} : graph nat -> Value A -> StateAssertion A :=
| is_graph_intro n g s c m :
  (forall i, V g i ->
    exists v Lv L,
      Lookup (OfNat (n + i)) m v /\
      is_list Lv v c m /\
      is_elem_unique_list (neighbours g i) L /\
      Lv = nats2values L) ->
  is_set_size (V g) s ->
  is_graph g (RecV [Lab (OfNat n); Int (Z.of_nat s)]) c m.

Definition is_max_label {A} (g : wgraph A) (C : nat) :=
  max_cost (uncurry (E g)) (uncurry (W g)) C.

Inductive is_weighted_graph {A} : wgraph nat -> Value A -> StateAssertion A :=
| is_weighted_graph_intro n (g : wgraph nat) C s c m :
  (forall i, V g i ->
    exists v Lv L,
      Lookup (OfNat (n + i)) m v /\
      is_list Lv v c m /\
      is_elem_weighted_unique_list (neighbours g i) (W g i) L /\
      Lv = nat_pairs2values L) ->
  is_max_label g C ->
  is_set_size (V g) s ->
  is_weighted_graph g
    (RecV [Lab (OfNat n); Int (Z.of_nat s); Int (Z.of_nat C)]) c m.

Definition is_nat_function {V} (f : nat -> option nat) '(OfNat n0) : StateAssertion V :=
  fun c m =>
    forall n n', f n = Some n' <-> Lookup (OfNat (n0+n)) m (Int (Z.of_nat n')).

(*Parameter get_size get_neighbours mkheap h_insert h_empty h_extract_min h_decrease_key h_free l_is_nil l_head l_tail : Value string.*)

Parameter get_size_cost : forall (c : nat), Prop.

Definition get_size_spec {A} (get_size : Value A) : Prop :=
  forall vg g c,
    get_size_cost c ->
    triple_fun get_size
      (fun v => $c <*> <[v = vg]> <*> is_weighted_graph g vg)
      (fun v => <exists> n,
        <[v = Int (Z.of_nat n)]> <*> <[is_set_size (V g) n]> <*>
        is_weighted_graph g vg).

Parameter get_neighbours_cost : forall (c : nat), Prop.

Definition get_neighbours_spec {A} (get_neighbours : Value A) : Prop :=
  forall vg n (g : wgraph nat) c,
    get_neighbours_cost c ->
    triple_fun get_neighbours
      (fun v => $1 <*> <[v = vg]>)
      (fun v => <[
        triple_fun v
          (fun v => $c <*> <[v = Int (Z.of_nat n)]> <*> <[V g n]> <*>
            is_weighted_graph g vg)
          (fun v => <exists> L,
            <[is_elem_weighted_unique_list (neighbours g n) (W g n) L]> <*>
            is_list (nat_pairs2values L) v </\> is_weighted_graph g vg)
      ]>).

Parameter get_max_label_cost : forall (c : nat), Prop.

Definition get_max_label_spec {A} (get_max_label : Value A) : Prop :=
  forall vg g c,
    get_max_label_cost c ->
    triple_fun get_max_label
      (fun v => $c <*> <[v = vg]> <*> is_weighted_graph g vg)
      (fun v => <exists> C,
        <[v = Int (Z.of_nat C)]> <*> <[is_max_label g C]> <*>
        is_weighted_graph g vg).

Parameter is_heap :
  forall {V} (n C : nat) (P : nat -> Prop) (W : nat -> option nat)
    (* asymptotic number of credits required to extract all the elements *)
    (potential : nat),
    Value V -> StateAssertion V.

Parameter heap_time_bound :
  forall (n C t : nat), Prop.

(*
Parameter place_in_heap :
  forall {V} (h : Value V) (x p : nat), Prop.
*)

Parameter mkheap_cost : forall (n C c : nat), Prop.

Definition mkheap_spec {V} (mkheap : Value V) : Prop :=
  forall n C c,
    mkheap_cost n C c ->
    triple_fun mkheap
      (fun v => $1 <*> <[v = Int (Z.of_nat n)]>)
      (fun v => <[
        triple_fun v
          (fun v => $c <*> <[v = Int (Z.of_nat C)]>)
          (is_heap n C empty (fun _ => None) 0)
      ]>).

Definition set_value_at (W : nat -> option nat) (x y n : nat) : option nat :=
  if n =? x then Some y else W n.

(*Parameter h_insert_cost : forall (n C c : nat), Prop.*)

Definition h_insert_spec {V} (h_insert : Value V) : Prop :=
  forall n C (P : nat -> Prop) (W : nat -> option nat) h (p s k d c t : nat),
    (*h_insert_cost n C c ->*)
    c = t ->
    heap_time_bound n C t ->
    is_set_size P s ->
    s < n ->
    ~ P k ->
    triple_fun h_insert
      (fun v => $1 <*> <[v = h]>)
      (fun v => <[
        triple_fun v
          (fun v => $1 <*> <[v = Int (Z.of_nat k)]>)
          (fun v => <[
            triple_fun v
              (fun v => $c <*> <[v = Int (Z.of_nat d)]> <*> is_heap n C P W p h)
              (fun v => (<exists> c', $c') <*> <[v = U_val]> <*>
                <exists> p', <[p' < p + t]> <*>
                  is_heap n C (set_sum P (single k)) (set_value_at W k d) p' h)
          ]>)
      ]>).

Parameter h_empty_cost : forall (c : nat), Prop.

Definition h_empty_spec {V} (h_empty : Value V) : Prop :=
  forall n C (P : nat -> Prop) (W : nat -> option nat) h s c p,
    h_empty_cost c ->
    is_set_size P s ->
    triple_fun h_empty
      (fun v => $1 <*> <[v = h]> <*> is_heap n C P W p h)
      (fun v => <[v = Bool (s =? 0)]> <*> is_heap n C P W p h).

Definition unset_value_at (W : nat -> option nat) (x n : nat) : option nat :=
  if n =? x then None else W n.

Definition set_remove {A} (P : A -> Prop) (x y : A) : Prop :=
  P y /\ y <> x.

Parameter h_extract_min_cost : forall {V} (c : nat) (h : Value V), StateAssertion V.

Definition h_extract_min_spec {V} (h_extract_min : Value V) : Prop :=
  forall n C (P : nat -> Prop) (W : nat -> option nat) p h k d c,
    min_cost_elem P W k ->
    W k = Some d ->
    triple_fun h_extract_min
      (fun v => $c <*> <[v = h]> <*> is_heap n C P W p h </\> h_extract_min_cost c h)
      (fun v => (<exists> c', $c') <*> <[v = pair2Value nat2value nat2value (k,d)]> <*>
        <exists> p', <[p = p' + c]> <*> is_heap n C (set_remove P k) W p' h).

Parameter h_decrease_key_cost : forall {V} (c : nat) (h : Value V), StateAssertion V.

Definition h_decrease_key_spec {V} (h_decrease_key : Value V) : Prop :=
  forall n C (P : nat -> Prop) (W : nat -> option nat) p h k d c,
  P k ->
  triple_fun h_decrease_key
    (fun v => $1 <*> <[v = h]>)
    (fun v => <[
      triple_fun v
        (fun v => $1 <*> <[v = Int (Z.of_nat k)]>)
        (fun v => <[
          triple_fun v
            (fun v => $c <*> <[v = Int (Z.of_nat d)]> <*>
              is_heap n C P W p h </\> h_decrease_key_cost c h)
            (fun v => (<exists> c', $c') <*> <[v = U_val]> <*>
              <exists> p', <[p = p' + c]> <*> is_heap n C P (set_value_at W k d) p' h)
        ]>)
    ]>).

Parameter h_free_cost : forall (n C s c : nat), Prop.

Definition h_free_spec {V} (h_free : Value V) : Prop :=
  forall n C (P : nat -> Prop) (W : nat -> option nat) s c p,
  is_set_size P s ->
  h_free_cost n C s c ->
  triple_fun h_free
    (is_heap n C P W p <*>+ $c)
    (fun v => <exists> c', $c').

Definition is_nil_b {A} (L : list A) : bool :=
  match L with
  | nil => true
  | _ => false
  end.

Parameter l_is_nil_cost : forall (c : nat), Prop.

Definition l_is_nil_spec {V} (l_is_nil : Value V) : Prop :=
  forall (L : list (Value V)) l c,
    l_is_nil_cost c ->
    triple_fun l_is_nil
      (fun v => $c <*> <[v = l]> <*> is_list L l)
      (fun v => <[v = Bool (is_nil_b L)]> <*> is_list L l).

Parameter l_head_cost : forall (c : nat), Prop.

Definition l_head_spec {V} (l_head : Value V) : Prop :=
  forall (L : list (Value V)) h l c,
    l_head_cost c ->
    triple_fun l_head
      (fun v => $ c <*> <[v = l]> <*> is_list (h::L)%list l)
      (fun v => <[v = h]> <*> is_list (h::L)%list l).

Parameter l_tail_cost : forall (c : nat), Prop.

Definition l_tail_spec {V} (l_tail : Value V) : Prop :=
  forall (L : list (Value V)) h l t c,
    l_tail_cost c ->
    triple_fun l_tail
      (fun v => $c <*> <[v = l]> <*> is_list (h::L)%list l)
      (fun v => <[v = t]> <*> is_list (h::L)%list l </\> is_list L t).

Theorem triple_fun_generic_dijkstra
  (get_size get_max_label get_neighbours mkheap h_insert h_empty
    h_extract_min h_decrease_key h_free l_is_nil l_head l_tail : Value string) :
  is_closed_value get_size ->
  is_closed_value get_max_label ->
  is_closed_value get_neighbours ->
  is_closed_value mkheap ->
  is_closed_value h_insert ->
  is_closed_value h_empty ->
  is_closed_value h_extract_min ->
  is_closed_value h_decrease_key ->
  is_closed_value h_free ->
  is_closed_value l_is_nil ->
  is_closed_value l_head ->
  is_closed_value l_tail ->
  get_size_spec       get_size ->
  get_max_label_spec  get_max_label ->
  get_neighbours_spec get_neighbours ->
  mkheap_spec         mkheap ->
  h_insert_spec       h_insert ->
  h_empty_spec        h_empty ->
  h_extract_min_spec  h_extract_min ->
  h_decrease_key_spec h_decrease_key ->
  h_free_spec         h_free ->
  l_is_nil_spec       l_is_nil ->
  l_head_spec         l_head ->
  l_tail_spec         l_tail ->
  exists c0 cn cm, forall (g : wgraph nat) vg src D pred n m C t,
  is_set_size (V g) n ->
  is_set_size (uncurry (E g)) m ->
  is_max_label g C ->
  heap_time_bound n C t ->
  triple_fun
    (generic_dijkstra
      get_size get_max_label get_neighbours mkheap h_insert h_empty
      h_extract_min h_decrease_key h_free l_is_nil l_head l_tail)
    (fun v => $1 <*> <[v = vg]>)
    (fun v => <[triple_fun v
      (fun v => $ (c0 + cm*m + cn*n*t) <*> <[v = Int (Z.of_nat src)]> <*>
        is_weighted_graph g vg <*> <[V g src]> <*> <[Dijkstra_initial D pred src]>)
      (fun v => (<exists> c, $c) <*> <exists> lD lpred, <[v = RecV [Lab lD; Lab lpred]]> <*>
        is_weighted_graph g vg <*> is_nat_function D lD <*>
        is_nat_function pred lpred <*> <[Dijkstra_final D pred src g]>)]>).
Proof using.
(*unfold is_closed_value.*)
  intros Hclosed_get_size Hclosed_get_max_label Hclosed_get_neighbours Hclosed_mkheap
    Hclosed_h_insert Hclosed_h_empty Hclosed_h_extract_min Hclosed_h_decrease_key
    Hclosed_h_free Hclosed_l_is_nil Hclosed_l_head Hclosed_l_tail.
  unfold get_size_spec, get_neighbours_spec, get_max_label_spec, mkheap_spec, h_insert_spec, h_empty_spec,
    h_extract_min_spec, h_decrease_key_spec, h_free_spec, l_is_nil_spec, l_head_spec, l_tail_spec.
  intros. eexists ?[c0], ?[cn], ?[cm]. intros. unfold triple_fun, generic_dijkstra, StringLam. simpl. intros.
  repeat (rewrite map_v_shift_closed; [|repeat apply map_v_closed_value; assumption]).
  app_lambda. triple_pull_pure. subst. solve_simple_value; [|rewrite_empty_spec; rewrite pure_spec; auto].
  split_all; auto. intros. cbn. triple_pull_pure. solve_simple_value.
  rewrite_empty_spec. rewrite pure_spec. split_all; auto. intros.
  instantiate (c0 := S ?[cc0]). instantiate (cc0 := ?[c0]).
  triple_pull_1_credit. app_lambda. simpl. subst. solve_simple_value.
  split_all; auto. intros. cbn. triple_reorder_pure. repeat triple_pull_pure. subst.
  rewrite bind_v_shift, bind_v_id.
  instantiate (c0 := S ?[cc0]). instantiate (cc0 := ?[c0]).
  fold (inc_set string).
  repeat rewrite bind_v_liftS_shift_swap. repeat rewrite bind_v_shift. repeat rewrite bind_v_id. simpl.
  triple_pull_1_credit. app_lambda.
  2:{
    instantiate (c0 := S ?[cc0]). instantiate (cc0 := ?[c0]). triple_pull_1_credit.
    eapply triple_weaken, triple_frame, triple_fun_app.
    { apply implies_spec. intros. swap_star_ctx. normalize_star. swap_star_ctx. eassumption. }
    { prove_implies_refl. }
    { apply H. admit. }
    { solve_simple_value. swap_star. solve_star. eassumption. }
  }
  solve_simple_value. split_all; auto. intros. cbn.
  fold (inc_set (inc_set string)).
  fold (inc_set string).
  repeat rewrite bind_v_liftS_shift_swap. repeat rewrite bind_v_shift. repeat rewrite bind_v_id. simpl.
  instantiate (c0 := S ?[cc0]). instantiate (cc0 := ?[c0]).
  triple_pull_1_credit. app_lambda.
  2:{
    instantiate (c0 := S ?[cc0]). instantiate (cc0 := ?[c0]). triple_pull_1_credit.
    eapply triple_weaken, triple_frame, triple_fun_app.
    { apply implies_spec. intros.
      match goal with
      | [H : _ ?c ?m |- _ ?c ?m] => eapply star_implies_mono in H
      end.
      { apply star_assoc_l. eassumption. }
      { prove_implies_refl. }
      { apply implies_spec. intros. swap_star_ctx. apply star_assoc_r.
        match goal with
        | [H : _ ?c ?m |- _ ?c ?m] => eapply star_implies_mono in H
        end.
        { eassumption. }
        { apply implies_spec. intros.
          match goal with
          | [H : _ ?c ?m |- _ ?c ?m] => apply star_exists_l in H
          end.
          swap_star. eassumption. }
        { prove_implies_refl. } } }
    { prove_implies_refl. }
    { apply H0. admit. }
    { solve_simple_value. swap_star. swap_star_ctx. solve_star. eassumption. }
  }
  solve_simple_value. split_all; auto. intros. cbn.
  fold (inc_set (inc_set (inc_set string))).
  fold (inc_set (inc_set string)).
  fold (inc_set string).
  repeat rewrite bind_v_liftS_shift_swap. repeat rewrite bind_v_shift. repeat rewrite bind_v_id. simpl.
  (*TODO:
  triple_pull_exists.
  triple_reorder_pure.
  triple_pull_pure.*)
Admitted.
