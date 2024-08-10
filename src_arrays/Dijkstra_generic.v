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

Definition generic_dijkstra (get_size get_neighbours mkheap h_insert h_empty h_extract_min h_decrease_key h_free l_is_nil l_head l_tail : Value string) : Value string :=
  [-\] "g", [-\] "src", (*[-\] "dst",*)
    [let "n"] get_size <* Var "g" [in]
    [let "h"] mkheap <* Var "n" [in]
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
| is_graph_intro n g c m :
  (forall i, V g i ->
    exists v Lv L,
      Lookup (OfNat (n + i)) m v /\
      is_list Lv v c m /\
      is_elem_unique_list (neighbours g i) L /\
      Lv = nats2values L) ->
  is_graph g (Lab (OfNat n)) c m.

Inductive is_weighted_graph {A} : wgraph nat -> Value A -> StateAssertion A :=
| is_weighted_graph_intro n (g : wgraph nat) c m :
  (forall i, V g i ->
    exists v Lv L,
      Lookup (OfNat (n + i)) m v /\
      is_list Lv v c m /\
      is_elem_weighted_unique_list (neighbours g i) (W g i) L /\
      Lv = nat_pairs2values L) ->
  is_weighted_graph g (Lab (OfNat n)) c m.

Definition is_nat_function {V} (f : nat -> option nat) '(OfNat n0) : StateAssertion V :=
  fun c m =>
    forall n n', f n = Some n' <-> Lookup (OfNat (n0+n)) m (Int (Z.of_nat n')).

(*Parameter get_size get_neighbours mkheap h_insert h_empty h_extract_min h_decrease_key h_free l_is_nil l_head l_tail : Value string.*)

Definition get_size_spec {A} (get_size : Value A) : Prop :=
  forall g,
    triple_fun get_size
      (is_weighted_graph g)
      (fun v => <exists> n v',
        <[v = Int (Z.of_nat n)]> <*> <[is_set_size (V g) n]> <*>
          is_weighted_graph g v').

Definition get_neighbours_spec {A} (get_neighbours : Value A) : Prop :=
  forall l n (g : wgraph nat),
    triple_fun get_neighbours
      (fun v => <[v = Lab l]>)
      (fun v => <[
        triple_fun v
          (fun v => <[v = Int (Z.of_nat n)]> <*> <[V g n]> <*>
            is_weighted_graph g (Lab l))
          (fun v => <exists> L,
            <[is_elem_weighted_unique_list (neighbours g n) (W g n) L]> <*>
            is_list (nat_pairs2values L) v </\> is_weighted_graph g (Lab l))
      ]>).

Parameter is_heap :
  forall {V} (n : nat) (P : nat -> Prop) (W : nat -> option nat),
    Value V -> StateAssertion V.

Definition mkheap_spec {V} (mkheap : Value V) : Prop :=
  forall n,
    triple_fun mkheap
      (fun v => <[v = Int (Z.of_nat n)]>)
      (is_heap n empty (fun _ => None)).

Definition set_value_at (W : nat -> option nat) (x y n : nat) : option nat :=
  if n =? x then Some y else W n.

Definition h_insert_spec {V} (h_insert : Value V) : Prop :=
  forall n (P : nat -> Prop) (W : nat -> option nat) h (s k d : nat),
    is_set_size P s ->
    s < n ->
    ~ P k ->
    triple_fun h_insert
      (fun v => <[v = h]>)
      (fun v => <[
        triple_fun v
          (fun v => <[v = Int (Z.of_nat k)]>)
          (fun v => <[
            triple_fun v
              (fun v => <[v = Int (Z.of_nat d)]> <*> is_heap n P W h)
              (fun v => <[v = U_val]> <*>
                is_heap n (set_sum P (single k)) (set_value_at W k d) h)
          ]>)
      ]>).

Definition h_empty_spec {V} (h_empty : Value V) : Prop :=
  forall n (P : nat -> Prop) (W : nat -> option nat) h s,
    is_set_size P s ->
    triple_fun h_empty
      (fun v => <[v = h]> <*> is_heap n P W h)
      (fun v => <[v = Bool (s =? 0)]> <*> is_heap n P W h).

Definition unset_value_at (W : nat -> option nat) (x n : nat) : option nat :=
  if n =? x then None else W n.

Definition set_remove {A} (P : A -> Prop) (x y : A) : Prop :=
  P y /\ y <> x.

Definition h_extract_min_spec {V} (h_extract_min : Value V) : Prop :=
  forall n (P : nat -> Prop) (W : nat -> option nat) h k d,
    min_cost_elem P W k ->
    W k = Some d ->
    triple_fun h_extract_min
      (fun v => <[v = h]> <*> is_heap n P W h)
      (fun v => <[v = pair2Value nat2value nat2value (k,d)]> <*>
        is_heap n (set_remove P k) W h).

Definition h_decrease_key_spec {V} (h_decrease_key : Value V) : Prop :=
  forall n (P : nat -> Prop) (W : nat -> option nat) h k d,
  P k ->
  triple_fun h_decrease_key
    (fun v => <[v = h]>)
    (fun v => <[
      triple_fun v
        (fun v => <[v = Int (Z.of_nat k)]>)
        (fun v => <[
          triple_fun v
            (fun v => <[v = Int (Z.of_nat d)]> <*> is_heap n P W h)
            (fun v => <[v = U_val]> <*> is_heap n P (set_value_at W k d) h)
        ]>)
    ]>).

Definition h_free_spec {V} (h_free : Value V) : Prop :=
  forall n (P : nat -> Prop) (W : nat -> option nat),
  triple_fun h_free
    (is_heap n P W)
    (fun v => <[]>).

Definition is_nil_b {A} (L : list A) : bool :=
  match L with
  | nil => true
  | _ => false
  end.

Definition l_is_nil_spec {V} (l_is_nil : Value V) : Prop :=
  forall (L : list (Value V)) l,
    triple_fun l_is_nil
      (fun v => <[v = l]> <*> is_list L l)
      (fun v => <[v = Bool (is_nil_b L)]> <*> is_list L l).

Definition l_head_spec {V} (l_head : Value V) : Prop :=
  forall (L : list (Value V)) h l,
    triple_fun l_head
      (fun v => <[v = l]> <*> is_list (h::L)%list l)
      (fun v => <[v = h]> <*> is_list (h::L)%list l).

Definition l_tail_spec {V} (l_tail : Value V) : Prop :=
  forall (L : list (Value V)) h l t,
    triple_fun l_tail
      (fun v => <[v = l]> <*> is_list (h::L)%list l)
      (fun v => <[v = t]> <*> is_list (h::L)%list l </\> is_list L t).

Definition uncurry {A B C} (f : A -> B -> C) '(x,y) := f x y.

(*Definition is_max_label {A} (g : wgraph A) (C : nat) :=
  max_cost (uncurry (E g)) (uncurry (W g)) C.*)

Theorem triple_fun_generic_dijkstra
  (get_size get_neighbours mkheap h_insert h_empty
    h_extract_min h_decrease_key h_free l_is_nil l_head l_tail : Value string)
  (g : wgraph nat) l src D pred :
  get_size_spec       get_size ->
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
  exists c0 c2, forall n,
  is_set_size (V g) n ->
  triple_fun
    (generic_dijkstra
      get_size get_neighbours mkheap h_insert h_empty
      h_extract_min h_decrease_key h_free l_is_nil l_head l_tail)
    (fun v => <[v = Lab l]>)
    (fun v => <[triple_fun v
      (fun v => <[v = Int (Z.of_nat src)]> <*> is_weighted_graph g (Lab l) <*>
        <[V g src]> <*> <[Dijkstra_initial D pred src]> <*> sa_credits (c0 + c2*n*n))
      (fun v => <exists> lD lpred c, <[v = RecV [Lab lD; Lab lpred]]> <*>
        is_weighted_graph g (Lab l) <*> is_nat_function D lD <*>
        is_nat_function pred lpred <*> <[Dijkstra_final D pred src g]> <*> sa_credits c)]>).
Proof.
Admitted.
