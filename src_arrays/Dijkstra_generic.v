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
Require Import src_arrays.Dijkstra_aux.
Require Import src_arrays.Dijkstra_aux_graphs.

Definition generic_dijkstra (get_size get_max_label get_neighbours mkheap h_insert h_empty h_extract_min h_decrease_key h_free l_is_nil l_head l_tail : Value string) : Value string :=
  [-\] "g", [-\] "src", (*[-\] "dst",*)
    [let "n"] get_size <* Var "g" [in]
    [let "C"] get_max_label <* Var "g" [in]
    [let "h"] mkheap <* Var "n" <* Var "C" [in]
    [let "dist"] NewArray (Var "n") [in]
    [let "pred"] NewArray (Var "n") [in]
      init_array <* (Var "dist") <* (Var "n") <* (Int (-1));;
      init_array <* (Var "pred") <* (Var "n") <* (Int (-1));;
      assign_array_at <* Var "dist" <* Var "src" <* Int 0;;
      h_insert <* Var "h" <* Var "src" <* Int 0;;
      [while] [~] (h_empty <* Var "h") [do]
        [let "rec_current"] h_extract_min <* (Var "h") [in]
        [let "current"] Get 0 (Var "rec_current") [in]
        [let "dist_current"] Get 1 (Var "rec_current") [in]
        [let "neighs"] Ref (get_neighbours <* Var "g" <* Var "current") [in]
        (* neighs : a reference to a list *)
          [while] [~] (l_is_nil <* ! Var "neighs") [do]
            [let "rec_neigh"] l_head <* ! Var "neighs" [in]
            [let "neigh"] Get 0 (Var "rec_neigh") [in]
            [let "length"] Get 1 (Var "rec_neigh") [in]
            [let "dist_neigh"] read_array_at <* Var "dist" <* Var "neigh" [in]
            [let "new_dist"] Var "dist_current" [+] Var "length" [in]
              [if] (Var "dist_neigh" [<] Int 0) [then]
                assign_array_at <* Var "dist" <* Var "neigh" <* Var "new_dist";;
                assign_array_at <*Var "pred" <* Var "neigh" <* Var "current";;
                h_insert <* Var "h" <* Var "neigh" <* Var "new_dist"
              [else] [if] (Var "new_dist" [<] Var "dist_neigh") [then]
                assign_array_at <* Var "dist" <* Var "neigh" <* Var "new_dist";;
                assign_array_at <* Var "pred" <* Var "neigh" <* Var "current";;
                h_decrease_key <* Var "h" <* Var "neigh" <* Var "new_dist"
              [else]
                U_val (* Nothing happens. *)
              [end]
              [end]
            [end]
            [end]
            [end]
            [end]
            [end];;
            Var "neighs" <- l_tail <* ! Var "neighs"
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

Parameter is_list : forall {V}, list (Value V) -> Value V -> StateAssertion V.

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

Parameter get_size_cost : forall (c : nat), Prop.

Axiom get_size_cost_exists : exists c, get_size_cost c.

Definition get_size_spec {A} (get_size : Value A) : Prop :=
  forall vg g c,
    get_size_cost c ->
    triple_fun get_size
      (fun v => $c <*> <[v = vg]> <*> is_weighted_graph g vg)
      (fun v => <exists> n,
        <[v = Int (Z.of_nat n)]> <*> <[is_set_size (V g) n]> <*>
        is_weighted_graph g vg).

Parameter get_neighbours_cost : forall (c : nat), Prop.

Axiom get_neighbours_cost_exists : exists c, get_neighbours_cost c.

Definition get_neighbours_spec {A} (get_neighbours : Value A) : Prop :=
  forall vg n (g : wgraph nat) c,
    get_neighbours_cost c ->
    triple_fun_n_ary 1 get_neighbours
      (fun v1 v2 => $c <*>
        <[v1 = vg]> <*> <[v2 = Int (Z.of_nat n)]> <*> <[V g n]> <*>
        is_weighted_graph g vg)
      (fun v1 v2 res => <exists> L,
        <[is_elem_weighted_unique_list (neighbours g n) (W g n) L]> <*>
        is_list (nat_pairs2values L) res <*>
        (is_list (nat_pairs2values L) res <-*> is_weighted_graph g vg)).

Parameter get_max_label_cost : forall (c : nat), Prop.

Axiom get_max_label_cost_exists : exists c, get_max_label_cost c.

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

Axiom heap_time_bound_ge_1 :
  forall n C t, heap_time_bound n C t -> t >= 1.

Axiom equiv_set_heap :
  forall V n C P P' W potential (h : Value V),
    set_equiv P P' ->
    is_heap n C P W potential h ->>
      is_heap n C P' W potential h.

Parameter mkheap_cost : forall (n C c : nat), Prop.

Axiom mkheap_cost_exists : exists c0, forall n C t, exists c1 c,
  heap_time_bound n C t ->
  c1 + c = c0 * t /\ mkheap_cost n C c.

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
  forall n C (P : nat -> Prop) (W : nat -> option nat) (p s k d c t : nat),
    (*h_insert_cost n C c ->*)
    c = t ->
    heap_time_bound n C t ->
    is_set_size P s ->
    s < n ->
    ~ P k ->
    triple_fun_n_ary 2 h_insert
      (fun h v2 v3 => $c <*> <[v2 = Int (Z.of_nat k)]> <*> <[v3 = Int (Z.of_nat d)]> <*> is_heap n C P W p h)
      (fun h v2 v3 res => (<exists> c', $c') <*> <[res = U_val]> <*>
        <exists> p', <[p' < p + t]> <*>
          is_heap n C (set_sum P (single k)) (set_value_at W k d) p' h).

Parameter h_empty_cost : forall (c : nat), Prop.

Axiom h_empty_cost_exists : exists c, h_empty_cost c.

Definition h_empty_spec {V} (h_empty : Value V) : Prop :=
  forall n C (P : nat -> Prop) (W : nat -> option nat) h s c p,
    h_empty_cost c ->
    is_set_size P s ->
    triple_fun h_empty
      (fun v => $c <*> <[v = h]> <*> is_heap n C P W p h)
      (fun v => <[v = Bool (s =? 0)]> <*> is_heap n C P W p h).

Definition unset_value_at (W : nat -> option nat) (x n : nat) : option nat :=
  if n =? x then None else W n.

Definition set_remove {A} (P : A -> Prop) (x y : A) : Prop :=
  P y /\ y <> x.

(*
Parameter h_extract_min_cost : forall {V} (c : nat) (h : Value V), StateAssertion V.

Axiom h_extract_min_cost_exists : forall {V} n C P W p h c (m : Map V),
  is_heap n C P W p h c m ->
  is_set_size P s ->
  s > 0 ->
  exists k, h_extract_min_cost k h c m.
*)

Definition h_extract_min_spec {V} (h_extract_min : Value V) : Prop :=
  forall n C (P : nat -> Prop) (W : nat -> option nat) p h k d c,
    c = p ->
    min_cost_elem P W k ->
    W k = Some d ->
    triple_fun h_extract_min
      (fun v => $c <*> <[v = h]> <*> is_heap n C P W p h)
      (fun v => <exists> c' cx p', $c' <*> <[c' = p' + cx]> <*>
        <[v = pair2Value nat2value nat2value (k,d)]> <*>
        is_heap n C (set_remove P k) W p' h).

(*
Parameter h_decrease_key_cost : forall {V} (c : nat) (h : Value V), StateAssertion V.
*)

Definition h_decrease_key_spec {V} (h_decrease_key : Value V) : Prop :=
  forall n C (P : nat -> Prop) (W : nat -> option nat) p h k d c,
  c = p ->
  P k ->
  triple_fun_n_ary 2 h_decrease_key
    (fun v1 v2 v3 => $1 <*> $c <*> <[v1 = h]> <*> <[v2 = Int (Z.of_nat k)]> <*>
      <[v3 = Int (Z.of_nat d)]> <*> is_heap n C P W p h)
    (fun v1 v2 v3 res => <exists> c' cx p', $c' <*> <[c' <= p' + cx]> <*>
      <[res = U_val]> <*> is_heap n C P (set_value_at W k d) p' h).

Parameter h_free_cost : forall (n C s c : nat), Prop.

Definition h_free_spec {V} (h_free : Value V) : Prop :=
  forall n C (P : nat -> Prop) (W : nat -> option nat) s c p,
  is_set_size P s ->
  h_free_cost n C s c ->
  triple_fun h_free
    (is_heap n C P W p <*>+ $c)
    (fun v => <[v = U_val]> <*> <exists> c', $c').

Axiom h_free_cost_exists : exists c0, forall n C t s, exists c1 c,
  heap_time_bound n C t ->
  c1 + c = c0 * (t+s) /\ h_free_cost n C s c.

Parameter l_is_nil_cost : forall (c : nat), Prop.

Axiom l_is_nil_cost_exists : exists c, l_is_nil_cost c.

Definition l_is_nil_spec {V} (l_is_nil : Value V) : Prop :=
  forall (L : list (Value V)) l c,
    l_is_nil_cost c ->
    triple_fun l_is_nil
      (fun v => $c <*> <[v = l]> <*> is_list L l)
      (fun v => <[v = Bool (is_nil_b L)]> <*> is_list L l).

Parameter l_head_cost : forall (c : nat), Prop.

Axiom l_head_cost_exists : exists c, l_head_cost c.

Definition l_head_spec {V} (l_head : Value V) : Prop :=
  forall (L : list (Value V)) h l c,
    l_head_cost c ->
    triple_fun l_head
      (fun v => $ c <*> <[v = l]> <*> is_list (h::L)%list l)
      (fun v => <[v = h]> <*> is_list (h::L)%list l).

Parameter l_tail_cost : forall (c : nat), Prop.

Axiom l_tail_cost_exists : exists c, l_tail_cost c.

Definition l_tail_spec {V} (l_tail : Value V) : Prop :=
  forall (L : list (Value V)) h l t c,
    l_tail_cost c ->
    triple_fun l_tail
      (fun v => $c <*> <[v = l]> <*> is_list (h::L)%list l)
      (fun v => <[v = t]> <*> is_list L l <*> (is_list L l <-*> is_list (h::L)%list t)).

Lemma is_set_size_with_neighbours A B (P : A -> Prop) s g n x f L1 L2 :
  is_irreflexive g ->
  is_set_size (V g) n ->
  is_set_size P s ->
  P x ->
  @is_elem_weighted_unique_list A B (neighbours g x) f (L1 ++ L2)%list ->
  exists s', s' < n /\ is_set_size
    (set_sum (set_remove P x) (fun y => List.In y (List.map fst L1))) s'.
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

Lemma Dijkstra_invariant_if_D_some A
  (D : A -> option nat) (pred : A -> option A) (P : A -> Prop)
  (s : A) (g : wgraph A) x n n1 n2 pr1 pr2 :
  Dijkstra_invariant D pred P s g ->
  D x = Some n ->
  pred x = Some pr1 ->
  E g pr2 x ->
  D pr1 = Some n1 ->
  D pr2 = Some n2 ->
  n = n1 + W g pr1 x ->
  n2 + W g pr2 x < n ->
  (P = empty /\ x = s) \/ (P s /\ neighbourhood g P x).
Proof.
Admitted.

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
  exists c0 cn cm, forall (g : wgraph nat) vg src n m C t,
  n >= 1 ->
  V g src ->
  is_irreflexive g ->
  is_init_range (V g) ->
  is_set_size (V g) n ->
  is_set_size (uncurry (E g)) m ->
  is_max_label g C ->
  heap_time_bound n C t ->
  triple_fun_n_ary 1
    (generic_dijkstra
      get_size get_max_label get_neighbours mkheap h_insert h_empty
      h_extract_min h_decrease_key h_free l_is_nil l_head l_tail)
    (fun v1 v2 => $ (c0 + cm*m + cn*n*t) <*>
      <[v1 = vg]> <*> <[v2 = Int (Z.of_nat src)]> <*>
      is_weighted_graph g vg)
    (fun v1 v2 res => (<exists> c, $c) <*> <exists> lD lpred D pred,
      <[res = RecV [Lab lD; Lab lpred]]> <*>
      is_weighted_graph g vg <*> is_nat_function D lD <*>
      is_nat_function pred lpred <*> <[Dijkstra_final D pred src g]>).
Proof.
(*unfold is_closed_value.*)
  intros Hclosed_get_size Hclosed_get_max_label Hclosed_get_neighbours Hclosed_mkheap
    Hclosed_h_insert Hclosed_h_empty Hclosed_h_extract_min Hclosed_h_decrease_key
    Hclosed_h_free Hclosed_l_is_nil Hclosed_l_head Hclosed_l_tail.
  intros Hspec_get_size Hspec_get_max_label Hspec_get_neighbours Hspec_mkheap
    Hspec_h_insert Hspec_h_empty Hspec_h_extract_min Hspec_h_decrease_key
    Hspec_h_free Hspec_l_is_nil Hspec_l_head Hspec_l_tail.
  specialize get_size_cost_exists as (c_size&?).
  specialize get_neighbours_cost_exists as (c_neighbours&?).
  specialize get_max_label_cost_exists as (c_max_label&?).
  specialize mkheap_cost_exists as (c_mkheap&Hmkheap_cost).
  specialize h_empty_cost_exists as (c_h_empty&?).
  specialize h_free_cost_exists as (c_h_free&Hh_free_cost).
  specialize l_is_nil_cost_exists as (c_is_nil&?).
  specialize l_head_cost_exists as (c_l_head&?).
  specialize l_tail_cost_exists as (c_l_tail&?).
  eexists ?[c0], ?[cn], ?[cm]. intros. simpl.
  unfold triple_fun, generic_dijkstra, StringLam. simpl. intros.
  lazymatch goal with
  | [H : heap_time_bound _ _ ?t |- _] =>
    apply heap_time_bound_ge_1 in H as ?;
    assert (exists t', t = S t') as (?&?) by (destruct t; eauto; lia);
    subst t
  end.
  rewrite_all_map_v_closed.
  repeat lazymatch goal with [H : is_closed_value _ |- _] => clear H end.
  app_lambda. triple_pull_pure. subst. solve_simple_value; [|rewrite_empty_spec; rewrite pure_spec; auto].
  split_all; auto. intros. cbn. triple_pull_pure. solve_simple_value.
  rewrite_empty_spec. rewrite pure_spec. split_all; auto. intros.
  triple_reorder_credits. app_lambda. simpl. subst. solve_simple_value.
  split_all; auto. intros. cbn. triple_reorder_pure. repeat triple_pull_pure. subst.
  rewrite bind_v_shift, bind_v_id.
  instantiate (c0 := S ?[cc0]). instantiate (cc0 := ?[c0]).
  fold_all_inc_set_string. rewrite_all_binds. simpl.
  triple_pull_1_credit. app_lambda.
  2:{
    unfold get_size_spec in Hspec_get_size.
    instantiate (c0 := c_size + ?[cc0]). instantiate (cc0 := ?[c0]).
    do 2 rewrite <- Nat.add_assoc.
    triple_reorder_credits. triple_pull_credits c_size.
    eapply triple_weaken, triple_frame, triple_fun_app.
    { apply implies_spec. intros. swap_star_ctx. conormalize_star. eassumption. }
    { prove_implies_refl. }
    { eauto. }
    { solve_simple_value. swap_star. solve_star. eassumption. }
  }
  clear get_size Hspec_get_size.
  solve_simple_value. split_all; auto. intros. cbn. rewrite_all_binds. simpl.
  triple_reorder_exists. triple_pull_exists.
  triple_reorder_pure. repeat triple_pull_pure.
  instantiate (c0 := S ?[cc0]). instantiate (cc0 := ?[c0]).
  triple_pull_1_credit. app_lambda.
  2:{
    unfold get_max_label_spec in Hspec_get_max_label.
    instantiate (c0 := c_max_label + ?[cc0]). instantiate (cc0 := ?[c0]).
    rewrite <- Nat.add_assoc.
    triple_reorder_credits. triple_pull_credits c_max_label.
    eapply triple_weaken, triple_frame, triple_fun_app.
    { apply implies_spec. intros. swap_star_ctx. conormalize_star.
      match goal with
      | [H : _ ?c ?m |- _ ?c ?m] => eapply star_implies_mono in H
      end.
      { eassumption. }
      { prove_implies_refl. }
      { prove_implies_refl. } }
    { prove_implies_refl. }
    { eauto. }
    { solve_simple_value. swap_star. normalize_star. solve_star. eassumption. }
  }
  clear get_max_label Hspec_get_max_label.
  solve_simple_value. split_all; auto. intros. cbn. rewrite_all_binds. simpl.
  triple_reorder_exists. repeat triple_pull_exists.
  triple_reorder_pure. repeat triple_pull_pure. subst.
  lazymatch goal with
  | [H1 : is_max_label g _, H2 : is_max_label g _ |- _] =>
    specialize (max_label_unique _ _ _ _ H1 H2) as <-
  end.
  lazymatch goal with
  | [H1 : is_set_size (V (G g)) ?n1,
     H2 : is_set_size (V (G g)) ?n2
    |- _ ] => apply (is_set_size_unique _ _ _ _ H1) in H2 as <-
  end.
  destruct n as [|n'] eqn:Hn; [lia|]. rewrite <- Hn.
  edestruct Hmkheap_cost as (c1'&c'&Hcost_eq&?); eauto.
  instantiate (c0 := S ?[cc0]). instantiate (cc0 := ?[c0]).
  triple_pull_1_credit. app_lambda.
  2:{
    unfold mkheap_spec in Hspec_mkheap.
    instantiate (c0 := S (S ?[cc0])). instantiate (cc0 := ?[c0]). simpl.
    triple_pull_credits 2. triple_reorder_credits.
    eapply triple_weaken, triple_frame, triple_fun_app2.
    4:solve_simple_value.
    1:{ apply star_assoc. }
    2:{
      instantiate (c0 := S ?[cc0]). instantiate (cc0 := ?[c0]).
      triple_pull_1_credit.
      instantiate (cn := ?[ccn] + c_mkheap). instantiate (ccn := ?[cn]).
      erewrite (Nat.mul_add_distr_r _ c_mkheap n),
        (Nat.mul_add_distr_r _ (c_mkheap*n)).
      do 2 erewrite (Nat.add_assoc _ _ (c_mkheap*n*_)).
      erewrite (Nat.add_comm _ (c_mkheap*n*_)).
      lazymatch goal with
      | [|- triple _ (_ <*> (_ <*> $ S (?c1+?c2))) _] =>
        triple_reorder (@sa_credits string (S (c1+c2)));
        rewrite <- Nat.add_succ_r;
        triple_pull_credits c1
      end.
      triple_reorder_credits.
      erewrite Hn, (Nat.mul_succ_r c_mkheap),
        (Nat.mul_add_distr_r (c_mkheap*n') c_mkheap),
        (Nat.add_comm (c_mkheap*n'*_) (c_mkheap*_)), <- Hn.
      lazymatch goal with
      | [|- triple _ ($ (?c1 + _) <*> _) _] =>
        triple_pull_credits c1
      end.
      triple_reorder_credits. rewrite <- Hcost_eq, (Nat.add_comm c1' c').
      lazymatch goal with
      | [|- triple _ ($ (?c1 + _) <*> _) _] =>
        triple_pull_credits c1
      end.
      triple_reorder_credits.
      eapply triple_weaken, triple_frame, triple_fun_app.
      3:{ apply Hspec_mkheap. eauto. }
      3:solve_simple_value.
      { rewrite <- Hn. apply implies_spec. intros. solve_star. swap_star.
        solve_star. swap_star. revert_implies. prove_implies_rev. }
      { apply implies_post_spec. intros. normalize_star.
        solve_star; [apply triple_fun_frame; eassumption|].
        simpl. solve_star. swap_star. solve_star. swap_star. eassumption. }
    }
    1:{ prove_implies_refl. }
  }
  clear mkheap Hspec_mkheap.
  solve_simple_value. split_all; auto. intros. cbn. rewrite_all_binds. simpl.
  triple_reorder_credits.
  eapply triple_weaken with (Q := (fun x => (<exists> c, $c) <*> _) <*>+ _),
    triple_frame with (H := $c1' <*> $(c_mkheap*n'*_)).
  { prove_implies. }
  { apply implies_post_spec. intros. normalize_star. swap_star_ctx.
    normalize_star. swap_star_ctx. revert_implies. apply star_implies_mono.
    { apply implies_spec. intros. solve_star.
      eapply credits_star_l; try reflexivity.
      eapply star_implies_mono; eauto.
      { apply credits_star_l. reflexivity. }
      { prove_implies_refl. } }
    { prove_implies_refl. } }
  rewrite <- Hn. instantiate (c0 := S ?[cc0]). instantiate (cc0 := ?[c0]).
  triple_pull_1_credit. app_lambda.
  2:{
    triple_pull_1_credit.
    apply triple_new_array_content. solve_simple_value.
    { lia. }
    { match goal with
      | [H : ?Q ?c ?m |- ?F ?v ?c ?m] =>
        unify F (fun t => <[t = v]> <*> Q)
      end.
      simpl. solve_star. }
  }
  solve_simple_value. split_all; auto. intros. cbn. rewrite_all_binds. simpl.
  triple_reorder_exists. repeat triple_pull_exists.
  triple_reorder_pure. repeat triple_pull_pure. omit_subst Hn.
  instantiate (c0 := S ?[cc0]). instantiate (cc0 := ?[c0]).
  triple_pull_1_credit. app_lambda.
  2:{
    instantiate (c0 := S ?[cc0]). instantiate (cc0 := ?[c0]).
    triple_pull_1_credit.
    apply triple_new_array_content. solve_simple_value.
    { lia. }
    { match goal with
      | [H : ?Q ?c ?m |- ?F ?v ?c ?m] =>
        unify F (fun t => <[t = v]> <*> Q)
      end.
      simpl. solve_star. }
  }
  solve_simple_value. split_all; auto. intros. cbn. rewrite_all_binds. simpl.
  triple_reorder_exists. repeat triple_pull_exists.
  triple_reorder_pure. repeat triple_pull_pure. omit_subst Hn.
  (*instantiate (c0 := S ?[cc0]). instantiate (cc0 := ?[c0]).
  triple_pull_1_credit.*) rewrite Nat2Z.id.
  triple_reorder (@sa_credits string 1).
  eapply triple_seq.
  - pose proof triple_fun_n_ary_app as Hn_ary.
    pose proof triple_fun_n_ary_weaken as Hweaken.
    pose proof triple_fun_n_ary_init_array as Hinit_array.
    instantiate (c0 := 11 + ?[cc0]). instantiate (cc0 := ?[c0]).
    instantiate (cn := 16 + ?[ccn]). instantiate (ccn := ?[cn]).
    erewrite (Nat.mul_add_distr_r 16 _ n), (Nat.mul_add_distr_r (16 * n)),
      (Nat.mul_comm 16 n), Nat.mul_succ_r, (Nat.add_comm _ (n*16)).
    simpl.
    erewrite <- (Nat.add_assoc (n*16)), (Nat.add_assoc _ (n*16)),
      (Nat.add_comm _ (n*16)), <- (Nat.add_assoc (n*16)),
      (Nat.add_assoc _ (n*16)), (Nat.add_comm _ (n*16)),
      <- (Nat.add_assoc (n*16)).
    triple_reorder_credits.
    triple_pull_credits (11 + n*16). triple_reorder_credits.
    eapply triple_weaken with
      (P := ($_ <*> array_content _ _) <*>
        ($ (_ + _) <*> is_weighted_graph _ _<*>
          is_heap _ _ _ _ _ _ <*> array_content _ _)), triple_frame.
    { prove_implies_rev. }
    { intros. apply star_assoc_r. }
    triple_reorder_credits. triple_pull_credits 3. triple_reorder_credits.
    triple_pull_credits 2. triple_reorder_credits.
    clear v1.
    lazymatch goal with
    | [|- triple (Val init_array <* ?e1' <* ?e2' <* ?e3') _ _] =>
      remember e1' as e1 eqn:He1; remember e2' as e2 eqn:He2;
      remember e3' as e3 eqn:He3;
      destruct e1 as [v1| | | | | | | | | | | | | |]; try discriminate;
      destruct e2 as [v2| | | | | | | | | | | | | |]; try discriminate;
      destruct e3 as [v3| | | | | | | | | | | | | |]; try discriminate;
      injection He1 as Hv1; injection He2 as Hv2; injection He3 as Hv3;
      revert v1 v2 v3 Hv1 Hv2 Hv3
    end.
    lazymatch goal with
    | [|- forall v1 v2 v3, _ -> _ -> _ ->
        triple (Val init_array <* Val v1 <* Val v2 <* Val v3)
          ($2 <*> @?P0 v1 v2 v3) (@?Q0 v1 v2 v3)
      ] =>
      intros v1 v2 v3; intros;
      specialize Hn_ary with
        (v := init_array) (e := Val v1) (es := [Val v2;Val v3]%list)
        (P := P0 v1 v2 v3)
    end.
    lazymatch goal with
    | [H : forall A s, _ -> triple_fun_n_ary ?n' init_array (@?P A s) (@?Q A s)
      |- triple _
        (_ <*> (_ <*> (_ <*> array_content (List.repeat ?x ?s) _))) _
      ] =>
      let A := constr:(List.repeat x s) in
      specialize Hn_ary with (Q1 := P A s) (Q2 := Q A s);
      specialize Hweaken with (n := n')
    end.
    simpl in Hn_ary, Hweaken, Hinit_array.
    eapply Hn_ary.
    { apply Hinit_array. symmetry. apply List.repeat_length. }
    { solve_simple_value. revert_implies. prove_implies_refl. }
    { solve_simple_value. revert_implies. prove_implies_refl. }
    { solve_simple_value. revert_implies. rewrite <- Hv3. prove_implies_refl. }
    { simpl. prove_implies. apply implies_spec. intros. solve_star. }
  - instantiate (c0 := S ?[cc0]). instantiate (cc0 := ?[c0]).
    triple_reorder_credits. triple_pull_1_credit.
    eapply triple_seq.
    + pose proof triple_fun_n_ary_app as Hn_ary.
      pose proof triple_fun_n_ary_weaken as Hweaken.
      pose proof triple_fun_n_ary_init_array as Hinit_array.
      instantiate (c0 := 11 + ?[cc0]). instantiate (cc0 := ?[c0]).
      instantiate (cn := 16 + ?[ccn]). instantiate (ccn := ?[cn]).
      erewrite (Nat.mul_add_distr_r 16 _ n), (Nat.mul_add_distr_r (16 * n)),
        (Nat.mul_comm 16 n), (Nat.mul_succ_r (n*16)), (Nat.add_comm _ (n*16)).
      simpl.
      erewrite <- (Nat.add_assoc (n*16)), (Nat.add_assoc _ (n*16)),
        (Nat.add_comm _ (n*16)), <- (Nat.add_assoc (n*16)),
        (Nat.add_assoc _ (n*16)), (Nat.add_comm _ (n*16)),
        <- (Nat.add_assoc (n*16)), (Nat.add_assoc _ (n*16)),
        (Nat.add_comm _ (n*16)), <- (Nat.add_assoc (n*16)).
      triple_pull_credits (11 + n*16). triple_reorder_credits.
      eapply triple_weaken with
        (P := ($_ <*> array_content _ _) <*>
          ($ (_ + _) <*> is_weighted_graph _ _<*>
            is_heap _ _ _ _ _ _ <*> array_content _ _)), triple_frame.
      { prove_implies_rev. }
      { intros. apply star_assoc_r. }
      triple_reorder_credits. triple_pull_credits 3. triple_reorder_credits.
      triple_pull_credits 2. triple_reorder_credits.
      lazymatch goal with
      | [|- triple (Val init_array <* ?e1' <* ?e2' <* ?e3') _ _] =>
        remember e1' as e1 eqn:He1; remember e2' as e2 eqn:He2;
        remember e3' as e3 eqn:He3;
        destruct e1 as [v1'| | | | | | | | | | | | | |]; try discriminate;
        destruct e2 as [v2| | | | | | | | | | | | | |]; try discriminate;
        destruct e3 as [v3| | | | | | | | | | | | | |]; try discriminate;
        injection He1 as Hv1; injection He2 as Hv2; injection He3 as Hv3;
        revert v1' v2 v3 Hv1 Hv2 Hv3
      end.
      lazymatch goal with
      | [|- forall v1' v2 v3, _ -> _ -> _ ->
          triple (Val init_array <* Val v1' <* Val v2 <* Val v3)
            ($2 <*> @?P0 v1' v2 v3) (@?Q0 v1' v2 v3)
        ] =>
        intros v1' v2 v3; intros;
        specialize Hn_ary with
          (v := init_array) (e := Val v1') (es := [Val v2;Val v3]%list)
          (P := P0 v1' v2 v3)
      end.
      lazymatch goal with
      | [H : forall A s, _ -> triple_fun_n_ary ?n' init_array (@?P A s) (@?Q A s)
        |- triple _
          (_ <*> (_ <*> (_ <*> array_content (List.repeat ?x ?s) _))) _
        ] =>
        let A := constr:(List.repeat x s) in
        specialize Hn_ary with (Q1 := P A s) (Q2 := Q A s);
        specialize Hweaken with (n := n')
      end.
      simpl in Hn_ary, Hweaken, Hinit_array.
      eapply Hn_ary.
      { apply Hinit_array. symmetry. apply List.repeat_length. }
      { solve_simple_value. revert_implies. prove_implies_refl. }
      { solve_simple_value. revert_implies. prove_implies_refl. }
      { solve_simple_value. revert_implies. rewrite <- Hv3. prove_implies_refl. }
      { simpl. prove_implies. apply implies_spec. intros. solve_star. }
    + instantiate (c0 := S ?[cc0]). instantiate (cc0 := ?[c0]).
      triple_reorder_credits. triple_pull_1_credit.
      eapply triple_seq.
      * pose proof triple_fun_n_ary_app as Hn_ary.
        pose proof triple_fun_n_ary_weaken as Hweaken.
        pose proof triple_fun_n_ary_assign_array_at as Hassign_array_at.
        instantiate (c0 := 5+ ?[cc0]). instantiate (cc0 := ?[c0]). simpl.
        triple_pull_credits 5. triple_reorder_credits.
        triple_pull_credits 4. triple_reorder_credits.
        triple_pull_credits 2. triple_reorder_credits.
        clear_state_assertions.
        lazymatch goal with
        | [|- triple (Val assign_array_at <* Val ?v <* _ <* _) _ _] =>
          eapply triple_weaken with
            (P := ($_ <*> ($_ <*> ($_ <*> (array_content _ v)))) <*> ($ _ <*> _)),
            triple_frame;
            [| |revert v]
        end.
        { prove_implies_rev. }
        { intros. apply star_assoc. }
        lazymatch goal with
        | [|-
          forall a,
            triple (Val (@?f a) <* (@?e1 a) <* (@?e2 a) <* (@?e3 a))
              ($2 <*> (@?P0 a))
              (@?Q1 a)
          ] =>
          intros a;
          specialize Hn_ary with
            (v := f a) (e := e1 a) (es := [e2 a;e3 a]%list)
            (P := P0 a)
        end.
        lazymatch goal with
        | [H : forall A A' A1 ov A2 i x, _ -> _ -> _ ->
            triple_fun_n_ary ?n' assign_array_at (@?P A i x) (@?Q A')
          |- triple (Val assign_array_at <* Val ?a <* Val (Int (Z.of_nat ?i)) <* Val ?y)
            ($_ <*> ($_ <*> ($_ <*> array_content (List.repeat ?x ?s) ?v))) _
          ] =>
          let A := constr:(List.repeat x s) in
          let A' := constr:((List.repeat x i ++ Some y::List.repeat x (s-S i))%list) in
          specialize Hn_ary with
            (Q1 := P A i y) (Q2 := Q A')
        end.
        specialize (Hweaken _ assign_array_at 2).
        simpl in Hn_ary, Hassign_array_at, Hweaken. eapply Hn_ary.
        { rewrite <- Hn in *.
          assert (src < n) by eauto using init_range_lt_size.
          assert (n = src + (1 + (n-(S src)))) as -> by lia.
          eapply Hassign_array_at; eauto using List.repeat_length.
          rewrite List.repeat_app. simpl. repeat f_equal. lia. }
        { solve_simple_value. revert_implies. prove_implies_refl. }
        { solve_simple_value. revert_implies. remember (Int (Z.of_nat src)).
          prove_implies_refl. }
        { solve_simple_value. revert_implies. remember (Int 0).
          prove_implies_refl. }
        { simpl. apply implies_spec. intros. swap_star. solve_star. swap_star.
          solve_star. revert_implies. prove_implies. }
      * clear_state_assertions. triple_reorder_credits.
        (*destruct n as [|n'] eqn:Hn; [lia|]. rewrite <- Hn.*)
        instantiate (c0 := 4+?[cc0]). instantiate (cc0 := ?[c0]). simpl.
        triple_pull_1_credit. eapply triple_seq.
        -- pose proof triple_fun_n_ary_app as Hn_ary.
          pose proof triple_fun_n_ary_weaken as Hweaken.
          unfold h_insert_spec in Hspec_h_insert.
          instantiate (cn := S ?[ccn]). instantiate (ccn := ?[cn]).
          simpl.
          erewrite (Nat.mul_add_distr_r n).
          do 4 erewrite (Nat.add_assoc _ (n*S _)), (Nat.add_comm _ (n*S _)),
            <- (Nat.add_assoc (n*S _)).
          lazymatch goal with
          | [|- triple _ ($ S (S (S (n*S ?k + _))) <*> _) _] =>
            rename k into t_credits
          end.
          triple_pull_credits (3+n*S t_credits). triple_reorder_credits.
          rewrite Hn. simpl (S _). rewrite <- Hn.
          triple_pull_credits (3+S t_credits). triple_reorder_credits.
          triple_pull_credits 3. triple_reorder_credits.
          triple_pull_credits 2. triple_reorder_credits.
          lazymatch goal with
          | [|- triple (Val h_insert <* Val ?v <* _ <* _) _ _] =>
            eapply triple_weaken with
              (P := ($2 <*> ($1 <*> ($ (S t_credits) <*>
                (is_heap n _ _ _ _ v)))) <*> ($ _ <*> $ _ <*> _)),
              triple_frame;
              [| |revert v]
          end.
          { prove_implies_rev. }
          { intros. apply star_assoc. }
          lazymatch goal with
          | [|-
            forall a,
              triple (Val (@?f a) <* (@?e1 a) <* (@?e2 a) <* (@?e3 a))
                ($2 <*> (@?P0 a))
                (@?Q1 a)
            ] =>
            intros a;
            specialize Hn_ary with
              (v := f a) (e := e1 a) (es := [e2 a;e3 a]%list)
              (P := P0 a)
          end.
          lazymatch goal with
          | [H : forall n C P W p s k d c t, _ -> _ -> _ -> _ -> _ ->
              triple_fun_n_ary _ h_insert
                (@?Pre n C P W p k d c) (@?Post n C P W p k d t)
            |- triple
              (Val h_insert <* Val ?h <* Val (Int (Z.of_nat ?s')) <* Val (Int ?x))
              ($_ <*> ($_ <*> ($ ?t' <*> is_heap ?n' ?C' ?P' ?W' ?p' ?h))) _
            ] =>
            let d' := constr:(Z.to_nat x) in
            let c' := constr:(t') in
            specialize Hn_ary with
              (Q1 := Pre n' C' P' W' p' s' d' c')
              (Q2 := Post n' C' P' W' p' s' d' t');
            specialize Hspec_h_insert with
              (n := n') (C := C') (P := P') (W := W') (p := p') (k := s')
              (d := d') (c := t') (t := t')
          end.
          specialize (Hweaken _ assign_array_at 2).
          simpl in Hn_ary, Hspec_h_insert, Hweaken. eapply triple_weaken, Hn_ary.
          { prove_implies_refl. }
          { apply implies_post_spec. intros ? ? ? HQ.
            apply star_assoc, star_comm, star_assoc, star_pure_l in HQ as (->&?).
            solve_star. eassumption. }
          { eapply Hspec_h_insert; unfold empty, not; auto.
            { rewrite Hn. assumption. }
            { apply empty_set_size. }
            { lia. } }
          { solve_simple_value. revert_implies. prove_implies_refl. }
          { solve_simple_value. revert_implies. remember (Int (Z.of_nat src)).
            prove_implies_refl. }
          { solve_simple_value. revert_implies. remember (Int 0).
            prove_implies_refl. }
          { simpl. apply implies_spec. intros. swap_star. solve_star. swap_star.
            solve_star. revert_implies. prove_implies. }
        -- triple_reorder_exists. repeat triple_pull_exists.
          triple_reorder_pure. triple_pull_pure.
          instantiate (c0 := 4 + (c_h_empty + ?[cc0])). instantiate (cc0 := ?[c0]).
          triple_reorder_credits.
          lazymatch goal with
          | [|- triple _ ($ _ <*> ($ _ <*> ($ ?c <*> _))) _] =>
            triple_reorder (@sa_credits string c)
          end.
          triple_pull_1_credit.
          eapply triple_seq.
          ++ instantiate (cn := ?[ccn] + ?[cn0]). instantiate (ccn := ?[cn]).
            erewrite (Nat.mul_add_distr_r _ _ n), (Nat.mul_add_distr_r (_*n) (_*n) _).
            do 4 erewrite (Nat.add_assoc _ _ (_*n*_)).
            do 3 rewrite <- Nat.add_succ_l.
            erewrite (Nat.add_comm _ (_*n*_)).
            lazymatch goal with
            | [|- triple _
                ($ (?c + _) <*> (_ <*> (_ <*> (_ <*>
                  array_content ?pred _ <*> array_content ?D _ <*> _))))
                _
              ] =>
              triple_pull_credits c; triple_reorder_credits;
              remember pred as pred_list eqn:Hpred_list;
              remember D as D_list eqn:HD_list
            end.
            eapply triple_weaken, triple_frame.
            { apply star_comm. }
            { intros. simpl. apply star_assoc_r. }
            assert (is_nat_fun_of_val_list D_list
              (fun i => if i =? src then Some 0 else None)).
            { subst.
              unfold is_nat_fun_of_val_list, fun_of_list, list_of_f, nat2value.
              split.
              { eexists. rewrite List.map_app. f_equal.
                { rewrite List.map_repeat. reflexivity. }
                { rewrite List.map_cons. f_equal. rewrite List.map_repeat.
                  reflexivity. } }
              { intros. destruct Nat.eqb_spec with i src.
                { subst.
                  rewrite List.app_nth2; rewrite List.repeat_length; [|lia].
                  rewrite Nat.sub_diag. simpl.
                  split; intros [= ?]; repeat f_equal; lia. }
                { assert (i < src \/ i > src) as [] by lia.
                  { rewrite List.app_nth1; [|rewrite List.repeat_length; lia].
                    erewrite List.nth_error_nth;
                      [|apply List.nth_error_repeat; lia].
                    split; [|discriminate]. intros [= ?]. lia. }
                  { rewrite List.app_nth2; rewrite List.repeat_length; [|lia].
                    destruct i as [|i]; [lia|]. rewrite Nat.sub_succ_l; [|lia].
                    simpl.
                    assert (i < n' \/ i >= n') as [] by lia.
                    { erewrite List.nth_error_nth;
                        [|apply List.nth_error_repeat; lia].
                      split; [|discriminate]. intros [= ?]. lia. }
                    { rewrite List.nth_overflow; [|rewrite List.repeat_length; lia].
                      split; discriminate. } } } } }
            assert (is_nat_fun_of_val_list pred_list (fun i => None)).
            { subst. unfold is_nat_fun_of_val_list, fun_of_list, list_of_f.
              split.
              { eexists. rewrite List.map_repeat. reflexivity. }
              { intros.
                assert (i < S n' \/ i >= S n') as [] by lia.
                { erewrite List.nth_error_nth;
                    [|apply List.nth_error_repeat; lia].
                  split; [|discriminate]. intros [= ?]. lia. }
                { rewrite List.nth_overflow; [|rewrite List.repeat_length; lia].
                  split; discriminate. } } }
            unfold set_value_at.
            remember (fun i => if i =? src then Some 0 else None) as D eqn:HD.
            remember (fun i => None) as pred eqn:Hpred.
            assert (Dijkstra_initial D pred src) as Hinitial.
            { subst. unfold Dijkstra_initial. rewrite Nat.eqb_refl.
              split_all; auto. intros ? ->%Nat.eqb_neq. reflexivity. }
            apply valid_initial with (g := g) in Hinitial; auto.
            triple_reorder_credits.
            lazymatch goal with
            | [|- triple _ ($ S (S ?cr) <*> ($ ?n1 <*> ($ ?n2 <*> _))) _] =>
              eapply triple_weaken with
                (P := ($ S (S cr) <*> _) <*> ($ n1 <*> $ n2))
                (Q := (fun res => <[res = U_val]> <*> ((<exists> c, $c) <*> _)) <*>+
                  ($ n1 <*> $ n2)),
                triple_frame
            end.
            { prove_implies. }
            { apply implies_post_spec. intros. apply star_assoc_r. eassumption. }
            remember (fun (D : nat -> option nat) v => D v <> None)
              as nonzeroD eqn:HnonzeroD.
            assert (src < n).
            { subst. eapply init_range_lt_size; eassumption. }
            triple_pull_credits 2. triple_reorder_credits.
            lazymatch goal with
            | [|- triple _
                ($2 <*> ($ (S (c_h_empty + ?c0 + (?cm * m + (_ + (_ + ?cn * n * ?t))))) <*>
                  (is_weighted_graph ?g ?vg <*>
                    array_content _ ?a_pred <*> array_content _ ?a_D <*>
                    is_heap ?n' ?C ?P0 _ ?pot ?h)))
                (fun res => <[@?Q' res]> <*> _)
              ] =>
              let pre :=
                constr:($2 <*> ((<exists> D_list pred_list P P' D pred sv sv' se,
                <[(P = empty /\ P' = P0) \/ (P src /\ P' = neighbourhood g P)]> <*>
                <[is_set_size P sv]> <*>
                <[is_set_size P' sv']> <*>
                <[is_set_size (uncurry (E (induced_subgraph P g))) se]> <*>
                <[sv + sv' <= n]> <*>
                <[List.length D_list = n]> <*>
                <[List.length pred_list = n]> <*>
                <[is_nat_fun_of_val_list D_list D]> <*>
                <[is_nat_fun_of_val_list pred_list pred]> <*>
                <[Dijkstra_invariant D pred P src g]> <*>
                $ (S (c_h_empty + pot + c0 + (cm * (m - se) + cn * (n - sv) * t))) <*>
                is_weighted_graph g vg <*> array_content pred_list a_pred <*>
                array_content D_list a_D <*> is_heap n' C P' D pot h) <*>
                (<exists> c, $c)))
              in
              let post :=
                constr:(fun b => (<exists> D_list pred_list P P' D pred sv sv' se,
                <[negb (sv' =? 0) = b]> <*>
                <[(P = empty /\ P' = P0) \/ (P src /\ P' = neighbourhood g P)]> <*>
                <[is_set_size P sv]> <*>
                <[is_set_size P' sv']> <*>
                <[is_set_size (uncurry (E (induced_subgraph P g))) se]> <*>
                <[sv + sv' <= n]> <*>
                <[List.length D_list = n]> <*>
                <[List.length pred_list = n]> <*>
                <[is_nat_fun_of_val_list D_list D]> <*>
                <[is_nat_fun_of_val_list pred_list pred]> <*>
                <[Dijkstra_invariant D pred P src g]> <*>
                $ (pot + c0 + (cm * (m - se) + cn * (n - sv) * t)) <*>
                is_weighted_graph g vg <*> array_content pred_list a_pred <*>
                array_content D_list a_D <*> is_heap n' C P' D pot h) <*>
                (<exists> c, $c))
              in
              remember pot as potential eqn:Hpot;
              eapply triple_weaken with
                (P := pre) (Q := fun res => <[Q' res]> <*> post false),
                triple_while with (Q := post)
            end.
            { prove_implies. apply implies_spec. intros ? ? Hpre.
              eapply star_implies_mono in Hpre; [|
                lazymatch goal with
                | [|- $ (S (?c0 + (?n1 + (?k1 + (?k2 + ?n2))))) ->> _] =>
                  apply credits_star_r with
                    (c1 := k1 + k2 - potential)
                    (c2 := (S (potential + c0 + (n1 + n2))));
                    lia
                end|prove_implies_refl].
              normalize_star. swap_star_ctx. eapply star_implies_mono; eauto.
              { clear_state_assertions. apply implies_spec. intros.
                eexists D_list, pred_list, empty, (set_sum _ _), D, pred, 0, 1, 0.
                solve_star.
                { apply empty_set_size. }
                { apply equiv_set_size with (single src), single_set_size.
                  unfold set_equiv, empty, set_sum. tauto. }
                { apply equiv_set_size with empty.
                  { unfold set_equiv. intros []. simpl. unfold empty. tauto. }
                  { apply empty_set_size. } }
                { lia. }
                { subst D_list. rewrite List.app_length. simpl.
                  repeat rewrite List.repeat_length. lia. }
                { subst pred_list. rewrite List.repeat_length. reflexivity. }
                { do 2 rewrite Nat.sub_0_r. revert_implies.
                  rewrite (Nat.add_assoc potential), (Nat.add_comm potential).
                  subst potential. prove_implies. } }
              { apply implies_spec. intros. solve_star. eassumption. } }
            { intros. rewrite <- Hpot. prove_implies. apply star_comm. }
            ** unfold h_empty_spec in Hspec_h_empty.
              triple_reorder_exists. repeat triple_pull_exists.
              triple_reorder_pure. repeat triple_pull_pure.
              triple_pull_1_credit.
              eapply triple_weaken, triple_bneg.
              { prove_implies_refl. }
              { apply implies_post_spec. intros. normalize_star.
                eexists. apply star_pure_l. split; eauto. revert_implies.
                prove_implies_refl. }
              unfold triple_fun in Hspec_h_empty.
              do 2 rewrite <- (Nat.add_assoc c_h_empty).
              triple_pull_credits c_h_empty. triple_reorder_credits.
              lazymatch goal with
              | [Hsize : is_set_size (V (G g)) _,
                  H : (_ = empty /\ ?X = set_sum empty _) \/
                    (_ src /\ ?X = ?P) |- _] =>
                apply subset_size with (P' := P) in Hsize as (?&?&?)
              end.
              { lazymatch goal with
                | [H : (_ = empty /\ ?P' = set_sum empty _) \/
                        (_ src /\ ?P' = neighbourhood _ _) |- _] =>
                  assert (exists s, is_set_size P' s) as (?&?);
                    [destruct H as [(?&->)| (?&->)]; eexists|]
                end.
                { apply equiv_set_size with (single src).
                  { subst. unfold set_equiv. intros. symmetry.
                    apply set_sum_empty_l. }
                  { apply single_set_size. } }
                { eassumption. }
                eapply triple_weaken, triple_frame, Hspec_h_empty.
                { apply implies_spec. intros. solve_star. swap_star. solve_star.
                  revert_implies. prove_implies_rev. apply star_comm. }
                { apply implies_post_spec. intros. normalize_star.
                  lazymatch goal with
                  | [
                    H0 : is_set_size ?P' ?s1,
                    H1 : is_set_size ?P' ?s2,
                    H2 : (is_heap _ _ ?P' _ _ _ <*> _) _ _ |- _
                  ] =>
                    specialize (is_set_size_unique _ _ _ _ H0 H1) as ->
                  end.
                  lazymatch goal with
                  | [H : (_ = empty /\ _ = set_sum empty _) \/
                          (_ src /\ _ = neighbourhood _ _) |- _] =>
                    destruct H as [(?&?) | (?&?)]
                  end.
                  { eexists. apply star_pure_l. split; eauto.
                    do 9 (apply star_exists_l; eexists).
                    repeat apply star_assoc_l. apply star_pure_l. split; eauto.
                    apply star_pure_l. split.
                    { left. eauto. }
                    solve_star;
                      try lazymatch goal with
                      [|- Dijkstra_invariant _ _ _ _ _] => eassumption
                      end;
                      try lazymatch goal with
                      [|- is_nat_fun_of_val_list _ _] => eassumption
                      end;
                      eauto.
                    revert_implies. prove_implies_rev. apply implies_spec.
                    intros. solve_star. eassumption. }
                  { eexists. apply star_pure_l. split; eauto.
                    do 9 (apply star_exists_l; eexists).
                    repeat apply star_assoc_l. apply star_pure_l. split; eauto.
                    apply star_pure_l. split.
                    { right. eauto. }
                    solve_star;
                      try lazymatch goal with
                      [|- Dijkstra_invariant _ _ _ _ _] => eassumption
                      end;
                      try lazymatch goal with
                      [|- is_nat_fun_of_val_list _ _] => eassumption
                      end;
                      subst; eauto.
                    revert_implies. prove_implies_rev. apply implies_spec.
                    intros. solve_star. eassumption. } }
                { eassumption. }
                { eassumption. }
              }
              { intros.
                lazymatch goal with
                | [H : is_set_size ?P _
                  |- Decidable.decidable (neighbourhood _ ?P _)] =>
                  unfold is_set_size, is_elem_unique_list in H;
                  destruct H as (?&(?&?)&?)
                end.
                eapply decidable_neighbourhood; eauto.
                { unfold Decidable.decidable. lia. }
                { intros.
                  lazymatch goal with
                  | [H : is_set_size ?P _
                    |- Decidable.decidable (?P _)] =>
                    unfold is_set_size, is_elem_unique_list in H;
                    destruct H as (?&(?&?)&?)
                  end.
                  eapply decidable_if_elem_list; eauto.
                  unfold Decidable.decidable. lia. }
                { intros.
                  lazymatch goal with
                  | [H : is_set_size (uncurry ?P) _
                    |- Decidable.decidable (?P _ _)] =>
                    unfold is_set_size, is_elem_unique_list in H;
                    destruct H as (?&(?&?)&?)
                  end.
                  change (?f ?x ?y) with (uncurry f (x,y)).
                  eapply decidable_if_elem_list; eauto. intros.
                  eapply decidable_uncurry; unfold Decidable.decidable; lia. } }
              { unfold is_subset. unfold neighbourhood.
                intros ? (?&?&?&?%E_closed2). assumption. }
            ** generalize dependent h_empty.
              generalize dependent pred.
              generalize dependent D.
              generalize dependent pred_list.
              generalize dependent D_list.
              generalize dependent nonzeroD.
              (* clear all initial state hypotheses *)
              intros _ _ _ _ _ _ _ _ _ _ _ _ _ _ _.
              triple_reorder_exists. repeat triple_pull_exists.
              triple_reorder_pure. repeat triple_pull_pure.
              triple_reorder_credits. instantiate (cn := ?[cn_0] + ?[cn_t]).
              rewrite Bool.negb_true_iff, Nat.eqb_neq in *.
              erewrite (Nat.mul_comm _ (n - _)). rewrite Hn.
              rewrite Nat.sub_succ_l; [|lia]. rewrite <- Hn. simpl "*".
              erewrite (Nat.mul_add_distr_r _ ((n' - _) * _)).
              erewrite (Nat.add_assoc (_ * (m - _))).
              erewrite (Nat.add_comm (_ * (m-_)) _).
              erewrite <- (Nat.add_assoc _ (_ * (m - _))).
              lazymatch goal with
              | [|- triple _ ($ (?c0 + (?c1 + _)) <*> _) _] =>
                rewrite (Nat.add_assoc c0 c1), (Nat.add_comm c0 c1),
                  <- (Nat.add_assoc c1 c0)
              end.
              lazymatch goal with
              | [|- triple _ ($ ((?c1 + ?c2)*?t + _) <*> _) _] =>
                erewrite (Nat.mul_add_distr_r c1 c2 t),
                  <- (Nat.add_assoc (c1*t))
              end.
              erewrite (Nat.mul_comm _ (S _)). simpl "*".
              erewrite <- Nat.add_assoc.
              lazymatch goal with
              | [Hneq : ?s <> 0,
                 Hsize : is_set_size _ ?s,
                 Hinvariant : Dijkstra_invariant ?D ?pred _ _ _ |- _] =>
                eapply nonempty_has_min_cost_elem_option_nat
                  with (W := D) in Hsize as Hmincost';
                try destruct Hmincost' as (x_min&Hmincost);
                unfold Decidable.decidable; try lia;
                assert (exists y, D x_min = Some y) as Hissome
              end.
              { lazymatch goal with
                | [H : (_ = empty /\ _ = set_sum empty _) \/
                        (_ src /\ _ = neighbourhood _ _) |- _] =>
                  destruct H as [(?&?) | (?&?)]
                end.
                { lazymatch goal with
                  | [H : Dijkstra_invariant _ _ _ _ _ |- _] =>
                    unfold Dijkstra_invariant,
                      Dijkstra_distance_invariant,
                      Dijkstra_predecessors_invariant,
                      are_valid_distances in H;
                    destruct H as (?&(Hdist_inv&?)&Hpred_inv)
                  end.
                  specialize Hdist_inv with src [src]%list.
                  subst. unfold empty, set_sum in *.
                  eapply Some_min_cost_elem with (x := src) (P := single src);
                    unfold single in *; auto.
                  { apply Hdist_inv.
                    unfold is_shortest_path, min_cost_elem, is_path. simpl.
                    split; [|lia]. split; auto using List.NoDup.
                    constructor. simpl. unfold set_sum, intersect, single. auto. }
                  { unfold min_cost_elem in *. intuition. } }
                { lazymatch goal with
                  | [H : is_set_size (V (G g)) _ |- _] =>
                    unfold is_set_size, is_elem_unique_list in H;
                    destruct H as (?&(?&?)&?)
                  end.
                  lazymatch goal with
                  | [H : is_set_size (uncurry (E (G g))) _ |- _] =>
                    unfold is_set_size, is_elem_unique_list in H;
                    destruct H as (?&(?&?)&?)
                  end.
                  lazymatch goal with
                  | [H : Dijkstra_invariant _ _ _ _ _ |- _] =>
                    eapply invariant_D_is_some_for_neighbours
                  end;
                  eauto.
                  { subst. unfold min_cost_elem, neighbourhood in Hmincost.
                    destruct Hmincost as ((?&?&?&?%E_closed2)&?). assumption. }
                  { subst. unfold min_cost_elem in Hmincost.
                    destruct Hmincost as (?&?). assumption. } } }
              destruct Hissome.
              instantiate (cn_0 := S ?[ccn_0]). instantiate (ccn_0 := ?[cn_0]).
              triple_pull_1_credit.
              app_lambda.
              2:{
                unfold h_extract_min_spec in Hspec_h_extract_min.
                erewrite <- Hpot, <- (Nat.add_assoc potential),
                  (Nat.add_assoc _ potential), (Nat.add_comm _ potential),
                  <- (Nat.add_assoc potential), (Nat.add_assoc _ potential),
                  (Nat.add_comm _ potential), <- (Nat.add_assoc potential),
                  (Nat.add_assoc _ potential), (Nat.add_comm _ potential),
                  <- (Nat.add_assoc potential).
                triple_reorder_credits. triple_pull_credits potential.
                triple_reorder_credits.
                lazymatch goal with
                | [|- triple _
                    (_ <*> (_ <*> (_ <*> (_ <*>
                      is_heap n C ?P' ?W' ?p' ?h')))) _] =>
                  specialize Hspec_h_extract_min with
                    (n := n) (C := C) (P := P') (W := W') (p := p') (h := h')
                end.
                eapply triple_weaken, triple_frame, triple_fun_app.
                4:solve_simple_value.
                3:{ apply Hspec_h_extract_min; eauto. }
                { rewrite <- Hpot. apply implies_spec. intros. solve_star.
                  swap_star. solve_star. conormalize_star. swap_star_ctx.
                  revert_implies. prove_implies. }
                { prove_implies_refl. }
              }
              clear h_extract_min Hspec_h_extract_min.
              lazymatch goal with
              | [Hfun : is_nat_fun_of_val_list ?L ?f,
                 Heq : ?f x_min = Some ?n
                 |- _] =>
                remember Hfun eqn:HHfun; clear HHfun;
                unfold is_nat_fun_of_val_list, list_of_f, fun_of_list in Hfun;
                destruct Hfun as ((_&_)&Hfun);
                apply Hfun in Heq; clear Hfun
              end.
              solve_simple_value. split; auto. intros. cbn. rewrite_all_binds.
              triple_reorder_exists. repeat triple_pull_exists.
              triple_reorder_pure. repeat triple_pull_pure.
              lazymatch goal with
              | [H1 : List.length _ = n, H2 : List.length _ = n |- _] =>
                rename H1 into Hlen1; rename H2 into Hlen2
              end.
              revert Hn Hpot Hlen1 Hlen2. subst. intros. triple_reorder_credits.
              instantiate (cn_0 := S (S ?[ccn_0])). instantiate (ccn_0 := ?[cn_0]).
              eapply triple_weaken.
              { apply implies_spec. intros. swap_star_ctx. eassumption. }
              { prove_implies_refl. }
              triple_pull_1_credit. app_lambda.
              2:{
                triple_pull_1_credit.
                eapply triple_get with
                  (Q := fun v => <[v = nat2value x_min]> <*> _).
                remember (nat2value x_min). solve_simple_value. constructor.
              }
              solve_simple_value. split; auto. intros. cbn. rewrite_all_binds.
              triple_pull_pure. revert Hn Hpot Hlen1 Hlen2. subst. intros.
              instantiate (cn_0 := S (S ?[ccn_0])). instantiate (ccn_0 := ?[cn_0]).
              triple_pull_1_credit. app_lambda.
              2:{
                triple_pull_1_credit.
                lazymatch goal with
                | [|- triple (Get 1 (Val (RecV [_;?v']))) _ _] =>
                  eapply triple_get with (Q := fun v => <[v = v']> <*> _);
                  remember v'
                end.
                solve_simple_value. repeat constructor.
              }
              solve_simple_value. split; auto. intros. cbn. rewrite_all_binds.
              triple_pull_pure. revert Hn Hpot Hlen1 Hlen2. subst. intros.
              clear_state_assertions.
              instantiate (cn_0 := 4 + c_neighbours + ?[ccn_0]).
              instantiate (ccn_0 := ?[cn_0]). simpl. triple_pull_1_credit.
              app_lambda.
              2:{
                pose proof triple_fun_n_ary_app as Hn_ary.
                pose proof triple_fun_n_ary_weaken as Hweaken.
                unfold get_neighbours_spec in Hspec_get_neighbours.
                triple_pull_1_credit. apply triple_ref.
                rewrite <- (Nat.add_assoc c_neighbours).
                triple_pull_credits (1+S c_neighbours). triple_reorder_credits.
                triple_pull_credits 2. triple_pull_1_credit.
                lazymatch goal with
                | [|- triple (Val get_neighbours <* Val ?v <* _) _ _] =>
                  eapply triple_weaken with
                    (P := ($1 <*> ($1 <*> ($ c_neighbours <*>
                      is_weighted_graph g v))) <*> ($ _ <*> $ _ <*> $ _ <*> _)),
                    triple_frame;
                    [| |revert v]
                end.
                { prove_implies_rev. }
                { prove_implies_refl. }
                lazymatch goal with
                | [|-
                  forall a,
                    triple (Val (@?f a) <* (@?e1 a) <* (@?e2 a))
                      ($1 <*> (@?P0 a))
                      (@?Q1 a)
                  ] =>
                  intros vg;
                  specialize Hn_ary with
                    (v := f vg) (e := e1 vg) (es := [e2 vg]%list)
                    (P := P0 vg)
                end.
                lazymatch goal with
                | [H : forall vg n g c, _ ->
                    triple_fun_n_ary _ get_neighbours
                      (@?Pre vg n g c) (@?Post vg n g c)
                  |- triple
                    (Val get_neighbours <* Val ?vg' <* Val (Int (Z.of_nat ?n')))
                    ($_ <*> ($_ <*> ($ ?c' <*> is_weighted_graph g ?vg'))) _
                  ] =>
                  specialize Hn_ary with
                    (Q1 := Pre vg' n' g c')
                    (Q2 := Post vg' n' g c');
                  specialize Hspec_get_neighbours with
                    (vg := vg') (n := n') (g := g) (c := c')
                end.
                simpl in Hn_ary, Hspec_get_neighbours, Hweaken. eapply Hn_ary.
                { eapply Hspec_get_neighbours. assumption. }
                { solve_simple_value. revert_implies. prove_implies_refl. }
                { solve_simple_value. revert_implies. remember (Int (Z.of_nat x_min)).
                  prove_implies_refl. }
                { simpl. prove_implies. apply implies_spec. intros.
                  solve_star. unfold min_cost_elem in Hmincost.
                  destruct Hmincost as (Hx_min&?).
                  lazymatch goal with
                  | [H : (_ = empty /\ _ = set_sum empty _) \/
                          (_ src /\_ = neighbourhood _ _) |- _] =>
                    destruct H as [(?&->) | (?&->)]
                  end.
                  { unfold set_sum, empty, single in Hx_min.
                    destruct Hx_min as [[]| ->]. assumption. }
                  { unfold neighbourhood in Hx_min.
                    destruct Hx_min as (?&?&?&?%E_closed2). assumption. } }
              }
              clear get_neighbours Hspec_get_neighbours.
              solve_simple_value. split; auto. intros. cbn. rewrite_all_binds.
              triple_reorder_exists. repeat triple_pull_exists.
              triple_reorder_pure. repeat triple_pull_pure.
              revert Hn Hpot Hlen1 Hlen2. subst. intros.
              instantiate (cn_0 := S ?[ccn_0]). instantiate (ccn_0 := ?[cn_0]).
              triple_pull_1_credit. eapply triple_seq.
              --- instantiate (cn_0 := 3 + ?[ccn_0]). instantiate (ccn_0 := ?[cn_0]).
                triple_reorder_credits.
                rewrite <- (Nat.sub_succ n'). rewrite <- Hn.
                (*lazymatch goal with
                | [|- triple _ ($ S (S (S (_ + (_ + (_ + (_ + (_ + ((n-?t')*_*?t)))))))) <*> _) _] =>
                  repeat rewrite (Nat.mul_succ_r (n-t'));
                  rewrite (Nat.mul_add_distr_l (n-t'));
                  repeat erewrite (Nat.mul_add_distr_r _ (n-t') t);
                  erewrite (Nat.mul_add_distr_r _ ((n-t')*_) t);
                  erewrite (Nat.add_comm _ ((n-t')*_*t));
                  repeat erewrite <- (Nat.add_assoc ((n-t')*_*t))
                end.*)
                lazymatch goal with
                | [|- triple _
                    ($ S (S (S (?cn_0 + (?c0_n + (?c_t + (?c0 + (?cm_m + ?cr))))))) <*>
                      ($ ?n1 <*> ($ (?pot + ?n2) <*>
                      (((_ <*> is_heap _ _ _ _ ?pot _) <*> _) <*> _)))) _] =>
                  eapply triple_weaken with
                    (P := ($ S (S (S (cn_0 + (cm_m + c_t)))) <*> ($ pot <*> _)) <*>
                      ($ n1 <*> $ n2 <*> $ (c0_n + c0 + cr)))
                    (Q := (fun res => <[res = U_val]> <*>
                      ((<exists> c, $c) <*> _)) <*>+
                      ($ n1 <*> $ n2 <*> $ (c0_n + c0 + cr))),
                    triple_frame
                end.
                { eapply implies_trans.
                  { apply star_implies_mono; [|prove_implies_refl].
                    lazymatch goal with
                    | [|- $ S (S (S (?cn_0 + (?c0_n + (?c_t + (?c0 + (?cm_m + ?cr))))))) ->> _] =>
                      apply credits_star_r with
                        (c1 := S (S (S (cn_0 + (cm_m + c_t))))) (c2 := c0_n + c0 + cr)
                    end.
                    lia. }
                  { prove_implies_rev. eapply implies_trans; [|apply star_comm].
                    prove_implies. eapply implies_trans; [|apply star_assoc_r].
                    apply star_implies_mono; [|prove_implies_refl].
                    apply credits_star_r. lia. } }
                { intros. prove_implies. }
                triple_reorder_credits. triple_pull_credits 2.
                triple_reorder_credits.
                instantiate (cn_0 := S c_is_nil + ?[ccn_0]).
                instantiate (ccn_0 := ?[cn_0]).
                lazymatch goal with
                | [H : potential < _ |- _] => clear potential H Hpot
                end.
                lazymatch goal with
                | [H : Dijkstra_invariant ?D_init ?pred_init ?P_init src g
                  |- triple _
                    ($2 <*> ($ (S (S c_is_nil+?cn_0+(?cm*(m-?km)+?cn_t(*(n-?kn)*?cn'*?t*)))) <*>
                      ($ ?pot' <*>
                      ((((array_content _ ?a_pred <*> array_content _ ?a_D) <*>
                        is_heap ?n' ?C ?P0 ?D' ?pot' ?h) <*>
                        (is_list ?L ?l' <*>
                        (is_list ?L ?l' <-*> is_weighted_graph ?g ?vg))) <*>
                        <(?p_l :== ?l')>))))
                    (fun res => <[@?Q' res]> <*> _)
                  ] =>
                  let pre :=
                    constr:($2 <*>
                    ((<exists> Neigh_list_processed Neigh_list_todo P'
                      D_list pred_list D pred sp st l pot,
                    <[is_elem_weighted_unique_list
                        (neighbours g x_min)
                        (W g x_min)
                        (Neigh_list_processed ++ Neigh_list_todo)%list]> <*>
                    <[List.length Neigh_list_processed = sp]> <*>
                    <[List.length Neigh_list_todo = st]> <*>
                    <[List.length D_list = n]> <*>
                    <[List.length pred_list = n]> <*>
                    <[forall x, List.In x (List.map fst Neigh_list_todo) ->
                        D x = D_init x]> <*>
                    <[forall x, List.In x (List.map fst Neigh_list_todo) ->
                        pred x = pred_init x]> <*>
                    <[is_nat_fun_of_val_list D_list D]> <*>
                    <[is_nat_fun_of_val_list pred_list pred]> <*>
                    <[P' = set_sum P0 (fun x => List.In x (List.map fst Neigh_list_processed))]> <*>
                    <[km + sp + st <= m]> <*>
(*                    <[is_set_size P0 kn]> <*>
                    <[is_set_size (uncurry (E (induced_subgraph P0 g))) km]> <*>
                    <[sv < n]> <*>
                    <[Dijkstra_invariant D pred P src g]> <*>*)
                    $ (S (S c_is_nil + cn_0 + (cm*((m-km)-sp) + cn_t(*cn'*(n-kn)*t*)))) <*>
                    $ pot <*>
                    is_list (nat_pairs2values Neigh_list_todo) l <*>
                    (is_list (nat_pairs2values Neigh_list_todo) l <-*>
                      is_weighted_graph g vg) <*>
                    array_content pred_list a_pred <*>
                    array_content D_list a_D <*> is_heap n' C P' D pot h <*>
                    <(p_l :== l)>) <*>
                    (<exists> c, $c)))
                  in
                  let post :=
                    constr:(fun b =>
                    (<exists> l Neigh_list_processed Neigh_list_todo P'
                      D_list pred_list D pred sp st pot,
                    <[negb (st =? 0) = b]> <*>
                    <[is_elem_weighted_unique_list
                        (neighbours g x_min)
                        (W g x_min)
                        (Neigh_list_processed ++ Neigh_list_todo)%list]> <*>
                    <[List.length Neigh_list_processed = sp]> <*>
                    <[List.length Neigh_list_todo = st]> <*>
                    <[List.length D_list = n]> <*>
                    <[List.length pred_list = n]> <*>
                    <[forall x, List.In x (List.map fst Neigh_list_todo) ->
                        D x = D_init x]> <*>
                    <[forall x, List.In x (List.map fst Neigh_list_todo) ->
                        pred x = pred_init x]> <*>
                    <[is_nat_fun_of_val_list D_list D]> <*>
                    <[is_nat_fun_of_val_list pred_list pred]> <*>
                    <[P' = set_sum P0 (fun x => List.In x (List.map fst Neigh_list_processed))]> <*>
                    <[km + sp + st <= m]> <*>
(*                    <[is_set_size P0 kn]> <*>
                    <[is_set_size (uncurry (E (induced_subgraph P0 g))) km]> <*>
                    <[sv < n]> <*>
                    <[Dijkstra_invariant D pred P src g]> <*>*)
                    $ (cn_0 + (cm*((m-km)-sp) + cn_t(*cn'*(n-kn)*t*))) <*>
                    $ pot <*>
                    is_list (nat_pairs2values Neigh_list_todo) l <*>
                    (is_list (nat_pairs2values Neigh_list_todo) l <-*>
                      is_weighted_graph g vg) <*>
                    array_content pred_list a_pred <*>
                    array_content D_list a_D <*> is_heap n' C P' D pot h <*>
                    <(p_l :== l)>) <*>
                    (<exists> c, $c))
                  in
                  remember pot' as potential eqn:Hpot;
                  eapply triple_weaken with
                    (P := pre) (Q := fun res => <[Q' res]> <*> post false),
                    triple_while with (Q := post)
                end.
                { (*rewrite <- Hpot.*) prove_implies. apply implies_spec.
                  intros ? ? Hpre.
                  eapply star_implies_mono in Hpre; [|
                    lazymatch goal with
                    | [|- $ ?c ->> _] =>
                      apply credits_star_r with (c1 := 0) (c2 := c);
                      lia
                    end|prove_implies_refl].
                  normalize_star. swap_star_ctx. eapply star_implies_mono; eauto.
                  { clear_state_assertions.
                    apply implies_spec. intros.
                    lazymatch goal with
                    | [H : is_elem_weighted_unique_list _ _ ?L,
                      Hpre : (_ <*> (_ <*> (array_content ?pred_list _ <*>
                        array_content ?D_list _ <*> _ <*> _ <*> <(_ :== ?l)>))) _ _
                      |- _] =>
                      eexists nil, L, _, D_list, pred_list, _, _, 0, _, l
                    end.
                    solve_star; eauto.
                    { rewrite Nat.add_0_r.
                      lazymatch goal with
                      | [H : is_elem_weighted_unique_list _ _ _ |- _] =>
                        apply elem_weighted_unique_list_to_size in H
                      end.
                      unfold is_elem_weighted_unique_list in *.
                      lazymatch goal with
                      | [H : is_set_size ?P0 ?s |- ?s + _ <= _] =>
                        eapply subset_size_le with
                          (P' := set_sum P0 (cross (single x_min) (neighbours g x_min)))
                          (P := uncurry (E g)); auto
                      end.
                      { intros. eapply decidable_if_finite.
                        { intros.
                        apply decidable_uncurry; unfold Decidable.decidable; lia. }
                        { apply disjoint_sum_size.
                          { unfold are_disjoint_sets, uncurry, cross, single, neighbours.
                            intros (a&b) ((?&?&?)&<-&?).
                            lazymatch goal with
                            | [H : _ = empty /\ _ = _ \/
                              (_ src /\_ = neighbourhood _ _) |- _] =>
                              destruct H as [(->&?)| (?&->)]
                            end.
                            { unfold empty in *. assumption. }
                            { unfold min_cost_elem in Hmincost.
                              unfold neighbourhood in *. tauto. } }
                          { eassumption. }
                          { apply cross_size; eauto using single_set_size. } } }
                      { apply disjoint_sum_size.
                        { unfold are_disjoint_sets, uncurry, cross, single, neighbours.
                          intros (a&b) ((?&?&?)&<-&?).
                          lazymatch goal with
                          | [H : _ = empty /\ _ = _ \/
                            (_ src /\ _ = neighbourhood _ _) |- _] =>
                            destruct H as [(->&?)| (?&->)]
                          end.
                          { unfold empty in *. assumption. }
                          { unfold min_cost_elem in Hmincost.
                            unfold neighbourhood in *. tauto. } }
                        { eassumption. }
                        { rewrite <- Nat.mul_1_l.
                          apply cross_size; eauto using single_set_size. } }
                      { unfold is_subset, uncurry, cross, set_sum, single, neighbours.
                        intros [] [(?&?&?)|(->&?)]; auto. } }
                    { rewrite Nat.sub_0_r.
                      eapply star_implies_mono; [prove_implies_refl| |eassumption].
                      (*revert_implies.*)
                      (*rewrite (Nat.mul_comm (n-_)).*) simpl. prove_implies_rev.
                      apply star_implies_mono; [|prove_implies_refl].
                      apply equiv_set_heap. unfold set_equiv, set_sum. tauto. } }
                  { apply implies_spec. intros. exists 0. assumption. } }
                { intros. (*rewrite <- Hpot.*) prove_implies. apply star_comm. }
                +++ unfold l_is_nil_spec in Hspec_l_is_nil.
                  triple_reorder_exists. repeat triple_pull_exists.
                  triple_reorder_pure. repeat triple_pull_pure.
                  rewrite <- (Nat.add_assoc c_is_nil).
                  triple_reorder_credits. triple_pull_credits (S (S c_is_nil)).
                  triple_reorder_credits. triple_pull_credits 2.
                  triple_pull_1_credit.
                  eapply triple_weaken, triple_bneg.
                  { prove_implies_refl. }
                  { apply implies_post_spec. intros. normalize_star.
                    eexists. apply star_pure_l. split; eauto. revert_implies.
                    prove_implies_refl. }
                  eapply triple_fun_app.
                  2:{ eapply triple_weaken, triple_deref.
                    { prove_implies_rev. }
                    { simpl. intros. prove_implies. }
                    { solve_simple_value. } }
                  { eapply triple_fun_weaken, triple_fun_frame, Hspec_l_is_nil.
                    3:eassumption.
                    { intros. simpl. prove_implies.
                      eapply implies_trans; [apply star_comm|].
                      prove_implies. prove_implies_rev. }
                    { apply implies_post_spec. intros. normalize_star.
                      eexists. apply star_pure_l. split; eauto.
                      swap_star_ctx. normalize_star. swap_star_ctx. normalize_star.
                      swap_star_ctx. normalize_star. revert_implies.
                      (*eapply implies_trans;
                        [apply star_implies_mono;
                          [apply implies_refl|apply star_assoc_r]|].
                      eapply implies_trans; [apply star_assoc_l|].*)
                      eapply implies_trans; [apply star_comm|].
                      apply star_implies_mono.
                      { apply implies_spec. intros. do 6 eexists.
                        lazymatch goal with
                        | [_ : Dijkstra_invariant ?D ?pred _ _ _,
                          _ : forall _, List.In _ _ -> ?fD _ = ?D _,
                          _ : forall _, List.In _ _ -> ?fpred _ = ?pred _
                          |- _] =>
                          exists fD, fpred
                        end.
                        solve_star.
                        { f_equal.
                          lazymatch goal with
                          | [|- (List.length ?L =? 0) = is_nil_b (nat_pairs2values ?L')] =>
                            unify L L'; destruct L'; simpl; reflexivity
                          end. }
                        { eassumption. }
                        8:{ swap_star_ctx. normalize_star. swap_star_ctx.
                          normalize_star. swap_star_ctx. normalize_star.
                          lazymatch goal with
                          | [H : ?x = ?y, H' : ($ (_ + (_ * (_ - ?y) + _ * _)) <*> _) ?c ?m
                          |- ($ (_ + (_ * (_ - ?x) + _ * _)) <*> _) ?c ?m] =>
                            rewrite H
                          end.
                          eapply star_implies_mono; try eassumption.
                          { prove_implies_refl. }
                          { prove_implies. subst. prove_implies. }
                        }
                        { assumption. }
                        { assumption. }
                        { assumption. }
                        { assumption. }
                        { assumption. }
                        { eassumption. }
                        { subst. assumption. } }
                      { apply implies_spec. intros. solve_star. eassumption. } } }
                +++ clear Hlen1 Hlen2.
                  triple_reorder_exists. repeat triple_pull_exists.
                  triple_reorder_pure. repeat triple_pull_pure.
                  rewrite Bool.negb_true_iff, Nat.eqb_neq in *.
                  destruct m as [|m'] eqn:Hm; [lia|].
                  rewrite Nat.sub_succ_l, Nat.sub_succ_l, Nat.mul_succ_r; try lia.
                  rewrite <- (Nat.add_assoc (_ * (m' - _ - _))),
                    (Nat.add_assoc _ (_ * (m' - _ - _))),
                    (Nat.add_assoc (_+(_ * (m' - _ - _)))),
                    (Nat.add_comm (_+_ * (m' - _ - _))),
                    (Nat.mul_comm _ (m' - _ - _)),
                    <- (Nat.add_assoc _ (_ + (m' - _ - _)*_)).
                  lazymatch goal with
                  | [Hneq : ?l <> 0, Hlen : List.length ?L = ?l |- _] =>
                    destruct L; simpl in Hlen; [lia|]
                  end.
                  triple_reorder_credits.
                  lazymatch goal with
                  | [H1 : List.length _ = n, H2 : List.length _ = n |- _] =>
                    rename H1 into Hlen1; rename H2 into Hlen2
                  end.
                  lazymatch goal with
                  | [Hlist : is_elem_weighted_unique_list _ _ (_ ++ ?p::_)%list,
                    Hfun : is_nat_fun_of_val_list ?A' ?f,
                    Hfun' : is_nat_fun_of_val_list ?A'' ?f'
                    |- triple _
                      ($_ <*> ($_ <*> ($ _ <*> (_ <*> array_content ?A'' ?a' <*>
                        array_content ?A' ?a <*> _ <*> _)))) _
                    ] =>
                    destruct p as (i'&w');
                    remember Hfun eqn:Heqn; clear Heqn;
                    remember Hfun' eqn:Heqn; clear Heqn;
                    unfold is_nat_fun_of_val_list,
                      list_of_f, fun_of_list in Hfun, Hfun';
                    destruct Hfun as ((L&Heq)&Hfun);
                    destruct Hfun' as ((L'&Heq'')&Hfun');
                    rewrite Heq in Hfun;
                    rewrite Heq'' in Hfun';
                    assert (exists L1 x L2,
                      L = (L1 ++ x :: L2)%list /\ List.length L1 = i')
                      as (?&x'&?&Heq'&Hlen3)
                      by (
                        edestruct (@List.nth_split _ i' L 0%Z)
                          as (?&?&?&?);
                        [ unfold is_elem_weighted_unique_list,
                            is_elem_weighted_list, neighbours in Hlist;
                          destruct Hlist as (Hin&?); specialize Hin with i' w';
                          destruct Hin as ((Hin%E_closed2&?)&?);
                            [apply List.in_or_app; simpl; auto|];
                          erewrite <- List.map_length; rewrite <- Heq, Hlen1;
                          rewrite Hn; eapply init_range_lt_size; eauto
                        | eauto ]
                      );
                    assert (exists L1 x L2,
                      L' = (L1 ++ x :: L2)%list /\ List.length L1 = i')
                      as (?&x''&?&Heq'''&Hlen4)
                      by (
                        edestruct (@List.nth_split _ i' L' 0%Z)
                          as (?&?&?&?);
                        [ unfold is_elem_weighted_unique_list,
                            is_elem_weighted_list, neighbours in Hlist;
                          destruct Hlist as (Hin&?); specialize Hin with i' w';
                          destruct Hin as ((Hin%E_closed2&?)&?);
                            [apply List.in_or_app; simpl; auto|];
                          erewrite <- List.map_length; rewrite <- Heq'', Hlen2;
                          rewrite Hn; eapply init_range_lt_size; eauto
                        | eauto ]
                      )
                  end.
                  rewrite Heq, Heq', List.map_app. simpl List.map.
                  instantiate (cm := S ?[ccm] + ?[cm2]). instantiate (ccm := ?[cm]).
                  instantiate (cn_t := ?[ccn_t] + ?[cn_t2]).
                  instantiate (ccn_t := ?[cn_t]).
                  lazymatch goal with
                  | [Hpred : is_nat_fun_of_val_list ?pred_list ?pred,
                     HD : is_nat_fun_of_val_list ?D_list ?D,
                     HeqD_list : ?D_list = _ ?DL,
                     HeqDL : ?DL = (?L1 ++ ?t::?L2)%list
                    |- triple _
                      ($(S ?cm + ?cm2 + (?cr + ?cr2 + (?cn_t + ?cn_t2)*?t')) <*> ( ($?pot <*> ($?c2 <*>
                        (?P1 <*> ?P2 <*>
                        array_content ?pred_list ?a_pred <*>
                        array_content (?f1 ?L1 ++ Some (Int ?t):: ?f2 ?L2) ?a_D <*>
                        is_heap ?n ?C ?H ?W ?pot ?h <*>
                        ?P3)))))
                      _] =>
                    (*let P := constr:($c0 <*> ( ($pot <*> ($c2 <*>
                      (P1 <*> P2 <*>
                      array_content pred_list a_pred <*>
                      array_content (f1 L1 ++ Some (Int t):: f2 L2) a_D <*>
                      is_heap n C H W pot h <*>
                      P3)))))
                    in*)
                    assert (S cm + cm2 + (cr + cr2 + (cn_t + cn_t2)*t')
                      = S cm + cn_t*t' + (cm2 + cr + cr2 + cn_t2*t'))
                      as -> by lia;
                    triple_pull_credits (S cm + cn_t*t');
                    triple_pull_1_credit;
                    eapply triple_seq with
                      (Q1 :=
                        ((<exists> D' pred' D_list' pred_list' H W pot,
                        (*<[distance_decrease g src D D' pred pred']> <*>*)
                        <[is_nat_fun_of_val_list D_list' D']> <*>
                        <[is_nat_fun_of_val_list pred_list' pred']> <*>
                        $c2 <*> P1 <*> P2 <*> P3 <*>
                        array_content D_list' a_D <*>
                        is_heap n C H W pot h <*>
                        array_content pred_list' a_pred) <*>
                        <exists> c, $c) <*> $(cm2 + cr + cr2 + cn_t2*t'))
                  end.
                 (*eapply triple_seq.*)
                  *** eapply triple_weaken, triple_frame.
                    2:{
                      apply implies_post_spec. intros.
                      apply star_assoc_r. revert_implies. prove_implies_refl.
                    }
                    { apply implies_spec. intros. swap_star. revert_implies.
                      prove_implies_rev. }
                    instantiate (cm := S ?[ccm]). instantiate (ccm := ?[cm]).
                    triple_pull_1_credit. app_lambda.
                    2:{
                      unfold l_head_spec in Hspec_l_head.
                      instantiate (cm := S c_l_head + ?[ccm]).
                      instantiate (ccm := ?[cm]).
                      rewrite <- (Nat.add_assoc (S c_l_head)).
                      triple_reorder_credits. triple_pull_credits (S c_l_head).
                      triple_pull_1_credit.
                      eapply triple_fun_app.
                      { apply triple_fun_frame, Hspec_l_head. eassumption. }
                      { eapply triple_weaken, triple_deref.
                        { prove_implies_rev. }
                        { intros. simpl. prove_implies. eapply implies_trans.
                          { apply star_comm. }
                          { apply star_assoc. } }
                        { solve_simple_value. revert_implies. prove_implies_rev. } }
                    }
                    clear l_head Hspec_l_head.
                    solve_simple_value. split; auto. intros. cbn.
                    rewrite_all_binds. triple_reorder_pure. repeat triple_pull_pure.
                    instantiate (cm := S ?[ccm]). instantiate (ccm := ?[cm]).
                    triple_pull_1_credit. app_lambda.
                    2:{
                      instantiate (cm := S ?[ccm]). instantiate (ccm := ?[cm]).
                      triple_pull_1_credit. eapply triple_weaken, triple_get.
                      { prove_implies_refl. }
                      { prove_implies_refl. }
                      solve_simple_value.
                      { constructor. }
                      { lazymatch goal with
                        | [H : ?P ?c ?m |- ?Q ?v' ?c ?m] =>
                          remember v' as v_int eqn:Hv_int;
                          assert ((<[v_int = v']> <*> P) c m) as Hassertion
                            by (subst; solve_star);
                          clear H
                        end.
                        clear Hv_int. revert_implies. clear_state_assertions.
                        prove_implies_refl. }
                    }
                    solve_simple_value. split; auto. intros. cbn.
                    rewrite_all_binds. triple_reorder_pure. repeat triple_pull_pure.
                    revert Hn Hpot Hlen1 Hlen2 Hlen3 Hlen4 Hm. subst. intros.
                    instantiate (cm := S ?[ccm]). instantiate (ccm := ?[cm]).
                    triple_pull_1_credit. app_lambda.
                    2:{
                      instantiate (cm := S ?[ccm]). instantiate (ccm := ?[cm]).
                      triple_pull_1_credit. eapply triple_weaken, triple_get.
                      { prove_implies_refl. }
                      { prove_implies_refl. }
                      solve_simple_value.
                      { repeat constructor. }
                      { lazymatch goal with
                        | [H : ?P ?c ?m |- ?Q ?v' ?c ?m] =>
                          remember v' as v_int eqn:Hv_int;
                          assert ((<[v_int = v']> <*> P) c m) as Hassertion
                            by (subst; solve_star);
                          clear H
                        end.
                        clear Hv_int. revert_implies. clear_state_assertions.
                        prove_implies_refl. }
                    }
                    solve_simple_value. split; auto. intros. cbn.
                    rewrite_all_binds. triple_reorder_pure. repeat triple_pull_pure.
                    revert Hn Hpot Hlen1 Hlen2 Hlen3 Hlen4 Hm. subst. intros.
                    clear_state_assertions.
                    instantiate (cm := S ?[ccm]). instantiate (ccm := ?[cm]).
                    triple_pull_1_credit. app_lambda.
                    2:{
                      pose proof triple_fun_n_ary_app as Hn_ary.
                      pose proof triple_fun_n_ary_weaken as Hweaken.
                      pose proof triple_fun_n_ary_read_array_at as Hread_array_at.
                      instantiate (cm := 5 + ?[ccm]). instantiate (ccm := ?[cm]).
                      triple_pull_credits 4. triple_reorder_credits.
                      triple_pull_credits 2. triple_pull_1_credit.
                      lazymatch goal with
                      | [|- triple (Val read_array_at <* Val ?v <* _) _ _] =>
                        eapply triple_weaken with
                          (P := ($1 <*> ($1 <*> ($ 2 <*> array_content _ v))) <*> _),
                          triple_frame;
                          [| |revert v]
                      end.
                      { prove_implies_rev. }
                      { prove_implies_refl. }
                      lazymatch goal with
                      | [|-
                        forall a,
                          triple (Val (@?f a) <* (@?e1 a) <* (@?e2 a))
                            ($1 <*> (@?P0 a))
                            (@?Q1 a)
                        ] =>
                        intros a;
                        specialize Hn_ary with
                          (v := f a) (e := e1 a) (es := [e2 a]%list)
                          (P := P0 a)
                      end.
                      lazymatch goal with
                      | [Hlist : is_elem_weighted_unique_list
                          _ _ (_ ++ (?i',?w')::_)%list,
                        H : forall A A1 x A2 i, _ -> _ ->
                          triple_fun_n_ary _ read_array_at
                            (@?Pre A i) (@?Post A x)
                        |- triple
                          (Val read_array_at <* Val ?a <* Val (Int (Z.of_nat ?i')))
                          ($_ <*> ($_ <*> ($ _ <*> array_content ?A' ?a))) _
                        ] =>
                        specialize Hn_ary with
                          (Q1 := Pre A' i') (Q2 := Post A' (Int x'));
                        specialize Hread_array_at with
                          (A := A') (i := i') (x := Int x')
                      end.
                      simpl in Hn_ary, Hread_array_at, Hweaken. eapply Hn_ary.
                      { eapply Hread_array_at; auto. rewrite List.map_length.
                        eassumption. }
                      { solve_simple_value. revert_implies. prove_implies_refl. }
                      { solve_simple_value. revert_implies.
                        remember (Int (Z.of_nat i')). prove_implies_refl. }
                      { simpl. prove_implies. apply implies_spec. intros.
                        solve_star. }
                    }
                    solve_simple_value. split; auto. intros. cbn. rewrite_all_binds.
                    clear_state_assertions. triple_reorder_pure.
                    repeat triple_pull_pure. revert Hn Hpot Hlen1 Hlen2 Hlen3 Hlen4 Hm.
                    subst. intros. triple_pull_1_credit. app_lambda.
                    2:{ instantiate (cm := S ?[ccm]). instantiate (ccm := ?[cm]).
                      triple_pull_1_credit.
                      lazymatch goal with
                      | [|- triple (Val (Int ?i1) [+] Val (Int ?i2)) ($1 <*> ?P) _] =>
                        eapply triple_iadd with
                          (Q1 := fun i1' => <[i1' = i1]> <*> P)
                          (Q2 := fun i1' i2' => <[i1' = i1]> <*> <[i2' = i2]> <*> P)
                      end.
                      { solve_simple_value. }
                      { intros. triple_pull_pure. solve_simple_value. }
                      (*lazymatch goal with
                      | [H : _ = Some (Int ?i1) |-
                          triple (Val (Int ?i1) [+] Val (Int ?i2)) _ _] =>
                        remember i1 as i1' eqn:Hi1; remember i2 as i2' eqn:Hi2;
                        rewrite Hi1 in H
                      end.
                      generalize dependent i2'. generalize dependent i1'.
                      lazymatch goal with
                      | [|- forall i1', _ -> forall i2', _ = ?i2 ->
                          triple _ ($1 <*> @?P i1' i2') (@?Q i1' i2')] =>
                        intros ? -> ? ->;
                        eapply triple_iadd
                          with (Q1 := P i2) (Q2 := P)
                      end.
                      { solve_simple_value. revert_implies.
                        prove_implies_refl. }
                      { intros. solve_simple_value. revert_implies.
                      prove_implies_refl. }*)
                    }
                    solve_simple_value. split; auto. intros. cbn. rewrite_all_binds.
                    clear_state_assertions. triple_reorder_exists.
                    repeat triple_pull_exists. triple_reorder_pure.
                    repeat triple_pull_pure. revert Hn Hpot Hlen1 Hlen2 Hlen3 Hlen4 Hm.
                    subst. intros.
                    instantiate (cm := 14+?[ccm]). instantiate (ccm := ?[cm]).
                    simpl. triple_pull_credits 14. triple_reorder_credits.
                    simpl. triple_pull_credits 2. triple_reorder_credits.
                    triple_pull_1_credit.
                    rewrite List.map_app in *. simpl in *.
                    lazymatch goal with
                    | [Hpred : is_nat_fun_of_val_list (?L1++?ox::?L2) ?pred,
                       HD : is_nat_fun_of_val_list (?L1'++?ox'::?L2') ?D
                      |- triple _
                        ($1 <*> ($1 <*> ($?c0 <*> ($?c1 <*> ($?pot <*> ($?c2 <*>
                          (?P1 <*> array_content (?L1++?ox::?L2) ?a_D <*>
                          is_heap ?n ?C ?H ?W ?pot ?h <*> ?P2 <*> ?P3 <*>
                          array_content (?L1'++?ox'::?L2') ?a_pred)))))))
                        _] =>
                      let P := constr:($c0 <*> ($c1 <*> ($pot <*> ($c2 <*>
                        (P1 <*> array_content (L1++ox::L2) a_D <*>
                        is_heap n C H W pot h <*> P2 <*> P3 <*>
                        array_content (L1'++ox'::L2') a_pred)))))
                      in
                      eapply triple_if with
                        (Q1 := fun b : bool => <[(x' <? 0)%Z = b]> <*> P)
                        (*(Q2 := fun v => <[v = U_val]> <*>
                          ((<exists> D' pred' oy oy',
                          <[distance_decrease g src D D' pred pred']> <*>
                          <[is_nat_fun_of_val_list (L1++oy::L2) D']> <*>
                          <[is_nat_fun_of_val_list (L1'++oy'::L2') pred']> <*>
                          $c1 <*> $c2 <*> P1 <*>
                          array_content (L1++oy::L2) a_D <*>
                          is_heap n C H W pot h <*> P2 <*> P3 <*>
                          array_content (L1'++oy'::L2') a_pred) <*>
                          <exists> c, $c))*)
                    end.
(*
                    lazymatch goal with
                    | [Hpred : is_nat_fun_of_val_list (?L1++?ox::?L2) ?pred,
                       HD : is_nat_fun_of_val_list (?L1'++?ox'::?L2') ?D
                      |- triple _
                        ($1 <*> ($1 <*> ($?c0 <*> ($?c1 <*> ($?pot <*> ($?c2 <*>
                          ((is_list (?hd::?L) ?l <-*> is_weighted_graph ?g ?vg) <*>
                          array_content (?L1++?ox::?L2) ?a_D <*>
                          is_heap ?n ?C ?H ?W ?pot ?h <*> ?P2 <*>
                          is_list (?hd::?L) ?l <*>
                          array_content (?L1'++?ox'::?L2') ?a_pred)))))))
                        _] =>
                      let P := constr:($c0 <*> ($c1 <*> ($pot <*> ($c2 <*>
                        ((is_list (hd::L) l <-*> is_weighted_graph g vg) <*>
                        array_content (L1++ox::L2) a_D <*>
                        is_heap n C H W pot h <*> P2 <*>
                        is_list (hd::L) l <*>
                        array_content (L1'++ox'::L2') a_pred)))))
                      in
                      eapply triple_if with
                        (Q1 := fun b : bool => <[(x' <? 0)%Z = b]> <*> P)
                        (Q2 := fun v => <[v = U_val]> <*>
                          ((<exists> D' pred' oy oy',
                          <[distance_decrease g src D D' pred pred']> <*>
                          <[is_nat_fun_of_val_list (L1++oy::L2) D']> <*>
                          <[is_nat_fun_of_val_list (L1'++oy'::L2') pred']> <*>
                          $c1 <*> $c2 <*>
                          (is_list L l <-*> is_weighted_graph g vg) <*>
                          array_content (L1++oy::L2) a_D <*>
                          is_heap n C H W pot h <*> P2 <*>
                          is_list L l <*>
                          array_content (L1'++oy'::L2') a_pred) <*>
                          <exists> c, $c))
                    end.
*)
                    ----
                      lazymatch goal with
                      | [|- triple _ ($1 <*> ?P) _] =>
                        eapply triple_weaken, triple_clt with
                          (Q1 := fun i1 => <[i1 = x']> <*> P)
                          (Q2 := fun i1 i2 => <[i1 = x']> <*> <[i2 = 0%Z]> <*> P)
                      end.
                      { prove_implies_refl. }
                      { apply implies_post_spec. intros. normalize_star. subst.
                        solve_star. }
                      ++++ solve_simple_value.
                      ++++ intros. triple_reorder_pure. repeat triple_pull_pure.
                        solve_simple_value.
                    ---- clear h_decrease_key Hspec_h_decrease_key.
                      triple_reorder_pure. repeat triple_pull_pure.
                      rewrite Z.ltb_lt in *.
                      (*instantiate (cm := S ?[ccm]). instantiate (ccm := ?[cm]).*)
                      simpl. triple_pull_1_credit. eapply triple_seq.
                      ++++
                        pose proof triple_fun_n_ary_app as Hn_ary.
                        pose proof triple_fun_n_ary_weaken as Hweaken.
                        pose proof triple_fun_n_ary_assign_array_at
                          as Hassign_array_at.
                        (*instantiate (cm := 5+ ?[ccm]). instantiate (ccm := ?[cm]).*)
                        simpl.
                        triple_pull_credits 5. triple_reorder_credits.
                        triple_pull_credits 4. triple_reorder_credits.
                        triple_pull_credits 2. triple_reorder_credits.
                        clear_state_assertions.
                        lazymatch goal with
                        | [|- triple (Val assign_array_at <* Val ?v <* _ <* _) _ _] =>
                          eapply triple_weaken with
                            (P := ($_ <*> ($_ <*> ($_ <*> (array_content _ v)))) <*> ($ _ <*> _)),
                            triple_frame;
                            [| |revert v]
                        end.
                        { prove_implies_rev. }
                        { intros. apply star_assoc. }
                        lazymatch goal with
                        | [|-
                          forall a,
                            triple (Val (@?f a) <* (@?e1 a) <* (@?e2 a) <* (@?e3 a))
                              ($2 <*> (@?P0 a))
                              (@?Q1 a)
                          ] =>
                          intros a;
                          specialize Hn_ary with
                            (v := f a) (e := e1 a) (es := [e2 a;e3 a]%list)
                            (P := P0 a)
                        end.
                        lazymatch goal with
                        | [H : forall A A' A1 ov A2 i x, _ -> _ -> _ ->
                            triple_fun_n_ary ?n' assign_array_at (@?P A i x) (@?Q A')
                          |- triple (Val assign_array_at <* Val ?a <* Val (Int (Z.of_nat ?i)) <* Val ?y)
                            ($_ <*> ($_ <*> ($_ <*> array_content (?A1' ++ Some ?x::?A2')%list ?v))) _
                          ] =>
                          let A := constr:((A1' ++ Some x::A2')%list) in
                          let A' := constr:((A1' ++ Some y::A2')%list) in
                          specialize Hn_ary with
                            (Q1 := P A i y) (Q2 := Q A')
                        end.
                        specialize (Hweaken _ assign_array_at 2).
                        simpl in Hn_ary, Hassign_array_at, Hweaken. eapply Hn_ary.
                        { eapply Hassign_array_at; auto.
                          rewrite List.map_length. assumption. }
                        { solve_simple_value. revert_implies. prove_implies_refl. }
                        { solve_simple_value. revert_implies. remember (Int (Z.of_nat i')).
                          prove_implies_refl. }
                        { solve_simple_value. revert_implies.
                          lazymatch goal with
                          | [|- _ ->> _ ?v] => remember v
                          end.
                          prove_implies_refl. }
                        { simpl. apply implies_spec. intros. swap_star. solve_star. swap_star.
                          solve_star. revert_implies. prove_implies. }
                      ++++ (*instantiate (cm := S ?[ccm]). instantiate (ccm := ?[cm]).*)
                        simpl. triple_pull_1_credit. eapply triple_seq.
                        ****
                          pose proof triple_fun_n_ary_app as Hn_ary.
                          pose proof triple_fun_n_ary_weaken as Hweaken.
                          pose proof triple_fun_n_ary_assign_array_at
                            as Hassign_array_at.
                          (*instantiate (cm := 5+ ?[ccm]). instantiate (ccm := ?[cm]).*)
                          simpl.
                          (*triple_pull_credits 5. triple_reorder_credits.*)
                          triple_pull_credits 4. triple_reorder_credits.
                          triple_pull_credits 2. triple_reorder_credits.
                          clear_state_assertions.
                          lazymatch goal with
                          | [|- triple (Val assign_array_at <* Val ?v <* _ <* _) _ _] =>
                            eapply triple_weaken with
                              (P := ($_ <*> ($_ <*> ($_ <*> (array_content _ v)))) <*> ($ _ <*> _)),
                              triple_frame;
                              [| |revert v]
                          end.
                          { prove_implies_rev. }
                          { intros. apply star_assoc. }
                          lazymatch goal with
                          | [|-
                            forall a,
                              triple (Val (@?f a) <* (@?e1 a) <* (@?e2 a) <* (@?e3 a))
                                ($2 <*> (@?P0 a))
                                (@?Q1 a)
                            ] =>
                            intros a;
                            specialize Hn_ary with
                              (v := f a) (e := e1 a) (es := [e2 a;e3 a]%list)
                              (P := P0 a)
                          end.
                          lazymatch goal with
                          | [H : forall A A' A1 ov A2 i x, _ -> _ -> _ ->
                              triple_fun_n_ary ?n' assign_array_at (@?P A i x) (@?Q A')
                            |- triple (Val assign_array_at <* Val ?a <* Val (Int (Z.of_nat ?i)) <* Val ?y)
                              ($_ <*> ($_ <*> ($_ <*> array_content (?A1' ++ Some ?x::?A2')%list ?v))) _
                            ] =>
                            let A := constr:((A1' ++ Some x::A2')%list) in
                            let A' := constr:((A1' ++ Some y::A2')%list) in
                            specialize Hn_ary with
                              (Q1 := P A i y) (Q2 := Q A')
                          end.
                          specialize (Hweaken _ assign_array_at 2).
                          simpl in Hn_ary, Hassign_array_at, Hweaken. eapply Hn_ary.
                          { eapply Hassign_array_at; auto.
                            rewrite List.map_length. assumption. }
                          { solve_simple_value. revert_implies. prove_implies_refl. }
                          { solve_simple_value. revert_implies. remember (Int (Z.of_nat i')).
                            prove_implies_refl. }
                          { solve_simple_value. revert_implies.
                            lazymatch goal with
                            | [|- _ ->> _ ?v] => remember v
                            end.
                            prove_implies_refl. }
                          { simpl. apply implies_spec. intros. swap_star. solve_star. swap_star.
                            solve_star. revert_implies. prove_implies. }
                        **** triple_reorder_credits.
                          pose proof triple_fun_n_ary_app as Hn_ary.
                          pose proof triple_fun_n_ary_weaken as Hweaken.
                          unfold h_insert_spec in Hspec_h_insert.
                          instantiate (cm := 3+ ?[ccm]). instantiate (ccm := ?[cm]).
                          instantiate (cn_t := S ?[ccn_t]). instantiate (ccn_t := ?[cn_t]).
                          simpl.
                          lazymatch goal with
                          | [H : heap_time_bound ?n ?C ?t |- _] =>
                            remember t as t_credits eqn:Ht_credits
                          end.
                          erewrite <- (Nat.add_succ_l _ (_*t_credits)),
                            <- Ht_credits, (Nat.add_comm t_credits).
                          repeat erewrite (Nat.add_assoc _ _ t_credits).
                          erewrite (Nat.add_comm _ t_credits).
                          triple_pull_credits (3+t_credits). triple_reorder_credits.
                          triple_pull_credits 3. triple_reorder_credits.
                          triple_pull_credits 2. triple_reorder_credits.
                          lazymatch goal with
                          | [|- triple (Val h_insert <* Val ?v <* _ <* _) _ _] =>
                            eapply triple_weaken with
                              (P := ($2 <*> ($1 <*> ($ (t_credits) <*>
                                (is_heap n _ _ _ _ v)))) <*> ($ _ <*> $ _ <*> _)),
                              triple_frame;
                              [| |revert v]
                          end.
                          { prove_implies_rev. }
                          { intros.
                            eapply implies_trans with
                              (Q := (<exists> c, $c) <*>
                                (<exists> a b c, is_heap n _ a b c _ <*> _) <*> _).
                            { prove_implies_refl. }
                            { apply implies_spec. intros.
                              normalize_star. swap_star_ctx. normalize_star.
                              swap_star_ctx. normalize_star. swap_star_ctx.
                              normalize_star.
                               apply star_assoc. swap_star.
                              revert_implies.
                              eapply implies_trans; [apply star_assoc_l|].
                              eapply implies_trans; [apply star_assoc_l|].
                              eapply implies_trans; [apply star_assoc_l|].
                              eapply implies_trans;
                                [apply star_implies_mono;
                                  [apply star_comm|prove_implies_refl]|].
                              eapply implies_trans; [apply star_assoc_r|].
                              (*eapply implies_trans; [apply star_comm|].*)
                              (*eapply implies_trans; [apply star_assoc_r|].*)
                              eapply implies_trans;
                                [apply star_implies_mono;
                                  [prove_implies_refl|apply star_assoc_r]|].
                              eapply implies_trans; [apply star_assoc_l|].
                              apply star_implies_mono.
                              { apply implies_spec. intros. eexists.
                                eapply credits_star_l; try reflexivity.
                                eapply star_implies_mono; eauto; [prove_implies_refl|].
                                eapply credits_star_l; reflexivity. }
                              { eapply implies_trans; [apply star_comm|].
                                eapply implies_trans; [apply star_assoc|].
                                eapply implies_trans; [apply star_comm|].
                                eapply implies_trans; [apply star_assoc|].
                                eapply implies_trans; [apply star_assoc|].
                                apply star_implies_mono; [prove_implies_refl|].
                                apply implies_spec. intros. do 7 eexists.
                                conormalize_star. swap_star. apply star_assoc.
                                eapply star_implies_mono;
                                  [|prove_implies_refl|eassumption].
                                apply implies_spec. intros.
                                swap_star. conormalize_star.
                                eapply star_implies_mono;
                                  [|prove_implies_refl|eassumption].
                                apply implies_spec. intros. conormalize_star.
                                eapply star_implies_mono;
                                  [|prove_implies_refl|eassumption].
                                apply implies_spec. intros. conormalize_star.
                                swap_star_ctx. conormalize_star.
                                eapply star_implies_mono;
                                  [|prove_implies_refl|eassumption].
                                prove_implies. } } }
                          lazymatch goal with
                          | [|-
                            forall a,
                              triple (Val (@?f a) <* (@?e1 a) <* (@?e2 a) <* (@?e3 a))
                                ($2 <*> (@?P0 a))
                                (@?Q1 a)
                            ] =>
                            intros a;
                            specialize Hn_ary with
                              (v := f a) (e := e1 a) (es := [e2 a;e3 a]%list)
                              (P := P0 a)
                          end.
                          lazymatch goal with
                          | [H : forall n C P W p s k d c t, _ -> _ -> _ -> _ -> _ ->
                              triple_fun_n_ary _ h_insert
                                (@?Pre n C P W p k d c) (@?Post n C P W p k d t)
                            |- triple
                              (Val h_insert <* Val ?h <* Val (Int (Z.of_nat ?s')) <* Val (Int ?x))
                              ($_ <*> ($_ <*> ($ ?t' <*> is_heap ?n' ?C' ?P' ?W' ?p' ?h))) _
                            ] =>
                            let d' := constr:(Z.to_nat x) in
                            let c' := constr:(t') in
                            specialize Hn_ary with
                              (Q1 := Pre n' C' P' W' p' s' d' c')
                              (Q2 := Post n' C' P' W' p' s' d' t');
                            specialize Hspec_h_insert with
                              (n := n') (C := C') (P := P') (W := W') (p := p') (k := s')
                              (d := d') (c := t') (t := t')
                          end.
                          specialize (Hweaken _ assign_array_at 2).
                          simpl in Hn_ary, Hspec_h_insert, Hweaken. eapply triple_weaken, Hn_ary.
                          { prove_implies_refl. }
                          { apply implies_post_spec. intros ? ? ? HQ.
                            normalize_star. swap_star_ctx. normalize_star.
                            solve_star. swap_star. solve_star. swap_star.
                            solve_star.
                            (*{ unfold distance_decrease. (*TODO*) }*)
                            { rewrite <- (Nat2Z.inj_add).
                              eapply nat_function_update. eassumption. }
                            { eapply nat_function_update. eassumption. }
                            { swap_star. eassumption. } }
                          { rewrite <- Hn in *.
                            edestruct is_set_size_with_neighbours as (?&?&?); eauto.
                            { unfold min_cost_elem in Hmincost.
                              destruct Hmincost as (?&?). eassumption. }
                            eapply Hspec_h_insert; unfold empty, not; auto.
                            { eassumption. }
                            { eassumption. }
                            { unfold set_sum, set_remove. intros [(Hin&Hneq)|Hin].
                              { lazymatch goal with
                                | [H : forall _ _,
                                    List.nth _ (_ _ ++ Some (Int x')::_ _)%list _ = _
                                    <-> ?f _ = _
                                  |- _] =>
                                  assert (f i' = None);
                                    [destruct (f i') eqn:Hf;
                                      [rewrite <- H in Hf|]|]
                                end.
                                { rewrite List.app_nth2 in Hf.
                                  { rewrite List.map_length in Hf. subst.
                                    rewrite Nat.sub_diag in Hf. simpl in Hf.
                                    injection Hf. lia. }
                                  { rewrite List.map_length. lia. } }
                                { reflexivity. }
                                lazymatch goal with
                                | [H : Dijkstra_invariant ?D _ _ src g,
                                  H' : ?f i' = None,
                                  H'' : forall _, _ -> ?f _ = ?D _
                                  |- _] =>
                                  rewrite H'' in H';
                                  [apply Dijkstra_invariant_nonnone
                                    with (x := i') in H|];
                                  auto
                                end.
                                lazymatch goal with
                                | [H : (_ = empty /\ _ = set_sum empty (single src)) \/
                                    (_ src /\ _ = neighbourhood _ _)
                                  |- _] =>
                                  unfold empty, single, set_sum in H;
                                  destruct H as [(->&->)|(?&->)]
                                end.
                                { destruct Hin as [[]| ->]. auto. }
                                { auto. } }
                              { lazymatch goal with
                                | [H : is_elem_weighted_unique_list _ _ (?L++_)%list,
                                  H' : List.In i' (List.map fst ?L)
                                  |- _] =>
                                  unfold is_elem_weighted_unique_list in H;
                                  rewrite List.map_app in H;
                                  destruct H as (?&H%List.NoDup_remove_2);
                                  apply H
                                end.
                                simpl. apply List.in_or_app. auto. } } }
                          { solve_simple_value. revert_implies. prove_implies_refl. }
                          { solve_simple_value. revert_implies. remember (Int (Z.of_nat i')).
                            prove_implies_refl. }
                          { solve_simple_value. revert_implies.
                            lazymatch goal with
                            | [|- _ ->> _ ?v] => remember v
                            end.
                            prove_implies_refl. }
                          { simpl. apply implies_spec. intros. swap_star. solve_star. swap_star.
                            solve_star.
                            { rewrite <- Nat2Z.inj_add. repeat f_equal.
                              rewrite Nat2Z.id. reflexivity. }
                            { revert_implies. prove_implies. } }
                    ---- clear h_insert Hspec_h_insert.
                      triple_reorder_pure. repeat triple_pull_pure.
                      rewrite Z.ltb_nlt in *.
                      triple_pull_credits 2. triple_reorder_credits.
                      triple_pull_1_credit.
                      lazymatch goal with
                      | [|- triple (If (Val (Int ?t) [<] _) _ _) ($1 <*> ($1 <*> ?P)) _] =>
                        eapply triple_if with
                          (Q1 := fun b : bool => <[(t <? x')%Z = b]> <*> P)
                      end.
                      ++++
                        lazymatch goal with
                        | [|- triple (Val (Int ?t) [<] _) ($1 <*> ?P) _] =>
                          eapply triple_weaken, triple_clt with
                            (Q1 := fun i1 => <[i1 = t]> <*> P)
                            (Q2 := fun i1 i2 => <[i1 = t]> <*> <[i2 = x']> <*> P)
                        end.
                        { prove_implies_refl. }
                        { apply implies_post_spec. intros. normalize_star. subst.
                          solve_star. }
                        **** solve_simple_value.
                        **** intros. triple_reorder_pure. repeat triple_pull_pure.
                          solve_simple_value.
                      ++++ triple_reorder_pure. repeat triple_pull_pure.
                        rewrite Z.ltb_lt in *.
                        instantiate (cm := S ?[ccm]). instantiate (ccm := ?[cm]).
                        simpl. triple_pull_1_credit. eapply triple_seq.
                        ****
                          pose proof triple_fun_n_ary_app as Hn_ary.
                          pose proof triple_fun_n_ary_weaken as Hweaken.
                          pose proof triple_fun_n_ary_assign_array_at
                            as Hassign_array_at.
                          (*instantiate (cm := 5+ ?[ccm]). instantiate (ccm := ?[cm]).*)
                          simpl.
                          triple_pull_credits 5. triple_reorder_credits.
                          triple_pull_credits 4. triple_reorder_credits.
                          triple_pull_credits 2. triple_reorder_credits.
                          clear_state_assertions.
                          lazymatch goal with
                          | [|- triple (Val assign_array_at <* Val ?v <* _ <* _) _ _] =>
                            eapply triple_weaken with
                              (P := ($_ <*> ($_ <*> ($_ <*> (array_content _ v)))) <*> ($ _ <*> _)),
                              triple_frame;
                              [| |revert v]
                          end.
                          { prove_implies_rev. }
                          { intros. apply star_assoc. }
                          lazymatch goal with
                          | [|-
                            forall a,
                              triple (Val (@?f a) <* (@?e1 a) <* (@?e2 a) <* (@?e3 a))
                                ($2 <*> (@?P0 a))
                                (@?Q1 a)
                            ] =>
                            intros a;
                            specialize Hn_ary with
                              (v := f a) (e := e1 a) (es := [e2 a;e3 a]%list)
                              (P := P0 a)
                          end.
                          lazymatch goal with
                          | [H : forall A A' A1 ov A2 i x, _ -> _ -> _ ->
                              triple_fun_n_ary ?n' assign_array_at (@?P A i x) (@?Q A')
                            |- triple (Val assign_array_at <* Val ?a <* Val (Int (Z.of_nat ?i)) <* Val ?y)
                              ($_ <*> ($_ <*> ($_ <*> array_content (?A1' ++ Some ?x::?A2')%list ?v))) _
                            ] =>
                            let A := constr:((A1' ++ Some x::A2')%list) in
                            let A' := constr:((A1' ++ Some y::A2')%list) in
                            specialize Hn_ary with
                              (Q1 := P A i y) (Q2 := Q A')
                          end.
                          specialize (Hweaken _ assign_array_at 2).
                          simpl in Hn_ary, Hassign_array_at, Hweaken. eapply Hn_ary.
                          { eapply Hassign_array_at; auto.
                            rewrite List.map_length. assumption. }
                          { solve_simple_value. revert_implies. prove_implies_refl. }
                          { solve_simple_value. revert_implies. remember (Int (Z.of_nat i')).
                            prove_implies_refl. }
                          { solve_simple_value. revert_implies.
                            lazymatch goal with
                            | [|- _ ->> _ ?v] => remember v
                            end.
                            prove_implies_refl. }
                          { simpl. apply implies_spec. intros. swap_star. solve_star. swap_star.
                            solve_star. revert_implies. prove_implies. }
                        **** (*instantiate (cm := S ?[ccm]). instantiate (ccm := ?[cm]).*)
                          simpl. triple_pull_1_credit. eapply triple_seq.
                          -----
                            pose proof triple_fun_n_ary_app as Hn_ary.
                            pose proof triple_fun_n_ary_weaken as Hweaken.
                            pose proof triple_fun_n_ary_assign_array_at
                              as Hassign_array_at.
                            (*instantiate (cm := 5+ ?[ccm]). instantiate (ccm := ?[cm]).*)
                            simpl.
                            eapply triple_weaken.
                            { eapply implies_trans; [apply star_assoc|].
                              apply star_implies_mono; [|prove_implies_refl].
                              apply credits_star_l. reflexivity. }
                            { prove_implies_refl. }
                            triple_pull_credits 5. triple_reorder_credits.
                            triple_pull_credits 4. triple_reorder_credits.
                            triple_pull_credits 2. triple_reorder_credits.
                            clear_state_assertions.
                            lazymatch goal with
                            | [|- triple (Val assign_array_at <* Val ?v <* _ <* _) _ _] =>
                              eapply triple_weaken with
                                (P := ($_ <*> ($_ <*> ($_ <*> (array_content _ v)))) <*> ($ _ <*> _)),
                                triple_frame;
                                [| |revert v]
                            end.
                            { prove_implies_rev. }
                            { intros. apply star_assoc. }
                            lazymatch goal with
                            | [|-
                              forall a,
                                triple (Val (@?f a) <* (@?e1 a) <* (@?e2 a) <* (@?e3 a))
                                  ($2 <*> (@?P0 a))
                                  (@?Q1 a)
                              ] =>
                              intros a;
                              specialize Hn_ary with
                                (v := f a) (e := e1 a) (es := [e2 a;e3 a]%list)
                                (P := P0 a)
                            end.
                            (*rewrite List.map_app in *. simpl.*)
                            lazymatch goal with
                            | [H : forall A A' A1 ov A2 i x, _ -> _ -> _ ->
                                triple_fun_n_ary ?n' assign_array_at (@?P A i x) (@?Q A')
                              |- triple (Val assign_array_at <* Val ?a <* Val (Int (Z.of_nat ?i)) <* Val ?y)
                                ($_ <*> ($_ <*> ($_ <*> array_content (?A1' ++ Some ?x::?A2')%list ?v))) _
                              ] =>
                              let A := constr:((A1' ++ Some x::A2')%list) in
                              let A' := constr:((A1' ++ Some y::A2')%list) in
                              specialize Hn_ary with
                                (Q1 := P A i y) (Q2 := Q A')
                            end.
                            specialize (Hweaken _ assign_array_at 2).
                            simpl in Hn_ary, Hassign_array_at, Hweaken. eapply Hn_ary.
                            { eapply Hassign_array_at; auto.
                              rewrite List.map_length. assumption. }
                            { solve_simple_value. revert_implies. prove_implies_refl. }
                            { solve_simple_value. revert_implies. remember (Int (Z.of_nat i')).
                              prove_implies_refl. }
                            { solve_simple_value. revert_implies.
                              lazymatch goal with
                              | [|- _ ->> _ ?v] => remember v
                              end.
                              prove_implies_refl. }
                            { simpl. apply implies_spec. intros. swap_star. solve_star. swap_star.
                              solve_star. revert_implies. prove_implies. }
                          -----
                            triple_reorder_credits.
                            pose proof triple_fun_n_ary_app as Hn_ary.
                            pose proof triple_fun_n_ary_weaken as Hweaken.
                            unfold h_decrease_key_spec in Hspec_h_decrease_key.
                            instantiate (cm := 2+ ?[ccm]). instantiate (ccm := ?[cm]).
                            triple_pull_credits 4. triple_reorder_credits.
                            triple_pull_credits 3. triple_reorder_credits.
                            eapply triple_weaken.
                            { eapply implies_trans; [apply star_assoc_l|].
                              eapply implies_trans; [apply star_assoc_l|].
                              apply star_implies_mono; [|prove_implies_refl].
                              eapply implies_trans; [apply star_assoc_r|].
                              apply star_implies_mono; [prove_implies_refl|].
                              apply star_comm. }
                            { prove_implies_refl. }
                            triple_reorder_credits.
                            triple_pull_credits 2. triple_reorder_credits.
                            (*instantiate (cm := 3+ ?[ccm]). instantiate (ccm := ?[cm]).
                            instantiate (cn_t := S ?[ccn_t]). instantiate (ccn_t := ?[cn_t]).*)
                            (*simpl.*)
                            (*lazymatch goal with
                            | [H : heap_time_bound ?n ?C ?t |- _] =>
                              remember t as t_credits eqn:Ht_credits
                            end.
                            erewrite <- (Nat.add_succ_l _ (_*t_credits)),
                              <- Ht_credits, (Nat.add_comm t_credits).
                            repeat erewrite (Nat.add_assoc _ _ t_credits).
                            erewrite (Nat.add_comm _ t_credits).
                            triple_pull_credits (3+t_credits). triple_reorder_credits.
                            triple_pull_credits 3. triple_reorder_credits.
                            triple_pull_credits 2. triple_reorder_credits.*)
                            lazymatch goal with
                            | [|- triple
                                (Val h_decrease_key <* Val ?v <* _ <* _)
                                ($2 <*> ($1 <*> ($ _ <*> ($1 <*> ($ ?pot <*> _))))) _] =>
                              eapply triple_weaken with
                                (P := ($2 <*> ($1 <*> ($1 <*> ($ pot <*>
                                  (is_heap n _ _ _ _ v))))) <*> ($ _ <*> $ _ <*> _)),
                                triple_frame;
                                [| |revert v]
                            end.
                            { prove_implies_rev. }
                            { intros.
                              eapply implies_trans with
                                (Q := (<exists> c cx p, $c <*> <[c <= p + cx]>) <*>
                                  (<exists> a b c, is_heap n _ a b c _ <*> _) <*> _).
                              { prove_implies_refl. }
                              { apply implies_spec. intros.
                                normalize_star. swap_star_ctx. normalize_star.
                                swap_star_ctx. normalize_star. swap_star_ctx.
                                normalize_star.
                                apply star_assoc. swap_star.
                                revert_implies.
                                eapply implies_trans; [apply star_assoc_l|].
                                eapply implies_trans; [apply star_assoc_l|].
                                eapply implies_trans; [apply star_assoc_l|].
                                eapply implies_trans;
                                  [apply star_implies_mono;
                                    [apply star_comm|prove_implies_refl]|].
                                eapply implies_trans; [apply star_assoc_r|].
                                (*eapply implies_trans; [apply star_comm|].*)
                                (*eapply implies_trans; [apply star_assoc_r|].*)
                                eapply implies_trans;
                                  [apply star_implies_mono;
                                    [prove_implies_refl|apply star_assoc_r]|].
                                eapply implies_trans;
                                  [apply star_implies_mono;
                                    [prove_implies_refl|apply star_assoc_r]|].
                                eapply implies_trans; [apply star_assoc_l|].
                                apply star_implies_mono.
                                { apply implies_spec. intros. eexists.
                                  eapply credits_star_l; try reflexivity.
                                  (*eapply star_implies_mono; eauto; [prove_implies_refl|].
                                  eapply credits_star_l; reflexivity.*)
                                  eassumption. }
                                { eapply implies_trans; [apply star_assoc|].
                                  eapply implies_trans; [apply star_comm|].
                                  eapply implies_trans; [apply star_assoc|].
                                  eapply implies_trans; [apply star_comm|].
                                  eapply implies_trans; [apply star_assoc|].
                                  eapply implies_trans; [apply star_assoc|].
                                  apply star_implies_mono; [prove_implies_refl|].
                                  apply implies_spec. intros. do 7 eexists.
                                  conormalize_star. swap_star. apply star_assoc.
                                  eapply star_implies_mono;
                                    [|prove_implies_refl|eassumption].
                                  apply implies_spec. intros.
                                  swap_star. conormalize_star.
                                  eapply star_implies_mono;
                                    [|prove_implies_refl|eassumption].
                                  apply implies_spec. intros. conormalize_star.
                                  eapply star_implies_mono;
                                    [|prove_implies_refl|eassumption].
                                  apply implies_spec. intros. conormalize_star.
                                  swap_star_ctx. conormalize_star.
                                  eapply star_implies_mono;
                                    [|prove_implies_refl|eassumption].
                                  prove_implies. } } }
                            rewrite <- Nat2Z.inj_add.
                            lazymatch goal with
                            | [|-
                              forall a,
                                triple (Val (@?f a) <* (@?e1 a) <* (@?e2 a) <* (@?e3 a))
                                  ($2 <*> (@?P0 a))
                                  (@?Q1 a)
                              ] =>
                              intros a;
                              specialize Hn_ary with
                                (v := f a) (e := e1 a) (es := [e2 a;e3 a]%list)
                                (P := P0 a)
                            end.
                            lazymatch goal with
                            | [H : forall n C P W p h k d c, _ -> _ ->
                                triple_fun_n_ary _ h_decrease_key
                                  (@?Pre n C P W p h k d c) (@?Post n C P W p h k d c)
                              |- triple
                                (Val h_decrease_key <* Val ?h' <* Val (Int (Z.of_nat ?s')) <* Val (Int ?x))
                                ($_ <*> ($_ <*> ($_ <*> ($ ?pot' <*> is_heap ?n' ?C' ?P' ?W' ?pot' ?h')))) _
                              ] =>
                              let d' := constr:(Z.to_nat x) in
                              let c' := constr:(pot') in
                              specialize Hn_ary with
                                (Q1 := Pre n' C' P' W' pot' h' s' d' c')
                                (Q2 := Post n' C' P' W' pot' h' s' d' c');
                              specialize Hspec_h_decrease_key with
                                (n := n') (C := C') (P := P') (W := W') (p := pot') (h := h')
                                (k := s') (d := d') (c := c')
                            end.
                            specialize (Hweaken _ h_decrease_key 2).
                            simpl in Hn_ary, Hspec_h_decrease_key, Hweaken.
                            eapply triple_weaken, Hn_ary.
                            { prove_implies_refl. }
                            { apply implies_post_spec. intros ? ? ? HQ.
                              normalize_star. swap_star_ctx. normalize_star.
                              solve_star. swap_star. solve_star. swap_star.
                              solve_star.
                              (*{ unfold distance_decrease. (*TODO*) }*)
                              { eapply nat_function_update. eassumption. }
                              { eapply nat_function_update. eassumption. }
                              { swap_star. rewrite Nat.add_0_l. eassumption. } }
                            { admit. (*eapply Hspec_h_decrease_key; unfold empty, not; auto.
                              { lazymatch goal with
                                | [H : (Z.of_nat ?m_cost + Z.of_nat w' < x')%Z,
                                  H' : List.nth x_min ?L None = Some (Int (_ ?m_cost)),
                                  H'' : is_nat_fun_of_val_list ?L ?D
                                  |- _] =>
                                  assert (D x_min = Some m_cost);
                                  [unfold is_nat_fun_of_val_list, fun_of_list in H'';
                                    destruct H'' as (?&H''); apply H''; eassumption|]
                                end.
                                unfold set_sum, set_remove. left. split.
                                { (*apply Dijkstra_invariant_if_D_some.*)
                                  (*lazymatch goal with
                                  | [H : is_elem_weighted_unique_list _ _ (?L++_)%list
                                    |- _] =>
                                    unfold is_elem_weighted_unique_list in H;
                                    rewrite List.map_app in H;
                                    destruct H as (?&H%List.NoDup_remove_2)
                                  end.*)
                                  lazymatch goal with
                                  | [H : (_ = empty /\ _ = set_sum empty _) \/
                                      (_ src /\ _ = neighbourhood _ _)
                                      |- _] =>
                                    destruct H as [(->&->)|(?&->)]
                                  end.
                                  { exfalso.
                                    lazymatch goal with
                                    | [H : is_elem_weighted_unique_list _ _ (?L++_)%list
                                      |- _] =>
                                      unfold is_elem_weighted_unique_list, is_elem_weighted_list in H;
                                      destruct H as (?&?)
                                    end.
                                    unfold min_cost_elem, set_sum, empty, single in Hmincost |- *.
                                    destruct Hmincost as ([[]| ->]&?). } admit. }
                                { intros ->.
                                  lazymatch goal with
                                  | [H : is_elem_weighted_unique_list _ _ (?L++_)%list,
                                    H' : List.In i' (List.map fst ?L)
                                    |- _] =>
                                    unfold is_elem_weighted_unique_list in H;
                                    rewrite List.map_app in H;
                                    destruct H as (?&H%List.NoDup_remove_2);
                                    apply H
                                  end.
                                  simpl. apply List.in_or_app. auto. } }*) }
                            { solve_simple_value. revert_implies. prove_implies_refl. }
                            { solve_simple_value. revert_implies. remember (Int (Z.of_nat i')).
                              prove_implies_refl. }
                            { solve_simple_value. revert_implies.
                              lazymatch goal with
                              | [|- _ ->> _ ?v] => remember v
                              end.
                              prove_implies_refl. }
                            { simpl. apply implies_spec. intros. swap_star. solve_star. swap_star.
                              solve_star. swap_star. solve_star.
                              { repeat f_equal. rewrite Nat2Z.id. reflexivity. }
                              { revert_implies. prove_implies. } }
                      ++++ triple_pull_pure. apply triple_value_implies.
                        apply implies_spec. intros.
                        repeat apply star_assoc_r. swap_star.
                        lazymatch goal with
                        | [H : _ ?c ?m |- _ ?c ?m] =>
                          do 2 eapply star_assoc_l in H;
                          eapply star_implies_mono in H;
                          eauto
                        end.
                        { apply implies_spec. intros. solve_star.
                          eapply credits_star_l; [reflexivity|].
                          eapply star_implies_mono; eauto; [|prove_implies_refl].
                          apply credits_star_l. reflexivity. }
                        apply implies_spec. intros. apply star_pure_l.
                        split; auto. do 7 eexists.
                        lazymatch goal with
                        | [H : (_ <*> (_ <*> array_content ?L ?a)) ?c ?m,
                           Hfun_a : is_nat_fun_of_val_list ?L _,
                           Hfun_b : is_nat_fun_of_val_list _ _
                          |- (_ <*> array_content _ ?a <*> _ <*> _) ?c ?m] =>
                          repeat apply star_assoc_l;
                          apply star_pure_l; split; [exact Hfun_a|];
                          apply star_pure_l; split; [exact Hfun_b|]
                        end.
                        eapply star_implies_mono; [prove_implies_refl| |eassumption].
                        prove_implies.
                  *** triple_reorder_exists. repeat triple_pull_exists.
                    triple_reorder_pure. repeat triple_pull_pure.
                    instantiate (cm2 := S ?[ccm2]). instantiate (ccm2 := ?[cm2]).
                    eapply triple_weaken.
                    { apply star_comm. }
                    { prove_implies_refl. }
                    triple_pull_1_credit.
                    eapply triple_weaken,
                      triple_frame with
                        (H := (_ <-*> _) <*> array_content _ _ <*>
                          is_heap _ _ _ _ _ _ <*> array_content _ _),
                      triple_assign.
                    { prove_implies_rev.
                      eapply implies_trans; [|apply star_comm].
                      prove_implies_rev. }
                    { intros. simpl. prove_implies_rev. apply implies_spec.
                      intros. normalize_star. swap_star_ctx. normalize_star.
                      revert_implies. eapply implies_trans; [apply star_assoc_r|].
                      apply star_implies_mono; [prove_implies_refl|].
                      eapply implies_trans; [|apply star_comm].
                      eapply implies_trans; [apply star_assoc_r|].
                      apply star_implies_mono; [prove_implies_refl|].
                      eapply implies_trans with
                        (Q := (<exists> (Neigh_list_processed : list (nat * nat))
                          (pred : nat -> option nat) (sp st : nat),
                          ?[xx]) <*> _);
                        [prove_implies_refl|].
                      apply implies_spec. intros. normalize_star. do 11 eexists.
                      conormalize_star.
                      eapply star_implies_mono; [|prove_implies_refl|eassumption].
                      apply implies_spec. intros. swap_star_ctx. normalize_star.
                      swap_star_ctx. revert_implies. prove_implies.
                      apply implies_spec. intros. eapply star_implies_mono.
                      { prove_implies_refl. }
                      { apply wand_wand. }
                      apply star_assoc_r.
                      lazymatch goal with
                      | [H : _ ?c ?m |- _ ?c ?m] => exact H
                      end. }
                    ---- solve_simple_value.
                    ---- unfold l_tail_spec in Hspec_l_tail.
                      eapply triple_fun_app.
                      2:{ instantiate (cm2 := S c_l_tail + ?[ccm2]).
                        instantiate (ccm2 := ?[cm2]).
                        rewrite <- (Nat.add_assoc (S c_l_tail)).
                        rewrite <- (Nat.add_assoc (S c_l_tail)).
                        triple_reorder_credits.
                        lazymatch goal with
                        | [|- triple _ ($ S (c_l_tail + ?cr1 + ?cr2) <*> _) _] =>
                          rewrite <- (Nat.add_assoc c_l_tail cr1 cr2)
                        end.
                        rewrite <- (Nat.add_succ_l c_l_tail).
                        triple_pull_credits (S c_l_tail).
                        triple_pull_1_credit.
                        eapply triple_weaken, triple_deref.
                        { prove_implies_rev. }
                        { intros. simpl. prove_implies. }
                        solve_simple_value. }
                      ++++ eapply triple_fun_weaken, triple_fun_frame, Hspec_l_tail.
                        { intros. simpl. prove_implies_rev. }
                        { intros. simpl.
                          eapply implies_trans; [apply star_comm|].
                          prove_implies. apply implies_spec. intros. swap_star_ctx.
                          lazymatch goal with
                          | [H : _ ?c ?m |- _ ?c ?m] =>
                            repeat apply star_assoc_r in H;
                            apply star_pure_l in H as (->&?)
                          end.
                          swap_star. solve_star. swap_star.
                          (* only that part of solve_star works here *)
                          repeat match goal with
                          | [|- ((_ <*> _) <*> _) ?c ?m ] =>
                            apply star_assoc_l; eauto
                          | [|- ((<exists> _, _) <*> _) ?c ?m ] =>
                            apply star_exists_l; eexists; eauto
                          | [|- (<exists> _, _) ?c ?m] => eexists
                          end.
                          (*repeat (apply star_pure_l; split); eauto.*)
                          (*eapply star_implies_mono with
                            (P := <exists> (Nlp : list (nat * nat))
                              (pred : nat -> option nat) (sp st : nat), _ <*> $3).
                          { apply implies_spec. intros. normalize_star.
                           solve_star. apply <- star_exists_l. }
                           solve_star. swap_star.
                          apply star_assoc_l. revert_implies. solve_star.*) all:admit. }
                        (*{ prove_implies_refl. }
                        { apply implies_post_spec. intros. swap_star.
                          apply star_assoc_l.
                          lazymatch goal with
                          | [H : _ ?c ?m |- _ ?c ?m] =>
                            repeat apply star_assoc_r in H;
                            apply star_pure_l in H as (->&?)
                          end.
                           normalize_star. conormalize_star.
                          swap_star_ctx. revert_implies.
                          eapply implies_trans; [apply star_assoc_r|].
                          apply star_implies_mono; [prove_implies_refl|].
                          eapply implies_trans; [apply star_assoc_r|].
                          eapply implies_trans; [|apply star_assoc_l].
                          apply star_implies_mono; [prove_implies_refl|].
                          eapply implies_trans; [|apply star_comm].
                          eapply implies_trans; [apply star_assoc_r|].
                          apply star_implies_mono; [prove_implies_refl|].
                          eapply implies_trans with
                            (Q := (<exists> (Neigh_list_processed : list (nat * nat))
                              (pred : nat -> option nat) (sp st : nat),
                              ?[xx]) <*> _);
                            [prove_implies_refl|].
                          apply implies_spec. intros. normalize_star. do 4 eexists.
                          apply star_assoc_l.
                          eapply star_implies_mono; [|prove_implies_refl|eassumption].
                          apply implies_refl.
                          admit.
                          (*prove_implies_refl.
                           apply H39.
                          lazymatch goal with
                          | [H : _ ?c ?m |- _ ?c ?m] => exact H
                          end.
                          eassumption.
                          eapply star_implies_mono; [|prove_implies_refl|eassumption].
                          conormalize_star.
                          eapply star_implies_mono; [|prove_implies_refl|eassumption].
                          apply implies_spec. intros. swap_star_ctx. normalize_star.
                          swap_star_ctx. revert_implies. prove_implies.
                          eassumption.*) }*)
                        { eassumption. }
                      (*++++ instantiate (cm2 := S c_l_tail + ?[ccm2]).
                        instantiate (ccm2 := ?[cm2]).
                        rewrite <- (Nat.add_assoc (S c_l_tail)).
                        rewrite <- (Nat.add_assoc (S c_l_tail)).
                        triple_reorder_credits.
                        lazymatch goal with
                        | [|- triple _ ($ S (c_l_tail + ?cr1 + ?cr2) <*> _) _] =>
                          rewrite <- (Nat.add_assoc c_l_tail cr1 cr2)
                        end.
                        rewrite <- (Nat.add_succ_l c_l_tail).
                        triple_pull_credits (S c_l_tail).
                        triple_pull_1_credit.
                        eapply triple_weaken, triple_deref.
                        { prove_implies_rev. }
                        { intros. simpl. prove_implies. }
                        solve_simple_value. revert_implies. prove_implies_rev.*)
              --- triple_reorder_exists. repeat triple_pull_exists.
                triple_reorder_pure. repeat triple_pull_pure.
                instantiate (cn_0 := 4+?[ccn_0]). instantiate (ccn_0 := ?[cn_0]).
                triple_reorder_credits. triple_pull_credits 4.
                triple_pull_1_credit.
                eapply triple_weaken, triple_free.
                { prove_implies_rev. }
                { apply implies_post_spec. intros. normalize_star. solve_star.
                  eassumption. }
                solve_simple_value. revert_implies. prove_implies.
                apply implies_spec. intros.
                solve_star;
                  try lazymatch goal with
                  [|- Dijkstra_invariant _ _ _ _ _] => eassumption
                  end;
                  try lazymatch goal with
                  [|- is_nat_fun_of_val_list _ _] => eassumption
                  end;
                  eauto.
                  { admit. }
                  { swap_star. revert_implies.
                    eapply implies_trans.
                    { apply star_implies_mono; [prove_implies_refl|].
                      apply star_implies_mono; [prove_implies_refl|].
                      apply star_implies_mono; [prove_implies_refl|].
                      apply star_implies_mono; [prove_implies_refl|].
                      apply star_implies_mono; [prove_implies_refl|].
                      apply star_implies_mono; [prove_implies_refl|].
                      apply star_implies_mono; [|prove_implies_refl].
                      apply star_implies_mono; [|prove_implies_refl].
                      apply star_implies_mono; [|prove_implies_refl].
                      apply wand_star_r. }
                   { prove_implies_rev. admit. } }
          ++ clear get_neighbours h_insert h_empty h_extract_min h_decrease_key
              l_is_nil l_head l_tail Hspec_get_neighbours Hspec_h_insert
              Hspec_h_empty Hspec_h_extract_min Hspec_h_decrease_key
              Hspec_l_is_nil Hspec_l_head Hspec_l_tail.
            triple_reorder_exists. repeat triple_pull_exists.
            triple_reorder_pure. repeat triple_pull_pure.
            triple_reorder_credits.
            rewrite Bool.negb_false_iff, Nat.eqb_eq in *.
            erewrite (Nat.add_comm x), <- (Nat.add_assoc _ x).
            edestruct Hh_free_cost with (s := 0) as (c1&c&Hcost_eq&?);
              eauto.
            rewrite Nat.add_0_r in Hcost_eq.
            instantiate (c0 := 2). instantiate (cn0 := c_h_free).
            rewrite Hn, (Nat.mul_succ_r c_h_free),
              (Nat.mul_add_distr_r (c_h_free*n') c_h_free), <- Hn.
            simpl. triple_pull_1_credit.
            eapply triple_seq.
            ** unfold h_free_spec in Hspec_h_free.
              erewrite (Nat.add_comm (c_h_free * n' * _)).
              lazymatch goal with
              | [|- triple _ ((_ <*> (_ <*> (_ <*> (_ <*>
                  ($ (?c1 + ?c2) <*> _)))))) _] =>
                triple_reorder (@sa_credits string (c1+c2));
                triple_pull_credits c1
              end.
              triple_reorder_credits. rewrite <- Hcost_eq, (Nat.add_comm c1).
              triple_pull_credits c. triple_reorder_credits.
              lazymatch goal with
              | [|- triple _ ($ ?c <*> _) _] =>
                eapply triple_weaken, triple_frame
                  with (P := $c <*> is_heap _ _ _ _ _ _)
              end.
              { prove_implies_rev. }
              { intros. simpl. apply star_assoc_r. }
              eapply triple_fun_app.
              --- subst. eapply Hspec_h_free; eauto.
              --- solve_simple_value. apply star_comm. eassumption.
            ** triple_reorder_exists. repeat triple_pull_exists.
              solve_simple_value. swap_star.
              lazymatch goal with
              | [|- ((<exists> _ _ _ _,
                <[RecV [?a1;?a2] = _]> <*> _ <*> _ <*> _ <*> _) <*> _) _ _] =>
                assert (exists l1 l2, a1 = Lab l1 /\ a2 = Lab l2)
              end.
              { admit. }
              solve_star.
               Search array_content Lab.
           admit.
Admitted.
