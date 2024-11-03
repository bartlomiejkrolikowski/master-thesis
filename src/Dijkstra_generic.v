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
Require Import src.Dijkstra_aux.
Require Import src.Dijkstra_aux_graphs.

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
  forall {V} (n C : nat) (P Q : nat -> Prop) (W : nat -> option nat)
    (* P - processed vertices *)
    (* Q - vertices in heap *)
    (* potential - the upper bound on the number of credits
        required to extract all the elements *)
    (potential : nat),
    Value V -> StateAssertion V.

Axiom equiv_set_heap :
  forall V n C P Q P' Q' W potential (h : Value V),
    set_equiv P P' ->
    set_equiv Q Q' ->
    is_heap n C P Q W potential h ->>
      is_heap n C P' Q' W potential h.

Parameter heap_time_bound :
  forall (n C t : nat), Prop.

Axiom heap_time_bound_ge_1 :
  forall n C t, heap_time_bound n C t -> t >= 1.

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
          (is_heap n C empty empty (fun _ => None) 0)
      ]>).

Definition set_value_at (W : nat -> option nat) (x y n : nat) : option nat :=
  if n =? x then Some y else W n.

(*Parameter h_insert_cost : forall (n C c : nat), Prop.*)

Definition h_insert_spec {V} (h_insert : Value V) : Prop :=
  forall n C (P Q : nat -> Prop) (W : nat -> option nat) (p s k d c t : nat),
    (*h_insert_cost n C c ->*)
    c = t ->
    heap_time_bound n C t ->
    is_set_size Q s ->
    s < n -> (* there is still space in heap *)
    k < n -> (* we need to be able to use k as an index in the array of locations *)
    (forall v, P v -> le (W v) (Some d)) ->
      (* we can't insert labels smaller than we extracted *)
    d <= n*C -> (* we can't insert labels grater than n*C *)
    ~ Q k ->
    triple_fun_n_ary 2 h_insert
      (fun h v2 v3 => $c <*> <[v2 = Int (Z.of_nat k)]> <*>
        <[v3 = Int (Z.of_nat d)]> <*> is_heap n C P Q W p h)
      (fun h v2 v3 res => (<exists> c', $c') <*> <[res = U_val]> <*>
        <exists> p', <[p' < p + t]> <*>
          is_heap n C P (set_sum Q (single k)) (set_value_at W k d) p' h).

Parameter h_empty_cost : forall (c : nat), Prop.

Axiom h_empty_cost_exists : exists c, h_empty_cost c.

Definition h_empty_spec {V} (h_empty : Value V) : Prop :=
  forall n C (P Q : nat -> Prop) (W : nat -> option nat) h s c p,
    h_empty_cost c ->
    is_set_size Q s ->
    triple_fun h_empty
      (fun v => $c <*> <[v = h]> <*> is_heap n C P Q W p h)
      (fun v => <[v = Bool (s =? 0)]> <*> is_heap n C P Q W p h).

Definition unset_value_at (W : nat -> option nat) (x n : nat) : option nat :=
  if n =? x then None else W n.

Definition h_extract_min_spec {V} (h_extract_min : Value V) : Prop :=
  forall n C (P Q : nat -> Prop) (W : nat -> option nat) p h k d c,
    c = p ->
    min_cost_elem Q W k ->
    W k = Some d ->
    triple_fun h_extract_min
      (fun v => $c <*> <[v = h]> <*> is_heap n C P Q W p h)
      (fun v => <exists> c' cx p', $c' <*> <[c' = p' + cx]> <*>
        <[v = pair2Value nat2value nat2value (k,d)]> <*>
        is_heap n C (add_single P k) (set_remove Q k) W p' h).

Definition h_decrease_key_spec {V} (h_decrease_key : Value V) : Prop :=
  forall n C (P Q : nat -> Prop) (W : nat -> option nat) p h k d c,
  c = p ->
  le (Some d) (W k) -> (* we decrease the label *)
  (forall v, P v -> le (W v) (Some d)) ->
    (* we can't decrease labels below what we extracted *)
  Q k ->
  triple_fun_n_ary 2 h_decrease_key
    (fun v1 v2 v3 => $1 <*> $c <*> <[v1 = h]> <*> <[v2 = Int (Z.of_nat k)]> <*>
      <[v3 = Int (Z.of_nat d)]> <*> is_heap n C P Q W p h)
    (fun v1 v2 v3 res => <exists> c' cx p', $c' <*> <[c' = p' + cx]> <*>
      <[res = U_val]> <*> is_heap n C P Q (set_value_at W k d) p' h).

Parameter h_free_cost : forall (n C s c : nat), Prop.

Definition h_free_spec {V} (h_free : Value V) : Prop :=
  forall n C (P Q : nat -> Prop) (W : nat -> option nat) s c p,
  is_set_size Q s ->
  h_free_cost n C s c ->
  triple_fun h_free
    (is_heap n C P Q W p <*>+ $c)
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

(* the main theorem *)

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
  (forall x y, W g x y >= 0) ->
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
          is_heap _ _ _ _ _ _ _ <*> array_content _ _)), triple_frame.
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
            is_heap _ _ _ _ _ _ _ <*> array_content _ _)), triple_frame.
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
                (is_heap n _ _ _ _ _ v)))) <*> ($ _ <*> $ _ <*> _)),
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
          | [H : forall n C P Q W p s k d c t, _ -> _ -> _ -> _ -> _ -> _ -> _ -> _ ->
              triple_fun_n_ary _ h_insert
                (@?Pre n C P Q W p k d c) (@?Post n C P Q W p k d t)
            |- triple
              (Val h_insert <* Val ?h <* Val (Int (Z.of_nat ?s')) <* Val (Int ?x))
              ($_ <*> ($_ <*> ($ ?t' <*> is_heap ?n' ?C' ?P' ?Q' ?W' ?p' ?h))) _
            ] =>
            let d' := constr:(Z.to_nat x) in
            let c' := constr:(t') in
            specialize Hn_ary with
              (Q1 := Pre n' C' P' Q' W' p' s' d' c')
              (Q2 := Post n' C' P' Q' W' p' s' d' t');
            specialize Hspec_h_insert with
              (n := n') (C := C') (P := P') (Q := Q') (W := W') (p := p')
              (k := s') (d := d') (c := t') (t := t')
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
            { lia. }
            { eapply init_range_lt_size; eauto. subst n. eassumption. }
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
            apply valid_initial with (g := g) in Hinitial;
              auto using Nat.eq_decidable.
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
            instantiate (cn := ?[cn1] + ?[cn2]).
            lazymatch goal with
            | [|- triple _
                ($2 <*> ($ (S (c_h_empty + ?c0 + (?cm * m +
                  (_ + (_ + (?cn1+?cn2)*n*?t))))) <*>
                  (is_weighted_graph ?g ?vg <*>
                    array_content _ ?a_pred <*> array_content _ ?a_D <*>
                    is_heap ?n' ?C ?P0 ?Q0 _ ?pot ?h)))
                (fun res => <[@?Q' res]> <*> _)
              ] =>
              let pre :=
                constr:($2 <*> ((<exists> D_list pred_list P Q D pred sv sv' se pot',
                <[(P = empty /\ Q = Q0) \/ (P src /\ Q = neighbourhood g P)]> <*>
                <[is_subset P (V g) /\ is_subset Q (V g)]> <*>
                <[is_set_size P sv /\ is_set_size Q sv']> <*>
                <[is_set_size (uncurry (E (induced_subgraph_with_edge P g))) se]> <*>
                <[sv + sv' <= n]> <*>
                <[List.length D_list = n /\ List.length pred_list = n]> <*>
                <[is_nat_fun_of_val_list D_list D /\
                  is_nat_fun_of_val_list pred_list pred]> <*>
                <[Dijkstra_invariant D pred P src g]> <*>
                $ (S (c_h_empty + pot' + c0 +
                  (cm*(m-se) + cn1*(n-sv)*t + cn2*(n-sv-sv')*t))) <*>
                is_weighted_graph g vg <*> array_content pred_list a_pred <*>
                array_content D_list a_D <*> is_heap n' C P Q D pot' h) <*>
                (<exists> c, $c)))
              in
              let post :=
                constr:(fun b => (<exists> D_list pred_list P Q D pred sv sv' se pot',
                <[negb (sv' =? 0) = b]> <*>
                <[(P = empty /\ Q = Q0) \/ (P src /\ Q = neighbourhood g P)]> <*>
                <[is_subset P (V g) /\ is_subset Q (V g)]> <*>
                <[is_set_size P sv /\ is_set_size Q sv']> <*>
                <[is_set_size (uncurry (E (induced_subgraph_with_edge P g))) se]> <*>
                <[sv + sv' <= n]> <*>
                <[List.length D_list = n /\ List.length pred_list = n]> <*>
                <[is_nat_fun_of_val_list D_list D /\
                  is_nat_fun_of_val_list pred_list pred]> <*>
                <[Dijkstra_invariant D pred P src g]> <*>
                $ (pot' + c0 + (cm*(m-se) + cn1*(n-sv)*t + cn2*(n-sv-sv')*t)) <*>
                is_weighted_graph g vg <*> array_content pred_list a_pred <*>
                array_content D_list a_D <*> is_heap n' C P Q D pot' h) <*>
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
                | [|- $ (S (?c0 + (?n1 + (?k1 + (?k2 + (?t1+?t1')*n*?t2))))) ->> _] =>
                  apply credits_star_r with
                    (c1 := k1 + k2 + t1'*t2 - potential)
                    (c2 := (S (potential + c0 + (n1 + t1*n*t2 + t1'*(n-1)*t2))));
                    lia
                end|prove_implies_refl].
              normalize_star. swap_star_ctx. eapply star_implies_mono; eauto.
              { clear_state_assertions. apply implies_spec. intros.
                eexists D_list, pred_list, empty, (set_sum _ _), D, pred, 0, 1, 0.
                solve_star; split_all.
                { unfold is_subset, empty. tauto. }
                { unfold is_subset, empty, set_sum, single. intros ? [[]|<-].
                  assumption. }
                { apply empty_set_size. }
                { apply equiv_set_size with (single src), single_set_size.
                  unfold set_equiv, empty, set_sum. tauto. }
                { apply equiv_set_size with empty.
                  { unfold set_equiv. intros []. simpl. unfold empty, set_sum2.
                    tauto. }
                  { apply empty_set_size. } }
                { lia. }
                { subst D_list. rewrite List.app_length. simpl.
                  repeat rewrite List.repeat_length. lia. }
                { subst pred_list. rewrite List.repeat_length. reflexivity. }
                { do 2 rewrite Nat.sub_0_r.
                  eapply star_implies_mono; eauto; prove_implies.
                  rewrite (Nat.add_assoc potential), (Nat.add_comm potential).
                  subst potential. prove_implies. } }
              { apply implies_spec. intros. solve_star. eassumption. } }
            { intros. prove_implies. apply star_comm. }
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
                  repeat lazymatch goal with
                  | [H : _ /\ _ |- _] => destruct H
                  end.
                  lazymatch goal with
                  | [
                    H0 : is_set_size ?P' ?s1,
                    H1 : is_set_size ?P' ?s2,
                    H2 : (is_heap _ _ _ ?P' _ _ _ <*> _) _ _ |- _
                  ] =>
                    specialize (is_set_size_unique _ _ _ _ H0 H1) as ->
                  end.
                  lazymatch goal with
                  | [H : (_ = empty /\ _ = set_sum empty _) \/
                          (_ src /\ _ = neighbourhood _ _) |- _] =>
                    destruct H as [(?&?) | (?&?)]
                  end.
                  { eexists. apply star_pure_l. split; eauto.
                    do 10 (apply star_exists_l; eexists).
                    repeat apply star_assoc_l. apply star_pure_l. split; eauto.
                    apply star_pure_l. split.
                    { left. eauto. }
                    solve_star; split_all;
                      try lazymatch goal with
                      [|- Dijkstra_invariant _ _ _ _ _] => eassumption
                      end;
                      try lazymatch goal with
                      [|- is_nat_fun_of_val_list _ _] => eassumption
                      end;
                      eauto.
                    swap_star_ctx. normalize_star.
                    eapply star_implies_mono;
                      [prove_implies_refl| |eassumption].
                    prove_implies_rev. apply implies_spec.
                    intros. solve_star. eassumption. }
                  { eexists. apply star_pure_l. split; eauto.
                    do 10 (apply star_exists_l; eexists).
                    repeat apply star_assoc_l. apply star_pure_l. split; eauto.
                    apply star_pure_l. split.
                    { right. eauto. }
                    solve_star; split_all;
                      try lazymatch goal with
                      [|- Dijkstra_invariant _ _ _ _ _] => eassumption
                      end;
                      try lazymatch goal with
                      [|- is_nat_fun_of_val_list _ _] => eassumption
                      end;
                      subst; eauto.
                    swap_star_ctx. normalize_star.
                    eapply star_implies_mono;
                      [prove_implies_refl| |eassumption].
                    prove_implies_rev. apply implies_spec.
                    intros. solve_star. eassumption. } }
                { eassumption. }
                { eassumption. }
              }
              { intros.
                repeat lazymatch goal with
                | [H : _ /\ _ |- _] => destruct H
                end.
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
                  eapply decidable_uncurry_eq; unfold Decidable.decidable; lia. } }
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
              triple_reorder_credits. instantiate (cn1 := ?[cn1_0] + ?[cn1_t]).
              rewrite Bool.negb_true_iff, Nat.eqb_neq in *.
              erewrite (Nat.mul_comm _ (n - _)), <- (Nat.sub_add_distr n). rewrite Hn.
              rewrite Nat.sub_succ_l; [|lia]. rewrite <- Hn. simpl "*".
              erewrite (Nat.mul_add_distr_r _ ((n' - _) * _)).
              erewrite (Nat.add_assoc (_ * (m - _))).
              erewrite (Nat.add_comm (_ * (m-_)) _).
              erewrite <- (Nat.add_assoc _ (_ * (m - _))).
              lazymatch goal with
              | [|- triple _ ($ (?c0 + (?c1 + _ + _)) <*> _) _] =>
                rewrite <- (Nat.add_assoc c1), (Nat.add_assoc c0 c1),
                  (Nat.add_comm c0 c1), <- (Nat.add_assoc c1 c0)
              end.
              lazymatch goal with
              | [|- triple _ ($ ((?c1 + ?c2)*?t + _) <*> _) _] =>
                erewrite (Nat.mul_add_distr_r c1 c2 t),
                  <- (Nat.add_assoc (c1*t))
              end.
              erewrite (Nat.mul_comm _ (S _)). simpl "*".
              erewrite <- Nat.add_assoc.
              repeat lazymatch goal with
              | [H : _ /\ _ |- _] => destruct H
              end.
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
                  eauto using decidable_if_finite, Nat.eq_decidable.
                  { subst. unfold min_cost_elem, neighbourhood in Hmincost.
                    destruct Hmincost as ((?&?&?&?%E_closed2)&?). assumption. }
                  { subst. unfold min_cost_elem in Hmincost.
                    destruct Hmincost as (?&?). assumption. } } }
              destruct Hissome.
              instantiate (cn1_0 := S ?[ccn1_0]). instantiate (ccn1_0 := ?[cn1_0]).
              triple_pull_1_credit.
              app_lambda.
              2:{
                unfold h_extract_min_spec in Hspec_h_extract_min.
                lazymatch goal with
                | [|- triple _
                    (_ <*> (_ <*> (_ <*> is_heap n C _ _ _ ?p _))) _] =>
                  rename p into potential'
                end.
                erewrite <- (Nat.add_assoc potential'),
                  (Nat.add_assoc _ potential'), (Nat.add_comm _ potential'),
                  <- (Nat.add_assoc potential'), (Nat.add_assoc _ potential'),
                  (Nat.add_comm _ potential'), <- (Nat.add_assoc potential'),
                  (Nat.add_assoc _ potential'), (Nat.add_comm _ potential'),
                  <- (Nat.add_assoc potential').
                triple_reorder_credits. triple_pull_credits potential'.
                triple_reorder_credits.
                lazymatch goal with
                | [|- triple _
                    (_ <*> (_ <*> (_ <*> (_ <*>
                      is_heap n C ?P' ?Q' ?W' ?p' ?h')))) _] =>
                  specialize Hspec_h_extract_min with
                    (n := n) (C := C) (P := P') (Q := Q') (W := W') (p := p')
                    (h := h')
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
              instantiate (cn1_0 := S (S ?[ccn1_0])). instantiate (ccn1_0 := ?[cn1_0]).
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
              instantiate (cn1_0 := S (S ?[ccn1_0])). instantiate (ccn1_0 := ?[cn1_0]).
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
              instantiate (cn1_0 := 4 + c_neighbours + ?[ccn1_0]).
              instantiate (ccn1_0 := ?[cn1_0]). simpl. triple_pull_1_credit.
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
              instantiate (cn1_0 := S ?[ccn1_0]). instantiate (ccn1_0 := ?[cn1_0]).
              triple_pull_1_credit. eapply triple_seq.
              --- instantiate (cn1_0 := 3 + ?[ccn1_0]). instantiate (ccn1_0 := ?[cn1_0]).
                triple_reorder_credits.
                rewrite <- (Nat.sub_succ n'). rewrite <- Hn.
                erewrite (Nat.mul_succ_r (n-_)), (Nat.mul_add_distr_r ((n-_)*_)).
                lazymatch goal with
                | [|- triple _
                    ($ S (S (S (?cn1_0 + (?c0_n + (?c_t + (?c0 + (?cm_m + (?cr + ?c_nt) + ?cn2_t))))))) <*>
                      ($ ?n1 <*> ($ (?pot + ?n2) <*>
                      (((_ <*> is_heap _ _ _ _ _ ?pot _) <*> _) <*> _)))) _] =>
                  eapply triple_weaken with
                    (P := ($ S (S (S (cn1_0 + (cm_m + c_t (*+ c_nt*) + cn2_t)))) <*> ($ pot <*> _)) <*>
                      ($ n1 <*> $ n2 <*> $ (c0_n + c0 + cr + c_nt)))
                    (Q := (fun res => <[res = U_val]> <*>
                      ((<exists> c, $c) <*> _)) <*>+
                      ($ n1 <*> $ n2 <*> $ (c0_n + c0 + cr + c_nt))),
                    triple_frame
                end.
                { eapply implies_trans.
                  { apply star_implies_mono; [|prove_implies_refl].
                    lazymatch goal with
                    | [|- $ S (S (S (?cn1_0 + (?c0_n + (?c_t + (?c0 + (?cm_m + (?cr + ?c_nt) + ?cn2_t))))))) ->> _] =>
                      apply credits_star_r with
                        (c1 := S (S (S (cn1_0 + (cm_m + c_t (*+ c_nt*) + cn2_t))))) (c2 := c0_n + c0 + cr + c_nt)
                    end.
                    lia. }
                  { prove_implies_rev. eapply implies_trans; [|apply star_comm].
                    prove_implies. eapply implies_trans; [|apply star_assoc_r].
                    apply star_implies_mono; [|prove_implies_refl].
                    apply credits_star_r. lia. } }
                { intros. prove_implies. }
                triple_reorder_credits. triple_pull_credits 2.
                triple_reorder_credits.
                instantiate (cn1_0 := S c_is_nil + ?[ccn1_0]).
                instantiate (ccn1_0 := ?[cn1_0]).
                lazymatch goal with
                | [H : potential < _ |- _] => clear potential H Hpot
                end.
                lazymatch goal with
                | [H : Dijkstra_invariant ?D_init ?pred_init ?P_init src g
                  |- triple _
                    ($2 <*> ($ (S (S c_is_nil+?cn1_0+(?cm*(m-?km)+?cn_t+?cn*(n-(?kn+?kn'))*?t))) <*>
                      ($ ?pot' <*>
                      ((((array_content _ ?a_pred <*> array_content _ ?a_D) <*>
                        is_heap ?n' ?C ?P0 ?Q0 ?D_init ?pot' ?h) <*>
                        (is_list ?L ?l' <*>
                        (is_list ?L ?l' <-*> is_weighted_graph ?g ?vg))) <*>
                        <(?p_l :== ?l')>))))
                    (fun res => <[@?Q' res]> <*> _)
                  ] =>
                  let pre :=
                    constr:($2 <*>
                    ((<exists> Neigh_list_processed Neigh_list_todo (*P*) Q
                      D_list pred_list D pred D' pred' sp st sv' l pot,
                    <[is_elem_weighted_unique_list
                        (neighbours g x_min)
                        (W g x_min)
                        (Neigh_list_processed ++ Neigh_list_todo)%list]> <*>
                    <[List.length Neigh_list_processed = sp /\
                      List.length Neigh_list_todo = st /\
                      List.length D_list = n /\ List.length pred_list = n]> <*>
                    <[(forall x, List.In x (List.map fst Neigh_list_todo) ->
                        D x = D_init x) /\
                      (forall x, List.In x (List.map fst Neigh_list_todo) ->
                        pred x = pred_init x) /\
                      (forall x, List.In x (List.map fst Neigh_list_processed) ->
                        D x = D' x) /\
                      (forall x, List.In x (List.map fst Neigh_list_processed) ->
                        pred x = pred' x) /\
                      (forall x, ~ List.In x (List.map fst
                        (Neigh_list_processed ++ Neigh_list_todo)) ->
                        D x = D' x) /\
                      (forall x, ~ List.In x (List.map fst
                        (Neigh_list_processed ++ Neigh_list_todo)) ->
                        pred x = pred' x) /\
                      distance_decrease g x_min D_init D' pred_init pred' (*/\
                      forall x y, P_init x -> Q y -> le (D x) (D y)*)]> <*>
                    <[is_nat_fun_of_val_list D_list D /\
                      is_nat_fun_of_val_list pred_list pred]> <*>
                    <[set_equiv Q (set_sum Q0 (fun x => ~ P_init x /\
                      List.In x (List.map fst Neigh_list_processed)))]> <*>
                    <[km + sp + st <= m /\ is_subset Q (V g) /\
                      is_set_size Q sv']> <*>
(*                    <[is_set_size Q0 kn]> <*>
                    <[is_set_size (uncurry (E (induced_subgraph Q0 g))) km]> <*>
                    <[sv < n]> <*>
                    <[Dijkstra_invariant D pred P src g]> <*>*)
                    $ (S (S c_is_nil + cn1_0 +
                      (cm*((m-km)-sp) + cn_t + cn*(n-((kn+1)+sv'))*t))) <*>
                    $ pot <*>
                    is_list (nat_pairs2values Neigh_list_todo) l <*>
                    (is_list (nat_pairs2values Neigh_list_todo) l <-*>
                      is_weighted_graph g vg) <*>
                    array_content pred_list a_pred <*>
                    array_content D_list a_D <*>
                    is_heap n' C (add_single P_init x_min) Q D pot h <*>
                    <(p_l :== l)>) <*>
                    (<exists> c, $c)))
                  in
                  let post :=
                    constr:(fun b =>
                    (<exists> l Neigh_list_processed Neigh_list_todo (*P*) Q
                      D_list pred_list D pred D' pred' sp st sv' pot,
                    <[negb (st =? 0) = b]> <*>
                    <[is_elem_weighted_unique_list
                        (neighbours g x_min)
                        (W g x_min)
                        (Neigh_list_processed ++ Neigh_list_todo)%list]> <*>
                    <[List.length Neigh_list_processed = sp /\
                      List.length Neigh_list_todo = st /\
                      List.length D_list = n /\ List.length pred_list = n]> <*>
                    <[(forall x, List.In x (List.map fst Neigh_list_todo) ->
                        D x = D_init x) /\
                      (forall x, List.In x (List.map fst Neigh_list_todo) ->
                        pred x = pred_init x) /\
                      (forall x, List.In x (List.map fst Neigh_list_processed) ->
                        D x = D' x) /\
                      (forall x, List.In x (List.map fst Neigh_list_processed) ->
                        pred x = pred' x) /\
                      (forall x, ~ List.In x (List.map fst
                        (Neigh_list_processed ++ Neigh_list_todo)) ->
                        D x = D' x) /\
                      (forall x, ~ List.In x (List.map fst
                        (Neigh_list_processed ++ Neigh_list_todo)) ->
                        pred x = pred' x) /\
                      distance_decrease g x_min D_init D' pred_init pred' (*/\
                      forall x y, P_init x -> Q y -> le (D x) (D y)*)]> <*>
                    <[is_nat_fun_of_val_list D_list D /\
                      is_nat_fun_of_val_list pred_list pred]> <*>
                    <[set_equiv Q (set_sum Q0 (fun x => ~ P_init x /\
                      List.In x (List.map fst Neigh_list_processed)))]> <*>
                    <[km + sp + st <= m /\ is_subset Q (V g) /\
                      is_set_size Q sv']> <*>
                    $ (cn1_0 + (cm*((m-km)-sp) + cn_t + cn*(n-((kn+1)+sv'))*t)) <*>
                    $ pot <*>
                    is_list (nat_pairs2values Neigh_list_todo) l <*>
                    (is_list (nat_pairs2values Neigh_list_todo) l <-*>
                      is_weighted_graph g vg) <*>
                    array_content pred_list a_pred <*>
                    array_content D_list a_D <*>
                    is_heap n' C (add_single P_init x_min) Q D pot h <*>
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
                      _ : _ = empty /\ ?Q = set_sum _ _ \/
                        _ src /\ ?Q = neighbourhood _ _,
                      Hsize : is_set_size ?Q ?s,
                      Hinv : Dijkstra_invariant ?D ?pred _ _ _,
                      Hpre : (_ <*> (_ <*> (array_content ?pred_list _ <*>
                        array_content ?D_list _ <*> _ <*> _ <*> <(_ :== ?l)>))) _ _
                      |- _] =>
                      let D'pred' :=
                        constr:(fun2pair (nat_decrease_distance x_min L D pred)) in
                      eexists nil, L, _, D_list, pred_list, D, pred,
                        (fst D'pred'), (snd D'pred'), 0, _, (s-1), l
                    end.
                    solve_star.
                    { simpl. split_all; try tauto.
                      { clear.
                        lazymatch goal with
                        | [|- forall _,
                          _ -> ?D _ = fst (nat_decrease_distance _ ?L ?D _ _)] =>
                          rename D into D';
                          induction L as [|(v&w) L' IHL]; simpl; intros u Hnin
                        end.
                        { destruct (D' x_min); simpl; reflexivity. }
                        { destruct (D' x_min); simpl.
                          { destruct Nat.eqb_spec with u v as [-> | ?].
                            { tauto. }
                            { auto. } }
                          { reflexivity. } } }
                      { clear.
                        lazymatch goal with
                        | [|- forall _,
                          _ -> ?pred _ = snd (nat_decrease_distance _ ?L ?D ?pred _)] =>
                          rename D into D'; rename pred into pred';
                          induction L as [|(v&w) L' IHL]; simpl; intros u Hnin
                        end.
                        { destruct (D' x_min); simpl; reflexivity. }
                        { destruct (D' x_min); simpl.
                          { destruct Nat.eqb_spec with u v as [-> | ?].
                            { tauto. }
                            { auto. } }
                          { reflexivity. } } }
                      { eapply distance_decrease_nat_decrease_distance; eauto.
                        { lazymatch goal with
                          | [H : is_nat_fun_of_val_list ?L ?D,
                            H' : List.nth x_min ?L None = _
                            |- ?D x_min = _] =>
                            unfold is_nat_fun_of_val_list, fun_of_list in H;
                            destruct H as (?&Hfun)
                          end.
                          apply Hfun. eassumption. } } }
                    { lazymatch goal with
                      | [H : (_<*>(_<*>(_<*>is_heap _ _ ?P ?Q _ _ _<*>_<*>_))) _ _
                        |- set_equiv ?Q' _] =>
                        unify Q Q'
                      end.
                      unfold set_equiv, set_sum. simpl. clear. tauto. }
                    { split_all.
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
                            apply decidable_uncurry_eq;
                              unfold Decidable.decidable; lia. }
                          { apply disjoint_sum_size.
                            { unfold are_disjoint_sets, uncurry, cross, single,
                                neighbours, set_sum2.
                              intros (a&b) ([(?&?&?)|(?&?&?)]&<-&?).
                              { lazymatch goal with
                                | [H : _ = empty /\ _ = _ \/
                                  (_ src /\_ = neighbourhood _ _) |- _] =>
                                  destruct H as [(->&?)| (?&->)]
                                end.
                                { unfold empty in *. assumption. }
                                { unfold min_cost_elem in Hmincost.
                                  unfold neighbourhood in *. tauto. } }
                              { lazymatch goal with
                                | [H : _ = empty /\ _ = _ \/
                                  (_ src /\_ = neighbourhood _ _) |- _] =>
                                  destruct H as [(->&?)| (?&->)]
                                end.
                                { unfold empty in *. assumption. }
                                { unfold min_cost_elem in Hmincost.
                                  unfold neighbourhood in *. tauto. } } }
                            { eassumption. }
                            { apply cross_size; eauto using single_set_size. } } }
                        { apply disjoint_sum_size.
                          { unfold are_disjoint_sets, uncurry, cross, single, neighbours.
                            intros (a&b) ([(?&?&?)|(?&?&?)]&<-&?).
                            { lazymatch goal with
                              | [H : _ = empty /\ _ = _ \/
                                (_ src /\ _ = neighbourhood _ _) |- _] =>
                                destruct H as [(->&?)| (?&->)]
                              end.
                              { unfold empty in *. assumption. }
                              { unfold min_cost_elem in Hmincost.
                                unfold neighbourhood in *. tauto. } }
                            { lazymatch goal with
                              | [H : _ = empty /\ _ = _ \/
                                (_ src /\ _ = neighbourhood _ _) |- _] =>
                                destruct H as [(->&?)| (?&->)]
                              end.
                              { unfold empty in *. assumption. }
                              { unfold min_cost_elem in Hmincost.
                                unfold neighbourhood in *. tauto. } } }
                          { eassumption. }
                          { rewrite <- Nat.mul_1_l.
                            apply cross_size; eauto using single_set_size. } }
                        { unfold is_subset, uncurry, cross, set_sum, set_sum2,
                            single, neighbours.
                          intros [] [[(?&?&?)|(?&?&?)]|(->&?)]; auto. } }
                      { simpl. unfold is_subset in *. unfold set_sum, set_remove.
                        firstorder. }
                      { apply set_remove_size_decr; auto using Nat.eq_decidable.
                        unfold min_cost_elem in Hmincost. revert Hmincost. clear.
                        tauto. } }
                    { erewrite Nat.sub_0_r, <- (Nat.add_assoc _ 1 (_ - 1)),
                        (Nat.add_comm 1 (_ - 1)), Nat.sub_add; [|lia].
                      eapply star_implies_mono; [prove_implies_refl| |eassumption].
                      simpl. prove_implies_rev. } }
                  { apply implies_spec. intros. exists 0. assumption. } }
                { intros. prove_implies. apply star_comm. }
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
                      eapply implies_trans; [apply star_comm|].
                      apply star_implies_mono.
                      { apply implies_spec. intros. do 6 eexists.
                        repeat lazymatch goal with
                        | [H : _ /\ _ |- _] => destruct H
                        end.
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
                          | [H : List.length ?L' = ?l
                            |- (?x =? 0) = is_nil_b (nat_pairs2values ?L')] =>
                            unify x (List.length L'); destruct L'; simpl; reflexivity
                          end. }
                        { eassumption. }
                        6:{ swap_star_ctx. normalize_star. swap_star_ctx.
                          normalize_star. swap_star_ctx. normalize_star.
                          eapply star_implies_mono; try eassumption.
                          { prove_implies_refl. }
                          { prove_implies. }
                        }
                        { auto. }
                        { eauto 10. }
                        { auto. }
                        { assumption. }
                        { subst. auto. } }
                      { apply implies_spec. intros. solve_star. eassumption. } } }
                +++ clear Hlen1 Hlen2.
                  triple_reorder_exists. repeat triple_pull_exists.
                  triple_reorder_pure. repeat triple_pull_pure.
                  rewrite Bool.negb_true_iff, Nat.eqb_neq in *.
                  destruct m as [|m'] eqn:Hm; [lia|].
                  rewrite Nat.sub_succ_l, Nat.sub_succ_l, Nat.mul_succ_r; try lia.
                  rewrite <- (Nat.add_assoc (_ * (m' - _ - _))),
                    <- (Nat.add_assoc (_ * (m' - _ - _))),
                    (Nat.add_assoc _ (_ * (m' - _ - _))),
                    (Nat.add_assoc (_+(_ * (m' - _ - _)))),
                    (Nat.add_comm (_+_ * (m' - _ - _))),
                    (Nat.mul_comm _ (m' - _ - _)),
                    <- (Nat.add_assoc _ (_ + (m' - _ - _)*_)).
                  repeat lazymatch goal with
                  | [H : _ /\ _ |- _] => destruct H
                  end.
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
                  instantiate (cn1_t := ?[ccn1_t] + ?[cn1_t2]).
                  instantiate (ccn1_t := ?[cn1_t]).
                  lazymatch goal with
                  | [Hpred : is_nat_fun_of_val_list ?pred_list ?pred,
                     HD : is_nat_fun_of_val_list ?D_list ?D,
                     HeqD_list : ?D_list = _ ?DL,
                     HeqDL : ?DL = (?L1 ++ ?t::?L2)%list,
                     Hmatch_D : forall _,
                        List.In _ (List.map fst (_::?Neigh_list_todo)) ->
                        ?D _ = ?D_init _,
                     Hmatch_pred : forall _,
                        List.In _ (List.map fst (_::?Neigh_list_todo)) ->
                        ?pred _ = ?pred_init _,
                     Hlist : is_elem_weighted_unique_list _ _
                        (?Neigh_list_processed ++ (i',w')::?Neigh_list_todo),
                     HDij_inv : Dijkstra_invariant ?D_init ?pred_init ?P_init src g
                    |- triple _
                      ($(S ?cm + ?cm2 + (?cn1_t + ?cn1_t2)*?t' + (?cr + ?cr2 + ?cr3)) <*>
                        ($?pot <*> ($?c2 <*> (?P1 <*> ?P2 <*>
                        array_content ?pred_list ?a_pred <*>
                        array_content (?f1 ?L1 ++ Some (Int ?t):: ?f2 ?L2) ?a_D <*>
                        is_heap ?n ?C ?Pr ?H ?W ?pot ?h <*>
                        ?P3))))
                      _] =>
                    assert (S cm + cm2 + (cn1_t + cn1_t2)*t' + (cr + cr2 + cr3)
                      = S cm + cn1_t*t' + (cm2 + cr + cr2 + cr3 + cn1_t2*t'))
                      as -> by lia;
                    triple_pull_credits (S cm + cn1_t*t');
                    triple_pull_1_credit;
                    eapply triple_seq with
                      (Q1 :=
                        ((<exists> D' pred' D'' pred'' D_list' pred_list' (*Pr'*) H' (*W*) sv' pot' c3,
                        <[is_nat_fun_of_val_list D_list' D' /\
                          is_nat_fun_of_val_list pred_list' pred']> <*>
                        <[List.length D_list' = n /\ List.length pred_list' = n]> <*>
                        <[(forall x, List.In x (List.map fst Neigh_list_todo) ->
                            D' x = D_init x) /\
                          (forall x, List.In x (List.map fst Neigh_list_todo) ->
                            pred' x = pred_init x) /\
                          (forall x, List.In x
                            (List.map fst (Neigh_list_processed ++ [(i',w')])) ->
                            D' x = D'' x) /\
                          (forall x, List.In x
                            (List.map fst (Neigh_list_processed ++ [(i',w')])) ->
                            pred' x = pred'' x) /\
                          (forall x, ~ List.In x (List.map fst
                            (Neigh_list_processed ++ (i',w')::Neigh_list_todo)) ->
                            D' x = D'' x) /\
                          (forall x, ~ List.In x (List.map fst
                            (Neigh_list_processed ++ (i',w')::Neigh_list_todo)) ->
                            pred' x = pred'' x) /\
                          distance_decrease g x_min D_init D'' pred_init pred'' (*/\
                          forall x y, Pr x -> H' y -> le (D' x) (D' y)*)]> <*>
                        <[set_equiv H' (set_sum (set_remove _ x_min)
                          (fun x => ~ P_init x /\ List.In x
                          (List.map fst (Neigh_list_processed ++ [(i',w')]))))]> <*>
                        <[is_subset H' (V g) /\ is_set_size H' sv' /\
                          (set_sum P_init H i' -> c3 = 2*t') /\ (* credits after other than insert *)
                          (~ set_sum P_init H i' -> c3 = 0)]> <*> (* credits after insert *)
                        $pot' <*> $c2 <*> $c3 <*> P1 <*> P2 <*> P3 <*>
                        array_content D_list' a_D <*>
                        is_heap n C Pr H' (*W*) D' pot' h <*>
                        array_content pred_list' a_pred) <*>
                        <exists> c, $c) <*> $(cm2 + cr + cr2 + cr3 + cn1_t2*t'))
                  end.
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
                          is_heap ?n ?C ?Pr ?H ?W ?pot ?h <*> ?P2 <*> ?P3 <*>
                          array_content (?L1'++?ox'::?L2') ?a_pred)))))))
                        _] =>
                      let P := constr:($c0 <*> ($c1 <*> ($pot <*> ($c2 <*>
                        (P1 <*> array_content (L1++ox::L2) a_D <*>
                        is_heap n C Pr H W pot h <*> P2 <*> P3 <*>
                        array_content (L1'++ox'::L2') a_pred)))))
                      in
                      eapply triple_if with
                        (Q1 := fun b : bool => <[(x' <? 0)%Z = b]> <*> P)
                    end.
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
                      simpl. triple_pull_1_credit. eapply triple_seq.
                      ++++
                        pose proof triple_fun_n_ary_app as Hn_ary.
                        pose proof triple_fun_n_ary_weaken as Hweaken.
                        pose proof triple_fun_n_ary_assign_array_at
                          as Hassign_array_at.
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
                          simpl.
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
                          instantiate (cn1_t := S (S ?[ccn1_t])).
                          instantiate (ccn1_t := ?[cn1_t]).
                          (*simpl.*)
                          lazymatch goal with
                          | [H : heap_time_bound ?n ?C ?t |- _] =>
                            remember t as t_credits eqn:Ht_credits
                          end.
                          simpl.
                          do 2 erewrite (*<- (Nat.add_succ_l _ (_*t_credits)),*)
                            (*<- Ht_credits,*) (Nat.add_comm t_credits).
                          repeat erewrite (Nat.add_assoc _ _ t_credits).
                          do 2 erewrite (Nat.add_comm _ t_credits).
                          erewrite (Nat.add_assoc t_credits t_credits).
                          triple_pull_credits (3+t_credits+t_credits). triple_reorder_credits.
                          triple_pull_credits (3+t_credits). triple_reorder_credits.
                          triple_pull_credits 3. triple_reorder_credits.
                          triple_pull_credits 2. triple_reorder_credits.
                          lazymatch goal with
                          | [|- triple (Val h_insert <* Val ?v <* _ <* _)
                              ($2 <*> ($1 <*> ($t_credits <*> (_ <*> (_ <*> ($?pot <*> _)))))) _] =>
                            eapply triple_weaken with
                              (P := ($2 <*> ($1 <*> ($ (t_credits) <*> ($ (t_credits) <*> ($pot <*>
                                (is_heap n _ _ _ _ pot v)))))) <*> ($ _ <*> $ _ <*> _)),
                              triple_frame;
                              [| |revert v]
                          end.
                          { prove_implies_rev. }
                          { intros.
                            eapply implies_trans with
                              (Q := (<exists> c, $c) <*> (<exists> a b c,
                                is_heap n _ _ a b c (*x32*) _ <*> _) <*> _ (*_ <*> $x32 <*> _*)).
                            { prove_implies_refl. }
                            { apply implies_spec. intros.
                              normalize_star. swap_star_ctx. normalize_star.
                              swap_star_ctx. normalize_star. swap_star_ctx.
                              normalize_star. apply star_assoc. swap_star.
                              revert_implies.
                              eapply implies_trans;
                                [apply star_implies_mono;
                                  [prove_implies_refl
                                  |eapply implies_trans;
                                    [eapply implies_trans; [apply star_comm|apply star_assoc_r]
                                    |apply star_implies_mono;
                                      [prove_implies_refl
                                      |eapply implies_trans;
                                        [apply star_assoc_r|apply star_comm]]]]|].
                              eapply implies_trans; [apply star_assoc_l|].
                              eapply implies_trans; [apply star_assoc_l|].
                              eapply implies_trans; [apply star_comm|].
                              eapply implies_trans; [apply star_assoc_l|].
                              eapply implies_trans;
                                [apply star_implies_mono;
                                  [apply star_assoc_l|prove_implies_refl]|].
                              eapply implies_trans; [apply star_assoc_r|].
                              apply star_implies_mono.
                              { apply implies_spec. intros. eexists.
                                eapply credits_star_l; try reflexivity.
                                eassumption. }
                              { eapply implies_trans; [apply star_comm|].
                                eapply implies_trans; [apply star_assoc|].
                                eapply implies_trans; [apply star_assoc|].
                                eapply implies_trans; [apply star_comm|].
                                eapply implies_trans; [apply star_assoc|].
                                eapply implies_trans; [apply star_assoc|].
                                apply star_implies_mono; [prove_implies_refl|].
                                apply implies_spec. intros. do 9 eexists.
                                exists 0.
                                conormalize_star. swap_star. apply star_assoc.
                                eapply star_implies_mono;
                                  [|prove_implies_refl|eassumption]. (* 2:{ prove_implies_refl. eapply star_implies_mono; [|prove_implies_refl|]. 2:{ apply H34. } } *)
                                apply implies_spec. intros.
                                swap_star. conormalize_star.
                                eapply star_implies_mono;
                                  [|prove_implies_refl|eassumption].
                                apply implies_spec. intros. conormalize_star.
                                eapply star_implies_mono;
                                  [|prove_implies_refl|eassumption].
                                apply implies_spec. intros. normalize_star.
                                swap_star_ctx. revert_implies.
                                prove_implies. } } }
                          lazymatch goal with
                          | [|-
                            forall a,
                              triple (Val (@?f a) <* (@?e1 a) <* (@?e2 a) <* (@?e3 a))
                                ($2 <*> ($1 <*> ($?t <*> ($?t' <*> ($?p' <*> @?P0 a)))))
                                (@?Q1 a)
                            ] =>
                            intros a;
                            specialize Hn_ary with
                              (v := f a) (e := e1 a) (es := [e2 a;e3 a]%list)
                              (P := $1 <*> ($t <*> P0 a))
                          end.
                          lazymatch goal with
                          | [H : forall n C P Q W p s k d c t,
                              _ -> _ -> _ -> _ -> _ -> _ -> _ -> _ ->
                              triple_fun_n_ary _ h_insert
                                (@?Pre n C P Q W p k d c) (@?Post n C P Q W p k d t)
                            |- triple
                              (Val h_insert <* Val ?h <* Val (Int (Z.of_nat ?s')) <* Val (Int ?x))
                              ($_ <*> ($_ <*> ($?t' <*> ($?t' <*>
                                ($?p' <*> is_heap ?n' ?C' ?P' ?Q' ?W' ?p' ?h))))) _
                            ] =>
                            let d' := constr:(Z.to_nat x) in
                            let c' := constr:(t') in
                            specialize Hn_ary with
                              (Q1 := Pre n' C' P' Q' W' p' s' d' c')
                              (Q2 := Post n' C' P' Q' W' p' s' d' t');
                            specialize Hspec_h_insert with
                              (n := n') (C := C') (P := P') (Q := Q') (W := W') (p := p')
                              (k := s') (d := d') (c := t') (t := t')
                          end.
                          (*specialize (Hweaken _ assign_array_at 2).*)
                          simpl in Hn_ary, Hspec_h_insert, Hweaken. eapply triple_weaken, triple_frame, Hn_ary.
                          { prove_implies_rev. }
                          { apply implies_post_spec. intros ? ? ? HQ.
                            normalize_star. swap_star_ctx. normalize_star.
                            solve_star. swap_star. solve_star. swap_star.
                            repeat lazymatch goal with
                            | [|- ((_ <*> _) <*> _) ?c ?m ] =>
                              apply star_assoc_l; eauto
                            | [|- (<[_]> <*> _) ?c ?m ] =>
                              apply star_pure_l; split_all
                            end.
                            { assumption. }
                            { rewrite <- (Nat2Z.inj_add).
                              eapply nat_function_update; eauto. }
                            { eapply nat_function_update; eauto. }
                            { rewrite <- Hlen1, List.app_length, List.app_length.
                              simpl. reflexivity. }
                            { rewrite <- Hlen2, List.app_length, List.app_length.
                              simpl. reflexivity. }
                            { unfold update_nat_function_at. intros i'' Hin.
                              lazymatch goal with
                              | [|- (if i'' =? ?x then _ else _) = _] =>
                                destruct Nat.eqb_spec with i'' x
                              end.
                              { exfalso. subst i''.
                                lazymatch goal with
                                | [H : is_elem_weighted_unique_list _ _
                                    (_ ++ (i',w')::_) |- _] =>
                                  unfold is_elem_weighted_unique_list in H;
                                  rewrite List.map_app in H; simpl in H;
                                  destruct H as (?&Hnin%List.NoDup_remove_2)
                                end.
                                apply Hnin. apply List.in_or_app. (*eauto.*)
                                rewrite <- Hlen3. erewrite <- List.map_length.
                                eauto. }
                              { eauto. } }
                            { unfold update_nat_function_at. intros i'' Hin.
                              lazymatch goal with
                              | [|- (if i'' =? ?x then _ else _) = _] =>
                                destruct Nat.eqb_spec with i'' x
                              end.
                              { exfalso. subst i''.
                                lazymatch goal with
                                | [H : is_elem_weighted_unique_list _ _
                                    (_ ++ (i',w')::_) |- _] =>
                                  unfold is_elem_weighted_unique_list in H;
                                  rewrite List.map_app in H; simpl in H;
                                  destruct H as (?&Hnin%List.NoDup_remove_2)
                                end.
                                apply Hnin. apply List.in_or_app. (*eauto.*)
                                rewrite <- Hlen4. erewrite <- List.map_length.
                                eauto. }
                              { eauto. } }
                            { unfold update_nat_function_at. intros i'' Hin.
                              rewrite List.map_length, Hlen3.
                              lazymatch goal with
                              | [|- (if i'' =? ?x then _ else _) = _] =>
                                destruct Nat.eqb_spec with i'' x
                              end.
                              { subst i''.
                                lazymatch goal with
                                | [H : distance_decrease g x_min ?D ?D' ?pred ?pred',
                                  Hneigh : is_elem_weighted_unique_list _ _
                                    (?L1++(i',w')::?L2)%list,
                                  HD : forall _, _ \/ _ -> ?f _ = ?D _,
                                  (*HD' : forall _, _ -> ?f _ = ?D' _*)
                                  HDSome : forall _ _, _ <-> ?f _ = Some _
                                  |- _ = ?g i'] =>
                                  unify D' g; unfold distance_decrease in H;
                                  unfold is_elem_weighted_unique_list,
                                    is_elem_weighted_list, neighbours in Hneigh;
                                  rewrite List.map_app in Hneigh; simpl in Hneigh;
                                  destruct Hneigh as (Hneigh&Hnin%List.NoDup_remove_2);
                                  specialize Hneigh with i' w';
                                  rewrite List.in_app_iff in Hneigh; simpl in Hneigh;
                                  destruct Hneigh as ((HE&HW)&_); auto;
                                  destruct H as (dv&Hdv&Hvalue);
                                  destruct Hvalue with i' as (((->&?)&?)&?);
                                  [assumption|
                                    destruct (D i') eqn:HDi'; auto;
                                    rewrite <- HD in HDi'; auto;
                                    rewrite <- HDSome, List.app_nth2,
                                      List.map_length, Hlen3, Nat.sub_diag in HDi';
                                    [simpl in HDi'; injection HDi'; lia|
                                      rewrite List.map_length; lia]|]
                                end.
                                subst w'. do 2 f_equal.
                                lazymatch goal with
                                | [H : List.nth x_min ?L None = Some (Int (Z.of_nat ?n)),
                                  Hfun : is_nat_fun_of_val_list ?L ?D
                                  |- ?n = dv] =>
                                  unfold is_nat_fun_of_val_list, fun_of_list in Hfun;
                                  destruct Hfun as (?&Hfun);
                                  apply Hfun in H; rewrite H in Hdv
                                end.
                                injection Hdv. auto. }
                                { lazymatch goal with
                                  | [H : forall _, List.In _ _ -> ?f _ = ?D' _
                                    |- ?f i'' = ?D' i''] =>
                                    apply H
                                  end.
                                  rewrite List.map_app in Hin.
                                  apply List.in_app_or in Hin.
                                  simpl in Hin. destruct Hin as [Hin|[->|[]]]; tauto. } }
                            { unfold update_nat_function_at. intros i'' Hin.
                              rewrite List.map_length, Hlen4.
                              lazymatch goal with
                              | [|- (if i'' =? ?x then _ else _) = _] =>
                                destruct Nat.eqb_spec with i'' x
                              end.
                              { subst i''.
                                lazymatch goal with
                                | [H : distance_decrease g x_min ?D ?D' ?pred ?pred',
                                  Hneigh : is_elem_weighted_unique_list _ _
                                    (?L1++(i',w')::?L2)%list,
                                  HD : forall _, _ \/ _ -> ?h _ = ?D _,
                                  Hpred : forall _, _ \/ _ -> ?f _ = ?pred _,
                                  HDSome : forall _ _, _ <-> ?h _ = Some _,
                                  HpredSome : forall _ _, _ <-> ?f _ = Some _
                                  |- _ = ?g i'] =>
                                  unify pred' g; unfold distance_decrease in H;
                                  unfold is_elem_weighted_unique_list,
                                    is_elem_weighted_list, neighbours in Hneigh;
                                  rewrite List.map_app in Hneigh; simpl in Hneigh;
                                  destruct Hneigh as (Hneigh&Hnin%List.NoDup_remove_2);
                                  specialize Hneigh with i' w';
                                  rewrite List.in_app_iff in Hneigh; simpl in Hneigh;
                                  destruct Hneigh as ((HE&HW)&_); auto;
                                  destruct H as (dv&Hdv&Hvalue);
                                  destruct Hvalue with i' as (((?&->)&?)&?);
                                  [assumption|
                                    destruct (D i') eqn:HDi'; auto;
                                    rewrite <- HD in HDi'; auto;
                                    rewrite <- HDSome, List.app_nth2,
                                      List.map_length, Hlen3, Nat.sub_diag in HDi';
                                    [simpl in HDi'; injection HDi'; lia|
                                      rewrite List.map_length; lia]|]
                                end.
                                reflexivity. }
                                { lazymatch goal with
                                  | [H : forall _, List.In _ _ -> ?f _ = ?pred' _
                                    |- ?f i'' = ?pred' i''] =>
                                    apply H
                                  end.
                                  rewrite List.map_app in Hin.
                                  apply List.in_app_or in Hin.
                                  simpl in Hin. destruct Hin as [Hin|[->|[]]]; tauto. } }
                            { unfold update_nat_function_at. intros i'' Hnin.
                              rewrite List.map_length, Hlen3.
                              destruct Nat.eqb_spec with i'' i'.
                              { exfalso. subst i''.
                                apply Hnin. rewrite List.map_app, List.in_app_iff.
                                simpl. auto. }
                              { rewrite List.map_app in Hnin. simpl in Hnin. eauto. } }
                            { unfold update_nat_function_at. intros i'' Hnin.
                              rewrite List.map_length, Hlen4.
                              destruct Nat.eqb_spec with i'' i'.
                              { exfalso. subst i''.
                                apply Hnin. rewrite List.map_app, List.in_app_iff.
                                simpl. auto. }
                              { rewrite List.map_app in Hnin. simpl in Hnin. eauto. } }
                            { assumption. }
                            { lazymatch goal with
                              | [ H : set_equiv ?R ?R',
                                  H' : (is_heap n C ?P ?Q _ _ _ <*> _) _ _
                                |- set_equiv ?Q' _] =>
                                unify Q Q'; unfold set_sum;
                                unfold set_equiv in H |- *; intros; rewrite H
                              end.
                              unfold set_sum, single. rewrite List.map_app, List.in_app_iff.
                              simpl.
                              lazymatch goal with
                              | [|- (set_remove ?P x_min _ \/ _) \/ _ <->
                                  set_remove ?P' x_min _ \/ _] =>
                                unify P P'
                              end.
                              split; [|clear; tauto].
                              lazymatch goal with
                              | [|- (_ \/ ~ ?P _ /\_) \/ _ -> _ \/ ~ ?P _ /\ _] =>
                                assert (~ P i') as Hi'P
                              end.
                              { intros Hin.
                                eapply Dijkstra_invariant_D_is_some_in_set in Hin as (d&Heq);
                                  [|eassumption].
                                lazymatch goal with
                                | [H : forall _, i' = _ \/ _ -> ?f _ = ?D _,
                                  H' : forall _ _, List.nth _ _ None = _ <-> ?f _ = _,
                                  Heq : ?D i' = Some d
                                  |- _] =>
                                  rewrite <- H, <- H', List.app_nth2,
                                    List.map_length, Hlen3, Nat.sub_diag in Heq;
                                    [simpl in Heq; injection Heq; lia
                                    |rewrite List.map_length; lia|auto]
                                end. }
                              intros [Hin | ->]; [revert Hin|revert Hi'P];
                              clear; tauto. }
                            { unfold is_subset, set_sum, single. intros i'' [Hin|<-].
                              { auto. }
                              { lazymatch goal with
                                | [H : is_elem_weighted_unique_list _ _ (_++(i',w')::_)%list
                                  |- _] =>
                                  unfold is_elem_weighted_unique_list,
                                    is_elem_weighted_list, neighbours in H;
                                  destruct H as (Hin&_);
                                  specialize Hin with i' w'; simpl in Hin;
                                  rewrite List.in_app_iff in Hin; simpl in Hin;
                                  destruct Hin as ((?%E_closed2&?)&?); auto
                                end. } }
                            { apply disjoint_sum_size; eauto using single_set_size.
                              unfold are_disjoint_sets, single.
                              lazymatch goal with
                              | [H : set_equiv ?R' _,
                                H'' : Dijkstra_invariant _ _ ?P' _ _,
                                H''' : ?P' = empty /\ ?Q'' = _ \/
                                  ?P' src /\ ?Q'' = neighbourhood _ _,
                                H'''' : forall _ _,
                                  List.nth _ (_ ?LL1 ++ _::_ ?LL2) None = Some _ <-> ?f _ = _,
                                H''''' : forall _ _,
                                  List.nth _ (_ ?LL1' ++ _::_ ?LL2') None = Some _ <-> ?f' _ = _,
                                H6 : forall _, i' = _ \/ _ -> ?f _ = ?D' _,
                                H7 : forall _, i' = _ \/ _ -> ?f' _ = ?pred' _,
                                H8 : forall _, List.In _ _ -> ?f _ = ?D'' _,
                                H9 : forall _, List.In _ _ -> ?f' _ = ?pred'' _,
                                H10 : is_elem_weighted_unique_list _ _ (_++(i',w')::_),
                                H11 : is_nat_fun_of_val_list ?LD' ?D',
                                H12 : List.nth x_min ?LD' None = _
                                |- forall _, ~ (?R' _ /\ _)] =>
                                rename R' into R, H into HeqR, P' into P, Q'' into N, LL1 into L1,
                                  LL2 into L2, LL1' into L1', LL2' into L2', f into fD,
                                  f' into fD', D' into D, pred' into pred, D'' into D2,
                                  pred'' into pred2, LD' into LD,
                                  H'' into HDij_inv, H''' into Hor,
                                  H'''' into HD_nth, H''''' into Hpred_nth,
                                  H6 into HD, H7 into Hpred, H8 into HD2, H9 into Hpred2,
                                  H10 into Hneighs, H11 into Hfun, H12 into Hnth
                              end.
                              intros ? (HR&<-). apply HeqR in HR.
                              unfold set_sum, set_remove in HR.
                              destruct HR as [(HN&Hneq)|(Hnin&Hin)].
                              { destruct (D i') eqn:HDi'.
                                { rewrite <- HD, <- HD_nth in HDi'; auto.
                                  rewrite List.app_nth2, List.map_length, Hlen3,
                                    Nat.sub_diag in HDi';
                                    [|rewrite List.map_length, Hlen3; lia].
                                  simpl in HDi'. injection HDi'. lia. }
                                { destruct Hor as [(->&->)|(Hin&->)].
                                  { unfold set_sum, empty, single in HN.
                                    destruct HN as [[]|<-].
                                    eapply Dijkstra_invariant_nonnone with (x := src); eauto. }
                                  { apply Dijkstra_invariant_nonnone
                                      with (x := i') in HDij_inv; auto. } } }
                              { unfold is_elem_weighted_unique_list,
                                  is_elem_weighted_list, neighbours in Hneighs.
                                rewrite List.map_app in Hneighs.
                                destruct Hneighs as (?&Hnodup%List.NoDup_remove_2).
                                rewrite List.in_app_iff in Hnodup. auto. } }
                            { unfold set_sum.
                              lazymatch goal with
                              | [H : set_equiv ?R' _,
                                H'' : Dijkstra_invariant _ _ ?P' _ _,
                                H''' : ?P' = empty /\ ?Q'' = _ \/
                                  ?P' src /\ ?Q'' = neighbourhood _ _,
                                H'''' : forall _ _,
                                  List.nth _ (_ ?LL1 ++ _::_ ?LL2) None = Some _ <-> ?f _ = _,
                                H''''' : forall _ _,
                                  List.nth _ (_ ?LL1' ++ _::_ ?LL2') None = Some _ <-> ?f' _ = _,
                                H6 : forall _, i' = _ \/ _ -> ?f _ = ?D' _,
                                H7 : forall _, i' = _ \/ _ -> ?f' _ = ?pred' _,
                                H8 : forall _, List.In _ _ -> ?f _ = ?D'' _,
                                H9 : forall _, List.In _ _ -> ?f' _ = ?pred'' _,
                                H10 : is_elem_weighted_unique_list _ _ (_++(i',w')::_),
                                H11 : is_nat_fun_of_val_list ?LD' ?D',
                                H12 : List.nth x_min ?LD' None = _
                                |- (?P' _ \/ ?R' _) -> _] =>
                                rename R' into R, H into HeqR, P' into P, Q'' into N, LL1 into L1,
                                  LL2 into L2, LL1' into L1', LL2' into L2', f into fD,
                                  f' into fD', D' into D, pred' into pred, D'' into D2,
                                  pred'' into pred2, LD' into LD,
                                  H'' into HDij_inv, H''' into Hor,
                                  H'''' into HD_nth, H''''' into Hpred_nth,
                                  H6 into HD, H7 into Hpred, H8 into HD2, H9 into Hpred2,
                                  H10 into Hneighs, H11 into Hfun, H12 into Hnth
                              end.
                              intros [Hin|HR].
                              { eapply Dijkstra_invariant_D_is_some_in_set
                                  in Hin as (d&HDin); eauto.
                                rewrite <- HD, <- HD_nth in HDin; auto.
                                rewrite List.app_nth2, List.map_length, Hlen3,
                                  Nat.sub_diag in HDin;
                                  [|rewrite List.map_length, Hlen3; lia].
                                simpl in HDin. injection HDin. lia. }
                              { unfold single. exfalso. apply HeqR in HR.
                                unfold set_sum, set_remove in HR.
                                destruct HR as [(HN&Hneq)|(Hnin&Hin)].
                                { destruct (D i') eqn:HDi'.
                                  { rewrite <- HD, <- HD_nth in HDi'; auto.
                                    rewrite List.app_nth2, List.map_length, Hlen3,
                                      Nat.sub_diag in HDi';
                                      [|rewrite List.map_length, Hlen3; lia].
                                    simpl in HDi'. injection HDi'. lia. }
                                  { destruct Hor as [(->&->)|(Hin&->)].
                                    { unfold set_sum, empty, single in HN.
                                      destruct HN as [[]|<-].
                                      eapply Dijkstra_invariant_nonnone with (x := src); eauto. }
                                    { apply Dijkstra_invariant_nonnone
                                        with (x := i') in HDij_inv; auto. } } }
                                { unfold is_elem_weighted_unique_list,
                                    is_elem_weighted_list, neighbours in Hneighs.
                                  rewrite List.map_app in Hneighs.
                                  destruct Hneighs as (?&Hnodup%List.NoDup_remove_2).
                                  rewrite List.in_app_iff in Hnodup. auto. } } }
                            { reflexivity. }
                            { swap_star. solve_star. apply empty_star_l_intro. swap_star.
                              apply star_assoc. swap_star. unfold update_nat_function_at.
                              rewrite List.map_length, Hlen3.
                              lazymatch goal with
                              | [H : (is_heap n C _ _ (_ (Z.to_nat _)) _ _ <*> _)
                                  _ _ |- _] =>
                                rewrite Z2Nat.inj_add, Nat2Z.id, Nat2Z.id in H;
                                try lia;
                                unfold set_value_at in H
                              end.
                              eapply star_implies_mono; [prove_implies_refl| |eassumption].
                              eapply implies_trans;
                                [eapply star_implies_mono;
                                  [apply credits_star_l|prove_implies_refl];reflexivity|].
                              eapply implies_trans; [apply credits_star_l;reflexivity|].
                              apply credits_star_r.
                              lazymatch goal with
                              | [|- t_credits + ?k1 + ?k2 = ?k3 + ?k4] =>
                                unify (t_credits + k1 - k3 + k2) k4
                              end.
                              lia. } }
                          { rewrite <- Hn in *.
                            lazymatch goal with
                            | [H : Dijkstra_invariant ?D ?pred ?Q src g,
                              H' : min_cost_elem ?Q' _ x_min
                              |- _] =>
                              edestruct is_set_size_with_neighbours
                                with (P := Q') (P' := Q) as (?&?&?); eauto
                            end.
                            { unfold min_cost_elem in Hmincost.
                              destruct Hmincost as (?&?). eassumption. }
                            { unfold are_disjoint_sets. intros.
                              lazymatch goal with
                              | [H : (?P = empty /\ ?P' = _) \/ (?P src /\ ?P' = _)
                                |- ~ (?P' _ /\ ?P _)] =>
                                destruct H as [(->&->)|(?&->)]
                              end;
                              clear; unfold empty, neighbourhood; tauto. }
                            eapply Hspec_h_insert; unfold empty, not; auto.
                            { eapply equiv_set_size; [|eassumption].
                              unfold set_equiv in *. intros. symmetry. eauto. }
                            { assumption. }
                            { eapply init_range_lt_size; eauto.
                              lazymatch goal with
                              | [H : is_elem_weighted_unique_list _ _ (?L++_)
                                |- _] =>
                                unfold is_elem_weighted_unique_list,
                                  is_elem_weighted_list, neighbours in H;
                                destruct H as (H&?); specialize H with i' w';
                                rewrite List.in_app_iff in H; simpl in H;
                                destruct H as ((?%E_closed2&?)&?)
                              end;
                              auto. }
                            { lazymatch goal with
                              | [H' : set_equiv ?Q' _,
                                H'' : Dijkstra_invariant _ _ ?P' _ _,
                                H''' : ?P' = empty /\ ?Q'' = _ \/
                                  ?P' src /\ ?Q'' = neighbourhood _ _,
                                H'''' : forall _ _,
                                  List.nth _ (_ ?LL1 ++ _::_ ?LL2) None = Some _ <-> ?f _ = _,
                                H''''' : forall _ _,
                                  List.nth _ (_ ?LL1' ++ _::_ ?LL2') None = Some _ <-> ?f' _ = _,
                                H6 : forall _,
                                  i' = _ \/ List.In _ (_ ?Ns1') -> ?f _ = ?D' _,
                                H7 : forall _,
                                  i' = _ \/ List.In _ (_ ?Ns1') -> ?f' _ = ?pred' _,
                                H8 : forall _, List.In _ (_ ?Ns2') -> ?f _ = ?D'' _,
                                H9 : forall _, List.In _ (_ ?Ns2') -> ?f' _ = ?pred'' _,
                                H10 : is_elem_weighted_unique_list _ _ (_++(i',w')::_),
                                H11 : is_nat_fun_of_val_list ?LD' ?D',
                                H12 : List.nth x_min ?LD' None = _,
                                H14 : forall _, ~ _ -> ?f _ = ?D'' _,
                                H15 : forall _, ~ _ -> ?f' _ = ?pred'' _
                                  |- _] =>
                                rename P' into P, Q' into Q, Q'' into N, LL1 into L1,
                                  LL2 into L2, LL1' into L1', LL2' into L2', f into fD,
                                  f' into fD', D' into D, pred' into pred, D'' into D2,
                                  pred'' into pred2, LD' into LD, Ns1' into Ns1, Ns2' into Ns2,
                                  H' into HeqQ, H'' into HDij_inv, H''' into Hor,
                                  H'''' into HD_nth, H''''' into Hpred_nth,
                                  H6 into HD, H7 into Hpred, H8 into HD2, H9 into Hpred2,
                                  H10 into Hneighs, H11 into Hfun, H12 into Hnth,
                                  H14 into HD2out, H15 into Hpred2out
                              end.
                              lazymatch goal with
                              | [H : List.nth x_min _ _ = Some (Int (Z.of_nat ?x)) |- _] =>
                                rename x into y_min
                              end.
                              assert (D x_min = Some y_min) as HDmin.
                              { unfold is_nat_fun_of_val_list, fun_of_list in Hfun.
                                destruct Hfun as (?&Hfun). apply Hfun. assumption. }
                              intros u [HP|<-].
                              { destruct Hor as [(->&->)|(Hor1&Hor2)].
                                { contradiction. }
                                { assert (fD u = D u) as ->.
                                  { assert (Decidable.decidable (List.In u (i'::List.map fst Ns1)))
                                      as [Hin|Hnin].
                                    { apply decidable_in, Nat.eq_decidable. }
                                    { auto. }
                                    { erewrite <- Dijkstra_invariant_distance_decrease_in_P
                                        with (D := D) (D' := D2); eauto.
                                      assert (Decidable.decidable (List.In u (List.map fst Ns2)))
                                        as [Hin2|Hnin2].
                                      { apply decidable_in, Nat.eq_decidable. }
                                      { apply HD2. assumption. }
                                      { apply HD2out. rewrite List.in_app_iff. tauto. } } }
                                  edestruct Dijkstra_invariant_D_is_some_in_set
                                    with (v := u) as (?&Hd); eauto.
                                  rewrite Hd. assert (le (D u) (D x_min)).
                                  { eapply Dijkstra_invariant_D_ge_in_neighbourhood; eauto.
                                    unfold min_cost_elem in Hmincost. destruct Hmincost.
                                    subst N. assumption. }
                                  rewrite Z2Nat.inj_add, Nat2Z.id; try lia. transitivity y_min.
                                  { rewrite Hd, HDmin in *. simpl in *. assumption. }
                                  { lia. } } }
                              { rewrite HD2out.
                                { erewrite distance_decrease_min; eauto. rewrite HDmin. lia. }
                                { unfold is_elem_weighted_unique_list, is_elem_weighted_list,
                                    neighbours in Hneighs.
                                  destruct Hneighs as (Hneighs&?).
                                  change (i'::List.map fst ?L)%list with (List.map fst ((i',w')::L)).
                                  rewrite <- List.map_app, List.in_map_iff. intros ((?&?)&<-&Hin).
                                  rewrite Hneighs in Hin. simpl in Hin. destruct Hin.
                                  unfold is_irreflexive, not in *. eauto. } } }
                            { rewrite Z2Nat.inj_add, Nat2Z.id, Nat2Z.id; try lia.
                              lazymatch goal with
                              | [H : ?P' = _ /\ ?Q' = _ \/ ?P' src /\ ?Q' = _,
                                H' : is_set_size ?P' ?sP',
                                H'' : Dijkstra_invariant _ _ ?P' _ _,
                                H'''' : forall _ _,
                                  List.nth _ (_ ?LL1 ++ _::_ ?LL2) None = Some _ <-> ?f _ = _,
                                H''''' : forall _ _,
                                  List.nth _ (_ ?LL1' ++ _::_ ?LL2') None = Some _ <-> ?f' _ = _,
                                H6 : forall _, i' = _ \/ _ -> ?f _ = ?D' _,
                                H7 : forall _, i' = _ \/ _ -> ?f' _ = ?pred' _,
                                H8 : forall _, List.In _ _ -> ?f _ = ?D'' _,
                                H9 : forall _, List.In _ _ -> ?f' _ = ?pred'' _,
                                H10 : is_elem_weighted_unique_list _ _ (_++(i',w')::_),
                                H11 : is_nat_fun_of_val_list ?LD' ?D',
                                H12 : List.nth x_min ?LD' None = _
                                |- ?x + w' <= n*C] =>
                                rename x into w_min, P' into P, Q' into Q, sP' into sP,
                                  LL1 into L1, LL2 into L2, LL1' into L1', LL2' into L2',
                                  f into fD, f' into fD', D' into D, pred' into pred,
                                  D'' into D2, pred'' into pred2, LD' into LD, H into Hor,
                                  H'' into HDij_inv, H'''' into HD_nth, H''''' into Hpred_nth,
                                  H6 into HD, H7 into Hpred, H8 into HD2, H9 into Hpred2,
                                  H10 into Hneighs, H11 into Hfun, H12 into Hnth
                              end.
                              assert (is_set_size (add_single (add_single P x_min) i') (sP+2)).
                              { change 2 with (1+1). rewrite Nat.add_assoc.
                                unfold add_single.
                                repeat apply disjoint_sum_size; eauto using single_set_size.
                                { unfold are_disjoint_sets, set_sum, single.
                                  intros u ([HP|<-]&<-).
                                  { eapply Dijkstra_invariant_D_is_some_in_set
                                      in HP as (d&HDin); eauto.
                                    rewrite <- HD, <- HD_nth in HDin; auto.
                                    rewrite List.app_nth2, List.map_length, Hlen3,
                                      Nat.sub_diag in HDin;
                                      [|rewrite List.map_length, Hlen3; lia].
                                    simpl in HDin. injection HDin. lia. }
                                  { unfold is_elem_weighted_unique_list, is_elem_weighted_list,
                                      neighbours in Hneighs.
                                    destruct Hneighs as (Hneighs&?). specialize Hneighs with i' w'.
                                    rewrite List.in_app_iff in Hneighs. simpl in Hneighs.
                                    destruct Hneighs as ((?&?)&?); auto.
                                    unfold is_irreflexive, not in *. eauto. } }
                                unfold are_disjoint_sets, set_sum, single. intros u (HP&<-).
                                destruct Hor as [(->&->)|(?&->)]; [contradiction|].
                                unfold min_cost_elem, neighbourhood in Hmincost.
                                destruct Hmincost as ((?&?)&?). auto. }
                              transitivity ((sP+2)*C).
                              { change 2 with (1+1).
                                rewrite Nat.add_assoc, Nat.mul_add_distr_r, Nat.mul_1_l.
                                apply Nat.add_le_mono.
                                { assert (D x_min = Some w_min) as Hmin.
                                  { unfold is_nat_fun_of_val_list, fun_of_list in Hfun.
                                    destruct Hfun as (?&Hfun). apply Hfun. assumption. }
                                  destruct Hor as [(->&->)|(Hin&->)].
                                  { unfold min_cost_elem, set_sum, empty, single in Hmincost.
                                    destruct Hmincost as ([[]|<-]&?).
                                    erewrite Dijkstra_invariant_D_src in Hmin; eauto.
                                    injection Hmin. lia. }
                                  { eapply Dijkstra_invariant_closest_neighbour_le_C; eauto. } }
                                { lazymatch goal with
                                  | [H : is_max_label _ _ |- _] => rename H into Hlab
                                  end.
                                  unfold is_max_label, max_cost, uncurry in Hlab.
                                  destruct Hlab as ((i''&w'')&?&->&Hle).
                                  unfold is_elem_weighted_unique_list, is_elem_weighted_list,
                                    neighbours in Hneighs.
                                  destruct Hneighs as (Hneighs&?). specialize Hneighs with i' w'.
                                  rewrite List.in_app_iff in Hneighs. simpl in Hneighs.
                                  destruct Hneighs as ((?&->)&?); auto.
                                  specialize Hle with (x_min, i'). simpl in Hle. auto. } }
                              { apply Nat.mul_le_mono_r.
                                eapply subset_size_le
                                  with (P' := add_single (add_single P x_min) i'); eauto.
                                { intros u.
                                  unfold Decidable.decidable, add_single, single, set_sum.
                                  assert (Decidable.decidable (P u)) as [Hin|Hout].
                                  { eapply decidable_if_finite; eauto using Nat.eq_decidable. }
                                  { auto. }
                                  { destruct (Nat.eq_decidable x_min u) as [H'|H'],
                                      (Nat.eq_decidable i' u) as [H''|H''];
                                      revert Hout H' H''; clear; tauto. } }
                                { unfold is_subset, add_single, set_sum, single.
                                  assert (V g x_min /\ V g i') as (?&?).
                                  { unfold is_elem_weighted_unique_list, is_elem_weighted_list,
                                      neighbours in Hneighs.
                                    destruct Hneighs as (Hneighs&?). specialize Hneighs with i' w'.
                                    rewrite List.in_app_iff in Hneighs. simpl in Hneighs.
                                    destruct Hneighs as ((HE&?)&?);
                                      eauto using E_closed1, E_closed2. }
                                  intros u [[HP|<-]|<-]; auto. } } }
                            { lazymatch goal with
                              | [H : set_equiv ?P _ |- ?P _ -> _] =>
                                unfold set_equiv in H; rewrite H
                              end.
                              unfold set_sum, set_remove. intros [(Hin&Hneq)|(Hnin&Hin)].
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
                              eapply implies_trans; [apply star_comm|].
                              apply star_implies_mono; [|prove_implies_refl].
                              apply credits_star_r.
                              do 2 rewrite <- Nat.add_succ_l. apply Nat.add_assoc. }
                            { prove_implies_refl. }
                            triple_reorder_credits.
                            triple_pull_credits 2. triple_reorder_credits.
                            lazymatch goal with
                            | [|- triple
                                (Val h_decrease_key <* Val ?v <* _ <* _)
                                ($2 <*> ($1 <*> ($?t <*> ($ _ <*> ($1 <*> ($ ?pot <*> _)))))) _] =>
                              eapply triple_weaken with
                                (P := ($2 <*> ($1 <*> ($1 <*> ($ pot <*> ($t <*>
                                  (is_heap n _ _ _ _ _ v)))))) <*> ($ _ <*> $ _ <*> _)),
                                triple_frame;
                                [| |revert v]
                            end.
                            { prove_implies_rev. }
                            { intros.
                              eapply implies_trans with
                                (Q := (<exists> c cx p, $c <*> <[c <= p + cx]>) <*>
                                  (<exists> a b c, is_heap n _ _ a b c _ <*> _) <*> _).
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
                                  eassumption. }
                                { eapply implies_trans; [apply star_assoc|].
                                  eapply implies_trans; [apply star_comm|].
                                  eapply implies_trans; [apply star_assoc|].
                                  eapply implies_trans; [apply star_comm|].
                                  eapply implies_trans; [apply star_assoc|].
                                  eapply implies_trans; [apply star_assoc|].
                                  apply star_implies_mono; [prove_implies_refl|].
                                  apply implies_spec. intros. do 9 eexists.
                                  lazymatch goal with
                                  | [_ : heap_time_bound _ _ ?t |- _] => exists (2*t)
                                  end.
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
                                  apply implies_spec. intros.
                                  normalize_star. swap_star_ctx. revert_implies.
                                  prove_implies. } } }
                            rewrite <- Nat2Z.inj_add.
                            lazymatch goal with
                            | [|-
                              forall a,
                                triple (Val (@?f a) <* (@?e1 a) <* (@?e2 a) <* (@?e3 a))
                                  ($2 <*> ($1 <*> ($1 <*> ($?pot' <*> ($?t <*> (@?P0 a))))))
                                  (@?Q1 a)
                              ] =>
                              intros a;
                              specialize Hn_ary with
                                (v := f a) (e := e1 a) (es := [e2 a;e3 a]%list)
                                (P := ($1 <*> ($1 <*> ($pot' <*> P0 a))))
                            end.
                            lazymatch goal with
                            | [H : forall n C P Q W p h k d c, _ -> _ -> _ -> _ ->
                                triple_fun_n_ary _ h_decrease_key
                                  (@?Pre n C P Q W p h k d c) (@?Post n C P Q W p h k d c)
                              |- triple
                                (Val h_decrease_key <* Val ?h' <* Val (Int (Z.of_nat ?s')) <* Val (Int ?x))
                                ($_ <*> ($_ <*> ($_ <*> ($ ?pot' <*> ($_ <*> is_heap ?n' ?C' ?P' ?Q' ?W' ?pot' ?h'))))) _
                              ] =>
                              let d' := constr:(Z.to_nat x) in
                              let c' := constr:(pot') in
                              specialize Hn_ary with
                                (Q1 := Pre n' C' P' Q' W' pot' h' s' d' c')
                                (Q2 := Post n' C' P' Q' W' pot' h' s' d' c');
                              specialize Hspec_h_decrease_key with
                                (n := n') (C := C') (P := P') (Q := Q') (W := W') (p := pot') (h := h')
                                (k := s') (d := d') (c := c')
                            end.
                            specialize (Hweaken _ h_decrease_key 2).
                            simpl in Hn_ary, Hspec_h_decrease_key, Hweaken.
                            eapply triple_weaken, triple_frame, Hn_ary.
                            { prove_implies_rev. }
                            { apply implies_post_spec. intros ? ? ? HQ.
                              normalize_star. swap_star_ctx. normalize_star.
                              solve_star. swap_star. solve_star. swap_star.
                              repeat lazymatch goal with
                              | [|- ((_ <*> _) <*> _) ?c ?m ] =>
                                apply star_assoc_l; eauto
                              | [|- (<[_]> <*> _) ?c ?m ] =>
                                apply star_pure_l; split_all
                              end.
                              { assumption. }
                              { eapply nat_function_update; eauto. }
                              { eapply nat_function_update; eauto. }
                              { rewrite <- Hlen1, List.app_length, List.app_length.
                                simpl. reflexivity. }
                              { rewrite <- Hlen2, List.app_length, List.app_length.
                                simpl. reflexivity. }
                              { unfold update_nat_function_at. intros i'' Hin.
                                lazymatch goal with
                                | [|- (if i'' =? ?x then _ else _) = _] =>
                                  destruct Nat.eqb_spec with i'' x
                                end.
                                { exfalso. subst i''.
                                  rewrite List.map_length, Hlen3 in Hin.
                                  lazymatch goal with
                                  | [H : is_elem_weighted_unique_list _ _
                                      (_ ++ (i',w')::_) |- _] =>
                                    unfold is_elem_weighted_unique_list in H;
                                    rewrite List.map_app in H; simpl in H;
                                    destruct H as (?&Hnin%List.NoDup_remove_2)
                                  end.
                                  apply Hnin. apply List.in_or_app. eauto. }
                                { eauto. } }
                              { unfold update_nat_function_at. intros i'' Hin.
                                lazymatch goal with
                                | [|- (if i'' =? ?x then _ else _) = _] =>
                                  destruct Nat.eqb_spec with i'' x
                                end.
                                { exfalso. subst i''.
                                  rewrite List.map_length, Hlen4 in Hin.
                                  lazymatch goal with
                                  | [H : is_elem_weighted_unique_list _ _
                                      (_ ++ (i',w')::_) |- _] =>
                                    unfold is_elem_weighted_unique_list in H;
                                    rewrite List.map_app in H; simpl in H;
                                    destruct H as (?&Hnin%List.NoDup_remove_2)
                                  end.
                                  apply Hnin. apply List.in_or_app. eauto. }
                                { eauto. } }
                              { unfold update_nat_function_at. intros i'' Hin.
                                rewrite List.map_length, Hlen3.
                                lazymatch goal with
                                | [|- (if i'' =? ?x then _ else _) = _] =>
                                  destruct Nat.eqb_spec with i'' x
                                end.
                                { subst i''.
                                  lazymatch goal with
                                  | [H : distance_decrease g x_min ?D ?D' ?pred ?pred',
                                    Hneigh : is_elem_weighted_unique_list _ _
                                      (?L1++(i',w')::?L2)%list,
                                    HD : forall _, _ \/ _ -> ?f _ = ?D _,
                                    HDSome : forall _ _, _ <-> ?f _ = Some _,
                                    Hlist : List.nth x_min ?L None = Some (Int (Z.of_nat ?n)),
                                    Hfun : is_nat_fun_of_val_list ?L ?D,
                                    Hfun' : is_nat_fun_of_val_list ?L' ?f
                                    |- _ = ?g i'] =>
                                    unify D' g; unfold distance_decrease in H;
                                    unfold is_nat_fun_of_val_list, fun_of_list in Hfun, Hfun';
                                    destruct Hfun as (?&Hfun); destruct Hfun' as (?&Hfun');
                                    unfold is_elem_weighted_unique_list,
                                      is_elem_weighted_list, neighbours in Hneigh;
                                    rewrite List.map_app in Hneigh; simpl in Hneigh;
                                    destruct Hneigh as (Hneigh&Hnin%List.NoDup_remove_2);
                                    specialize Hneigh with i' w';
                                    rewrite List.in_app_iff in Hneigh; simpl in Hneigh;
                                    destruct Hneigh as ((HE&HW)&_); auto;
                                    destruct H as (dv&Hdv&Hvalue);
                                    apply Hfun in Hlist; rewrite Hlist in Hdv;
                                    injection Hdv as <-;
                                    edestruct Hvalue with i' as ((?&((->&?)&?))&?);
                                    [assumption|
                                      rewrite <- HD, <- Hfun', List.app_nth2,
                                      List.map_length, Hlen3, Nat.sub_diag; auto;
                                      [simpl; do 2 f_equal; rewrite Z2Nat.id; auto; lia|
                                        rewrite List.map_length; lia]|
                                      rewrite <- HW;
                                      lazymatch goal with
                                      | [|- _ < ?k] => unify k (Z.to_nat x')
                                      end;
                                      lia|]
                                  end.
                                  do 2 f_equal. assumption. }
                                  { lazymatch goal with
                                    | [H : forall _, List.In _ _ -> ?f _ = ?D' _
                                      |- ?f i'' = ?D' i''] =>
                                      apply H
                                    end.
                                    rewrite List.map_app in Hin.
                                    apply List.in_app_or in Hin.
                                    simpl in Hin. destruct Hin as [Hin|[->|[]]]; tauto. } }
                              { unfold update_nat_function_at. intros i'' Hin.
                                rewrite List.map_length, Hlen4.
                                lazymatch goal with
                                | [|- (if i'' =? ?x then _ else _) = _] =>
                                  destruct Nat.eqb_spec with i'' x
                                end.
                                { subst i''.
                                  lazymatch goal with
                                  | [H : distance_decrease g x_min ?D ?D' ?pred ?pred',
                                    Hneigh : is_elem_weighted_unique_list _ _
                                      (?L1++(i',w')::?L2)%list,
                                    Hpred : forall _, _ \/ _ -> ?h _ = ?pred _,
                                    HD : forall _, _ \/ _ -> ?f _ = ?D _,
                                    HDSome : forall _ _, _ <-> ?f _ = Some _,
                                    Hlist : List.nth x_min ?L None = Some (Int (Z.of_nat ?n)),
                                    Hfun : is_nat_fun_of_val_list ?L ?D,
                                    Hfun' : is_nat_fun_of_val_list ?L' ?f
                                    |- _ = ?g i'] =>
                                    unify pred' g; unfold distance_decrease in H;
                                    unfold is_nat_fun_of_val_list, fun_of_list in Hfun, Hfun';
                                    destruct Hfun as (?&Hfun); destruct Hfun' as (?&Hfun');
                                    unfold is_elem_weighted_unique_list,
                                      is_elem_weighted_list, neighbours in Hneigh;
                                    rewrite List.map_app in Hneigh; simpl in Hneigh;
                                    destruct Hneigh as (Hneigh&Hnin%List.NoDup_remove_2);
                                    specialize Hneigh with i' w';
                                    rewrite List.in_app_iff in Hneigh; simpl in Hneigh;
                                    destruct Hneigh as ((HE&HW)&_); auto;
                                    destruct H as (dv&Hdv&Hvalue);
                                    apply Hfun in Hlist; rewrite Hlist in Hdv;
                                    injection Hdv as <-;
                                    edestruct Hvalue with i' as ((?&((->&?)&?))&?);
                                    [assumption|
                                      rewrite <- HD, <- Hfun', List.app_nth2,
                                      List.map_length, Hlen3, Nat.sub_diag; auto;
                                      [simpl; do 2 f_equal; rewrite Z2Nat.id; auto; lia|
                                        rewrite List.map_length; lia]|
                                      rewrite <- HW;
                                      lazymatch goal with
                                      | [|- _ < ?k] => unify k (Z.to_nat x')
                                      end;
                                      lia|]
                                  end.
                                  symmetry. assumption. }
                                  { lazymatch goal with
                                    | [H : forall _, List.In _ _ -> ?f _ = ?pred' _
                                      |- ?f i'' = ?pred' i''] =>
                                      apply H
                                    end.
                                    rewrite List.map_app in Hin.
                                    apply List.in_app_or in Hin.
                                    simpl in Hin. destruct Hin as [Hin|[->|[]]]; tauto. } }
                              { unfold update_nat_function_at. intros i'' Hnin.
                                rewrite List.map_length, Hlen3.
                                destruct Nat.eqb_spec with i'' i'.
                                { exfalso. subst i''.
                                  apply Hnin. rewrite List.map_app, List.in_app_iff.
                                  simpl. auto. }
                                { rewrite List.map_app in Hnin. simpl in Hnin. eauto. } }
                              { unfold update_nat_function_at. intros i'' Hnin.
                                rewrite List.map_length, Hlen4.
                                destruct Nat.eqb_spec with i'' i'.
                                { exfalso. subst i''.
                                  apply Hnin. rewrite List.map_app, List.in_app_iff.
                                  simpl. auto. }
                                { rewrite List.map_app in Hnin. simpl in Hnin. eauto. } }
                              { assumption. }
                              (*{ admit. }*)
                              { lazymatch goal with
                                | [ H : set_equiv ?P ?R,
                                    H' : (is_heap n C _ ?Q _ _ _ <*> _) _ _
                                  |- set_equiv ?Q' _] =>
                                  unify Q Q'; unfold set_sum;
                                  unfold set_equiv in H |- *; intros; rewrite H
                                end.
                                unfold set_sum, single.
                                rewrite List.map_app, List.in_app_iff. simpl.
                                split; [clear; tauto|]. intros [?|(?&[?|[<-|[]]])]; auto.
                                left. unfold set_remove. split.
                                { lazymatch goal with
                                  | [H : (Z.of_nat ?m_cost + Z.of_nat w' < x')%Z,
                                    H' : List.nth x_min ?L None = Some (Int (_ ?m_cost)),
                                    H'' : is_nat_fun_of_val_list ?L ?D
                                    |- _] =>
                                    assert (D x_min = Some m_cost) as HDSome;
                                    [unfold is_nat_fun_of_val_list, fun_of_list in H'';
                                      destruct H'' as (?&H''); apply H''; eassumption|]
                                  end.
                                  lazymatch goal with
                                  | [H : Dijkstra_invariant _ _ _ _ _ |- _] =>
                                    eapply Dijkstra_invariant_if_D_some with
                                      (x := i') (pr2 := x_min) in H
                                      as [(HP&?)|(?&?)]
                                  end.
                                  { lazymatch goal with
                                    | [H : (_ = empty /\ _ = set_sum empty _) \/
                                        (_ src /\ _ = neighbourhood _ _)
                                        |- _] =>
                                      destruct H as [(->&->)|(Hin&->)]
                                    end.
                                    { unfold set_sum, empty, single. auto. }
                                    { exfalso. rewrite HP in Hin. unfold empty in Hin.
                                      assumption. } }
                                  { lazymatch goal with
                                    | [H : (_ = empty /\ _ = set_sum empty _) \/
                                        (_ src /\ _ = neighbourhood _ _)
                                        |- _] =>
                                      destruct H as [(->&->)|(Hin&->)]
                                    end.
                                    { contradiction. }
                                    { assumption. } }
                                  { lazymatch goal with
                                    | [Heq : forall _, _ -> ?f _ = ?D _,
                                      Hfun : forall _ _, _ <-> ?f _ = _
                                      |- ?D i' = _] =>
                                      rewrite <- Heq; auto; apply Hfun
                                    end.
                                    rewrite List.app_nth2;
                                    rewrite List.map_length; subst i'; [|lia].
                                    rewrite Nat.sub_diag. simpl. repeat f_equal.
                                    symmetry. apply Z2Nat.id. lia. }
                                  { lazymatch goal with
                                    | [H : is_elem_weighted_unique_list _ _ (_++(i',w')::_)%list
                                      |- _] =>
                                      unfold is_elem_weighted_unique_list,
                                        is_elem_weighted_list, neighbours in H;
                                      edestruct H as (((?&?)&?)&?); [|eassumption]
                                    end.
                                    { apply List.in_or_app. simpl. auto. } }
                                  { eassumption. }
                                  { lazymatch goal with
                                    | [H : is_elem_weighted_unique_list _ _ (_++(i',w')::_)%list
                                      |- _] =>
                                      unfold is_elem_weighted_unique_list,
                                        is_elem_weighted_list, neighbours in H;
                                      edestruct H as (((?&Heq)&?)&?)
                                    end.
                                    { apply List.in_or_app. simpl. auto. }
                                    { rewrite <- Heq. lia. } } }
                                { lazymatch goal with
                                  | [H : is_elem_weighted_unique_list _ _ (_++(i',w')::_)%list
                                    |- _] =>
                                    unfold is_elem_weighted_unique_list,
                                      is_elem_weighted_list, neighbours in H;
                                    edestruct H as (((?&?)&?)&?)
                                  end.
                                  { apply List.in_or_app. simpl. auto. }
                                  { intros ->.
                                    lazymatch goal with
                                    | [H : is_irreflexive _ |- _] =>
                                      unfold is_irreflexive in H; eapply H
                                    end.
                                    eassumption. } } }
                              { assumption. }
                              { eassumption. }
                              { reflexivity. }
                              { split_all; eauto. unfold set_sum. intros HnIn.
                                lazymatch goal with
                                | [H : ~(?P' i' \/ ?Q' i'),
                                  H' : set_equiv ?Q' _,
                                  H'' : Dijkstra_invariant _ _ ?P' _ _,
                                  H''' : ?P' = empty /\ ?Q'' = _ \/
                                    ?P' src /\ ?Q'' = neighbourhood _ _,
                                  H'''' : forall _ _,
                                    List.nth _ (_ ?LL1 ++ _::_ ?LL2) None = Some _ <-> ?f _ = _,
                                  H''''' : forall _ _,
                                    List.nth _ (_ ?LL1' ++ _::_ ?LL2') None = Some _ <-> ?f' _ = _,
                                  H6 : forall _, i' = _ \/ _ -> ?f _ = ?D' _,
                                  H7 : forall _, i' = _ \/ _ -> ?f' _ = ?pred' _,
                                  H8 : forall _, List.In _ _ -> ?f _ = ?D'' _,
                                  H9 : forall _, List.In _ _ -> ?f' _ = ?pred'' _,
                                  H10 : is_elem_weighted_unique_list _ _ (_++(i',w')::_),
                                  H11 : is_nat_fun_of_val_list ?LD' ?D',
                                  H12 : List.nth x_min ?LD' None = _
                                  |- _] =>
                                  rename P' into P, Q' into Q, Q'' into N, LL1 into L1,
                                    LL2 into L2, LL1' into L1', LL2' into L2', f into fD,
                                    f' into fD', D' into D, pred' into pred, D'' into D2,
                                    pred'' into pred2, LD' into LD,
                                    H' into HeqQ, H'' into HDij_inv, H''' into Hor,
                                    H'''' into HD_nth, H''''' into Hpred_nth,
                                    H6 into HD, H7 into Hpred, H8 into HD2, H9 into Hpred2,
                                    H10 into Hneighs, H11 into Hfun, H12 into Hnth
                                end.
                                unfold is_elem_weighted_unique_list,
                                  is_elem_weighted_list, neighbours in Hneighs.
                                destruct Hneighs as (Hneighs&?). specialize Hneighs with i' w'.
                                rewrite List.in_app_iff in Hneighs. simpl in Hneighs.
                                destruct Hneighs as ((?&HW)&?); auto.
                                exfalso. apply HnIn. unfold set_equiv in HeqQ. right.
                                apply HeqQ. unfold set_sum, set_remove. left. split.
                                { eapply Dijkstra_invariant_if_D_some
                                    with (x := i') (n := Z.to_nat x') (pr2 := x_min)
                                    in HDij_inv.
                                  { destruct Hor as [(->&->)|(Hin&->)].
                                    { destruct HDij_inv as [(?&?)|([]&?)].
                                      unfold set_sum, single. auto. }
                                    { destruct HDij_inv as [(->&?)|(?&?)]; auto.
                                      contradiction. } }
                                  { rewrite <- HD, <- HD_nth; auto.
                                    rewrite List.app_nth2; rewrite List.map_length, Hlen3;
                                      [|lia].
                                    rewrite Nat.sub_diag. simpl. repeat f_equal. lia. }
                                  { assumption. }
                                  { unfold is_nat_fun_of_val_list, fun_of_list in Hfun.
                                    destruct Hfun as (?&Hfun). apply Hfun. eassumption. }
                                  { rewrite <- HW. lia. } }
                                { intros ->. unfold is_irreflexive, not in *. eauto. } }
                              { do 2 apply star_assoc_r. swap_star.
                                rewrite Nat.add_0_l, Nat.add_0_r.
                                unfold update_nat_function_at.
                                rewrite List.map_length, Hlen3.
                                lazymatch goal with
                                | [H : (is_heap n C _ _ (_ (Z.to_nat _)) _ _ <*> (_ <*> $?k))
                                    _ _ |- _] =>
                                  rewrite Nat2Z.id in H; try lia;
                                  unfold set_value_at in H;
                                  subst k
                                end.
                                eapply star_implies_mono; [prove_implies_refl| |eassumption].
                                eapply implies_trans; [apply credits_star_l; try reflexivity|].
                                eapply implies_trans;
                                  [|apply star_implies_mono;
                                    [apply credits_star_r; try reflexivity|apply implies_refl]].
                                eapply implies_trans; [|apply credits_star_r; try reflexivity].
                                erewrite (Nat.add_assoc (S (_ + S _))),
                                  (Nat.add_comm (S (_ + S _))).
                                prove_implies_refl.
                                (*apply credits_star_r. reflexivity.*) } }
                            { eapply Hspec_h_decrease_key; unfold empty, not; auto.
                              { lazymatch goal with
                                | [H' : set_equiv ?Q' _,
                                  H'' : Dijkstra_invariant _ _ ?P' _ _,
                                  H''' : ?P' = empty /\ ?Q'' = _ \/
                                    ?P' src /\ ?Q'' = neighbourhood _ _,
                                  H'''' : forall _ _,
                                    List.nth _ (_ ?LL1 ++ _::_ ?LL2) None = Some _ <-> ?f _ = _,
                                  H''''' : forall _ _,
                                    List.nth _ (_ ?LL1' ++ _::_ ?LL2') None = Some _ <-> ?f' _ = _,
                                  H6 : forall _, i' = _ \/ _ -> ?f _ = ?D' _,
                                  H7 : forall _, i' = _ \/ _ -> ?f' _ = ?pred' _,
                                  H8 : forall _, List.In _ _ -> ?f _ = ?D'' _,
                                  H9 : forall _, List.In _ _ -> ?f' _ = ?pred'' _,
                                  H10 : is_elem_weighted_unique_list _ _ (_++(i',w')::_),
                                  H11 : is_nat_fun_of_val_list ?LD' ?D',
                                  H12 : List.nth x_min ?LD' None = _
                                  |- _] =>
                                  rename P' into P, Q' into Q, Q'' into N, LL1 into L1,
                                    LL2 into L2, LL1' into L1', LL2' into L2', f into fD,
                                    f' into fD', D' into D, pred' into pred, D'' into D2,
                                    pred'' into pred2, LD' into LD,
                                    H' into HeqQ, H'' into HDij_inv, H''' into Hor,
                                    H'''' into HD_nth, H''''' into Hpred_nth,
                                    H6 into HD, H7 into Hpred, H8 into HD2, H9 into Hpred2,
                                    H10 into Hneighs, H11 into Hfun, H12 into Hnth
                                end.
                                destruct (fD i') eqn:HfD; trivial.
                                apply HD_nth in HfD.
                                rewrite List.app_nth2, List.map_length, Hlen3, Nat.sub_diag in HfD.
                                { simpl in HfD. injection HfD. lia. }
                                { rewrite List.map_length. lia. } }
                              { lazymatch goal with
                                | [H' : set_equiv ?Q' _,
                                  H'' : Dijkstra_invariant _ _ ?P' _ _,
                                  H''' : ?P' = empty /\ ?Q'' = _ \/
                                    ?P' src /\ ?Q'' = neighbourhood _ _,
                                  H'''' : forall _ _,
                                    List.nth _ (_ ?LL1 ++ _::_ ?LL2) None = Some _ <-> ?f _ = _,
                                  H''''' : forall _ _,
                                    List.nth _ (_ ?LL1' ++ _::_ ?LL2') None = Some _ <-> ?f' _ = _,
                                  H6 : forall _,
                                    i' = _ \/ List.In _ (_ ?Ns1') -> ?f _ = ?D' _,
                                  H7 : forall _,
                                    i' = _ \/ List.In _ (_ ?Ns1') -> ?f' _ = ?pred' _,
                                  H8 : forall _, List.In _ (_ ?Ns2') -> ?f _ = ?D'' _,
                                  H9 : forall _, List.In _ (_ ?Ns2') -> ?f' _ = ?pred'' _,
                                  H10 : is_elem_weighted_unique_list _ _ (_++(i',w')::_),
                                  H11 : is_nat_fun_of_val_list ?LD' ?D',
                                  H12 : List.nth x_min ?LD' None = _,
                                  H14 : forall _, ~ _ -> ?f _ = ?D'' _,
                                  H15 : forall _, ~ _ -> ?f' _ = ?pred'' _
                                    |- _] =>
                                  rename P' into P, Q' into Q, Q'' into N, LL1 into L1,
                                    LL2 into L2, LL1' into L1', LL2' into L2', f into fD,
                                    f' into fD', D' into D, pred' into pred, D'' into D2,
                                    pred'' into pred2, LD' into LD, Ns1' into Ns1, Ns2' into Ns2,
                                    H' into HeqQ, H'' into HDij_inv, H''' into Hor,
                                    H'''' into HD_nth, H''''' into Hpred_nth,
                                    H6 into HD, H7 into Hpred, H8 into HD2, H9 into Hpred2,
                                    H10 into Hneighs, H11 into Hfun, H12 into Hnth,
                                    H14 into HD2out, H15 into Hpred2out
                                end.
                                lazymatch goal with
                                | [H : List.nth x_min _ _ = Some (Int (Z.of_nat ?x)) |- _] =>
                                  rename x into y_min
                                end.
                                assert (D x_min = Some y_min) as HDmin.
                                { unfold is_nat_fun_of_val_list, fun_of_list in Hfun.
                                  destruct Hfun as (?&Hfun). apply Hfun. assumption. }
                                intros u [HP|<-].
                                { destruct Hor as [(->&->)|(Hor1&Hor2)].
                                  { contradiction. }
                                  { assert (fD u = D u) as ->.
                                    { assert (Decidable.decidable (List.In u (i'::List.map fst Ns1)))
                                        as [Hin|Hnin].
                                      { apply decidable_in, Nat.eq_decidable. }
                                      { auto. }
                                      { erewrite <- Dijkstra_invariant_distance_decrease_in_P
                                          with (D := D) (D' := D2); eauto.
                                        assert (Decidable.decidable (List.In u (List.map fst Ns2)))
                                          as [Hin2|Hnin2].
                                        { apply decidable_in, Nat.eq_decidable. }
                                        { apply HD2. assumption. }
                                        { apply HD2out. rewrite List.in_app_iff. tauto. } } }
                                    edestruct Dijkstra_invariant_D_is_some_in_set
                                      with (v := u) as (?&Hd); eauto.
                                    rewrite Hd. assert (le (D u) (D x_min)).
                                    { eapply Dijkstra_invariant_D_ge_in_neighbourhood; eauto.
                                      unfold min_cost_elem in Hmincost. destruct Hmincost.
                                      subst N. assumption. }
                                    rewrite Nat2Z.id. transitivity y_min.
                                    { rewrite Hd, HDmin in *. simpl in *. assumption. }
                                    { lia. } } }
                                { rewrite HD2out.
                                  { erewrite distance_decrease_min; eauto. rewrite HDmin. lia. }
                                  { unfold is_elem_weighted_unique_list, is_elem_weighted_list,
                                      neighbours in Hneighs.
                                    destruct Hneighs as (Hneighs&?).
                                    change (i'::List.map fst ?L)%list with (List.map fst ((i',w')::L)).
                                    rewrite <- List.map_app, List.in_map_iff. intros ((?&?)&<-&Hin).
                                    rewrite Hneighs in Hin. simpl in Hin. destruct Hin.
                                    unfold is_irreflexive, not in *. eauto. } } }
                              { lazymatch goal with
                                | [ H : set_equiv ?P ?P' |- ?P _] =>
                                  unfold set_equiv in H |- *; rewrite H
                                end.
                                unfold set_sum, set_remove. left. split.
                                { lazymatch goal with
                                  | [H : (Z.of_nat ?m_cost + Z.of_nat w' < x')%Z,
                                    H' : List.nth x_min ?L None = Some (Int (_ ?m_cost)),
                                    H'' : is_nat_fun_of_val_list ?L ?D
                                    |- _] =>
                                    assert (D x_min = Some m_cost) as HDSome;
                                    [unfold is_nat_fun_of_val_list, fun_of_list in H'';
                                      destruct H'' as (?&H''); apply H''; eassumption|]
                                  end.
                                  lazymatch goal with
                                  | [H : Dijkstra_invariant _ _ _ _ _ |- _] =>
                                    eapply Dijkstra_invariant_if_D_some with
                                      (x := i') (pr2 := x_min) in H
                                      as [(HP&?)|(?&?)]
                                  end.
                                  { lazymatch goal with
                                    | [H : (_ = empty /\ _ = set_sum empty _) \/
                                        (_ src /\ _ = neighbourhood _ _)
                                        |- _] =>
                                      destruct H as [(->&->)|(Hin&->)]
                                    end.
                                    { unfold set_sum, empty, single. auto. }
                                    { exfalso. rewrite HP in Hin. unfold empty in Hin.
                                      assumption. } }
                                  { lazymatch goal with
                                    | [H : (_ = empty /\ _ = set_sum empty _) \/
                                        (_ src /\ _ = neighbourhood _ _)
                                        |- _] =>
                                      destruct H as [(->&->)|(Hin&->)]
                                    end.
                                    { contradiction. }
                                    { assumption. } }
                                  { lazymatch goal with
                                    | [Heq : forall _, _ -> ?f _ = ?D _,
                                      Hfun : forall _ _, _ <-> ?f _ = _
                                      |- ?D i' = _] =>
                                      rewrite <- Heq; auto; apply Hfun
                                    end.
                                    rewrite List.app_nth2;
                                    rewrite List.map_length; subst i'; [|lia].
                                    rewrite Nat.sub_diag. simpl. repeat f_equal.
                                    symmetry. apply Z2Nat.id. lia. }
                                  { lazymatch goal with
                                    | [H : is_elem_weighted_unique_list _ _ (_++(i',w')::_)%list
                                      |- _] =>
                                      unfold is_elem_weighted_unique_list,
                                        is_elem_weighted_list, neighbours in H;
                                      edestruct H as (((?&?)&?)&?); [|eassumption]
                                    end.
                                    { apply List.in_or_app. simpl. auto. } }
                                  { eassumption. }
                                  { lazymatch goal with
                                    | [H : is_elem_weighted_unique_list _ _ (_++(i',w')::_)%list
                                      |- _] =>
                                      unfold is_elem_weighted_unique_list,
                                        is_elem_weighted_list, neighbours in H;
                                      edestruct H as (((?&Heq)&?)&?)
                                    end.
                                    { apply List.in_or_app. simpl. auto. }
                                    { rewrite <- Heq. lia. } } }
                                { lazymatch goal with
                                  | [H : is_elem_weighted_unique_list _ _ (_++(i',w')::_)%list
                                    |- _] =>
                                    unfold is_elem_weighted_unique_list,
                                      is_elem_weighted_list, neighbours in H;
                                    edestruct H as (((?&?)&?)&?)
                                  end.
                                  { apply List.in_or_app. simpl. auto. }
                                  { intros ->.
                                    lazymatch goal with
                                    | [H : is_irreflexive _ |- _] =>
                                      unfold is_irreflexive in H; eapply H
                                    end.
                                    eassumption. } } } }
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
                      ++++ triple_pull_pure. simpl.
                        repeat change (S (?x + ?y)) with (S x + y).
                        lazymatch goal with
                        | [_ : heap_time_bound _ _ ?t
                          |- triple _ ($10 <*> ($ (_ + (_ + ?t')) <*> _)) _] =>
                          erewrite (Nat.add_assoc _ _ t'), (Nat.add_comm _ t')
                        end.
                        simpl. do 6 rewrite Nat.add_succ_r.
                        repeat change (S (?x + ?y)) with (S x + y).
                        eapply triple_weaken.
                        { apply star_implies_mono; [prove_implies_refl|].
                          apply star_implies_mono; [|prove_implies_refl].
                          apply credits_star_r. reflexivity. }
                        { prove_implies_refl. }
                        triple_reorder_credits. apply triple_value_implies.
                        apply implies_spec. intros.
                        repeat apply star_assoc_r. swap_star.
                        lazymatch goal with
                        | [H : _ ?c ?m |- _ ?c ?m] =>
                          eapply star_assoc_l in H;
                          eapply star_implies_mono in H;
                          eauto
                        end.
                        { apply implies_spec. intros. solve_star.
                          eapply credits_star_l; [reflexivity|].
                          eassumption. }
                        apply implies_spec. intros. apply star_pure_l.
                        split; auto. do 9 eexists.
                        lazymatch goal with
                        | [_ : heap_time_bound _ _ ?t |- _] => exists (2*t)
                        end.
                        lazymatch goal with
                        | [H : (_<*>(_<*>(_<*>(_ <*>array_content ?L ?a)))) ?c ?m,
                           Hfun_a : is_nat_fun_of_val_list ?L _,
                           Hfun_b : is_nat_fun_of_val_list _ _
                          |- (_ <*> array_content _ ?a <*> _ <*> _) ?c ?m] =>
                          repeat apply star_assoc_l;
                          apply star_pure_l; split_all; [exact Hfun_a|exact Hfun_b|]
                        end.
                        rewrite Z.ltb_nlt in *. solve_star.
                        { split_all; try eassumption; eauto.
                          { intros i'' Hin.
                            rewrite List.map_app in Hin.
                            apply List.in_app_or in Hin as [Hin|Heq].
                            { lazymatch goal with
                              | [H : forall _, List.In _ _ -> ?f _ = ?D' _
                                |- ?f i'' = ?D' i''] =>
                                apply H
                              end.
                              assumption. }
                            { simpl in Heq. destruct Heq as [<-|[]].
                              lazymatch goal with
                              | [H : distance_decrease g x_min ?D ?D' ?pred ?pred',
                                Hneigh : is_elem_weighted_unique_list _ _
                                  (?L1++(i',w')::?L2)%list,
                                HD : forall _, _ \/ _ -> ?f _ = ?D _,
                                HDSome : forall _ _, _ <-> ?f _ = Some _,
                                Hfun : is_nat_fun_of_val_list ?L ?D,
                                Hfun' : is_nat_fun_of_val_list ?L' ?f,
                                Hlist : List.nth x_min ?L None = Some (Int (Z.of_nat ?n))
                                |- _ = ?g i'] =>
                                unify D' g; unfold distance_decrease in H;
                                unfold is_elem_weighted_unique_list,
                                  is_elem_weighted_list, neighbours in Hneigh;
                                unfold is_nat_fun_of_val_list, fun_of_list
                                  in Hfun, Hfun';
                                destruct Hfun as (?&Hfun); destruct Hfun' as (?&Hfun');
                                rewrite List.map_app in Hneigh; simpl in Hneigh;
                                destruct Hneigh as (Hneigh&Hnin%List.NoDup_remove_2);
                                specialize Hneigh with i' w';
                                rewrite List.in_app_iff in Hneigh; simpl in Hneigh;
                                destruct Hneigh as ((HE&HW)&_); auto;
                                destruct H as (dv&Hdv&Hvalue);
                                edestruct Hvalue with i' as ((?&(?&(->&?)))&?);
                                [assumption|
                                  rewrite <- HD, <- Hfun', List.app_nth2,
                                  List.map_length, Hlen3, Nat.sub_diag; auto;
                                  [simpl; do 2 f_equal; rewrite Z2Nat.id; auto; lia|
                                    rewrite List.map_length; lia]|
                                  rewrite <- HW; apply Hfun in Hdv;
                                  rewrite Hdv in Hlist;
                                  injection Hlist as ->%Nat2Z.inj; lia|]
                              end.
                              auto. } }
                          { intros i'' Hin.
                            rewrite List.map_app in Hin.
                            apply List.in_app_or in Hin as [Hin|Heq].
                            { lazymatch goal with
                              | [H : forall _, List.In _ _ -> ?f _ = ?D' _
                                |- ?f i'' = ?D' i''] =>
                                apply H
                              end.
                              assumption. }
                            { simpl in Heq. destruct Heq as [<-|[]].
                              lazymatch goal with
                              | [H : distance_decrease g x_min ?D ?D' ?pred ?pred',
                                Hneigh : is_elem_weighted_unique_list _ _
                                  (?L1++(i',w')::?L2)%list,
                                HD : forall _, _ \/ _ -> ?f _ = ?D _,
                                HDSome : forall _ _, _ <-> ?f _ = Some _,
                                Hfun : is_nat_fun_of_val_list ?L ?D,
                                Hfun' : is_nat_fun_of_val_list ?L' ?f,
                                Hlist : List.nth x_min ?L None = Some (Int (Z.of_nat ?n)),
                                Hpred : forall _, _ \/ _ -> ?f' _ = ?pred _,
                                HpredSome : forall _ _, _ <-> ?f' _ = Some _
                                |- _ = ?g i'] =>
                                unify pred' g; unfold distance_decrease in H;
                                unfold is_elem_weighted_unique_list,
                                  is_elem_weighted_list, neighbours in Hneigh;
                                unfold is_nat_fun_of_val_list, fun_of_list
                                  in Hfun, Hfun';
                                destruct Hfun as (?&Hfun); destruct Hfun' as (?&Hfun');
                                rewrite List.map_app in Hneigh; simpl in Hneigh;
                                destruct Hneigh as (Hneigh&Hnin%List.NoDup_remove_2);
                                specialize Hneigh with i' w';
                                rewrite List.in_app_iff in Hneigh; simpl in Hneigh;
                                destruct Hneigh as ((HE&HW)&_); auto;
                                destruct H as (dv&Hdv&Hvalue);
                                edestruct Hvalue with i' as ((?&(?&(?&->)))&?);
                                [assumption|
                                  rewrite <- HD, <- Hfun', List.app_nth2,
                                  List.map_length, Hlen3, Nat.sub_diag; auto;
                                  [simpl; do 2 f_equal; rewrite Z2Nat.id; auto; lia|
                                    rewrite List.map_length; lia]|
                                  rewrite <- HW; apply Hfun in Hdv;
                                  rewrite Hdv in Hlist;
                                  injection Hlist as ->%Nat2Z.inj; lia|]
                              end.
                              eauto. } }
                          { intros i'' Hnin.
                            destruct Nat.eqb_spec with i'' i'.
                            { exfalso. subst i''.
                              apply Hnin. rewrite List.map_app, List.in_app_iff.
                              simpl. auto. }
                            { rewrite List.map_app in Hnin. simpl in Hnin. eauto. } }
                          { intros i'' Hnin.
                            destruct Nat.eqb_spec with i'' i'.
                            { exfalso. subst i''.
                              apply Hnin. rewrite List.map_app, List.in_app_iff.
                              simpl. auto. }
                            { rewrite List.map_app in Hnin. simpl in Hnin. eauto. } } }
                        { lazymatch goal with
                          | [ H : set_equiv ?P ?R,
                              H' : (_ <*> (_ <*> (_ <*> (_ <*>
                                is_heap n C _ ?Q _ _ _ <*> _ <*> _ <*> _)))) _ _
                            |- set_equiv ?Q' _] =>
                            unify Q Q'; unfold set_sum;
                            unfold set_equiv in H |- *; intros; rewrite H
                          end.
                          unfold set_sum, single. rewrite List.map_app, List.in_app_iff.
                          simpl. split; [clear; tauto|].
                          lazymatch goal with
                          | [|- _ \/ ~ ?P _ /\ _ -> _ \/ ~ ?P _ /\ _] =>
                            assert (P i') as Hi'P
                          end.
                          { lazymatch goal with
                            | [H : is_elem_weighted_unique_list _ _ (?L1++(i',w')::?L2),
                              H' : forall _, i' = _ \/ _ -> ?f _ = ?D _,
                              H'' : forall _ _, List.nth _ _ _ = _ <-> ?f _ = _,
                              H''' : Dijkstra_invariant ?D ?pred _ _ _
                              |- _] =>
                              rename H into Hneigh, H' into HD, H'' into Hnth,
                                H''' into Hinv;
                              unfold is_elem_weighted_unique_list,
                                is_elem_weighted_list, neighbours in Hneigh;
                              destruct Hneigh as (Hin&Hnodup);
                              specialize Hin with i' w';
                              rewrite List.in_app_iff in Hin; simpl in Hin;
                              destruct Hin as ((HE&->)&_); auto;
                              assert (D i' = Some (Z.to_nat x')) as Heq
                            end.
                            { rewrite <- HD, <- Hnth, List.app_nth2; auto;
                                rewrite List.map_length, Hlen3; auto.
                              rewrite Nat.sub_diag. simpl. do 2 f_equal. lia. }
                            eapply Dijkstra_invariant_if_D_some_neighbour_le_W; eauto.
                            { unfold closest_neighbour.
                              lazymatch goal with
                              | [H : (_ = empty /\ _ = set_sum empty _) \/
                                  (_ src /\ _ = neighbourhood _ _)
                                |- _] =>
                                destruct H as [(->&->)|(?&->)]
                              end.
                              { eapply Dijkstra_invariant_D_some in Hinv
                                  as [Hi'|[[]|(?&?&[]&?)]];
                                  eauto.
                                subst src. unfold min_cost_elem in Hmincost.
                                destruct Hmincost as (Hsingle&_).
                                unfold set_sum, single, empty in Hsingle.
                                destruct Hsingle as [[]| ->]. exfalso.
                                unfold is_irreflexive, empty, not in *. eauto. }
                              { eassumption. } }
                            { lazymatch goal with
                              | [H : is_nat_fun_of_val_list ?L ?D,
                                H' : List.nth _ _ _ = _,
                                _ : Dijkstra_invariant ?D ?pred _ _ _
                                |- _] =>
                                rename H into Hlist, H' into Hnth'
                              end.
                              unfold is_nat_fun_of_val_list, fun_of_list in Hlist.
                              destruct Hlist as (?&Hlist). rewrite Hlist in Hnth'.
                              eassumption. }
                            { lia. } }
                          intros [Hin | (Hnin&[Hin| [<-|[]]])];
                            [revert Hin|revert Hnin Hin|revert Hnin Hi'P];
                            clear; tauto. }
                        { split_all; eauto. unfold set_sum. intros HnIn.
                          lazymatch goal with
                          | [H : ~(?P' i' \/ ?Q' i'),
                            H' : set_equiv ?Q' _,
                            H'' : Dijkstra_invariant _ _ ?P' _ _,
                            H''' : ?P' = empty /\ ?Q'' = _ \/
                              ?P' src /\ ?Q'' = neighbourhood _ _,
                            H'''' : forall _ _,
                              List.nth _ (_ ?LL1 ++ _::_ ?LL2) None = Some _ <-> ?f _ = _,
                            H''''' : forall _ _,
                              List.nth _ (_ ?LL1' ++ _::_ ?LL2') None = Some _ <-> ?f' _ = _,
                            H6 : forall _, i' = _ \/ _ -> ?f _ = ?D' _,
                            H7 : forall _, i' = _ \/ _ -> ?f' _ = ?pred' _,
                            H8 : forall _, List.In _ _ -> ?f _ = ?D'' _,
                            H9 : forall _, List.In _ _ -> ?f' _ = ?pred'' _,
                            H10 : is_elem_weighted_unique_list _ _ (_++(i',w')::_),
                            H11 : is_nat_fun_of_val_list ?LD' ?D',
                            H12 : List.nth x_min ?LD' None = _
                            |- _] =>
                            rename P' into P, Q' into Q, Q'' into N, LL1 into L1,
                              LL2 into L2, LL1' into L1', LL2' into L2', f into fD,
                              f' into fD', D' into D, pred' into pred, D'' into D2,
                              pred'' into pred2, LD' into LD,
                              H' into HeqQ, H'' into HDij_inv, H''' into Hor,
                              H'''' into HD_nth, H''''' into Hpred_nth,
                              H6 into HD, H7 into Hpred, H8 into HD2, H9 into Hpred2,
                              H10 into Hneighs, H11 into Hfun, H12 into Hnth
                          end.
                          exfalso. apply HnIn. unfold set_equiv in HeqQ. left.
                          (*apply HeqQ. unfold set_sum, set_remove. left. split.*)
                          { unfold is_elem_weighted_unique_list,
                              is_elem_weighted_list, neighbours in Hneighs.
                            destruct Hneighs as (Hneighs&?). specialize Hneighs with i' w'.
                            rewrite List.in_app_iff in Hneighs. simpl in Hneighs.
                            destruct Hneighs as ((?&HW)&?); auto.
                            destruct Hor as [(->&->)|(Hin&->)].
                            { eapply Dijkstra_invariant_D_some with (x := i') in HDij_inv
                                as [<- |[[]|(?&?&[]&?)]];
                                eauto.
                              { unfold min_cost_elem in Hmincost.
                                destruct Hmincost as (Hsingle&_).
                                unfold set_sum, single, empty in Hsingle.
                                destruct Hsingle as [[]| ->]. exfalso.
                                unfold is_irreflexive, empty, not in *. eauto. }
                              { rewrite <- HD, <- HD_nth; auto.
                                rewrite List.app_nth2; rewrite List.map_length, Hlen3;
                                  [|lia].
                                rewrite Nat.sub_diag. simpl. repeat f_equal. symmetry.
                                apply Z2Nat.id. lia. } }
                            { unfold min_cost_elem, set_sum, single, empty
                                in Hmincost |- *.
                              eapply Dijkstra_invariant_if_D_some_neighbour_le_W
                                with (u := x_min) (v := i') (dv := Z.to_nat x')
                                in HDij_inv.
                              { assumption. }
                              { unfold closest_neighbour. assumption. }
                              { assumption. }
                              { unfold is_nat_fun_of_val_list, fun_of_list in Hfun.
                                destruct Hfun as (?&Hfun). apply Hfun. eassumption. }
                              { rewrite <- HD, <- HD_nth; auto.
                                rewrite List.app_nth2; rewrite List.map_length, Hlen3;
                                  [|lia].
                                rewrite Nat.sub_diag. simpl. repeat f_equal. lia. }
                              { lia. } } } }
                        swap_star. apply star_assoc_l. swap_star_ctx. normalize_star.
                        swap_star_ctx. normalize_star. simpl. rewrite Nat.add_0_r.
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
                        is_heap _ _ _ _ _ ?[p] _ <*> $?p <*> array_content _ _),
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
                      apply implies_spec. intros. normalize_star. do 14 eexists.
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
                        | [|- triple _ ($ S (c_l_tail + ?cr1 + ?cr2 + ?cr3) <*> _) _] =>
                          rewrite <- (Nat.add_assoc c_l_tail cr1 cr2),
                            <- (Nat.add_assoc c_l_tail (cr1+cr2) cr3)
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
                          repeat lazymatch goal with
                          | [H : _ /\ _ |- _] => destruct H
                          end.
                          swap_star. solve_star. swap_star.
                          (* only that part of solve_star works here *)
                          repeat lazymatch goal with
                          | [|- ((_ <*> _) <*> _) ?c ?m ] =>
                            apply star_assoc_l; eauto
                          | [|- ((<exists> _, _) <*> _) ?c ?m ] =>
                            apply star_exists_l; eexists; eauto
                          | [|- (<exists> _, _) ?c ?m] => eexists
                          end.
                          repeat (apply star_pure_l; split_all).
                          { lazymatch goal with
                            | [H : is_elem_weighted_unique_list _ _
                                (?L1++?x::?L2)%list
                              |- is_elem_weighted_unique_list _ _ ?L] =>
                              unify ((L1++[x])++L2)%list L
                            end.
                            rewrite <- List.app_assoc. simpl. eassumption. }
                          { rewrite List.app_length. simpl. rewrite Nat.add_1_r.
                            apply f_equal. eassumption. }
                          { lazymatch goal with
                            | [H : S ?n = ?k |- ?n = _] =>
                              destruct k; [discriminate|]; injection H; auto
                            end. }
                          { eassumption. }
                          { eassumption. }
                          { eauto. }
                          { eauto. }
                          { eauto. }
                          { eauto. }
                          { rewrite <- List.app_assoc. simpl. eauto. }
                          { rewrite <- List.app_assoc. simpl. eauto. }
                          { eassumption. }
                          { eassumption. }
                          { eassumption. }
                          { eassumption. }
                          { lia. }
                          { assumption. }
                          { eassumption. }
                          swap_star. solve_star. (*swap_star. solve_star.*)
                          eapply star_implies_mono; [prove_implies_refl| |eassumption].
                          prove_implies_rev.
                          repeat change (?x + ?y*?x) with (S y * x).
                          repeat change (S (?x + ?y)) with (S x + y).
                          lazymatch goal with
                          | [|- _ ->> ($3 <*> $?c) <*> _] =>
                            eassert (?[y] = c) as _ by reflexivity
                          end.
                          instantiate (cm2 := 3 + (S (S c_is_nil)) + ?[ccm2]).
                          instantiate (ccm2 := ?[cm2]). instantiate (cn1_t := 0).
                          instantiate (cn2 := 2+?[ccn2]). instantiate (ccn2 := ?[cn2]).
                          lazymatch goal with
                          | [H : ?s' + _ <= n
                            |- $(_ + ?c*(n-(?s'+1+?s1'))*?t0 + _) <*>
                              ($?k1'<*>($?t'<*>$?k2')) ->>
                              _ <*> $(_ + (_ + _*(n-(_+1+?s2'))*_))] =>
                            instantiate (y := k1'+k2'+?cm2+(s2'-s1')*?[yy]);
                            rename s1' into s1, s2' into s2, k1' into k1,
                              t' into t, k2' into k2, s' into s
                          end.
                          lazymatch goal with
                          | [H : set_sum ?P' ?Q' i' -> t = _,
                            H' : ~ set_sum ?P' ?Q' i' -> t = 0
                            |- _] =>
                            rename H into HifIn, H' into HifNot, P' into P, Q' into Q
                          end.
                          assert (Decidable.decidable (set_sum P Q i')) as [HIn|HNot] (*by admit*).
                          { unfold set_sum.
                            apply Decidable.dec_or; eapply decidable_if_finite;
                              eauto using Nat.eq_decidable. }
                          { lazymatch goal with
                            | [H : set_equiv ?P' _, H' : set_equiv ?Q _,
                              H'' : is_set_size ?P' s1, H''' : is_set_size ?Q s2
                              |- _] =>
                              rename H into HequivR, H' into HequivQ, P' into R,
                                H'' into HsizeR, H''' into HsizeQ
                            end.
                          { assert (s2 = s1) (*by admit*).
                            { eapply is_set_size_unique, equiv_set_size; eauto.
                              unfold set_equiv in HequivQ, HequivR |- *. intros u.
                              rewrite HequivQ, HequivR. unfold set_sum in HIn |- *.
                              destruct HIn as [HP|HR].
                              { apply or_iff_compat_l.
                                rewrite List.map_app, List.in_app_iff. simpl.
                                revert HP. clear. intuition. subst. tauto. }
                              { apply HequivR in HR. unfold set_sum in HR.
                                revert HR. clear. rewrite List.map_app, List.in_app_iff.
                                simpl. intuition; subst; auto. } }
                            rewrite HifIn; auto.
                            (* folding the lhs of the entailment *)
                            eapply implies_trans;
                              [apply star_implies_mono;
                                [prove_implies_refl
                                |apply star_implies_mono;
                                  [prove_implies_refl|apply credits_star_l]]|];
                              try reflexivity.
                            eapply implies_trans;
                              [apply star_implies_mono;
                                [prove_implies_refl|apply credits_star_l]|];
                              try reflexivity.
                            eapply implies_trans; [apply credits_star_l|];
                              try reflexivity.
                            (* folding the rhs of the entailment *)
                            eapply implies_trans;
                              [|apply star_implies_mono;
                                [apply credits_star_r|prove_implies_refl]];
                              try reflexivity.
                            eapply credits_star_r. lia. } }
                          { assert (s2 = s1+1) as -> (*by admit*).
                            { lazymatch goal with
                              | [H : set_equiv ?P' _, H' : set_equiv ?Q' _,
                                H'' : is_set_size ?P' s1, H''' : is_set_size ?Q' s2
                                |- _] =>
                                rename H into HequivQ, H' into HequivR, Q' into R,
                                  H'' into HsizeQ, H''' into HsizeR
                              end.
                              eapply is_set_size_unique, equiv_set_size
                                with (P := add_single Q i'); eauto.
                              { unfold set_equiv, add_single, set_sum, single
                                  in HNot, HequivQ, HequivR |- *.
                                intros u.
                                rewrite HequivQ, HequivR, List.map_app, List.in_app_iff.
                                simpl. revert HNot. clear. intuition. subst. auto. }
                              { unfold add_single.
                                apply disjoint_sum_size; auto using single_set_size.
                                unfold are_disjoint_sets, set_sum, single in HNot |- *.
                                intros ? (?&<-). auto. } }
                              rewrite HifNot; auto.
                              (* folding the lhs of the entailment *)
                              eapply implies_trans;
                                [apply star_implies_mono;
                                  [prove_implies_refl
                                  |apply star_implies_mono;
                                    [prove_implies_refl|apply credits_star_l]]|];
                                try reflexivity.
                              eapply implies_trans;
                                [apply star_implies_mono;
                                  [prove_implies_refl|apply credits_star_l]|];
                                try reflexivity.
                              eapply implies_trans; [apply credits_star_l|];
                                try reflexivity.
                              (* folding the rhs of the entailment *)
                              eapply implies_trans;
                                [|apply star_implies_mono;
                                  [apply credits_star_r|prove_implies_refl]];
                                try reflexivity.
                              eapply credits_star_r.
                              instantiate (cn2 := 0).
                              assert (n > s+1+s1) (*by admit*).
                              { unfold gt, lt. rewrite <- Nat.add_assoc, (Nat.add_comm 1 s1).
                                change (1+s + (s1 + 1) <= n).
                                lazymatch goal with
                                | [H : set_equiv Q _ |- _] => rename H into HeqQ
                                end.
                                unfold set_equiv, set_sum, set_remove in HeqQ.
                                lazymatch goal with
                                | [H : P = empty /\ _ = _ \/
                                    P src /\ _ = neighbourhood _ _ |- _] =>
                                  rename H into Hor
                                end.
                                lazymatch goal with
                                | [H : is_elem_weighted_unique_list _ _ (?L1' ++ (i',w')::?L2')
                                  |- _] =>
                                  rename H into Hneighs, L1' into L1, L2' into L2
                                end.
                                unfold is_elem_weighted_unique_list,
                                  is_elem_weighted_list, neighbours in Hneighs.
                                destruct Hneighs as (Hneighs&?).
                                lazymatch goal with
                                | [H : set_equiv ?R' _, H' : is_set_size ?R' ?s
                                  |- _ + ?s <= _] =>
                                  rename H into HeqR, H' into HsizeR, R' into R
                                end.
                                assert (are_disjoint_sets (add_single P x_min) R).
                                { unfold are_disjoint_sets, add_single, set_sum, single.
                                  intros u ([HP|<-]&HR); apply HeqR in HR.
                                  { destruct HR as [(?&?)|(?&?)]; auto.
                                    destruct Hor as [(->&->)|(?&->)].
                                    { unfold empty, single, set_sum in *. auto. }
                                    { unfold neighbourhood in *. tauto. } }
                                  { destruct HR as [(?&?)|(?&Hin)]; auto.
                                    apply List.in_map_iff in Hin as ((i''&w'')&<-&Hin).
                                    assert (List.In (i'',w'') (L1 ++ (i',w')::L2)) as Hin'.
                                    { change (?L1 ++ ?x :: ?L2)%list with (L1++[x]++L2)%list.
                                      rewrite List.app_assoc, List.in_app_iff. auto. }
                                    apply Hneighs in Hin' as (HE&?). simpl in HE.
                                    unfold is_irreflexive, not in *. eauto. } }
                                assert (is_set_size (add_single P x_min) (1+s)).
                                { rewrite Nat.add_comm. unfold add_single.
                                  eapply disjoint_sum_size; eauto using single_set_size.
                                  unfold are_disjoint_sets, single. intros u (HP&<-).
                                  destruct Hor as [(->&->)|(?&->)]; auto.
                                  unfold min_cost_elem, neighbourhood in Hmincost.
                                  tauto. }
                                subst n.
                                eapply subset_size_le with (P' := set_sum (add_single P x_min) R);
                                  eauto.
                                { intros. eapply decidable_if_finite.
                                  { apply Nat.eq_decidable. }
                                  { eapply disjoint_sum_size; eauto. } }
                                { apply disjoint_sum_size; auto. }
                                { unfold is_subset, add_single, single, set_sum in *.
                                  intros u [[HP|<-]|HQ]; eauto. specialize Hneighs with i' w'.
                                  destruct Hneighs as ((?%E_closed1&?)&?); auto.
                                  apply List.in_or_app. simpl. auto. } }
                                  assert (n - (s+1+s1) = n-(s+1+(s1+1)) + 1) as -> by lia.
                                  simpl. repeat f_equal. instantiate (yy := 0). lia. } }
                                { eassumption. }
              --- repeat lazymatch goal with
                  | [H : is_nat_fun_of_val_list _ _ |- _] => clear H
                  end.
                clear Hlen1 Hlen2.
                triple_reorder_exists. repeat triple_pull_exists.
                triple_reorder_pure. repeat triple_pull_pure.
                instantiate (cn1_0 := 4+?[ccn1_0]). instantiate (ccn1_0 := ?[cn1_0]).
                triple_reorder_credits. triple_pull_credits 4.
                triple_pull_1_credit.
                eapply triple_weaken, triple_free.
                { prove_implies_rev. }
                { apply implies_post_spec. intros. normalize_star. solve_star.
                  eassumption. }
                solve_simple_value. revert_implies. prove_implies.
                apply implies_spec. intros.
                repeat lazymatch goal with
                | [H : _ /\ _ |- _] => destruct H
                end.
                rewrite Bool.negb_false_iff, Nat.eqb_eq in * |-.
                lazymatch goal with
                | [H : forall _, List.In _ _ -> ?f _ = ?D' _,
                  H' : forall _, List.In _ _ -> ?f' _ = ?pred' _,
                  H'' : forall _, ~ List.In _ _ -> ?f _ = ?D' _,
                  H''' : forall _, ~ List.In _ _ -> ?f' _ = ?pred' _,
                  Hdist : distance_decrease g x_min ?D ?D' ?pred ?pred'
                  |- _] =>
                  rename Hdist into Hdist_dec; rename H into HD;
                  rename H' into Hpred; rename H'' into HD';
                  rename H''' into Hpred';
                  assert (distance_decrease g x_min D f pred f');
                    [|clear Hdist_dec]
                end.
                { unfold distance_decrease in Hdist_dec |- *.
                  destruct Hdist_dec as (?&->&Hd). eexists. split; auto.
                  intros u. specialize Hd with u as (HdE&HdnE). split.
                  { intros.
                    lazymatch goal with
                    | [H : is_elem_weighted_unique_list _ _ (?L1++?L2),
                      H' : List.length ?L2 = ?l,
                      H'' : ?l = 0
                      |- _] =>
                      rewrite H'' in H'; destruct L2; simpl in H';
                      [|discriminate]; rewrite List.app_nil_r in H;
                      unfold is_elem_weighted_unique_list,
                        is_elem_weighted_list, neighbours in H;
                      destruct H as (Hneigh&Hnodup);
                      assert (List.In u (List.map fst L1))
                    end.
                    { apply List.in_map_iff. eexists. rewrite Hneigh. simpl.
                      auto. }
                    destruct HdE as (HdNone&HdSome); auto. split.
                    { rewrite HD, Hpred; auto. }
                    { intros du. specialize HdSome with du.
                      rewrite HD, Hpred; auto. } }
                  { intros.
                    lazymatch goal with
                    | [H : is_elem_weighted_unique_list _ _ (?L1++?L2),
                      H' : List.length ?L2 = ?l,
                      H'' : ?l = 0
                      |- _] =>
                      rewrite H'' in H'; destruct L2; simpl in H';
                      [|discriminate]; rewrite List.app_nil_r in H;
                      unfold is_elem_weighted_unique_list,
                        is_elem_weighted_list, neighbours in H;
                      destruct H as (Hneigh&Hnodup);
                      assert (~ List.In u (List.map fst L1))
                    end.
                    { rewrite List.in_map_iff. intros ((?&?)&Hfst&Hin).
                      rewrite Hneigh in Hin. simpl in Hfst. rewrite Hfst in Hin.
                      tauto. }
                    rewrite HD', Hpred'; auto; rewrite List.app_nil_r; auto. } }
                lazymatch goal with
                | [H : (_ = empty /\ _ = set_sum empty _) \/
                    (_ src /\ _ = neighbourhood _ _)
                  |- _] =>
                  destruct H as [(->&->)|(?&->)]
                end.
                { unfold min_cost_elem, set_sum, empty, single in Hmincost.
                  destruct Hmincost as ([[]| ->]&_).
                  repeat lazymatch goal with
                  | [|- ((_ <*> _) <*> _) ?c ?m ] =>
                    apply star_assoc_l; eauto
                  | [|- (<[_]> <*> _) ?c ?m ] =>
                    apply star_pure_l; split_all
                  | [|- ((<exists> _, _) <*> _) ?c ?m ] =>
                    apply star_exists_l; eexists; eauto
                  | [|- (<exists> _, _) ?c ?m] => eexists
                  end;
                  try lazymatch goal with
                  [|- Dijkstra_invariant _ _ _ _ _] =>
                    eapply valid_invariant_init; eauto
                  end;
                  try lazymatch goal with
                  [|- is_nat_fun_of_val_list _ _] => eassumption
                  end;
                  try lazymatch goal with
                  [|- List.length _ = n] => eassumption
                  end.
                  { right. unfold add_single, empty, single, set_sum. auto. }
                  { eassumption. }
                  { unfold neighbourhood, is_subset. intros ? (?&?&?&?%E_closed2).
                    assumption. }
                  { eassumption. }
                  { unfold is_set_size, neighbourhood.
                    lazymatch goal with
                    | [H : is_elem_weighted_unique_list _ _ (_++_)%list |- _] =>
                      apply elem_unique_list_of_weighted_unique in H;
                      unfold neighbours in H
                    end.
                    eexists. split.
                    { eapply equiv_elem_unique_list; eauto. unfold set_equiv.
                      unfold is_irreflexive, not in *. intros. split.
                      { intros. split.
                        { intros [[]| ->]. eauto. }
                        { eauto. } }
                      { intros (?&?&[[]| ->]&?). assumption. } }
                    { rewrite List.map_length, List.app_length.
                      lazymatch goal with
                      | [H : ?n1 = _, H' : ?n2 = _ |- ?n1 + ?n2 = _] =>
                        rewrite H, H'
                      end.
                      reflexivity. } }
                  { apply disjoint_sum_size2.
                    { unfold are_disjoint_sets, uncurry. intros []. clear. tauto. }
                    { eapply equiv_set_size, empty_set_size.
                      unfold set_equiv, empty, uncurry, add_single, set_sum, single.
                      intros (u&w). unfold is_irreflexive, not in *. split.
                      { contradiction. }
                      { intros ([[]|<-]&[[]|<-]&?). eauto. } }
                    { lazymatch goal with
                      | [H : is_elem_weighted_unique_list _ _ (?L1++?L2)%list,
                        H' : List.length ?L1 = ?y1,
                        H'' : List.length ?L2 = ?y2
                        |- _] =>
                        rename H into Hlist, L1 into N1, L2 into N2,
                          y1 into s1, y2 into s2, H' into Hs1, H'' into Hs2
                      end.
                      eapply equiv_set_size with
                        (P := cross (add_single empty x_min) (neighbours g x_min)).
                      { unfold set_equiv, cross, add_single, single, empty,
                          neighbours, set_sum, uncurry.
                        intros []. split.
                        { intros ([[]|<-]&?). split_all; auto. intros [[]|<-].
                          unfold is_irreflexive, not in *. eauto. }
                        { intros ([[]|<-]&?&?). auto. } }
                      { apply cross_size.
                        { unfold add_single.
                          apply disjoint_sum_size;
                            auto using empty_set_size, single_set_size.
                          unfold are_disjoint_sets, empty. clear. tauto. }
                        { eapply elem_weighted_unique_list_to_size.
                          eassumption. } } } }
                  { lazymatch goal with
                    | [H : is_elem_weighted_unique_list _ _ (?L1++?L2)%list,
                      H' : List.length ?L1 = ?y1,
                      H'' : List.length ?L2 = ?y2
                      |- ?x + (?y1+?y2) <= n] =>
                      rename H into Hlist, L1 into N1, L2 into N2,
                        y1 into s1, y2 into s2, H' into Hs1, H'' into Hs2
                    end.
                    eapply subset_size_le with
                      (P := V g)
                      (P' := set_sum (single x_min) (neighbours g x_min)).
                    { intros. unfold set_sum. apply Decidable.dec_or.
                      { unfold single. apply Nat.eq_decidable. }
                      { eapply decidable_if_elem_list.
                        { apply Nat.eq_decidable. }
                        { apply elem_unique_list_of_weighted_unique in Hlist.
                          unfold is_elem_unique_list in Hlist.
                          destruct Hlist as (?&?). eassumption. } } }
                    { rewrite Hn. assumption. }
                    { apply disjoint_sum_size.
                      { unfold are_disjoint_sets, single, neighbours.
                        unfold is_irreflexive, not in *. intros ? (->&?).
                        eauto. }
                      { eapply equiv_set_size; eauto. unfold set_equiv.
                        unfold set_sum, empty, single. clear. tauto. }
                      { apply elem_weighted_unique_list_to_size in Hlist.
                        rewrite List.app_length, Hs1, Hs2 in Hlist. assumption. } }
                    { unfold is_subset, set_sum, single, neighbours.
                      intros ? [<-|?]; eauto using E_closed2. } }
                  swap_star. solve_star. conormalize_star. swap_star_ctx.
                  conormalize_star. swap_star_ctx. conormalize_star.
                  swap_star_ctx. conormalize_star. swap_star_ctx.
                  conormalize_star. swap_star_ctx.
                  lazymatch goal with
                  | [H : _ ?c ?m |- _ ?c ?m] => apply star_assoc_l in H
                  end.
                  eapply star_implies_mono; [apply wand_star_r| |eassumption].
                  prove_implies. eapply implies_trans; [|apply star_assoc_l].
                  lazymatch goal with
                  | [H : is_elem_weighted_unique_list _ _ (?L1++?L2)%list,
                    H' : List.length ?L2 = ?s2,
                    H'' : ?s2 = 0
                    |- _] =>
                    rewrite H'' in H'; destruct L2; [|discriminate];
                    rename H into Hneighs
                  end.
                  rewrite List.app_nil_r in Hneighs |- *.
                  apply star_implies_mono.
                  { apply equiv_set_heap.
                    { unfold set_equiv. reflexivity. }
                    { lazymatch goal with
                      | [H : set_equiv ?P _ |- set_equiv ?P _] =>
                        rename H into Hequiv
                      end.
                      unfold set_equiv in Hequiv |- *. intros y. rewrite Hequiv.
                      unfold set_sum, set_remove, empty, single, neighbourhood.
                      rewrite List.in_map_iff.
                      unfold is_elem_weighted_unique_list,
                        is_elem_weighted_list in Hneighs.
                      destruct Hneighs as (Hin&?). split.
                      { intros [([[]|<-]&Hneq)|(?&(?&?)&<-&(Hneigh&?)%Hin)];
                          simpl in *.
                        { revert Hneq. clear. tauto. }
                        { split.
                          { unfold is_irreflexive, not in *. intros [?|<-]; eauto. }
                          { eauto. } } }
                      { intros (?&?&[[]|<-]&?). right. split; auto. eexists.
                        rewrite Hin. unfold neighbours. simpl. auto. } } }
                  { instantiate (cn1_0 := S c_h_empty). simpl.
                    repeat change (?x + ?y*?x) with (S y * x).
                    repeat change (S (?x + ?y)) with (S x + y).
                    lazymatch goal with
                    | [H : ?x + ?y + ?z <= m,
                      H' : is_elem_weighted_unique_list (neighbours _ _) _ ?L',
                      H'' : List.length ?L' = ?y,
                      H''' : is_set_size empty ?s1',
                      H'''' : is_set_size (set_sum empty (single x_min)) ?s2',
                      H''''' : set_equiv ?P'
                        (set_sum (set_remove (set_sum empty (single x_min)) x_min) _),
                      H'''''' : is_set_size ?P ?sP'
                      |- _] =>
                      rename x into a, y into b, L' into L, s1' into s1,
                        s2' into s2, sP' into sP, P' into P, H''''' into HeqP;
                      rewrite H''; subst z
                    end.
                    assert (a = 0) as ->.
                    { lazymatch goal with
                      | [H : is_set_size _ a |- _] => rename H into Ha
                      end.
                      eapply is_set_size_unique; eauto.
                      eapply equiv_set_size; eauto using empty_set_size.
                      unfold set_equiv, empty, uncurry, set_sum2. clear. tauto. }
                    assert (s1 = 0) as ->.
                    { lazymatch goal with
                      | [H : is_set_size _ s1 |- _] => rename H into Hs1
                      end.
                      eapply is_set_size_unique; eauto.
                      eapply equiv_set_size; eauto using empty_set_size.
                      unfold set_equiv, empty, uncurry, set_sum2. clear. tauto. }
                    assert (s2 = 1) as ->.
                    { lazymatch goal with
                      | [H : is_set_size _ s2 |- _] => rename H into Hs2
                      end.
                      eapply is_set_size_unique; eauto.
                      eapply equiv_set_size; eauto using single_set_size.
                      unfold set_equiv, set_sum, empty, single. intros.
                      split; eauto. intros [[]|?]. assumption. }
                    assert (sP = b) as ->.
                    { eapply is_set_size_unique; eauto. eapply equiv_set_size.
                      { unfold set_equiv in *. symmetry. eauto. }
                      { unfold set_sum, set_remove, empty, single, is_set_size,
                          is_elem_unique_list, is_elem_list.
                        exists (List.map fst L).
                        unfold is_elem_weighted_unique_list in Hneighs.
                        rewrite List.map_length. intuition. subst. tauto. } }
                    lazymatch goal with
                    | [|- $ (_+(_+?c0'+_)) <*> _ <*> $?c1 <*> $?c2 <*> $?c3 <*>
                        $ (?c4 + _ + _ + _) ->> _] =>
                      apply implies_spec; intros; apply star_exists_l;
                      exists (c0'+c1+c2+c3+c4)
                    end.
                    normalize_star. eapply credits_star_r; auto. revert_implies.
                    repeat (eapply implies_trans;
                      [apply star_implies_mono; [prove_implies_refl|]
                      |apply credits_star_l]);
                      try prove_implies_refl; auto.
                      lia. } }
                { lazymatch goal with
                  | [H : is_elem_weighted_unique_list _ _ (?L1 ++ ?L2)%list,
                    H' : Dijkstra_invariant _ _ ?P' _ _,
                    H'' : is_set_size (V (G g)) _
                    |- _] =>
                    remember H'' eqn:Heq; clear Heq;
                    unfold is_set_size, is_elem_unique_list in H'';
                    destruct H'' as (?&(?&?)&?);
                    destruct exists_filtered with
                      (P := fun x => ~ P' x) (L := List.map fst (L1++L2)%list)
                  end.
                  { intros. apply Decidable.dec_not.
                    eapply decidable_if_finite; eauto using Nat.eq_decidable. }
                  edestruct neighbour_of_list_in_finite_decidable_graph with
                    (x := x_min) as (?&(?&Hlist)%elem_list_to_unique);
                    eauto using Nat.eq_decidable.
                  { intros.
                    lazymatch goal with
                    | [|- _ (E ?g ?u ?v)] => fold (uncurry (E g) (u,v))
                    end.
                    eapply decidable_if_finite;
                      eauto using decidable_uncurry_eq, Nat.eq_decidable. }
                  repeat lazymatch goal with
                  | [|- ((_ <*> _) <*> _) ?c ?m ] =>
                    apply star_assoc_l; eauto
                  | [|- (<[_]> <*> _) ?c ?m ] =>
                    apply star_pure_l; split_all
                  | [|- ((<exists> _, _) <*> _) ?c ?m ] =>
                    apply star_exists_l; eexists; eauto
                  | [|- (<exists> _, _) ?c ?m] => eexists
                  end;
                  try lazymatch goal with
                  [|- Dijkstra_invariant _ _ _ _ _] =>
                    eapply valid_invariant; eauto
                  end;
                  try lazymatch goal with
                  [H : forall _, _ -> ?f1 _ = ?g1 _,
                  H' : forall _, _ -> ?f2 _ = ?g2 _
                  |- distance_decrease g ?v ?g1 ?f1' ?g2 ?f2'] =>
                    unify f1 f1'; unify f2 f2'; unify v x_min
                  end;
                  try lazymatch goal with
                  [|- is_nat_fun_of_val_list _ _] => eassumption
                  end;
                  try lazymatch goal with
                  [|- List.length _ = n] => eassumption
                  end.
                  { right. unfold add_single, set_sum, single. auto. }
                  { unfold is_subset, add_single, set_sum, single. intros ? [?|<-].
                    { auto. }
                    { unfold min_cost_elem, neighbourhood in Hmincost.
                      destruct Hmincost as ((?&?&?&?%E_closed2)&?). assumption. } }
                  { unfold neighbourhood, is_subset. intros ? (?&?&?&?%E_closed2).
                    assumption. }
                  { unfold add_single. apply disjoint_sum_size.
                    { unfold are_disjoint_sets, single.
                      intros ? (Hin&<-).
                      unfold min_cost_elem, neighbourhood in Hmincost.
                      revert Hmincost Hin. clear. tauto. }
                    { eassumption. }
                    { apply single_set_size. } }
                  { eapply neighbourhood_add_new_single_size; eauto.
                    { eapply elem_unique_list_of_weighted_unique. eassumption. }
                    { unfold min_cost_elem in Hmincost. tauto. } }
                  { apply edges_add_single_size;
                      eauto using elem_weighted_unique_list_to_size.
                    unfold is_set_size. eexists. split; eauto. }
                  { lazymatch goal with
                    | [H : is_elem_weighted_unique_list _ _ (?L1++?L2)%list,
                      H' : List.length ?L1 = ?y1,
                      H'' : List.length ?L2 = ?y2,
                      H''' : is_set_size ?P ?x,
                      H'''' : is_set_size ?Q ?y,
                      H''''' : is_filtered_list _ (List.map _ (_++_)%list) ?L
                      |- ?x + 1 + (?y+?z-1) <= n] =>
                      rename H into Hlist', L1 into N1, L2 into N2, L into N12,
                        x into sP, y into sQ, y1 into s1, y2 into s2, P into P',
                        H' into Hs1, H'' into Hs2, H''' into HsP, H'''' into HsQ,
                        H''''' into Hfiltered
                    end.
                    eapply subset_size_le with
                      (P := V g)
                      (P' := set_sum (add_single P' x_min)
                        (neighbourhood g (add_single P' x_min))).
                    { intros u. unfold set_sum. apply Decidable.dec_or.
                      { unfold add_single, single, set_sum.
                        apply Decidable.dec_or;
                          eauto using decidable_if_finite, Nat.eq_decidable. }
                      { unfold is_set_size, is_elem_unique_list in HsQ.
                          destruct HsQ as (?&(?&?)&?). unfold Decidable.decidable.
                          rewrite neighbourhood_add_single. apply Decidable.dec_or.
                          { eapply decidable_if_elem_list;
                              eauto using Nat.eq_decidable. }
                          { change (?f (?g u) /\ ?h u)
                              with ((fun x => f (g x) /\ h x) u).
                            eapply decidable_if_elem_list.
                            { apply Nat.eq_decidable. }
                            { eassert (is_elem_list (intersect
                                (neighbours g x_min) (fun x => ~ P' x)) _).
                              { eapply elem_list_intersect_filtered; eauto.
                                apply elem_unique_list_of_weighted_unique in Hlist'.
                                unfold is_elem_unique_list in Hlist'.
                                destruct Hlist' as (?&?). eassumption. }
                              { lazymatch goal with
                                | [H : is_elem_list (intersect ?Q (fun _ => ?P _)) _
                                  |- is_elem_list (fun _ => ?P _ /\ ?Q _) _] =>
                                  rename H into Hlist''
                                end.
                                unfold is_elem_list, intersect in Hlist'' |- *.
                                intros. rewrite Hlist''. clear. tauto. } } } } }
                    { rewrite Hn. assumption. }
                    { apply disjoint_sum_size.
                      { unfold are_disjoint_sets, add_single, single,
                          intersect, set_sum, neighbourhood. tauto. }
                      { unfold add_single. apply disjoint_sum_size.
                        { unfold are_disjoint_sets, single.
                          unfold is_irreflexive, not in *. intros ? (Hin&<-).
                          unfold min_cost_elem, neighbourhood in Hmincost. tauto. }
                        { assumption. }
                        { apply single_set_size. } }
                      { eapply neighbourhood_add_new_single_size; eauto.
                        { eapply elem_unique_list_of_weighted_unique. eassumption. }
                        { unfold min_cost_elem in Hmincost. tauto. } } }
                    { unfold is_subset, add_single, set_sum, single, neighbourhood.
                      intros ? [[?|<-]|(?&?&[?|<-]&?)]; eauto using E_closed2.
                      unfold min_cost_elem, neighbourhood in Hmincost.
                      destruct Hmincost as ((?&?&?&?%E_closed2)&?). assumption. } }
                  swap_star. solve_star. conormalize_star. swap_star_ctx.
                  conormalize_star. swap_star_ctx. conormalize_star.
                  swap_star_ctx. conormalize_star. swap_star_ctx.
                  conormalize_star. swap_star_ctx.
                  lazymatch goal with
                  | [H : _ ?c ?m |- _ ?c ?m] =>
                    apply star_assoc_l in H
                  end.
                  eapply star_implies_mono; [apply wand_star_r| |eassumption].
                  prove_implies. eapply implies_trans; [|apply star_assoc_l].
                  lazymatch goal with
                  | [H : is_elem_weighted_unique_list _ _ (?L1++?L2)%list,
                    H' : List.length ?L2 = ?s2,
                    H'' : ?s2 = 0
                    |- _] =>
                    rewrite H'' in H'; destruct L2; [|discriminate];
                    rename H into Hneighs
                  end.
                  rewrite List.app_nil_r in Hneighs |- *.
                  apply star_implies_mono.
                  { apply equiv_set_heap.
                    { unfold set_equiv. reflexivity. }
                    { lazymatch goal with
                      | [H : set_equiv ?P _ |- set_equiv ?P _] =>
                        rename H into Hequiv
                      end.
                      unfold set_equiv in Hequiv |- *. intros y. rewrite Hequiv.
                      unfold set_sum, set_remove, neighbourhood.
                      rewrite List.in_map_iff.
                      unfold is_elem_weighted_unique_list,
                        is_elem_weighted_list in Hneighs.
                      destruct Hneighs as (Hin&?).
                      split.
                      { intros [((?&?&?&?)&?)|(?&(?&?)&<-&(Hneigh&?)%Hin)];
                          simpl in *.
                        { split.
                          { intros []; auto. }
                          { eauto. } }
                        { unfold neighbours in Hneigh. split.
                          { unfold is_irreflexive, not in *. intros [?|<-]; eauto. }
                          { eauto. } } }
                      { intros (?&?&[?|<-]&?).
                        { eauto 15. }
                        { right. split; auto. eexists. rewrite Hin.
                          unfold neighbours. simpl. auto. } } } }
                  { match goal with
                    | [H : List.length _ = _, H' : is_filtered_list _ _ ?L'
                      |- _] => rewrite H; rename L' into L''
                    end.
                    instantiate (cn1_t2 := 0). instantiate (cm2 := 0). simpl.
                    repeat change (?x + ?y*?x) with (S y * x).
                    repeat change (S (?x + ?y)) with (S x + y).
                    lazymatch goal with
                    | [H : ?x + ?y + ?z <= m,
                      HH : ?xx + ?yy <= n,
                      H' : is_elem_unique_list (neighbour_of _ _) ?L',
                      HH' : is_set_size ?P' ?sP',
                      HHeq : set_equiv ?P' (set_sum (set_remove (neighbourhood _ _) x_min) _)
                      |- _] =>
                      rename x into a, y into b, L' into L, xx into a', yy into b',
                        P' into P, sP' into sP, HHeq into Hequiv
                    end.
                    rewrite <- (Nat.sub_add_distr m a b),
                      (Nat.sub_add_distr m (a + b) (List.length L)).
                    assert (sP <= b' + List.length L'' - 1).
                    { rewrite Nat.add_sub_swap.
                      { eapply sum_size_le; [| |eapply equiv_set_size; eauto].
                        { unfold min_cost_elem in Hmincost.
                          destruct Hmincost as (?&?).
                          apply set_remove_size_decr; eauto using Nat.eq_decidable. }
                        { unfold is_set_size. exists L''. split; eauto.
                          eapply subset_elem_unique_list.
                          { apply is_filtered_again.
                            lazymatch goal with
                            | [|- is_filtered_list _ (List.map fst ?L) _] =>
                              rewrite <- (List.app_nil_r L)
                            end.
                            eassumption. }
                          { eapply elem_unique_list_of_weighted_unique. eauto. }
                          { unfold is_subset. intros u.
                            unfold is_elem_weighted_unique_list,
                              is_elem_weighted_list in Hneighs.
                            destruct Hneighs as (Hneighs&?). rewrite List.in_map_iff.
                            intros (?&(?&?)&<-&(?&?)%Hneighs). simpl. assumption. } } }
                      { eapply subset_size_le with (P' := single x_min);
                          eauto using decidable_if_finite, single_set_size,
                            Nat.eq_decidable.
                        unfold is_subset, single. intros ? <-.
                        unfold min_cost_elem in Hmincost. tauto. } }
                    destruct Nat.le_gt_cases with (a'+1+b'+List.length L''-1) n.
                    { assert (n - (a'+1+sP) = n - (a'+1) - (b'+List.length L''-1)
                        + (b'+List.length L''-1-sP)) as -> by lia.
                      erewrite (*<- Nat.sub_add with (b'+List.length L''-1) (n - (a'+1)),*)
                        (Nat.mul_add_distr_r (n-(a'+1)-_+_)),
                        (Nat.mul_add_distr_r (n-(a'+1)-_+_)),
                        (Nat.mul_add_distr_r _ (b'+List.length L''-1-sP)).
                      destruct Nat.le_gt_cases with (List.length L) (m - (a+b)).
                      { erewrite <- Nat.sub_add with (List.length L) (m - (a+b)),
                          (Nat.mul_add_distr_l _ _ (List.length L));
                          auto.
                        lazymatch goal with
                        | [|- $ (_+(_+?c0+?c0'+(_+?cc0+(_+?cc0'+_)))) <*> _ <*> $?c1 <*> $?c2 <*> $?c3 <*>
                            $ (?c4 + _ + _ + _) ->> _] =>
                          apply implies_spec; intros; apply star_exists_l;
                          exists (c0+c0'+c1+c2+c3+c4+cc0+cc0')
                        end.
                        normalize_star. eapply credits_star_r; auto. revert_implies.
                        repeat (eapply implies_trans;
                          [apply star_implies_mono; [prove_implies_refl|]
                          |apply credits_star_l]);
                          try prove_implies_refl; auto.
                          lia. }
                      { rewrite Minus.not_le_minus_0_stt
                          with (m - (a+b)) (List.length L);
                          [|lia].
                        lazymatch goal with
                        | [|- $ (_+(?c0+?c0'+(_+?cc0+(_+?cc0'+_)))) <*> _ <*> $?c1 <*> $?c2 <*> $?c3 <*>
                            $ (?c4 + _ + _ + _) ->> _] =>
                          apply implies_spec; intros; apply star_exists_l;
                          exists (c0+c0'+c1+c2+c3+c4+cc0+cc0')
                        end.
                        normalize_star. eapply credits_star_r; auto. revert_implies.
                        repeat (eapply implies_trans;
                          [apply star_implies_mono; [prove_implies_refl|]
                          |apply credits_star_l]);
                          try prove_implies_refl; auto.
                          lia. } }
                    { rewrite Minus.not_le_minus_0_stt
                        with (n - (a'+1)) (b'+List.length L''-1); [|lia].
                      destruct Nat.le_gt_cases with (List.length L) (m - (a+b)).
                      { erewrite <- Nat.sub_add with (List.length L) (m - (a+b)),
                          (Nat.mul_add_distr_l _ _ (List.length L));
                          auto.
                        lazymatch goal with
                        | [|- $ (_+(_+?c0+?c0'+?cc0)) <*> _ <*> $?c1 <*> $?c2 <*> $?c3 <*>
                            $ (?c4 + _ + _ + _) ->> _] =>
                          apply implies_spec; intros; apply star_exists_l;
                          exists (c0+c0'+c1+c2+c3+c4+cc0)
                        end.
                        normalize_star. eapply credits_star_r; auto. revert_implies.
                        repeat (eapply implies_trans;
                          [apply star_implies_mono; [prove_implies_refl|]
                          |apply credits_star_l]);
                          try prove_implies_refl; auto.
                          lia. }
                      { rewrite Minus.not_le_minus_0_stt
                          with (m - (a+b)) (List.length L);
                          [|lia].
                        lazymatch goal with
                        | [|- $ (_+(?c0+?c0'+?cc0)) <*> _ <*> $?c1 <*> $?c2 <*> $?c3 <*>
                            $ (?c4 + _ + _ + _) ->> _] =>
                          apply implies_spec; intros; apply star_exists_l;
                          exists (c0+c0'+c1+c2+c3+c4+cc0)
                        end.
                        normalize_star. eapply credits_star_r; auto. revert_implies.
                        repeat (eapply implies_trans;
                          [apply star_implies_mono; [prove_implies_refl|]
                          |apply credits_star_l]);
                          try prove_implies_refl; auto.
                          lia. } } } }
          ++ clear get_neighbours h_insert h_empty h_extract_min h_decrease_key
              l_is_nil l_head l_tail Hspec_get_neighbours Hspec_h_insert
              Hspec_h_empty Hspec_h_extract_min Hspec_h_decrease_key
              Hspec_l_is_nil Hspec_l_head Hspec_l_tail Hcost_eq.
            triple_reorder_exists. repeat triple_pull_exists.
            triple_reorder_pure. repeat triple_pull_pure.
            triple_reorder_credits.
            rewrite Bool.negb_false_iff, Nat.eqb_eq in *.
            lazymatch goal with
            | [|- triple _ ($ (?x + ?y + _) <*> _) _] =>
              rewrite (Nat.add_comm x), <- (Nat.add_assoc y x)
            end.
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
                  with (P := $c <*> is_heap _ _ _ _ _ _ _)
              end.
              { prove_implies_rev. }
              { intros. simpl. apply star_assoc_r. }
              eapply triple_fun_app.
              --- repeat lazymatch goal with
                | [H : _ /\ _ |- _] => destruct H
                end.
                subst. eapply Hspec_h_free; eauto.
              --- solve_simple_value. apply star_comm. eassumption.
            ** triple_reorder_exists. repeat triple_pull_exists.
              solve_simple_value. swap_star.
              repeat lazymatch goal with
              | [H : _ /\ _ |- _] => destruct H
              end.
              lazymatch goal with
              | [|- ((<exists> _ _ _ _,
                <[RecV [?a1;?a2] = _]> <*> _ <*> _ <*> _ <*> _) <*> _) _ _] =>
                assert (exists l1 l2, a1 = Lab l1 /\ a2 = Lab l2) as (?&?&->&->)
              end.
              { lazymatch goal with
                | [H : (_ <*> _) _ _ |- _] =>
                  rename H into Hassertion
                end.
                unfold "<*>" in Hassertion. edestruct_direct.
                lazymatch goal with
                | [H : array_content _ ?a1 _ _,
                  H' : array_content _ ?a2 _ _
                  |- exists _ _, ?a1 = _ /\ ?a2 = _] =>
                  apply only_lab_is_array in H as (?&?);
                  apply only_lab_is_array in H' as (?&?)
                end.
                eauto. }
              solve_star. conormalize_star. swap_star_ctx. conormalize_star.
              swap_star_ctx. conormalize_star. swap_star_ctx.
              eapply star_implies_mono; [prove_implies_refl| |eassumption].
              eapply implies_spec. intros. swap_star. solve_star.
              eapply star_implies_mono; [| |eassumption].
              { apply array_content_to_is_nat_function. eassumption. }
              { eapply implies_trans; [|apply star_comm].
                apply star_implies_mono.
                { apply array_content_to_is_nat_function. eassumption. }
                { apply implies_spec. intros. solve_star.
                  { apply valid_final. eapply to_final_invariant; eauto.
                    { lazymatch goal with
                      | [H : (_ = empty /\ _ = set_sum empty _) \/
                          (_ src /\ _ = neighbourhood _ _) |- _] =>
                        destruct H as [(->&->)|(Hin&->)]
                      end.
                      { lazymatch goal with
                        | [Heq : ?s = 0, H : is_set_size _ ?s |- _] =>
                          rewrite Heq in H; rename H into Hsize
                        end.
                        unfold is_set_size, is_elem_unique_list, is_elem_list
                          in Hsize.
                        destruct Hsize as (L&(Hin&?)&?).
                        destruct L; [|discriminate]. simpl in Hin.
                        unfold set_sum, empty, single in Hin.
                        specialize Hin with src. tauto. }
                      { assumption. } }
                    { lazymatch goal with
                      | [H : (_ = empty /\ ?N = set_sum empty _) \/
                          (_ src /\ ?N = neighbourhood _ _),
                        H' : is_set_size ?N ?s,
                        H'' : ?s = 0
                        |- _] =>
                        rename H into Hset, H' into Hsize, H'' into Heq
                      end.
                      rewrite Heq in Hsize.
                      unfold is_set_size, is_elem_unique_list, is_elem_list
                        in Hsize.
                      destruct Hsize as ([]&(Hequiv&?)&?); [|discriminate].
                      simpl in Hequiv. destruct Hset as [(_&->)|(_&->)].
                      { exfalso. rewrite Hequiv.
                        unfold set_equiv, set_sum, single, empty. auto. }
                      { unfold set_equiv, empty. intros. symmetry. auto. } } }
                  { revert_implies. simpl.
                    repeat (eapply implies_trans;
                      [apply star_implies_mono
                      |apply credits_star_l; reflexivity]);
                      prove_implies_refl. } } }
Unshelve.
  all: now constructor.
Qed.
