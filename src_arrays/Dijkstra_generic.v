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

Definition assign_array_at : Value string :=
  ([-\] "array", [-\] "index", [-\] "value",
    (Var "array" >> Var "index") <- Var "value")%string.

Definition incr : Value string :=
  ([-\] "p", Var "p" <- ! Var "p" [+] Int 1)%string.

Definition init_array : Value string :=
  [-\] "array", [-\] "size", [-\] "value",
    [let "i"] Ref (Int 0) [in]
      [while] ! Var "i" [<] Var "size" [do]
        (*(Var "array" >> ! Var "i") <- Var "value";;*)
        assign_array_at <* Var "array" <* ! Var "i" <* Var "value";;
        incr <* Var "i"
      [end];;
      Free (Var "i")
    [end]%string.

Definition free_array_at : Value string :=
  ([-\] "array", [-\] "i", Free (Var "array" >> ! Var "i"))%string.

Definition free_array : Value string :=
  [-\] "array", [-\] "size",
    [let "i"] Ref (Int 0) [in]
      [while] ! Var "i" [<] Var "size" [do]
        (*Free (Var "array" >> ! Var "i");;
        Var "i" <- ! Var "i" [+] Int 1*)
        free_array_at <* Var "array" <* Var "i";;
        incr <* Var "i"
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

Ltac fold_and_apply f x :=
  try (progress fold (f x); fold_and_apply f (f x)).

Ltac fold_all_inc_set x :=
  fold_and_apply constr:(inc_set) x.

Ltac fold_all_inc_set_string :=
  fold_all_inc_set constr:(string).

Ltac reorder_exists P :=
  lazymatch P with
  | ?Q <*> ?Q' =>
    lazymatch ltac:(eval simpl in (ltac:(reorder_exists Q))) with
    | (<exists> x : ?T, @?Q1 x) =>
        let t := fresh x in
      reorder_exists ltac:(eval simpl in (<exists> t : T, Q1 t <*> Q'))
(*      let t := fresh x in
      let Q2 := ltac:(eval simpl in (fun t =>ltac:(reorder_exists ltac:(eval simpl in (Q1 t <*> Q'))))) in
      exact (<exists> x, Q2 x)*)
    | ?Q1 =>
      lazymatch ltac:(eval simpl in (ltac:(reorder_exists Q'))) with
      | (<exists> x : ?T, @?Q1' x) =>
        let t := fresh x in
        reorder_exists ltac:(eval simpl in (<exists> t : T, Q1 <*> Q1' t))
(*        let t := fresh x in
        let Q2 := ltac:(eval simpl in (fun t =>ltac:(reorder_exists ltac:(eval simpl in (Q1 <*> Q1' t))))) in
        exact (<exists> x, Q2 x)*)
      | ?Q1' => exact (Q1 <*> Q1')
      end
    end
  | <exists> t : ?T, @?Q t => (*idtac t T Q;*)
    let Q' := ltac:(eval simpl in ltac:(reorder_exists Q)) in
    (*idtac T Q'; idtac ">";*) exact (<exists> t : T, Q' t) (*; idtac "OK") || idtac "!")*)
  | fun t : ?T => @?Q t => (*idtac t T Q;*)
    let u := fresh t in(*exact (fun x : T => ltac:(eval simpl in ltac:(clear_empty Q)))*)
    let Q' := ltac:(eval simpl in (fun u =>ltac:(reorder_exists ltac:(eval simpl in (Q u))))) in
    (*idtac t T Q'; idtac ">!";*) exact Q' (*; idtac "OK!") || idtac "!!")*)
  | _ => exact P (*; idtac "<>"*)
  end.

(*Check ltac:(reorder_exists (<[]> <*> (<[1=1]> <*> (<exists> t, <[t < 1]>) <*> <[2=2]> <*> (<exists> x : nat, <[x=0]> <*> <exists> y, <[x=y]>) <*> (sa_credits 2 <*> <[3=3]> <*> <exists> z, sa_credits z) <*> sa_credits 5 <*> <exists> t, <[t>10]>) : StateAssertion string)).*)

Ltac prove_implies_reorder_exists :=
  lazymatch goal with
  | [|- ?Q <*> ?Q' ->> _ ] =>
    eapply implies_trans;
    [apply star_implies_mono; [prove_implies_reorder_exists|prove_implies_refl]|];
    lazymatch goal with
    | [|- (<exists> x, @?Q1 x) <*> ?Q1' ->> _] =>
      eapply implies_trans; [apply star_exists_l'|];
      prove_implies_reorder_exists
    | [|- ?Q1 <*> ?Q1' ->> _] =>
      eapply implies_trans;
      [apply star_implies_mono; [prove_implies_refl|prove_implies_reorder_exists]|];
      lazymatch goal with
      | [|- ?Q2 <*> (<exists> x, @?Q2' x) ->> _] =>
        eapply implies_trans; [apply star_exists_r'|];
        prove_implies_reorder_exists
      | [|- ?Q2 <*> ?Q2' ->> _] => apply implies_refl
      end
    end
  | [|- (<exists> x, @?P' x) ->> _] =>
    let t := fresh x in
    apply implies_trans with (Q := <exists> t, P' t); [prove_implies_refl|];
    apply exists_implies with (P := P'); prove_implies_reorder_exists
  | [|- forall x, ?Q ->> _] =>
    intros; prove_implies_reorder_exists
  | [|- ?P ->> _] => apply implies_refl
  end.

Ltac prove_implies_reorder_exists_bwd :=
  lazymatch goal with
  | [|- ?Q <*> ?Q' ->> _ ] =>
    eapply implies_trans;
    [|apply star_implies_mono; [prove_implies_reorder_exists_bwd|prove_implies_refl]];
    lazymatch goal with
    | [|- (<exists> x, @?Q1 x) <*> ?Q1' ->> _] =>
      eapply implies_trans; [|apply star_exists_l'];
      prove_implies_reorder_exists_bwd
    | [|- ?Q1 <*> ?Q1' ->> _] =>
      eapply implies_trans;
      [|apply star_implies_mono; [prove_implies_refl|prove_implies_reorder_exists_bwd]];
      lazymatch goal with
      | [|- ?Q2 <*> (<exists> x, @?Q2' x) ->> _] =>
        eapply implies_trans; [|apply star_exists_r'];
        prove_implies_reorder_exists_bwd
      | [|- ?Q2 <*> ?Q2' ->> _] => apply implies_refl
      end
    end
  | [|- (<exists> x, @?P' x) ->> _] =>
    let t := fresh x in
    apply implies_trans with (Q := <exists> t, P' t); [|prove_implies_refl];
    apply exists_implies with (P := P'); prove_implies_reorder_exists_bwd
  | [|- forall x, ?Q ->> _] =>
    intros; prove_implies_reorder_exists_bwd
  | [|- ?P ->> _] => apply implies_refl
  end.

Ltac triple_reorder_exists :=
  lazymatch goal with
  | [|- triple ?e ?P' ?Q'] =>
    apply triple_weaken with (P := ltac:(reorder_exists P')) (Q := Q');
      [prove_implies_reorder_exists|prove_implies_refl|]
  end.

(*Ltac prove_post_by_constant_eta_expansion :=
  match goal with
  | [H : ?P ?c ?m |- _ ?v ?c ?m]
  end.
*)

Ltac rewrite_all_binds :=
  fold_all_inc_set_string;
  repeat rewrite bind_v_liftS_shift_swap;
  repeat rewrite bind_v_shift;
  repeat rewrite bind_v_id.

Lemma only_lab_is_array V A a c m :
  @array_content V A a c m ->
  exists n, a = Lab (OfNat n).
Proof.
  intros [].
  - destruct l. eauto.
  - eauto.
Qed.

Ltac injection_ctx :=
  match goal with
  | [H : ?f _ = ?f _ |- _] => injection H; clear H; intros; subst
  end.

Lemma triple_fun_assign_array_at A A' A1 ov A2 a i x :
  List.length A1 = i ->
  A = (A1 ++ ov::A2)%list ->
  A' = (A1 ++ Some x::A2)%list ->
  triple_fun assign_array_at
    (fun v => $1 <*> <[v = a]>)
    (fun v => <[
      triple_fun v
        (fun v => $1 <*> <[v = Int (Z.of_nat i)]>)
        (fun v => <[
          triple_fun v
            (fun v => $3 <*> <[v = x]> <*> array_content A a)
            (fun v => <[v = U_val]> <*> array_content A' a)
        ]>)
    ]>).
Proof.
  intros. subst. unfold triple_fun, assign_array_at, StringLam. simpl. intros.
  app_lambda. solve_simple_value. normalize_star. subst. split_all; auto.
  intros. cbn. solve_simple_value. normalize_star. subst. split_all; auto.
  intros. app_lambda. solve_simple_value. normalize_star. split_all; auto.
  intros. cbn. solve_simple_value. normalize_star. subst. split_all; auto.
  intros. triple_pull_1_credit. app_lambda. solve_simple_value.
  swap_star_ctx. normalize_star. subst. split_all; auto. intros. cbn.
  rewrite_all_binds. unfold sa_star, sa_credits in * |-. edestruct_direct.
  match goal with
  | [H : array_content _ _ _ _ |- _] => apply only_lab_is_array in H as (?&->)
  end.
  eapply triple_weaken.
  1-2:intros; repeat (apply star_implies_mono; [prove_implies_refl|]);
    apply implies_spec; intros ? ? ?%array_content_app; eassumption.
  eapply triple_weaken.
  1-2:intros; repeat (apply star_implies_mono; [prove_implies_refl|]);
    apply implies_spec; intros ? ? ?%array_content_cons; eassumption.
  triple_reorder_exists. triple_pull_exists.
  triple_reorder_pure. repeat triple_pull_pure. subst. injection_ctx.
  triple_pull_1_credit.
  eapply triple_weaken, triple_frame,
    triple_assign with (Q2 := fun v' => <[v' = x]> <*> _).
  { prove_implies_rev. }
  { intros. simpl. prove_implies_rev. apply implies_spec. intros. normalize_star.
    swap_star_ctx. normalize_star. subst.
    match goal with
    | [H : _ ?c ?m |- _ ?c ?m] => apply empty_star_l_cancel in H
    end.
    solve_star. revert_implies. prove_implies. }
  2:solve_simple_value.
  triple_reorder_credits.
  lazymatch goal with
  | [|- triple (Val (Lab (OfNat ?n)) >> Val (Int ?i)) _ _] =>
    eapply triple_weaken, triple_shift with
      (Q1 := fun n' => <[n' = n]> <*> _)
      (Q2 := fun n' i' => <[n' = n]> <*> <[i' = i]> <*> _)
  end.
  { prove_implies. }
  { intros. simpl. apply implies_spec. intros. normalize_star. swap_star.
    solve_star. apply empty_star_l_intro. subst. rewrite Nat2Z.id.
    solve_star; eauto. }
  - solve_simple_value.
  - intros. simpl. solve_simple_value; normalize_star; eauto. lia.
Qed.

Lemma triple_fun_n_ary_assign_array_at A A' A1 ov A2 i x :
  List.length A1 = i ->
  A = (A1 ++ ov::A2)%list ->
  A' = (A1 ++ Some x::A2)%list ->
  triple_fun_n_ary 2 assign_array_at
    (fun a v2 v3 =>
      $2 <*> <[v2 = Int (Z.of_nat i)]> <*> <[v3 = x]> <*> array_content A a)
    (fun a v2 v3 v => <[v = U_val]> <*> array_content A' a).
Proof.
  simpl.
  intros. subst. unfold triple_fun, assign_array_at, StringLam. simpl. intros.
  app_lambda. solve_simple_value. normalize_star. subst. split_all; auto.
  intros. cbn. solve_simple_value. normalize_star. subst. split_all; auto.
  intros. app_lambda. solve_simple_value. normalize_star. split_all; auto.
  intros. cbn. solve_simple_value. normalize_star. subst. split_all; auto.
  intros. triple_reorder_credits. app_lambda. solve_simple_value.
  swap_star_ctx. normalize_star. subst. split_all; auto. intros. cbn.
  rewrite_all_binds. unfold sa_star, sa_credits in * |-. edestruct_direct.
  match goal with
  | [H : array_content _ _ _ _ |- _] => apply only_lab_is_array in H as (?&->)
  end.
  eapply triple_weaken.
  { intros. apply star_implies_mono; [prove_implies_refl|].
    apply star_implies_mono; [|prove_implies_refl].
    repeat (apply star_implies_mono; [prove_implies_refl|]).
    apply implies_spec. intros ? ? ?%array_content_app. revert_implies.
    repeat (apply star_implies_mono; [prove_implies_refl|]).
    apply implies_spec. intros ? ? ?%array_content_cons. eassumption. }
  { intros. repeat (apply star_implies_mono; [prove_implies_refl|]).
    apply implies_spec. intros. apply array_content_app. revert_implies.
    repeat (apply star_implies_mono; [prove_implies_refl|]).
    apply implies_spec. intros. apply array_content_cons. eassumption. }
  triple_reorder_exists. triple_pull_exists.
  triple_reorder_pure. repeat triple_pull_pure. subst. injection_ctx.
  triple_pull_1_credit.
  eapply triple_weaken, triple_frame,
    triple_assign with (Q2 := fun v' => <[v' = x]> <*> _).
  { prove_implies_rev. }
  { intros. simpl. prove_implies_rev. apply implies_spec. intros. normalize_star.
    swap_star_ctx. normalize_star. subst.
    match goal with
    | [H : _ ?c ?m |- _ ?c ?m] => apply empty_star_l_cancel in H
    end.
    solve_star. revert_implies. prove_implies. }
  2:solve_simple_value.
  triple_reorder_credits.
  lazymatch goal with
  | [|- triple (Val (Lab (OfNat ?n)) >> Val (Int ?i)) _ _] =>
    eapply triple_weaken, triple_shift with
      (Q1 := fun n' => <[n' = n]> <*> _)
      (Q2 := fun n' i' => <[n' = n]> <*> <[i' = i]> <*> _)
  end.
  { prove_implies. }
  { intros. simpl. apply implies_spec. intros. normalize_star. swap_star.
    solve_star. apply empty_star_l_intro. subst. rewrite Nat2Z.id.
    solve_star; eauto. }
  - apply triple_value_implies. apply implies_spec. intros. eexists.
    do 2 (apply star_pure_l; split; auto). eassumption.
  - intros. simpl. solve_simple_value; normalize_star; eauto. lia.
Qed.

Ltac find_witness_is_closed e :=
  lazymatch e with
  (* variables *)
  | @None ?T => exact (@None ltac:(find_witness_is_closed T))
  | Some ?x => exact (Some ltac:(find_witness_is_closed x))
  (* Value *)
  | U_val => exact U_val
  | Var ?x => exact (Var ltac:(find_witness_is_closed x))
  | Int ?i => exact (Int i)
  | Bool ?b => exact (Bool b)
  | Lab ?l => exact (Lab l)
  (*| RecV ?vs => exact (RecV (*TODO*)) *)
  | Lam ?e => exact (Lam ltac:(find_witness_is_closed e))
  (* Expr *)
  | Val ?v => exact (Val ltac:(find_witness_is_closed v))
  | App ?e1 ?e2 =>
    exact (App ltac:(find_witness_is_closed e1) ltac:(find_witness_is_closed e2))
  | UnOp ?k ?e => exact (UnOp k ltac:(find_witness_is_closed e))
  | BinOp ?k ?e1 ?e2 =>
    exact (BinOp k
      ltac:(find_witness_is_closed e1) ltac:(find_witness_is_closed e2))
(*  | RecE es => exact (ecE (*TODO*))
  | Get n e => Get n (map_labels_e f e)
  | Ref e => Ref (map_labels_e f e)
  | NewArray e => NewArray (map_labels_e f e)*)
  | Deref ?e => exact (Deref ltac:(find_witness_is_closed e))
  | Shift ?e1 ?e2 => exact (Shift ltac:(find_witness_is_closed e1) ltac:(find_witness_is_closed e2))
  | Assign ?e1 ?e2 => exact (Assign ltac:(find_witness_is_closed e1) ltac:(find_witness_is_closed e2))
(*  | Free e => Free (map_labels_e f e)
  | Seq e1 e2 => Seq (map_labels_e f e1) (map_labels_e f e2)
  | If e1 e2 e3 =>
    If (map_labels_e f e1) (map_labels_e f e2) (map_labels_e f e3)
  | While e1 e2 => While (map_labels_e f e1) (map_labels_e f e2)*)
  (* Coq types *)
  | option ?T => exact (option ltac:(find_witness_is_closed T))
  | ?T => exact Empty_set
  end.

(*Check (ltac:(find_witness_is_closed ltac:(eval compute in assign_array_at))).*)

Ltac prove_is_closed :=
  unfold is_closed_value, StringLam; compute; eexists ?[e];
  lazymatch goal with
  | [|- ?e' = _] => instantiate (e := (ltac:(find_witness_is_closed e')))
  end;
  simpl; reflexivity.

Lemma is_closed_value_assign_array_at :
  is_closed_value assign_array_at.
Proof.
  prove_is_closed.
Qed.

Opaque assign_array_at.

Global Hint Resolve is_closed_value_assign_array_at : is_closed_db.

Lemma triple_fun_incr l i :
  triple_fun incr
    (fun v => $4 <*> <[v = Lab l]> <*> <(l :== Int i)>)
    (fun v => <[v = U_val]> <*> <(l :== Int (i+1))>).
Proof.
  unfold triple_fun, incr, StringLam. simpl. intros. triple_pull_1_credit.
  app_lambda. solve_simple_value. split_all; auto. intros. cbn.
  triple_reorder_pure. triple_pull_pure. subst. triple_pull_1_credit.
  eapply triple_weaken, triple_assign with (Q2 := fun v' => <[v' = Int (i+1)]>).
  { prove_implies_rev. }
  { intros. simpl. prove_implies. apply implies_spec. intros. normalize_star.
    swap_star_ctx. normalize_star. subst. assumption. }
  - solve_simple_value.
  - triple_pull_1_credit.
    eapply triple_weaken, triple_iadd with
      (Q1 := fun i1 => <[i1 = i]> <*> _)
      (Q2 := fun i1 i2 => <[i1 = i]> <*> <[i2 = 1%Z]> <*> _).
    { prove_implies. }
    { apply implies_post_spec. intros. normalize_star. subst. swap_star.
      solve_star. eassumption. }
    + eapply triple_weaken, triple_deref.
      { apply empty_star_r_intro. }
      { apply implies_post_spec. intros. normalize_star. subst. solve_star.
        eassumption. }
      solve_simple_value.
    + intros. triple_pull_pure. subst. solve_simple_value. revert_implies.
      apply empty_star_r_cancel.
Qed.

Lemma triple_fun_n_ary_incr l i :
  triple_fun_n_ary 0 incr
    (fun v => $3 <*> <[v = Lab l]> <*> <(l :== Int i)>)
    (fun v res => <[res = U_val]> <*> <(l :== Int (i+1))>).
Proof.
  simpl.
  unfold triple_fun, incr, StringLam. simpl. intros. triple_reorder_credits.
  app_lambda. solve_simple_value. split_all; auto. intros. cbn.
  triple_reorder_pure. repeat triple_pull_pure. subst. triple_pull_1_credit.
  eapply triple_weaken, triple_assign with (Q2 := fun v' => <[v' = Int (i+1)]>).
  { prove_implies_rev. }
  { intros. simpl. prove_implies. apply implies_spec. intros. normalize_star.
    swap_star_ctx. normalize_star. subst. assumption. }
  - solve_simple_value.
  - triple_pull_1_credit.
    eapply triple_weaken, triple_iadd with
      (Q1 := fun i1 => <[i1 = i]> <*> _)
      (Q2 := fun i1 i2 => <[i1 = i]> <*> <[i2 = 1%Z]> <*> _).
    { prove_implies. }
    { apply implies_post_spec. intros. normalize_star. subst. swap_star.
      solve_star. eassumption. }
    + eapply triple_weaken, triple_deref.
      { apply empty_star_r_intro. }
      { apply implies_post_spec. intros. normalize_star. subst. solve_star.
        eassumption. }
      solve_simple_value.
    + intros. triple_pull_pure. subst. solve_simple_value. revert_implies.
      apply empty_star_r_cancel.
Qed.

Lemma is_closed_value_incr :
  is_closed_value incr.
Proof.
  prove_is_closed.
Qed.

Opaque incr.

Global Hint Resolve is_closed_value_incr : is_closed_db.

Ltac omit_subst H :=
  revert H; subst; intro.

Lemma triple_fun_init_array A a s x :
  s = List.length A ->
  triple_fun init_array
    (fun v => $1 <*> <[v = a]>)
    (fun v => <[
      triple_fun v
        (fun v => $1 <*> <[v = Int (Z.of_nat s)]>)
        (fun v => <[
          triple_fun v
            (fun v => <[v = x]> <*> $ (9 + s*16) <*> array_content A a)
            (fun v => <[v = U_val]> <*> array_content (List.repeat (Some x) s) a)
        ]>)
    ]>).
Proof.
  unfold triple_fun, init_array, StringLam. simpl. intros.
  repeat (rewrite map_v_shift_closed;
    [|repeat apply map_v_closed_value; auto with is_closed_db]).
  app_lambda. solve_simple_value. normalize_star. subst.
  split_all; auto. intros. cbn. subst. triple_pull_pure. subst.
  solve_simple_value. rewrite_empty_spec. rewrite pure_spec. split_all; auto.
  intros. app_lambda. solve_simple_value. normalize_star. subst.
  split_all; auto. intros. cbn. triple_pull_pure. subst. solve_simple_value.
  rewrite_empty_spec. rewrite pure_spec. split_all; auto. intros.
  triple_pull_1_credit. app_lambda. solve_simple_value. swap_star_ctx.
  normalize_star. subst. split_all; auto. intros. cbn.
  triple_reorder_pure. triple_pull_pure. subst. triple_pull_1_credit.
  app_lambda.
  2:{ triple_pull_1_credit.
      eapply triple_ref with (Q := fun v => <[v = Int 0]> <*> _).
      solve_simple_value. }
  solve_simple_value. split_all; auto. intros. cbn. repeat triple_pull_exists.
  triple_reorder_pure. triple_pull_pure. subst. triple_pull_1_credit.
  remember (List.length A) as s eqn:Hs.
  rewrite_all_binds. eapply triple_seq.
  - triple_reorder_pure. triple_pull_pure. omit_subst Hs.
    triple_reorder_credits. triple_pull_credits 2. triple_reorder_credits.
    eapply triple_weaken with
      (P := $2 <*> <exists> i,
        $(3+(s-Z.to_nat i)*16) <*> (array_content A a <*> <(x0 :== Int i)> <*>
          <[(i >= 0)%Z]>)).
    { prove_implies. apply implies_spec. intros. exists 0%Z. simpl.
      rewrite Nat.sub_0_r. revert_implies. prove_implies. apply implies_spec.
      intros. swap_star. solve_star. lia. }
    { prove_implies_refl. }
    apply triple_while with
      (Q := fun b => <exists> i, $(1+(s - Z.to_nat i)*16) <*>
        (array_content A a <*> <(x0 :== Int i)>) <*>
        (<[(i >= 0)%Z]> <*> <[b = (i <? Z.of_nat s)%Z]>)).
    + repeat triple_pull_exists. triple_pull_1_credit.
      eapply triple_weaken, triple_clt with
        (Q1 := fun i1 => $_ <*> (_ <*> <(x0 :== Int i1)>) <*> <[(i1 >= 0)%Z]>)
        (Q2 := fun i1 i2 =>
          <[i2 = Z.of_nat s]> <*> ($_ <*> (_ <*> <(x0 :== Int i1)>)) <*> <[(i1 >= 0)%Z]>).
      { prove_implies_refl. }
      { apply implies_post_spec. intros. normalize_star. omit_subst Hs.
        solve_star. do 2 apply star_assoc_r. swap_star. solve_star. }
      * triple_pull_1_credit. eapply triple_weaken, triple_deref.
        { prove_implies_rev. }
        { apply implies_post_spec. intros. normalize_star. omit_subst Hs.
          solve_star. swap_star. do 2 apply star_assoc_l. swap_star.
          apply star_assoc_l. eassumption. }
        solve_simple_value. revert_implies. prove_implies_rev.
      * intros. simpl. solve_simple_value.
    + triple_pull_exists. triple_reorder_pure. repeat triple_pull_pure.
      match goal with
      | [H : true = (_ <? _)%Z |- _] => symmetry in H; apply Z.ltb_lt in H
      end.
      destruct s; [simpl in *; lia|]. rewrite Nat.sub_succ_l; [|lia]. simpl.
      destruct (List.nth_split (n := Z.to_nat x1) A None) as (?&?&->&?).
      { lia. }
      pose proof triple_fun_n_ary_app as Hn_ary.
      pose proof triple_fun_n_ary_frame as Hframe.
      pose proof triple_fun_n_ary_weaken as Hweaken.
      triple_pull_1_credit. eapply triple_seq with (Q1 := (array_content _ a <*> _) <*> ($ _)).
      * triple_pull_credits 6. triple_reorder_credits.
        triple_pull_credits 5. triple_reorder_credits.
        triple_pull_credits 2. triple_reorder_credits.
        repeat match goal with
        | [H : ?T _ _ |- _] =>
          let TT := ltac:(type of T) in
          unify TT (StateAssertion string);
          (*idtac H T;*) clear H
        end.
        eapply triple_weaken with
          (P := ($_ <*> ($_ <*> ($_ <*> (array_content _ _ <*> _)))) <*> ($ _)).
        { prove_implies. }
        { intros. apply star_assoc. }
        apply triple_frame. revert a.
        match goal with
        | [|-
          forall a,
            triple (Val (@?f a) <* (@?e1 a) <* (@?e2 a) <* (@?e3 a))
              ($2 <*> (@?P0 a))
              (@?Q1 a)
          ] =>
          intros a;
          specialize Hn_ary with
            (v := f a) (e := e1 a) (es := [e2 a;e3 a]%list)
            (P := P0 a) (Q2 := fun a _ _ => Q1 a)
        end.
        pose proof triple_fun_n_ary_assign_array_at as Hassign_array_at.
        specialize (Hframe _ assign_array_at 2).
        specialize (Hweaken _ assign_array_at 2).
        simpl in Hn_ary, Hassign_array_at, Hframe, Hweaken. eapply Hn_ary.
        { eapply Hweaken.
          { intros. apply implies_refl. }
          { intros. apply star_assoc_r. }
          simpl. eapply Hframe.
          eapply Hassign_array_at; eauto. }
        { solve_simple_value. revert_implies. prove_implies_refl. }
        { triple_pull_1_credit.
          eapply triple_weaken, triple_deref;
            [prove_implies_rev| |solve_simple_value].
          apply implies_post_spec. intros. normalize_star. subst. solve_star.
          revert_implies.
          lazymatch goal with
          | [|- _ ->> _ ?x] =>
            let t := ltac:(fresh "x") in remember x as t
          end.
          prove_implies_refl. }
        { solve_simple_value. revert_implies. prove_implies_refl. }
        { simpl. apply implies_spec. intros. do 2 (swap_star; solve_star).
          { f_equal. lia. }
          revert_implies. prove_implies. }
      * triple_reorder_credits.
        triple_pull_credits 5. triple_reorder_credits.
        triple_pull_credits 4. triple_reorder_credits.
        triple_pull_credits 1. triple_reorder_credits.
        eapply triple_weaken with
          (P := ($_ <*> ($_ <*> ($_ <*> _))) <*> (array_content _ _ <*> $ _)),
          triple_frame.
        { prove_implies. }(*
        2:{
        apply triple_frame. revert a.
        match goal with
        | [|-
          forall a,
            triple (Val (@?f a) <* (@?e1 a) <* (@?e2 a) <* (@?e3 a))
              ($2 <*> (@?P0 a))
              (@?Q1 a)
          ] =>
          intros a;
          specialize Hn_ary with
            (v := f a) (e := e1 a) (es := [e2 a;e3 a]%list)
            (P := P0 a) (Q2 := fun a _ _ => Q1 a)
        end.
        pose proof triple_fun_n_ary_incr as Hincr.
        specialize (Hframe _ assign_array_at 2).
        specialize (Hweaken _ assign_array_at 2).
        simpl in Hn_ary, Hassign_array_at, Hframe, Hweaken. eapply Hn_ary.
        { eapply Hweaken.
          { intros. apply implies_refl. }
          { intros. apply star_assoc_r. }
          simpl. eapply Hframe.
          eapply Hassign_array_at; eauto. } }
        { apply implies_post_spec. intros. solve_star. swap_star. prove_implies_rev. intros. apply star_assoc. }*)
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
  intros Hspec_get_size Hspec_get_max_label Hspec_get_neighbours Hspec_mkheap
    Hspec_h_insert Hspec_h_empty Hspec_h_extract_min Hspec_h_decrease_key
    Hspec_h_free Hspec_l_is_nil Hspec_l_head Hspec_l_tail.
  eexists ?[c0], ?[cn], ?[cm]. intros. unfold triple_fun, generic_dijkstra, StringLam. simpl. intros.
  repeat (rewrite map_v_shift_closed; [|repeat apply map_v_closed_value; assumption]).
  app_lambda. triple_pull_pure. subst. solve_simple_value; [|rewrite_empty_spec; rewrite pure_spec; auto].
  split_all; auto. intros. cbn. triple_pull_pure. solve_simple_value.
  rewrite_empty_spec. rewrite pure_spec. split_all; auto. intros.
  instantiate (c0 := S ?[cc0]). instantiate (cc0 := ?[c0]).
  triple_pull_1_credit. app_lambda. simpl. subst. solve_simple_value.
  split_all; auto. intros. cbn. triple_reorder_pure. repeat triple_pull_pure. subst.
  rewrite bind_v_shift, bind_v_id.
  instantiate (c0 := S ?[cc0]). instantiate (cc0 := ?[c0]).
  (*Set Printing Implicit.*)
  fold_all_inc_set_string.
  repeat rewrite bind_v_liftS_shift_swap. repeat rewrite bind_v_shift. repeat rewrite bind_v_id. simpl.
  triple_pull_1_credit. app_lambda.
  2:{
    instantiate (c0 := S ?[cc0]). instantiate (cc0 := ?[c0]). triple_pull_1_credit.
    eapply triple_weaken, triple_frame, triple_fun_app.
    { apply implies_spec. intros. swap_star_ctx. normalize_star. swap_star_ctx. eassumption. }
    { prove_implies_refl. }
    { apply Hspec_get_size. admit. }
    { solve_simple_value. swap_star. solve_star. eassumption. }
  }
  solve_simple_value. split_all; auto. intros. cbn.
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
    { apply Hspec_get_max_label. admit. }
    { solve_simple_value. swap_star. swap_star_ctx. solve_star. eassumption. }
  }
  solve_simple_value. split_all; auto. intros. cbn.
  repeat rewrite bind_v_liftS_shift_swap. repeat rewrite bind_v_shift. repeat rewrite bind_v_id. simpl.
  triple_reorder_exists. repeat triple_pull_exists. triple_reorder_pure. repeat triple_pull_pure. subst.
  instantiate (c0 := S ?[cc0]). instantiate (cc0 := ?[c0]).
  triple_pull_1_credit. app_lambda.
  2:{
    instantiate (c0 := S (S ?[cc0])). instantiate (cc0 := ?[c0]).
    triple_pull_credits 2. triple_reorder_credits.
    eapply triple_weaken, triple_frame, triple_fun_app2.
    4:solve_simple_value.
    1:{ prove_implies_refl. }
    2:{
      instantiate (c0 := S ?[cc0]). instantiate (cc0 := ?[c0]). triple_pull_1_credit.
      eapply triple_weaken, triple_frame, triple_fun_app.
      3:apply Hspec_mkheap; admit.
      3:solve_simple_value.
      { apply implies_spec. intros. solve_star. swap_star. solve_star. eassumption. }
      { apply implies_post_spec. intros. normalize_star. solve_star; [eassumption|].
        simpl. swap_star. solve_star. eassumption. }
    }
    1:{ prove_implies_refl. }
  }
  solve_simple_value. split_all; auto. intros. cbn.
  repeat rewrite bind_v_liftS_shift_swap. repeat rewrite bind_v_shift. repeat rewrite bind_v_id. simpl.
  instantiate (c0 := S ?[cc0]). instantiate (cc0 := ?[c0]).
  triple_pull_1_credit. app_lambda.
  2:{
    triple_pull_1_credit.
    apply triple_new_array. solve_simple_value.
    { lia. }
    { match goal with
      | [H : ?Q ?c ?m |- ?F ?v ?c ?m] =>
        unify F (fun t => <[t = v]> <*> Q)
      end.
      simpl. solve_star. }
  }
  solve_simple_value. split_all; auto. intros. cbn.
  repeat rewrite bind_v_liftS_shift_swap. repeat rewrite bind_v_shift. repeat rewrite bind_v_id. simpl.
  triple_reorder_exists. repeat triple_pull_exists.
  triple_reorder_pure. repeat triple_pull_pure. subst.
  instantiate (c0 := S ?[cc0]). instantiate (cc0 := ?[c0]).
  triple_pull_1_credit. app_lambda.
  2:{
    instantiate (c0 := S ?[cc0]). instantiate (cc0 := ?[c0]).
    triple_pull_1_credit.
    apply triple_new_array. solve_simple_value.
    { lia. }
    { match goal with
      | [H : ?Q ?c ?m |- ?F ?v ?c ?m] =>
        unify F (fun t => <[t = v]> <*> Q)
      end.
      simpl. solve_star. }
  }
  solve_simple_value. split_all; auto. intros. cbn.
  repeat rewrite bind_v_liftS_shift_swap. repeat rewrite bind_v_shift. repeat rewrite bind_v_id. simpl.
  triple_reorder_exists. repeat triple_pull_exists.
  triple_reorder_pure. repeat triple_pull_pure. subst.
  instantiate (c0 := S ?[cc0]). instantiate (cc0 := ?[c0]).
  triple_pull_1_credit.
  eapply triple_seq.
  -- admit.
  -- admit.
  (*TODO:
  triple_pull_exists.
  triple_reorder_pure.
  triple_pull_pure.*)
Admitted.
