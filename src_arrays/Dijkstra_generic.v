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
      assign_array_at <* Var "dist" <* Var "src" <* Int 0;;
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

(*
Parameter place_in_heap :
  forall {V} (h : Value V) (x p : nat), Prop.
*)

Parameter mkheap_cost : forall (n C c : nat), Prop.

Axiom mkheap_cost_exists : forall n C, exists c, mkheap_cost n C c.

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
    (fun v1 v2 v3 => $c <*> <[v1 = h]> <*> <[v2 = Int (Z.of_nat k)]> <*>
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
      (fun v => <[v = t]> <*> is_list (h::L)%list l <*> (is_list (h::L)%list l <-*> is_list L t)).

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
(*
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
(*  | RecE es => exact (ecE (*TODO*))*)
  | Get ?n ?e => exact (Get n ltac:(find_witness_is_closed e))
  | Ref ?e => exact (Ref ltac:(find_witness_is_closed e))
  | NewArray ?e => exact (NewArray ltac:(find_witness_is_closed e))
  | Deref ?e => exact (Deref ltac:(find_witness_is_closed e))
  | Shift ?e1 ?e2 => exact (Shift ltac:(find_witness_is_closed e1) ltac:(find_witness_is_closed e2))
  | Assign ?e1 ?e2 => exact (Assign ltac:(find_witness_is_closed e1) ltac:(find_witness_is_closed e2))
  | Free ?e => exact (Free ltac:(find_witness_is_closed e))
  | Seq ?e1 ?e2 => exact (Seq ltac:(find_witness_is_closed e1) ltac:(find_witness_is_closed e2))
  | If ?e1 ?e2 ?e3 => exact
    (If ltac:(find_witness_is_closed e1)
      ltac:(find_witness_is_closed e2) ltac:(find_witness_is_closed e3))
  | While ?e1 ?e2 => exact (While ltac:(find_witness_is_closed e1) ltac:(find_witness_is_closed e2))
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
*)
Hint Unfold inc_set : is_closed_db.

Lemma is_closed_value_assign_array_at :
  is_closed_value assign_array_at.
Proof.
  unfold assign_array_at, StringLam. simpl.
  fold_all_inc_set_string.
  auto 20 with is_closed_db.
Qed.

Opaque assign_array_at.

Corollary is_limited_value_assign_array_at :
  is_limited_value Empty_set (fun x => match x with end) assign_array_at.
Proof.
  apply is_closed_value_assign_array_at.
Qed.

Global Hint Resolve is_closed_value_assign_array_at : is_closed_db.
Global Hint Resolve is_limited_value_assign_array_at : is_closed_db.

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
  unfold incr, StringLam. simpl.
  fold_all_inc_set_string.
  auto 20 with is_closed_db.
Qed.

Opaque incr.

Corollary is_limited_value_incr :
  is_limited_value Empty_set (fun x => match x with end) incr.
Proof.
  apply is_closed_value_incr.
Qed.

Global Hint Resolve is_closed_value_incr : is_closed_db.
Global Hint Resolve is_limited_value_incr : is_closed_db.

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
      (P := $2 <*> <exists> i A',
        $(3+(s-Z.to_nat i)*_) <*>
        (array_content (List.repeat (Some x) (Z.to_nat i) ++ A') a <*>
        <(x0 :== Int i)> <*> <[(i >= 0)%Z]> <*> <[(i <= Z.of_nat s)%Z]> <*>
        <[List.length A' = s - Z.to_nat i]>)%list).
    { prove_implies. apply implies_spec. intros. exists 0%Z, A. simpl.
      rewrite Nat.sub_0_r. revert_implies. prove_implies. apply implies_spec.
      intros. swap_star. solve_star. swap_star. solve_star; lia. }
    { prove_implies_refl. }
    apply triple_while with
      (Q := fun b => <exists> i A', $(1+(s - Z.to_nat i)*16) <*>
        (array_content (List.repeat (Some x) (Z.to_nat i) ++ A') a <*>
        <(x0 :== Int i)>) <*> (<[(i >= 0)%Z]> <*> <[(i <= Z.of_nat s)%Z]> <*>
        <[List.length A' = s - Z.to_nat i]> <*> <[b = (i <? Z.of_nat s)%Z]>)).
    + repeat triple_pull_exists. triple_pull_1_credit.
      eapply triple_weaken, triple_clt with
        (Q1 := fun i1 => <exists> A',
          $_ <*> (_ <*> <(x0 :== Int i1)>) <*>
          (<[(i1 >= 0)%Z]> <*> <[(i1 <= Z.of_nat s)%Z]> <*>
          <[List.length A' = _]>))
        (Q2 := fun i1 i2 => <[i2 = Z.of_nat s]> <*> <exists> A',
          ($_ <*> (_ <*> <(x0 :== Int i1)>)) <*>
          (<[(i1 >= 0)%Z]> <*> <[(i1 <= Z.of_nat s)%Z]> <*>
          <[List.length A' = _]>)).
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
    + repeat triple_pull_exists. triple_reorder_pure. repeat triple_pull_pure.
      match goal with
      | [H : true = (_ <? _)%Z |- _] => symmetry in H; apply Z.ltb_lt in H
      end.
      destruct s; [simpl in *; lia|]. rewrite Nat.sub_succ_l in *; try lia.
      lazymatch goal with
      | [H : List.length ?L = S (_ - _) |- _] =>
        destruct L; [discriminate|injection H as H]
      end.
      simpl "*".
      pose proof triple_fun_n_ary_app as Hn_ary.
      pose proof triple_fun_n_ary_frame as Hframe.
      pose proof triple_fun_n_ary_weaken as Hweaken.
      triple_pull_1_credit.
      eapply triple_seq with (Q1 := (array_content _ a <*> _) <*> ($ _)).
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
          eapply Hassign_array_at with
            (A1 := List.repeat (Some x) (Z.to_nat _));
          eauto. }
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
          { f_equal. rewrite List.repeat_length. symmetry. apply Z2Nat.id. lia. }
          revert_implies. prove_implies. }
      * triple_reorder_credits.
        triple_pull_credits 7. triple_reorder_credits.
        triple_pull_credits 4. triple_reorder_credits.
        triple_pull_credits 3. triple_reorder_credits.
        triple_pull_credits 0. triple_reorder_credits.
        repeat match goal with
        | [H : ?T _ _ |- _] =>
          let TT := ltac:(type of T) in
          unify TT (StateAssertion string);
          (*idtac H T;*) clear H
        end.
        eapply triple_weaken with
          (P := ($_ <*> ($_ <*> ($_ <*> ($_ <*> <(_ :== _)>)))) <*>
            (array_content _ _ <*> $ _))
          (Q := fun v => $3 <*> (<[_ = _]> <*> <(_ :== _)>) <*>
            (array_content _ _ <*> $ _)).
        { prove_implies. }
        { apply implies_post_spec. intros. normalize_star. swap_star_ctx.
          normalize_star. solve_star; eauto. swap_star. apply star_exists_l.
          eexists (Z.succ _). solve_star. swap_star. solve_star. swap_star.
          solve_star. swap_star. solve_star.
          { rewrite Z.ge_le_iff in *. eauto using Z.le_le_succ_r. }
          { lia. }
          { rewrite Z2Nat.inj_succ; try lia. simpl. eassumption. }
          rewrite Z2Nat.inj_succ; try lia. simpl List.repeat.
          rewrite List.repeat_cons, <- List.app_assoc. simpl.
          swap_star. revert_implies. prove_implies. }
        apply triple_frame.
        lazymatch goal with
        | [|- triple (_ <* Val ?v) _ _] =>
          let x := ltac:(fresh "v") in
          remember v as x; generalize dependent x
        end.
        match goal with
        | [|-
          forall a, _ ->
            triple (Val (@?f a) <* (@?e1 a))
              ($0 <*> (@?P0 a))
              (@?Q1 a)
          ] =>
          let x := ltac:(fresh a) in
          intros x ?;
          specialize Hn_ary with
            (v := f x) (e := e1 x) (es := []%list)
            (P := P0 x) (Q2 := fun x => Q1 x)
        end.
        pose proof triple_fun_n_ary_incr as Hincr.
        specialize (Hframe _ incr 0).
        specialize (Hweaken _ incr 0).
        simpl in Hn_ary, Hincr, Hframe, Hweaken. eapply Hn_ary.
        { rewrite <- Z.add_1_r. eapply Hweaken, Hframe, Hincr.
          { intros. apply implies_refl. }
          { intros. simpl. prove_implies. } }
        { solve_simple_value. revert_implies. prove_implies_refl. }
        { simpl. apply implies_spec. intros. do 2 (swap_star; solve_star).
          revert_implies. prove_implies. }
  - repeat triple_pull_exists. triple_reorder_pure. repeat triple_pull_pure.
    lazymatch goal with
    | [H : List.length ?L = s - ?n |- _] =>
      assert (n = s /\ List.length L = 0) as (->&?) by lia;
      destruct L; [|discriminate]
    end.
    rewrite Nat.sub_diag, List.app_nil_r. simpl.
    eapply triple_weaken, triple_free.
    { prove_implies_rev. }
    { intros. prove_implies. }
    solve_simple_value.
Qed.

Lemma triple_fun_n_ary_init_array A s :
  s = List.length A ->
  triple_fun_n_ary 2 init_array
    (fun a v2 x => <[v2 = Int (Z.of_nat s)]> <*> $ (8 + s*16) <*> array_content A a)
    (fun a _ x v => <[v = U_val]> <*> array_content (List.repeat (Some x) s) a).
Proof.
  unfold triple_fun_n_ary, triple_fun, init_array, StringLam. simpl. intros Hs a ?.
  repeat (rewrite map_v_shift_closed;
    [|repeat apply map_v_closed_value; auto with is_closed_db]).
  app_lambda. solve_simple_value. normalize_star. subst.
  split_all; auto. intros. cbn. subst. triple_pull_pure. subst.
  solve_simple_value. rewrite_empty_spec. rewrite pure_spec. split_all; auto.
  intros v2 ?. app_lambda. solve_simple_value. normalize_star. subst.
  split_all; auto. intros. cbn. triple_pull_pure. subst. solve_simple_value.
  rewrite_empty_spec. rewrite pure_spec. split_all; auto. intros x ?.
  triple_reorder_credits. app_lambda. solve_simple_value. swap_star_ctx.
  normalize_star. subst. split_all; auto. intros. cbn.
  triple_reorder_pure. triple_pull_pure. subst. triple_pull_1_credit.
  app_lambda.
  2:{ triple_pull_1_credit.
      eapply triple_ref with (Q := fun v => <[v = Int 0]> <*> _).
      solve_simple_value. }
  solve_simple_value. split_all; auto. intros. cbn. repeat triple_pull_exists.
  triple_reorder_pure. repeat triple_pull_pure. subst. triple_pull_1_credit.
  remember (List.length A) as s eqn:Hs.
  rewrite_all_binds. eapply triple_seq.
  - triple_reorder_credits. triple_pull_credits 2. triple_reorder_credits.
    eapply triple_weaken with
      (P := $2 <*> <exists> i A',
        $(3+(s-Z.to_nat i)*_) <*>
        (array_content (List.repeat (Some x) (Z.to_nat i) ++ A') a <*>
        <(x0 :== Int i)> <*> <[(i >= 0)%Z]> <*> <[(i <= Z.of_nat s)%Z]> <*>
        <[List.length A' = s - Z.to_nat i]>)%list).
    { prove_implies. apply implies_spec. intros. exists 0%Z, A. simpl.
      rewrite Nat.sub_0_r. revert_implies. prove_implies. apply implies_spec.
      intros. swap_star_ctx. normalize_star. subst.
      swap_star. solve_star. swap_star. solve_star; lia. }
    { prove_implies_refl. }
    apply triple_while with
      (Q := fun b => <exists> i A', $(1+(s - Z.to_nat i)*16) <*>
        (array_content (List.repeat (Some x) (Z.to_nat i) ++ A') a <*>
        <(x0 :== Int i)>) <*> (<[(i >= 0)%Z]> <*> <[(i <= Z.of_nat s)%Z]> <*>
        <[List.length A' = s - Z.to_nat i]> <*> <[b = (i <? Z.of_nat s)%Z]>)).
    + repeat triple_pull_exists. triple_pull_1_credit.
      eapply triple_weaken, triple_clt with
        (Q1 := fun i1 => <exists> A',
          $_ <*> (_ <*> <(x0 :== Int i1)>) <*>
          (<[(i1 >= 0)%Z]> <*> <[(i1 <= Z.of_nat s)%Z]> <*>
          <[List.length A' = _]>))
        (Q2 := fun i1 i2 => <[i2 = Z.of_nat s]> <*> <exists> A',
          ($_ <*> (_ <*> <(x0 :== Int i1)>)) <*>
          (<[(i1 >= 0)%Z]> <*> <[(i1 <= Z.of_nat s)%Z]> <*>
          <[List.length A' = _]>)).
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
    + repeat triple_pull_exists. triple_reorder_pure. repeat triple_pull_pure.
      match goal with
      | [H : true = (_ <? _)%Z |- _] => symmetry in H; apply Z.ltb_lt in H
      end.
      destruct s; [simpl in *; lia|]. rewrite Nat.sub_succ_l in *; try lia.
      lazymatch goal with
      | [H : List.length ?L = S (_ - _) |- _] =>
        destruct L; [discriminate|injection H as H]
      end.
      simpl "*".
      pose proof triple_fun_n_ary_app as Hn_ary.
      pose proof triple_fun_n_ary_frame as Hframe.
      pose proof triple_fun_n_ary_weaken as Hweaken.
      triple_pull_1_credit.
      eapply triple_seq with (Q1 := (array_content _ a <*> _) <*> ($ _)).
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
          eapply Hassign_array_at with
            (A1 := List.repeat (Some x) (Z.to_nat _));
          eauto. }
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
          { f_equal. rewrite List.repeat_length. symmetry. apply Z2Nat.id. lia. }
          revert_implies. prove_implies. }
      * triple_reorder_credits.
        triple_pull_credits 7. triple_reorder_credits.
        triple_pull_credits 4. triple_reorder_credits.
        triple_pull_credits 3. triple_reorder_credits.
        triple_pull_credits 0. triple_reorder_credits.
        repeat match goal with
        | [H : ?T _ _ |- _] =>
          let TT := ltac:(type of T) in
          unify TT (StateAssertion string);
          (*idtac H T;*) clear H
        end.
        eapply triple_weaken with
          (P := ($_ <*> ($_ <*> ($_ <*> ($_ <*> <(_ :== _)>)))) <*>
            (array_content _ _ <*> $ _))
          (Q := fun v => $3 <*> (<[_ = _]> <*> <(_ :== _)>) <*>
            (array_content _ _ <*> $ _)).
        { prove_implies. }
        { apply implies_post_spec. intros. normalize_star. swap_star_ctx.
          normalize_star. solve_star; eauto. swap_star. apply star_exists_l.
          eexists (Z.succ _). solve_star. swap_star. solve_star. swap_star.
          solve_star. swap_star. solve_star.
          { rewrite Z.ge_le_iff in *. eauto using Z.le_le_succ_r. }
          { lia. }
          { rewrite Z2Nat.inj_succ; try lia. simpl. eassumption. }
          rewrite Z2Nat.inj_succ; try lia. simpl List.repeat.
          rewrite List.repeat_cons, <- List.app_assoc. simpl.
          swap_star. revert_implies. prove_implies. }
        apply triple_frame.
        lazymatch goal with
        | [|- triple (_ <* Val ?v) _ _] =>
          let x := ltac:(fresh "v") in
          remember v as x; generalize dependent x
        end.
        match goal with
        | [|-
          forall a, _ ->
            triple (Val (@?f a) <* (@?e1 a))
              ($0 <*> (@?P0 a))
              (@?Q1 a)
          ] =>
          let x := ltac:(fresh a) in
          intros x ?;
          specialize Hn_ary with
            (v := f x) (e := e1 x) (es := []%list)
            (P := P0 x) (Q2 := fun x => Q1 x)
        end.
        pose proof triple_fun_n_ary_incr as Hincr.
        specialize (Hframe _ incr 0).
        specialize (Hweaken _ incr 0).
        simpl in Hn_ary, Hincr, Hframe, Hweaken. eapply Hn_ary.
        { rewrite <- Z.add_1_r. eapply Hweaken, Hframe, Hincr.
          { intros. apply implies_refl. }
          { intros. simpl. prove_implies. } }
        { solve_simple_value. revert_implies. prove_implies_refl. }
        { simpl. apply implies_spec. intros. do 2 (swap_star; solve_star).
          revert_implies. prove_implies. }
  - repeat triple_pull_exists. triple_reorder_pure. repeat triple_pull_pure.
    lazymatch goal with
    | [H : List.length ?L = s - ?n |- _] =>
      assert (n = s /\ List.length L = 0) as (->&?) by lia;
      destruct L; [|discriminate]
    end.
    rewrite Nat.sub_diag, List.app_nil_r. simpl.
    eapply triple_weaken, triple_free.
    { prove_implies_rev. }
    { intros. prove_implies. }
    solve_simple_value.
Qed.

Ltac rewrite_all_map_v_closed :=
  repeat (rewrite map_v_shift_closed;
    [|repeat apply map_v_closed_value; auto with is_closed_db]).

Lemma is_closed_value_init_array :
  is_closed_value init_array.
Proof.
  unfold init_array, StringLam. simpl.
  rewrite_all_map_v_closed.
  fold_all_inc_set_string.
  auto 40 with is_closed_db.
Qed.

Opaque init_array.

Corollary is_limited_value_init_array :
  is_limited_value Empty_set (fun x => match x with end) init_array.
Proof.
  apply is_closed_value_init_array.
Qed.

Global Hint Resolve is_closed_value_init_array : is_closed_db.
Global Hint Resolve is_limited_value_init_array : is_closed_db.
(*
Lemma triple_fun_n_ary_free_array A s :
  s = List.length A ->
  triple_fun_n_ary 2 free_array (* TODO *)
    (fun a v2 x => <[v2 = Int (Z.of_nat s)]> <*> $ (8 + s*16) <*> array_content A a)
    (fun a _ x v => <[v = U_val]> <*> array_content (List.repeat (Some x) s) a).
Proof.
  unfold triple_fun_n_ary, triple_fun, init_array, StringLam. simpl. intros Hs a ?.
  repeat (rewrite map_v_shift_closed;
    [|repeat apply map_v_closed_value; auto with is_closed_db]).
  app_lambda. solve_simple_value. normalize_star. subst.
  split_all; auto. intros. cbn. subst. triple_pull_pure. subst.
  solve_simple_value. rewrite_empty_spec. rewrite pure_spec. split_all; auto.
  intros v2 ?. app_lambda. solve_simple_value. normalize_star. subst.
  split_all; auto. intros. cbn. triple_pull_pure. subst. solve_simple_value.
  rewrite_empty_spec. rewrite pure_spec. split_all; auto. intros x ?.
  triple_reorder_credits. app_lambda. solve_simple_value. swap_star_ctx.
  normalize_star. subst. split_all; auto. intros. cbn.
  triple_reorder_pure. triple_pull_pure. subst. triple_pull_1_credit.
  app_lambda.
  2:{ triple_pull_1_credit.
      eapply triple_ref with (Q := fun v => <[v = Int 0]> <*> _).
      solve_simple_value. }
  solve_simple_value. split_all; auto. intros. cbn. repeat triple_pull_exists.
  triple_reorder_pure. repeat triple_pull_pure. subst. triple_pull_1_credit.
  remember (List.length A) as s eqn:Hs.
  rewrite_all_binds. eapply triple_seq.
  - triple_reorder_credits. triple_pull_credits 2. triple_reorder_credits.
    eapply triple_weaken with
      (P := $2 <*> <exists> i A',
        $(3+(s-Z.to_nat i)*_) <*>
        (array_content (List.repeat (Some x) (Z.to_nat i) ++ A') a <*>
        <(x0 :== Int i)> <*> <[(i >= 0)%Z]> <*> <[(i <= Z.of_nat s)%Z]> <*>
        <[List.length A' = s - Z.to_nat i]>)%list).
    { prove_implies. apply implies_spec. intros. exists 0%Z, A. simpl.
      rewrite Nat.sub_0_r. revert_implies. prove_implies. apply implies_spec.
      intros. swap_star_ctx. normalize_star. subst.
      swap_star. solve_star. swap_star. solve_star; lia. }
    { prove_implies_refl. }
    apply triple_while with
      (Q := fun b => <exists> i A', $(1+(s - Z.to_nat i)*16) <*>
        (array_content (List.repeat (Some x) (Z.to_nat i) ++ A') a <*>
        <(x0 :== Int i)>) <*> (<[(i >= 0)%Z]> <*> <[(i <= Z.of_nat s)%Z]> <*>
        <[List.length A' = s - Z.to_nat i]> <*> <[b = (i <? Z.of_nat s)%Z]>)).
    + repeat triple_pull_exists. triple_pull_1_credit.
      eapply triple_weaken, triple_clt with
        (Q1 := fun i1 => <exists> A',
          $_ <*> (_ <*> <(x0 :== Int i1)>) <*>
          (<[(i1 >= 0)%Z]> <*> <[(i1 <= Z.of_nat s)%Z]> <*>
          <[List.length A' = _]>))
        (Q2 := fun i1 i2 => <[i2 = Z.of_nat s]> <*> <exists> A',
          ($_ <*> (_ <*> <(x0 :== Int i1)>)) <*>
          (<[(i1 >= 0)%Z]> <*> <[(i1 <= Z.of_nat s)%Z]> <*>
          <[List.length A' = _]>)).
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
    + repeat triple_pull_exists. triple_reorder_pure. repeat triple_pull_pure.
      match goal with
      | [H : true = (_ <? _)%Z |- _] => symmetry in H; apply Z.ltb_lt in H
      end.
      destruct s; [simpl in *; lia|]. rewrite Nat.sub_succ_l in *; try lia.
      lazymatch goal with
      | [H : List.length ?L = S (_ - _) |- _] =>
        destruct L; [discriminate|injection H as H]
      end.
      simpl "*".
      pose proof triple_fun_n_ary_app as Hn_ary.
      pose proof triple_fun_n_ary_frame as Hframe.
      pose proof triple_fun_n_ary_weaken as Hweaken.
      triple_pull_1_credit.
      eapply triple_seq with (Q1 := (array_content _ a <*> _) <*> ($ _)).
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
          eapply Hassign_array_at with
            (A1 := List.repeat (Some x) (Z.to_nat _));
          eauto. }
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
          { f_equal. rewrite List.repeat_length. symmetry. apply Z2Nat.id. lia. }
          revert_implies. prove_implies. }
      * triple_reorder_credits.
        triple_pull_credits 7. triple_reorder_credits.
        triple_pull_credits 4. triple_reorder_credits.
        triple_pull_credits 3. triple_reorder_credits.
        triple_pull_credits 0. triple_reorder_credits.
        repeat match goal with
        | [H : ?T _ _ |- _] =>
          let TT := ltac:(type of T) in
          unify TT (StateAssertion string);
          (*idtac H T;*) clear H
        end.
        eapply triple_weaken with
          (P := ($_ <*> ($_ <*> ($_ <*> ($_ <*> <(_ :== _)>)))) <*>
            (array_content _ _ <*> $ _))
          (Q := fun v => $3 <*> (<[_ = _]> <*> <(_ :== _)>) <*>
            (array_content _ _ <*> $ _)).
        { prove_implies. }
        { apply implies_post_spec. intros. normalize_star. swap_star_ctx.
          normalize_star. solve_star; eauto. swap_star. apply star_exists_l.
          eexists (Z.succ _). solve_star. swap_star. solve_star. swap_star.
          solve_star. swap_star. solve_star.
          { rewrite Z.ge_le_iff in *. eauto using Z.le_le_succ_r. }
          { lia. }
          { rewrite Z2Nat.inj_succ; try lia. simpl. eassumption. }
          rewrite Z2Nat.inj_succ; try lia. simpl List.repeat.
          rewrite List.repeat_cons, <- List.app_assoc. simpl.
          swap_star. revert_implies. prove_implies. }
        apply triple_frame.
        lazymatch goal with
        | [|- triple (_ <* Val ?v) _ _] =>
          let x := ltac:(fresh "v") in
          remember v as x; generalize dependent x
        end.
        match goal with
        | [|-
          forall a, _ ->
            triple (Val (@?f a) <* (@?e1 a))
              ($0 <*> (@?P0 a))
              (@?Q1 a)
          ] =>
          let x := ltac:(fresh a) in
          intros x ?;
          specialize Hn_ary with
            (v := f x) (e := e1 x) (es := []%list)
            (P := P0 x) (Q2 := fun x => Q1 x)
        end.
        pose proof triple_fun_n_ary_incr as Hincr.
        specialize (Hframe _ incr 0).
        specialize (Hweaken _ incr 0).
        simpl in Hn_ary, Hincr, Hframe, Hweaken. eapply Hn_ary.
        { rewrite <- Z.add_1_r. eapply Hweaken, Hframe, Hincr.
          { intros. apply implies_refl. }
          { intros. simpl. prove_implies. } }
        { solve_simple_value. revert_implies. prove_implies_refl. }
        { simpl. apply implies_spec. intros. do 2 (swap_star; solve_star).
          revert_implies. prove_implies. }
  - repeat triple_pull_exists. triple_reorder_pure. repeat triple_pull_pure.
    lazymatch goal with
    | [H : List.length ?L = s - ?n |- _] =>
      assert (n = s /\ List.length L = 0) as (->&?) by lia;
      destruct L; [|discriminate]
    end.
    rewrite Nat.sub_diag, List.app_nil_r. simpl.
    eapply triple_weaken, triple_free.
    { prove_implies_rev. }
    { intros. prove_implies. }
    solve_simple_value.
Qed.
*)

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

Definition is_nat_fun_of_val_list {V}
  (L : list (option (Value V))) (f : nat -> option nat) : Prop :=
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

Ltac clear_state_assertions :=
  repeat match goal with
  | [H : ?P ?c ?m |- _] =>
    let T := ltac:(type of P) in
    unify T (StateAssertion string);
    clear c m H
  end.

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
      is_weighted_graph g vg <*> <[V g src]> <*> <[~ E g src src]>)
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
  specialize h_empty_cost_exists as (c_h_empty&?).
  eexists ?[c0], ?[cn], ?[cm]. intros. simpl. unfold triple_fun, generic_dijkstra, StringLam. simpl. intros.
  specialize mkheap_cost_exists with n C as (c_mkheap&?).
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
  (*Set Printing Implicit.*)
  fold_all_inc_set_string.
  repeat rewrite bind_v_liftS_shift_swap. repeat rewrite bind_v_shift. repeat rewrite bind_v_id. simpl.
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
  solve_simple_value. split_all; auto. intros. cbn.
  repeat rewrite bind_v_liftS_shift_swap. repeat rewrite bind_v_shift. repeat rewrite bind_v_id. simpl.
  triple_reorder_exists. triple_pull_exists. triple_reorder_pure. repeat triple_pull_pure.
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
  solve_simple_value. split_all; auto. intros. cbn.
  repeat rewrite bind_v_liftS_shift_swap. repeat rewrite bind_v_shift. repeat rewrite bind_v_id. simpl.
  triple_reorder_exists. repeat triple_pull_exists. triple_reorder_pure. repeat triple_pull_pure. subst.
  lazymatch goal with
  | [H1 : is_set_size (V (G g)) ?n1,
     H2 : is_set_size (V (G g)) ?n2
    |- _ ] => apply (is_set_size_unique _ _ _ _ H1) in H2 as <-
  end.
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
      instantiate (c0 := S ?[cc0]). instantiate (cc0 := ?[c0]). triple_pull_1_credit.
      eapply triple_weaken, triple_frame, triple_fun_app.
      3:{ apply Hspec_mkheap. admit. }
      3:solve_simple_value.
      { apply implies_spec. intros. solve_star. swap_star. solve_star. swap_star. eassumption. }
      { apply implies_post_spec. intros. normalize_star. solve_star; [apply triple_fun_frame; eassumption|].
        simpl. solve_star. swap_star. solve_star. swap_star. eassumption. }
    }
    1:{ prove_implies_refl. }
  }
  clear mkheap Hspec_mkheap.
  solve_simple_value. split_all; auto. intros. cbn.
  repeat rewrite bind_v_liftS_shift_swap. repeat rewrite bind_v_shift. repeat rewrite bind_v_id. simpl.
  instantiate (c0 := S ?[cc0]). instantiate (cc0 := ?[c0]).
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
  solve_simple_value. split_all; auto. intros. cbn.
  repeat rewrite bind_v_liftS_shift_swap. repeat rewrite bind_v_shift. repeat rewrite bind_v_id. simpl.
  triple_reorder_exists. repeat triple_pull_exists.
  triple_reorder_pure. repeat triple_pull_pure. subst.
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
  solve_simple_value. split_all; auto. intros. cbn.
  repeat rewrite bind_v_liftS_shift_swap. repeat rewrite bind_v_shift. repeat rewrite bind_v_id. simpl.
  triple_reorder_exists. repeat triple_pull_exists.
  triple_reorder_pure. repeat triple_pull_pure. subst.
  instantiate (c0 := S ?[cc0]). instantiate (cc0 := ?[c0]).
  triple_pull_1_credit. rewrite Nat2Z.id.
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
    triple_pull_credits (11 + n*16). triple_reorder_credits.
    eapply triple_weaken with (P := ($_ <*> array_content _ _) <*> ($ (_ + _) <*> is_weighted_graph _ _<*> is_heap _ _ _ _ _ _ <*> array_content _ _)), triple_frame.
    { prove_implies_rev. }
    { intros. apply star_assoc_r. }
    triple_reorder_credits. triple_pull_credits 3. triple_reorder_credits. triple_pull_credits 2. triple_reorder_credits.
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
      eapply triple_weaken with (P := ($_ <*> array_content _ _) <*> ($ (_ + _) <*> is_weighted_graph _ _<*> is_heap _ _ _ _ _ _ <*> array_content _ _)), triple_frame.
      { prove_implies_rev. }
      { intros. apply star_assoc_r. }
      triple_reorder_credits. triple_pull_credits 3. triple_reorder_credits. triple_pull_credits 2. triple_reorder_credits.
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
        { assert (src < n) by eauto using init_range_lt_size.
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
        destruct n as [|n'] eqn:Hn; [lia|]. rewrite <- Hn.
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
              (P := ($2 <*> ($1 <*> ($ (S t_credits) <*> (is_heap n _ _ _ _ v)))) <*> ($ _ <*> $ _ <*> _)),
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
            { lazymatch goal with
              | [H1 : is_max_label g _, H2 : is_max_label g _ |- _] =>
                specialize (max_label_unique _ _ _ _ H1 H2) as ->
              end.
              subst. assumption. }
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
          ++ lazymatch goal with
            | [|- triple _
                (_ <*> (_ <*> (_ <*> (_ <*>
                  array_content ?pred _ <*> array_content ?D _ <*> _))))
                _
              ] =>
              remember pred as pred_list eqn:Hpred_list;
              remember D as D_list eqn:HD_list
            end.
            assert (is_nat_fun_of_val_list D_list (fun i => if i =? src then Some 0 else None)).
            { subst. unfold is_nat_fun_of_val_list, fun_of_list. intros.
              destruct Nat.eqb_spec with i src.
              { subst. rewrite List.app_nth2; rewrite List.repeat_length; [|lia].
                rewrite Nat.sub_diag. simpl. split; intros [= ?]; repeat f_equal; lia. }
              { assert (i < src \/ i > src) as [] by lia.
                { rewrite List.app_nth1; [|rewrite List.repeat_length; lia].
                  erewrite List.nth_error_nth; [|apply List.nth_error_repeat; lia].
                  split; [|discriminate]. intros [= ?]. lia. }
                { rewrite List.app_nth2; rewrite List.repeat_length; [|lia].
                  destruct i as [|i]; [lia|]. rewrite Nat.sub_succ_l; [|lia].
                  simpl.
                  assert (i < n' \/ i >= n') as [] by lia.
                  { erewrite List.nth_error_nth; [|apply List.nth_error_repeat; lia].
                    split; [|discriminate]. intros [= ?]. lia. }
                  { rewrite List.nth_overflow; [|rewrite List.repeat_length; lia].
                    split; discriminate. } } } }
            assert (is_nat_fun_of_val_list pred_list (fun i => None)).
            { subst. unfold is_nat_fun_of_val_list, fun_of_list. intros.
              assert (i < S n' \/ i >= S n') as [] by lia.
              { erewrite List.nth_error_nth; [|apply List.nth_error_repeat; lia].
                split; [|discriminate]. intros [= ?]. lia. }
              { rewrite List.nth_overflow; [|rewrite List.repeat_length; lia].
                split; discriminate. } }
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
                constr:($2 <*> ((<exists> D_list pred_list P P' D pred sv se,
                <[(P = empty /\ P' = P0) \/ P' = neighbourhood g P]> <*>
                <[is_set_size P sv]> <*>
                <[is_set_size (uncurry (E (induced_subgraph P g))) se]> <*>
                <[sv < n]> <*>
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
                <[(P = empty /\ P' = P0) \/ P' = neighbourhood g P]> <*>
                <[is_set_size P sv]> <*>
                <[is_set_size P' sv']> <*>
                <[is_set_size (uncurry (E (induced_subgraph P g))) se]> <*>
                <[sv < n]> <*>
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
                eexists D_list, pred_list, empty, (set_sum _ _), D, pred, 0, 0.
                solve_star.
                { apply empty_set_size. }
                { apply equiv_set_size with empty.
                  { unfold set_equiv. intros []. simpl. unfold empty. tauto. }
                  { apply empty_set_size. } }
                { lia. }
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
                    ?X = ?P |- _] =>
                apply subset_size with (P' := P) in Hsize as (?&?&?)
              end.
              { lazymatch goal with
                | [H : (_ = empty /\ ?P' = set_sum empty _) \/
                        ?P' = neighbourhood _ _ |- _] =>
                  assert (exists s, is_set_size P' s) as (?&?);
                    [destruct H as [(?&->)| ->]; eexists|]
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
                  | [H : (_ = empty /\ _ = set_sum empty _) \/
                          _ = neighbourhood _ _ |- _] =>
                    destruct H as [(?&?) | ?]
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
                      eauto.
                    revert_implies. prove_implies_rev. apply implies_spec.
                    intros. solve_star. eassumption. }
                  { solve_star;
                      try lazymatch goal with
                      [|- Dijkstra_invariant _ _ _ _ _] => eassumption
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
              triple_reorder_credits.
              erewrite (Nat.mul_comm _ (n - _)). rewrite Hn.
              rewrite Nat.sub_succ_l; [|lia]. rewrite <- Hn. simpl "*".
              erewrite (Nat.mul_add_distr_r _ ((n' - _) * _)).
              erewrite (Nat.mul_comm _ (S _)). simpl "*".
              erewrite <- (Nat.add_assoc _ _ ((n' - _)*_*_)).
              erewrite (Nat.add_assoc (_ * (m - _))).
              erewrite (Nat.add_comm (_ * (m-_)) _).
              erewrite <- (Nat.add_assoc _ (_ * (m - _))).
              lazymatch goal with
              | [|- triple _ ($ (?c0 + (?c1 + _)) <*> _) _] =>
                rewrite (Nat.add_assoc c0 c1), (Nat.add_comm c0 c1),
                  <- (Nat.add_assoc c1 c0)
              end.
              rewrite Bool.negb_true_iff, Nat.eqb_neq in *.
              lazymatch goal with
              | [Hneq : ?s <> 0,
                 Hsize : is_set_size _ ?s,
                 Hinvariant : Dijkstra_invariant ?D ?pred _ _ _ |- _] =>
                eapply nonempty_has_min_cost_elem_option_nat
                  with (W := D) in Hsize as (x_min&Hmincost);
                  unfold Decidable.decidable; try lia;
                assert (exists y, D x_min = Some y) as Hissome
              end.
              { lazymatch goal with
                | [H : (_ = empty /\ _ = set_sum empty _) \/
                        _ = neighbourhood _ _ |- _] =>
                  destruct H as [(?&?) | ?]
                end.
                { lazymatch goal with
                  | [H : Dijkstra_invariant _ _ _ _ _ |- _] =>
                    unfold Dijkstra_invariant,
                      Dijkstra_distance_invariant,
                      Dijkstra_predecessors_invariant,
                      are_valid_distances in H;
                    destruct H as (?&Hdist_inv&Hpred_inv)
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
              instantiate (cn := S ?[ccn]). instantiate (ccn := ?[cn]).
              triple_pull_1_credit.
              app_lambda.
              2:{
                unfold h_extract_min_spec in Hspec_h_extract_min.
                erewrite <- Hpot, <- (Nat.add_assoc potential),
                  (Nat.add_assoc _ potential), (Nat.add_comm _ potential),
                  <- (Nat.add_assoc potential).
                triple_reorder_credits. triple_pull_credits potential.
                triple_reorder_credits.
                specialize Hspec_h_extract_min with (n := n) (C := x1) (P := x6) (W := x7) (p := x) (h := v).
                eapply triple_weaken, triple_frame, triple_fun_app.
                4:solve_simple_value.
                3:{ apply Hspec_h_extract_min; eassumption. }
                { rewrite <- Hpot. apply implies_spec. intros. solve_star.
                  swap_star. solve_star. conormalize_star. swap_star_ctx.
                  revert_implies. prove_implies. }
                { prove_implies_refl. }
              }
              solve_simple_value. split; auto. intros. cbn.
              repeat rewrite bind_v_liftS_shift_swap. repeat rewrite bind_v_shift. repeat rewrite bind_v_id.
              triple_reorder_exists. repeat triple_pull_exists.
              triple_reorder_pure. repeat triple_pull_pure. revert Hn Hpot.
              subst. intros. triple_reorder_credits.
              instantiate (cn := S (S ?[ccn])). instantiate (ccn := ?[cn]).
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
              solve_simple_value. split; auto. intros. cbn.
              repeat rewrite bind_v_liftS_shift_swap. repeat rewrite bind_v_shift. repeat rewrite bind_v_id.
              triple_pull_pure. revert Hpot Hn. subst. intros.
              instantiate (cn := S (S ?[ccn])). instantiate (ccn := ?[cn]).
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
              solve_simple_value. split; auto. intros. cbn.
              repeat rewrite bind_v_liftS_shift_swap. repeat rewrite bind_v_shift. repeat rewrite bind_v_id.
              triple_pull_pure. revert Hpot Hn. subst. intros.
              clear_state_assertions.
              instantiate (cn := S (S ?[ccn])).
              instantiate (ccn := ?[cn]). simpl. triple_pull_1_credit.
              app_lambda.
              2:{
                pose proof triple_fun_n_ary_app as Hn_ary.
                pose proof triple_fun_n_ary_weaken as Hweaken.
                unfold get_neighbours_spec in Hspec_get_neighbours.
                triple_pull_1_credit. apply triple_ref.
                triple_pull_credits (1+S c_neighbours). triple_reorder_credits.
                triple_pull_credits 2. triple_pull_1_credit.
                lazymatch goal with
                | [|- triple (Val get_neighbours <* Val ?v <* _) _ _] =>
                  eapply triple_weaken with
                    (P := ($1 <*> ($1 <*> ($ c_neighbours <*> is_weighted_graph g v))) <*> ($ _ <*> $ _ <*> $ _ <*> _)),
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
                          _ = neighbourhood _ _ |- _] =>
                    destruct H as [(?&->) | ->]
                  end.
                  { unfold set_sum, empty, single in Hx_min.
                    destruct Hx_min as [[]| ->]. assumption. }
                  { unfold neighbourhood in Hx_min.
                    destruct Hx_min as (?&?&?&?%E_closed2). assumption. } }
              }
              solve_simple_value. split; auto. intros. cbn.
              repeat rewrite bind_v_liftS_shift_swap. repeat rewrite bind_v_shift. repeat rewrite bind_v_id.
              triple_reorder_exists. repeat triple_pull_exists.
              triple_reorder_pure. repeat triple_pull_pure.
              admit.
          ++ admit.
Admitted.
