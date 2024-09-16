Require Import src.LambdaRef.
Require Import src.LamRefFacts.
Require Import src.LambdaAssertions_credits_perm.
Require Import src.LambdaTotalTriple_credits_perm.
Require Import src.LamRefLogicFactsTotal_credits_perm.
Require Import List.
Import ListNotations.
Require String.

(* state assertion and triple manipulation tactics *)

Ltac extract_exists P H :=
  match P with
  | <exists> x, _ => idtac
  | (<exists> x, _) <*> ?Q' => apply star_exists_l' in H
  | ?Q <*> (<exists> x, _) => apply star_comm in H; apply star_exists_l' in H
  | ?Q <*> ?Q' => eapply star_implies_mono in H; [clear H; apply implies_spec; intro H; extract_exists Q H|apply implies_refl]; apply star_exists_l' in H
  | ?Q <*> ?Q' => apply star_comm in H; eapply star_implies_mono in H; [clear H; apply implies_spec; intro H; extract_exists Q H|apply implies_refl]; extract_exists Q' H; apply star_exists_l' in H
  end.

Ltac extract_exists_in H :=
  match type of H with
  | ?P ?c ?m => extract_exists P H
  end.

Ltac extract_pure P H :=
  multimatch P with
  | <[_]> => idtac
  | <[_]> <*> ?Q' => idtac
  | ?Q <*> <[_]> => apply star_comm in H
  | ?Q <*> ?Q' => eapply star_implies_mono in H; [|clear H; apply implies_spec; intro H; extract_pure Q H|apply implies_refl]; apply star_assoc_l in H
  | ?Q <*> ?Q' => apply star_comm in H; eapply star_implies_mono in H; [|clear H; apply implies_spec; intro H; extract_pure Q H|apply implies_refl]; apply star_assoc_l in H
  end.

Ltac extract_pure_in H :=
  match type of H with
  | ?P ?c ?m => extract_pure P H
  end.
Ltac id' H :=
  match ltac:(H) with
  | ?X => exact X
  end.

Ltac reorder_pure P :=
  match P with
  | ?Q <*> ?Q' =>
    match ltac:(eval simpl in (ltac:(reorder_pure Q) <*> ltac:(reorder_pure Q'))) with
    | <[?P']> <*> ?Q1' => exact (<[P']> <*> ltac:(reorder_pure Q1'))
    | (<[?P']> <*> ?Q1) <*> ?Q1' => exact (<[P']> <*> ltac:(reorder_pure (Q1 <*> Q1')))
    | ?Q1 <*> <[?P']> => exact (<[P']> <*> ltac:(reorder_pure Q1))
    | ?Q1 <*> (<[?P']> <*> ?Q1') => exact (<[P']> <*> ltac:(reorder_pure (Q1' <*> Q1)))
    end
  | _ => exact P
  end.

Ltac prove_implies_reorder_pure :=
  match goal with
  | [|- ?Q <*> ?Q' ->> _] =>
    eapply implies_trans;
    [apply star_implies_mono; prove_implies_reorder_pure|];
    match goal with
    | [|- <[?P]> <*> ?Q1' ->> _ ] =>
      apply star_implies_mono; [apply implies_refl|];
      prove_implies_reorder_pure
    | [|- (<[?P]> <*> ?Q1) <*> ?Q1' ->> _ ] =>
      eapply implies_trans; [apply star_assoc_r|];
      apply star_implies_mono; [apply implies_refl|];
      prove_implies_reorder_pure
    | [|- ?Q1 <*> <[?P]> ->> _ ] =>
      eapply implies_trans; [apply star_comm|];
      apply star_implies_mono; [apply implies_refl|];
      prove_implies_reorder_pure
    | [|- ?Q1 <*> (<[?P]> <*> ?Q1') ->> _ ] =>
      eapply implies_trans; [apply star_comm|];
      eapply implies_trans; [apply star_assoc_r|];
      apply star_implies_mono; [apply implies_refl|];
      prove_implies_reorder_pure
    end
  | [|- ?P ->> _] => apply implies_refl
  end.
(*
Ltac prove_implies_reorder_pure_bwd :=
  match goal with
  | [|- _ ->> ?Q <*> ?Q'] =>
    eapply implies_trans;
    [|apply star_implies_mono; prove_implies_reorder_pure_bwd];
    match goal with
    | [|- _ ->> <[?P]> <*> ?Q1' ] =>
      apply star_implies_mono; [apply implies_refl|];
      prove_implies_reorder_pure_bwd
    | [|- _ ->> (<[?P]> <*> ?Q1) <*> ?Q1' ] =>
      eapply implies_trans; [|apply star_assoc_r];
      apply star_implies_mono; [apply implies_refl|];
      prove_implies_reorder_pure_bwd
    | [|- _ ->> ?Q1 <*> <[?P]> ] =>
      eapply implies_trans; [|apply star_comm];
      apply star_implies_mono; [apply implies_refl|];
      prove_implies_reorder_pure_bwd
    | [|- _ ->> ?Q1 <*> (<[?P]> <*> ?Q1') ] =>
      eapply implies_trans; [|apply star_comm];
      eapply implies_trans; [|apply star_assoc_r];
      apply star_implies_mono; [apply implies_refl|];
      prove_implies_reorder_pure_bwd
    end
  | [|- _ ->> ?P] => apply implies_refl
  end.
*)
Ltac triple_reorder_pure :=
  match goal with
  | [|- triple ?e ?P' ?Q'] =>
    apply triple_weaken with (P := ltac:(reorder_pure P')) (Q := Q');
      [prove_implies_reorder_pure|intros; apply implies_refl|]
  end.

Ltac triple_pull_pure :=
  match goal with
  | [|- triple ?e <[?P]> ?Q] =>
    apply -> triple_pure; intro
  | [|- triple ?e (<[?P]> <*> ?Q) ?Q'] =>
    apply -> triple_pure_star; intro
  end.

Ltac triple_pull_exists :=
  match goal with
  | [|- triple ?e (<exists> _, _) ?Q] =>
    apply -> triple_exists; intro
  | [|- triple ?e (?Q <*> <exists> _, _) ?Q'] =>
    apply -> triple_exists_star; intro
  end.

Ltac reorder_credits P :=
  match P with
  | ?Q <*> ?Q' =>
    match ltac:(eval simpl in (ltac:(reorder_credits Q) <*> ltac:(reorder_credits Q'))) with
    | sa_credits ?n <*> ?Q1' => exact (sa_credits n <*> ltac:(reorder_credits Q1'))
    | (sa_credits ?n <*> ?Q1) <*> ?Q1' => exact (sa_credits n <*> ltac:(reorder_credits (Q1 <*> Q1')))
    | ?Q1 <*> sa_credits ?n => exact (sa_credits n <*> ltac:(reorder_credits Q1))
    | ?Q1 <*> (sa_credits ?n <*> ?Q1') => exact (sa_credits n <*> ltac:(reorder_credits (Q1' <*> Q1)))
    end
  | _ => exact P
  end.

(*Check ltac:(reorder_credits (<[]> <*> (<[1=1]> <*> <[2=2]> <*> (sa_credits 2 <*> <[3=3]> <*> sa_credits 4) <*> sa_credits 5) : StateAssertion string)).*)

Ltac prove_implies_reorder_credits :=
  match goal with
  | [|- ?Q <*> ?Q' ->> _] =>
    eapply implies_trans;
    [apply star_implies_mono; prove_implies_reorder_credits|];
    match goal with
    | [|- sa_credits _ <*> ?Q1' ->> _ ] =>
      apply star_implies_mono; [apply implies_refl|];
      prove_implies_reorder_credits
    | [|- (sa_credits _ <*> ?Q1) <*> ?Q1' ->> _ ] =>
      eapply implies_trans; [apply star_assoc_r|];
      apply star_implies_mono; [apply implies_refl|];
      prove_implies_reorder_credits
    | [|- ?Q1 <*> sa_credits _ ->> _ ] =>
      eapply implies_trans; [apply star_comm|];
      apply star_implies_mono; [apply implies_refl|];
      prove_implies_reorder_credits
    | [|- ?Q1 <*> (sa_credits _ <*> ?Q1') ->> _ ] =>
      eapply implies_trans; [apply star_comm|];
      eapply implies_trans; [apply star_assoc_r|];
      apply star_implies_mono; [apply implies_refl|];
      prove_implies_reorder_credits
    end
  | [|- ?P ->> _] => apply implies_refl
  end.

Ltac triple_reorder_credits :=
  match goal with
  | [|- triple ?e ?P' ?Q'] =>
    apply triple_weaken with (P := ltac:(reorder_credits P')) (Q := Q');
      [prove_implies_reorder_credits|intros; apply implies_refl|]
  end.
(*
Ltac prove_implies_pull_credits n :=
  match goal with
  | [|- ?Q <*> ?Q' ->> _] =>
    eapply implies_trans;
    [apply star_implies_mono; [prove_implies_pull_credits n|apply implies_refl]|];
    match goal with
    | [|- sa_credits _ <*> ?Q1' ->> _ ] => idtac
    | [|- (sa_credits _ <*> ?Q1) <*> ?Q1' ->> _ ] =>
      eapply implies_trans; [apply star_assoc_r|]
    end
  | [|- ?Q <*> ?Q' ->> _] =>
    eapply implies_trans;
    [apply star_implies_mono; [apply implies_refl|prove_implies_pull_credits n]|];
    match goal with
    | [|- ?Q1 <*> sa_credits _ ->> _ ] =>
      eapply implies_trans; [apply star_comm|]
    | [|- ?Q1 <*> (sa_credits _ <*> ?Q1') ->> _ ] =>
      eapply implies_trans; [apply star_comm|];
      eapply implies_trans; [apply star_assoc_r|]
    end
  | [|- sa_credits _ <*> ?Q ->> _ ] =>
    eapply star_implies_mono;
    [eapply credits_star_r with (c1 := n); reflexivity|apply implies_refl]
  | [|- sa_credits _ ->> _] => eapply credits_star_r with (c1 := n); reflexivity
  | [|- ?P ->> _] => apply implies_refl
  end.
Ltac triple_pull_credits n :=
  match goal with
  | [|- triple ?e ?P' ?Q'] =>
    eapply triple_weaken with (Q := Q');
      [prove_implies_reorder_credits n|intros; apply implies_refl|]
  end.
*)

Ltac triple_pull_credits n :=
  match goal with
  | [|- triple ?e (sa_credits _) ?Q' ] =>
    eapply triple_weaken with (Q := Q');
    [eapply credits_star_r with (c1 := n); reflexivity
    |intros; apply implies_refl
    |]
  | [|- triple ?e (sa_credits _ <*> ?P') ?Q' ] =>
    eapply triple_weaken with (Q := Q');
    [eapply star_implies_mono;
      [eapply credits_star_r with (c1 := n); reflexivity|apply implies_refl]
    |intros; apply implies_refl
    |]
  end.

Ltac triple_pull_1_credit :=
  triple_reorder_credits; triple_pull_credits 1; triple_reorder_credits.

Ltac reorder X P :=
  match P with
  | ?Q <*> ?Q' =>
    match ltac:(eval simpl in (ltac:(reorder X Q) <*> ltac:(reorder X Q'))) with
    | X <*> ?Q1' => exact (X <*> ltac:(reorder X Q1'))
    | (X <*> ?Q1) <*> ?Q1' => exact (X <*> ltac:(reorder X (Q1 <*> Q1')))
    | ?Q1 <*> X => exact (X <*> ltac:(reorder X Q1))
    | ?Q1 <*> (X <*> ?Q1') => exact (X <*> ltac:(reorder X (Q1' <*> Q1)))
    end
  | _ => exact P
  end.
(*Check (fun x (y : Expr (_ string)) => ltac:(reorder (<(x :== -\ y)>) (<[]> <*> <[1=1]> <*> (<[2=2]> <*> (<[3=3]> <*> <[]> <*> <[4=4]> <*> (<[5=5]> <*> <(x :== -\ y)>) <*> <[6=6]>))))).*)
Ltac prove_implies_reorder X :=
  match goal with
  | [|- ?Q <*> ?Q' ->> _] =>
    eapply implies_trans;
    [apply star_implies_mono; prove_implies_reorder X|];
    match goal with
    | [|- X <*> ?Q1' ->> _ ] =>
      apply star_implies_mono; [apply implies_refl|];
      prove_implies_reorder X
    | [|- (X <*> ?Q1) <*> ?Q1' ->> _ ] =>
      eapply implies_trans; [apply star_assoc_r|];
      apply star_implies_mono; [apply implies_refl|];
      prove_implies_reorder X
    | [|- ?Q1 <*> X ->> _ ] =>
      eapply implies_trans; [apply star_comm|];
      apply star_implies_mono; [apply implies_refl|];
      prove_implies_reorder X
    | [|- ?Q1 <*> (X <*> ?Q1') ->> _ ] =>
      eapply implies_trans; [apply star_comm|];
      eapply implies_trans; [apply star_assoc_r|];
      apply star_implies_mono; [apply implies_refl|];
      prove_implies_reorder X
    end
  | [|- ?P ->> _] => apply implies_refl
  end.

Ltac prove_implies_reorder_bwd X :=
  match goal with
  | [|- _ ->> ?Q <*> ?Q'] =>
    eapply implies_trans;
    [|apply star_implies_mono; prove_implies_reorder_bwd X];
    match goal with
    | [|- _ ->> X <*> ?Q1' ] =>
      apply star_implies_mono; [apply implies_refl|];
      prove_implies_reorder_bwd X
    | [|- _ ->> (X <*> ?Q1) <*> ?Q1' ] =>
      eapply implies_trans; [|apply star_assoc_l];
      apply star_implies_mono; [apply implies_refl|];
      prove_implies_reorder_bwd X
    | [|- _ ->> ?Q1 <*> X ] =>
      eapply implies_trans; [|apply star_comm];
      apply star_implies_mono; [apply implies_refl|];
      prove_implies_reorder_bwd X
    | [|- _ ->> ?Q1 <*> (X <*> ?Q1') ] =>
      eapply implies_trans; [|apply star_comm];
      eapply implies_trans; [|apply star_assoc_l];
      apply star_implies_mono; [apply implies_refl|];
      prove_implies_reorder_bwd X
    end
  | [|- ?P ->> _] => apply implies_refl
  end.

Ltac triple_reorder X :=
  match goal with
  | [|- triple ?e ?P' ?Q'] =>
    eapply triple_weaken with (P := ltac:(reorder X P')) (Q := Q');
      [prove_implies_reorder X|intros; apply implies_refl|]
  end.

Ltac prove_implies_refl :=
  intros; simpl;
  try (match goal with
    | [x : ?T |- ?P ->> ?Q ?y] =>
      unify x y;
      generalize dependent x;
      intro x; repeat intros _;
      revert x
    end;
    lazymatch goal with
    | [|- forall x : ?T, @?P' x ->> @?Q' x] =>
      intro x;
      let QQ := ltac:(eval simpl in (Q' x)) in
      unify (P' x) QQ
    end);
  apply implies_refl.

Ltac rewrite_empty_spec :=
  match goal with
  | [H : <[]> ?c ?m |- _] => apply empty_spec in H as (->&->)
  end.

Ltac unify_not_evar X Y :=
  not_evar Y; unify X Y.

Ltac remove X P :=
  lazymatch ltac:(type of X) with
  | StateAssertion ?V =>
    match P with
    | ?Y => unify_not_evar X Y; exact (sa_empty : StateAssertion V)
    | ?Q <*> ?Q' =>
      match ltac:(eval simpl in (ltac:(remove X Q))) with
      | <[]> => exact Q'
      | ?Q1 => exact (Q1 <*> Q')
      end
    | ?Q <*> ?Q' =>
      match ltac:(eval simpl in (ltac:(remove X Q'))) with
      | <[]> => exact Q
      | ?Q1' => exact (Q <*> Q1')
      end
    end
  end.

Ltac prove_implies_reorder1 X :=
  match goal with
  | [|- ?Y ->> _] => unify_not_evar X Y; apply implies_refl
  | [|- ?Q <*> ?Q' ->> _] =>
    eapply implies_trans;
    [apply star_implies_mono; [prove_implies_reorder1 X|apply implies_refl]|];
    lazymatch goal with
    | [|- (?Y <*> ?Q1) <*> ?Q1' ->> _ ] => unify_not_evar X Y; apply star_assoc_r
    | [|- ?Y <*> ?Q1' ->> _ ] => unify_not_evar X Y; apply implies_refl
    end
  | [|- ?Q <*> ?Q' ->> _] =>
    eapply implies_trans;
    [apply star_implies_mono; [apply implies_refl|prove_implies_reorder1 X]|];
    lazymatch goal with
    | [|- ?Q1 <*> (?Y <*> ?Q1') ->> _ ] =>
      unify_not_evar X Y;
      eapply implies_trans;
      [apply star_assoc_l|];
      eapply implies_trans;
      [apply star_implies_mono; [apply star_comm|apply implies_refl]|];
      apply star_assoc_r
    | [|- ?Q1 <*> ?Y ->> _ ] => unify_not_evar X Y; apply star_comm
    end
  | [|- ?P ->> ?Q] => unify_not_evar Q P; apply implies_refl
  end.

Ltac prove_implies_reorder1_bwd X :=
  match goal with
  | [|- _ ->> ?Y] => unify_not_evar X Y; apply implies_refl
  | [|- _ ->> ?Q <*> ?Q'] =>
    eapply implies_trans;
    [|apply star_implies_mono; [prove_implies_reorder1_bwd X|apply implies_refl]];
    lazymatch goal with
    | [|- _ ->> (?Y <*> ?Q1) <*> ?Q1' ] => unify_not_evar X Y; apply star_assoc_l
    | [|- _ ->> ?Y <*> ?Q1' ] => unify_not_evar X Y; apply implies_refl
    end
  | [|- _ ->> ?Q <*> ?Q'] =>
    eapply implies_trans;
    [|apply star_implies_mono; [apply implies_refl|prove_implies_reorder1_bwd X]];
    lazymatch goal with
    | [|- _ ->> ?Q1 <*> (?Y <*> ?Q1') ] =>
      unify_not_evar X Y;
      eapply implies_trans;
      [|apply star_assoc_r];
      eapply implies_trans;
      [|apply star_implies_mono; [apply star_comm|apply implies_refl]];
      apply star_assoc_l
    | [|- _ ->> ?Q1 <*> ?Y ] => unify_not_evar X Y; apply star_comm
    end
  | [|- ?P ->> ?Q] => unify_not_evar P Q; apply implies_refl
  end.

Ltac triple_reorder1 X :=
  match goal with
  | [|- triple ?e ?P' ?Q'] =>
    apply triple_weaken with (P := X <*> ltac:(remove X P')) (Q := Q');
      [prove_implies_reorder1 X|prove_implies_refl|]
  end.

Ltac clear_empty P :=
  lazymatch P with
  | ?Q <*> ?Q' => (*idtac Q Q';*)
    match ltac:(eval simpl in (ltac:(clear_empty Q) <*> ltac:(clear_empty Q'))) with
    | <[]> <*> ?Q1' => (*idtac 1 Q1';*) exact Q1'
    | ?Q1 <*> <[]> => (*idtac 2 Q1;*) exact Q1
    | ?Q1 => (*idtac 3 Q1;*) exact Q1
    end
  | <exists> t : ?T, @?Q t => (*idtac t T Q;*)
    let Q' := ltac:(eval simpl in ltac:(clear_empty Q)) in
    (*idtac T Q'; idtac ">";*) exact (<exists> t : T, Q' t) (*; idtac "OK") || idtac "!")*)
  | fun t : ?T => @?Q t => (*idtac t T Q;*)
    let u := fresh t in(*exact (fun x : T => ltac:(eval simpl in ltac:(clear_empty Q)))*)
    let Q' := ltac:(eval simpl in (fun u =>ltac:(clear_empty ltac:(eval simpl in (Q u))))) in
    (*idtac t T Q'; idtac ">!";*) exact Q' (*; idtac "OK!") || idtac "!!")*)
  | _ => exact P (*; idtac "<>"*)
  end.

(*Goal True.
match constr:(fun x => x + 1) with
| fun t => @?y t => let a := fresh t in let b := constr:(fun a => y a) in idtac a b y
end.
Abort.
Check (ltac:(clear_empty ltac:(eval simpl in (fun (x:Label) (y : Expr (inc_set string)) =>  (<[]> <*> <[1=1]> <*> (<[2=2]> <*> <exists> n m : nat, (<[n=m]> <*> <[]> <*> <[4=4]> <*> (<[5=5]> <*> <(x :== -\y)>) <*> <[]> <*> <[6=6]>)):StateAssertion string))))).
Goal True. match constr:(fun x xx : nat => ((fun t => t + xx) x + 1) * 3) with
| fun z v => @?y z v * 3 => idtac "y =" y; pose (fun z : nat => ltac:(
  match ltac:(eval simpl in (fun v : nat => y z v)) with
  | fun r => @?a r => idtac "r =" r "; a =" a; let aa := (ltac:(eval simpl in (a))) in exact (aa 8)
  end) * 5)
end.*)

Ltac prove_implies_clear_empty :=
  lazymatch goal with
  | [|- ?Q <*> ?Q' ->> _ ] =>
    eapply implies_trans;
    [apply star_implies_mono; prove_implies_clear_empty|];
    lazymatch goal with
    | [|- <[]> <*> ?Q1' ->> _] => apply empty_star_l_cancel
    | [|- ?Q1 <*> <[]> ->> _] => apply empty_star_r_cancel
    | [|- ?Q1 ->> _] => apply implies_refl
    end
  | [|- (<exists> x, @?P' x) ->> _] =>
    apply exists_implies with (P := P'); prove_implies_clear_empty
  | [|- forall x, ?Q ->> _] =>
    intros; prove_implies_clear_empty
  | [|- ?P ->> _] => apply implies_refl
  end.

Ltac prove_implies_clear_empty_bwd :=
  lazymatch goal with
  | [|- _ ->> ?Q <*> ?Q' ] =>
    eapply implies_trans;
    [|apply star_implies_mono; prove_implies_clear_empty_bwd];
    lazymatch goal with
    | [|- _ ->> <[]> <*> ?Q1'] => apply empty_star_l_intro
    | [|- _ ->> ?Q1 <*> <[]>] => apply empty_star_r_intro
    | [|- _ ->> ?Q1] => apply implies_refl
    end
  | [|- _ ->> (<exists> x, @?Q' x)] =>
    apply exists_implies with (Q := Q'); prove_implies_clear_empty_bwd
  | [|- forall x, ?Q ->> _] =>
    intros; prove_implies_clear_empty_bwd
  | [|- _ ->> ?P] => apply implies_refl
  end.

Ltac triple_clear_empty :=
  match goal with
  | [|- triple ?e ?P' ?Q'] =>
    apply triple_weaken with (P := ltac:(clear_empty P')) (Q := Q');
      [prove_implies_clear_empty|prove_implies_refl|]
  end.

Ltac triple_clear_empty_r :=
  match goal with
  | [|- triple ?e ?P' ?Q'] =>
    apply triple_weaken with (P := P') (Q := ltac:(clear_empty Q'));
      [prove_implies_refl|prove_implies_clear_empty_bwd|]
  end.
(*Check (fun x (y : Expr (_ string)) => ltac:(clear_empty ltac:(eval simpl in ltac:(remove (<(x :== -\y)>) (<[]> <*> <[1=1]> <*> (<[2=2]> <*> (<[3=3]> <*> <[]> <*> <[4=4]> <*> (<[5=5]> <*> <(x :== -\ y)>) <*> <[]> <*> <[6=6]>))))))).*)


Ltac fold_and_apply f x :=
  try (progress fold (f x); fold_and_apply f (f x)).

Ltac fold_all_inc_set x :=
  fold_and_apply constr:(inc_set) x.

Ltac fold_all_inc_set_string :=
  fold_all_inc_set constr:(String.string).

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

(*
Goal True.
eassert (option (Value string)). shelve.
eassert (H = _). shelve.
lazymatch goal with
| [_ : H = ?yy |- _] =>
  epose (fun x (y : Expr (_ string)) => ltac:(clear_empty ltac:(eval simpl in ltac:(remove (<(x :?= Some (-\ y))> : StateAssertion string) (<[]> <*> <[1=1]> <*> (<[2=2]> <*> (<[3=3]> <*> <[]> <*> <[4=4]> <*> (<[5=5]> <*> <(x :== -\ y)>) <*> <[]> <*> <[6=6]>)))))))
end.
lazymatch goal with
| [_ : H = ?yy |- _] =>
  epose (fun x (y : Expr (_ string)) => ltac:(clear_empty ltac:(eval simpl in ltac:(remove (<(x :?= yy)> : StateAssertion string) (<[]> <*> <[1=1]> <*> (<[2=2]> <*> (<[3=3]> <*> <[]> <*> <[4=4]> <*> (<[5=5]> <*> <(x :== @U_val string)>) <*> <[]> <*> <[6=6]>)))))))
end.
Abort.

Ltac tmp P :=
  lazymatch P with
  | ?Q <*> ?Q' => (*idtac Q Q';*)
    tmp Q; tmp Q'
  | <exists> t : ?T, @?Q t => (*idtac t T Q;*)
    tmp Q
  | fun t : ?T => @?Q t => (*idtac t T Q;*)
    let u := fresh t in(*exact (fun x : T => ltac:(eval simpl in ltac:(clear_empty Q)))*)
    tmp (Q u)
  | ?X => (is_evar X; idtac "is_evar -" X) || idtac "!" X
  end.
*)

Ltac get_leftmost P :=
  lazymatch P with
  | ?Q <*> ?Q' => exact ltac:(get_leftmost Q)
  | _ => exact P
  end.

Ltac reorder_leftmost P :=
  let l := (ltac:(eval simpl in ltac:(get_leftmost P))) in
  exact (l <*> ltac:(remove l P)).
(*Check (fun x (y : Expr (_ string)) => ltac:(reorder_leftmost (((<[1=1]> <*> <[8=8]>) <*> <[7=7]>) <*> (<[2=2]> <*> (<[3=3]> <*> <[]> <*> <[4=4]> <*> (<[5=5]> <*> <(x :== -\ y)>) <*> <[]> <*> <[6=6]>))))).*)
Ltac prove_implies1 :=
  lazymatch goal with
  | [|- ?P ->> ?QQ] =>
    (unify P QQ; apply implies_refl) ||
    (let l := (ltac:(eval simpl in ltac:(get_leftmost P))) in
     let P' := (ltac:(eval simpl in ltac:(remove l P))) in
     let Q' := (ltac:(eval simpl in ltac:(remove l QQ))) in
     apply implies_trans with (Q := l <*> P');
     [prove_implies_reorder1 l|];
     apply implies_trans with (Q := l <*> Q');
     [|prove_implies_reorder1_bwd l];
     apply star_implies_mono;
     [apply implies_refl|])
  end.

Ltac prove_implies1_rev :=
  lazymatch goal with
  | [|- ?P ->> ?QQ] =>
    (unify P QQ; apply implies_refl) ||
    (let l := (ltac:(eval simpl in ltac:(get_leftmost QQ))) in
     let P' := (ltac:(eval simpl in ltac:(remove l P))) in
     let Q' := (ltac:(eval simpl in ltac:(remove l QQ))) in
     apply implies_trans with (Q := l <*> Q');
     [|prove_implies_reorder1_bwd l];
     apply implies_trans with (Q := l <*> P');
     [prove_implies_reorder1 l|];
     apply star_implies_mono;
     [apply implies_refl|])
  end.

Ltac prove_implies :=
  repeat prove_implies1.
Ltac prove_implies_rev :=
  repeat prove_implies1_rev.

Ltac fold_implies :=
  lazymatch goal with
  | [|- forall c m, ?P c m -> ?Q c m] => fold (P ->> Q)
  end.

Ltac revert_implies :=
  lazymatch goal with
  | [H : ?P ?c ?m |- ?Q ?c ?m] => revert c m H; fold_implies
  end.

Ltac triple_value_revert :=
  match goal with
  | [v : Value _ |- triple (Val ?v') _ _] => unify v v'; generalize dependent v
  | [|- triple (Val ?v') _ _] => remember v' as t; generalize dependent t
  end.

Ltac eta_expand_pre_triple_value :=
  triple_value_revert;
  lazymatch goal with
  | [|- forall v : ?T, triple (Val v) (@?P v) ?Q] =>
    change (forall v : T, triple v (P v) Q)
  | [|- forall (v : ?T) (x : ?H), triple (Val v) (@?P v) ?Q] =>
    change (forall (v : T) (x : H), triple v (P v) Q)
  end;
  intros.

Ltac solve_simple_value :=
  apply triple_value_implies; apply implies_spec; intros; solve_star;
  try eassumption.

Ltac solve_value_unify :=
  match goal with
  | [|- triple (Val ?v) ?P ?Q] =>
    unify P (Q v); apply triple_value_implies; apply implies_refl
  end.

Ltac app_lambda :=
  lazymatch goal with
  | [|- triple (Val (-\ ?e1') <* Val ?v2) (sa_credits 1 <*> ?P) ?Q] => (*idtac e1' v2 P Q;*)
    eapply triple_app with (P2 := P); [|eta_expand_pre_triple_value; solve_value_unify]
  | [|- triple (Val (-\ ?e1') <* ?e2) (sa_credits 1 <*> ?P) ?Q] => (*idtac e1' e2 P Q;*)
    eapply triple_app with (P2 := P)
  end.

Ltac triple_expand_empty_pre_r :=
  lazymatch goal with
  | [|- triple ?e ?P' ?Q'] =>
    apply triple_weaken with (P := P' <*> <[]>) (Q := Q');
      [apply empty_star_r_intro|prove_implies_refl|]
  end.

Ltac rewrite_all_binds :=
  fold_all_inc_set_string;
  repeat rewrite bind_v_liftS_shift_swap;
  repeat rewrite bind_v_shift;
  repeat rewrite bind_v_id.

Ltac rewrite_all_map_v_closed :=
  repeat (rewrite map_v_shift_closed;
    [|repeat apply map_v_closed_value; auto with is_closed_db]).

Ltac clear_state_assertions :=
  repeat match goal with
  | [H : ?P ?c ?m |- _] =>
    let T := ltac:(type of P) in
    unify T (StateAssertion String.string);
    clear c m H
  end.
