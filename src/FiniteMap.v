Require Import Nat.
Require List.
Import List.ListNotations.

Inductive Label : Set :=
| OfNat : nat -> Label.

Definition of_label '(OfNat n) := n.
Definition lift {A} (f : nat -> A) (l : Label) : A := f (of_label l).
Definition lift2 {A} (f : nat -> nat -> A) (l l' : Label) : A :=
  lift (lift f l) l'.

Definition label_eqb : Label -> Label -> bool := lift2 Nat.eqb.
Definition label_ltb : Label -> Label -> bool  := lift2 Nat.ltb.

Definition label_lt : Label -> Label -> Prop  := lift2 lt.

Declare Scope label_scope.

Notation "l =? l'" := (label_eqb l l') : label_scope.
Notation "l <? l'" := (label_ltb l l') : label_scope.

Notation "l < l'" := (label_lt l l') : label_scope.

Global Hint Unfold of_label : label.
Global Hint Unfold lift2 : label.
Global Hint Unfold lift  : label.
Global Hint Unfold label_eqb : label.
Global Hint Unfold label_ltb : label.
Global Hint Unfold label_lt  : label.

Definition FinMap (A : Set) : Set := list (Label * A).

(*Definition extend {V L : Set} (m : Map V L) (v : Value V L)
  : Map V (inc_set L) :=
  fun (l : inc_set L) =>
    match l with
    | Some l => shift_v (m l)
    | None   => shift_v v
    end.

Definition assign {V L : Set} (m : Map V L) (l : L) (v : Value V L) : Map V L.
Admitted.

Definition max_label {V : Set} (m : Map V) : Label :=
  List.fold_right
    (fun '(OfNat n, _) '(OfNat m) => OfNat (max n m)) (OfNat 0) m.
*)

Definition labels {A : Set} (m : FinMap A) : list Label :=
  List.map fst m.

Definition Is_fresh_label {A : Set} (l : Label) (m : FinMap A) : Prop :=
  ~ List.In l (labels m).

Inductive IsOrdered {A : Set} (R : A -> A -> Prop) : list A -> Prop :=
| IsOrdered_nil : IsOrdered R []
| IsOrdered_single x : IsOrdered R [x]
| IsOrdered_cons x y ys :
  R x y -> IsOrdered R (y :: ys) -> IsOrdered R (x :: y :: ys).

Definition Is_Valid_Map {A : Set} (m : FinMap A) : Prop :=
  IsOrdered label_lt (labels m).

Global Hint Unfold labels : lamref.
Global Hint Unfold Is_fresh_label : lamref.
Global Hint Unfold Is_Valid_Map : lamref.

Section label_section.
Open Scope label_scope.
Fixpoint lookup {A : Set} (l : Label) (m : FinMap A) : option A :=
  match m with
  | nil => None
  | (l', x) :: m' => if l =? l' then Some x else lookup l m'
  end%list.

Fixpoint update {A : Set} (l : Label) (x : A) (m : FinMap A) : FinMap A :=
  match m with
  | nil => [(l, x)]
  | (l', x') :: m' =>
    if l <? l'
    then (l, x) :: (l', x') :: m'
    else if l =? l' then ((l', x) :: m') else (l', x') :: (update l x m')
  end%list.
End label_section.

Definition list_max (l : list nat) : nat :=
  List.fold_right max 0 l.

Definition new_label {A : Set} (m : FinMap A) : Label :=
  OfNat (1 + list_max (List.map of_label (labels m))).
