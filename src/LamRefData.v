Require List.
Import List.ListNotations.

Require Import String.

Parameter Value : Set.
Parameter Expr : Set.
Parameter type : Set.

Axiom WF_Value : Value -> Prop.
Axiom WF_Expr : Expr -> Prop.
Axiom WF_type : type -> Prop.

Definition Constructor := (string * list type)%type.
Definition ADT := list Constructor.

Definition WF_Constructor (c : Constructor) : Prop :=
  List.Forall (fun t => WF_type t) (snd c).

Definition WF_ADT : ADT -> Prop :=
  List.Forall (fun c => WF_Constructor c).
