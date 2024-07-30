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

(*
Parameter log : Value string.
*)
Parameter pow : Value string.
Parameter mkset : Value string.
Parameter mklinkedlist : Value string.
(*
Definition mkheap : Value string :=
  [-\] "C",
    [let "size"] log <* Var "C" [in]
    [let "buckets"] NewArray (Var "size") [in]
    [let "i"] Ref (Int 0) [in]
      [while] ! Var "i" [<] Var "size" [do]
        (Var "array" >> ! Var "i") <- (mkset <* U_val);;
        Var "i" <- ! Var "i" [+] Int 1
      [end];;
      Free (Var "i")
    [end];;
    [let "min_rngs"] NewArray (Var "size") [in]
    [let "i"] Ref (Int 0) [in]
      [while] ! Var "i" [<] Var "size" [do]
        (Var "min_rngs" >> ! Var "i") <- (pow <* Int 2 <* Var "i");;
        Var "i" <- ! Var "i" [+] Int 1
      [end];;
      Free (Var "i")
    [end];;
    [let "max_rngs"] NewArray (Var "size") [in]
    [let "i"] Ref (Int 0) [in]
      [while] ! Var "i" [<] Var "size" [do]
        (Var "max_rngs" >> ! Var "i") <- (pow <* Int 2 <* (Var "i" [+] Int 1));;
        Var "i" <- ! Var "i" [+] Int 1
      [end];;
      Free (Var "i")
    [end];;
    [let "x"] Ref (Var "size") [in]
      RecV [Var "buckets"; Var "x"; Var "min_rngs"; Var "max_rngs"]
    [end]
    [end]
    [end]
    [end]
    [end]%string.
*)

Definition mkheap : Value string :=
  [-\] "n",
    [let "buckets"] mklinkedlist <* U_val [in]
    [let "key_positions"] NewArray (Var "n") [in]
    [let "key_refs"] NewArray (Var "n") [in]
      RecE [
        Val (Var "buckets");
        Val (Var "key_positions");
        Val (Var "key_refs");
        Ref (Int 0) (* size *)
      ]
    [end]
    [end]
    [end]%string.

Definition h_buckets : nat := 0.
Definition h_key_positions : nat := 1.
Definition h_key_refs : nat := 2.
Definition h_size : nat := 3.

Definition in_range : Value string :=
  ([-\] "x", [-\] "min", [-\] "max",
    (Var "min" [=] Var "x") [||]
    (Var "min" [<] Var "x") [||]
    (Var "x" [<] Var "max"))%string.

Parameter h_insert : Value string.

Definition h_empty : Value string :=
  ([-\] "h",
    Get h_size (Var "h") [=] Int 0)%string.

Parameter h_extract_min : Value string.
Parameter h_decrease_key : Value string.
Parameter h_free : Value string.
