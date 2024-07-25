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

Parameter log : Value string.
Parameter pow : Value string.
Parameter mkset : Value string.

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
      RecV [Var "buckets"; Ref (Var "size"); Var "min_rngs"; Var "max_rngs"]
    [end]
    [end]
    [end]
    [end]%string.
