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
      [end]
    [end]%string.

Definition generic_dijkstra (get_size get_neighbours mkheap h_insert h_empty h_extract_min h_decrease_key l_is_nil l_head l_tail : Value string) : Value string :=
  [-\] "g", [-\] "src", [-\] "dst",
    [let "n"] get_size <* Var "g" [in]
    [let "h"] mkheap <* Var "n" [in]
    [let "dist"] NewArray (Var "n") [in]
      init_array <* (Var "dist") <* (Var "n") <* (Int (-1));;
      (Var "array" >> ! Var "i") <- Int 0;;
      h_insert <* Var "h" <* RecV [Var "src"; Int 0];;
      [while] [~] (h_empty <* Var "h") [do]
        [let "rec_current"] h_extract_min <* (Var "h") [in]
        [let "current"] Get 0 (Var "rec_current") [in]
        [let "dist_current"] Get 1 (Var "rec_current") [in]
        [let "neighs"] get_neighbours <* Var "current" [in]
          [while] [~] (l_is_nil <* Var "neighs") [do]
            [let "neigh"] l_head <* Var "neighs" [in]
            [let "dist_neigh"] ! (Var "array" >> Var "neigh") [in]
            [let "new_dist"] Var "dist_current" [+] Int 1 [in]
              [if] (Var "dist_neigh" [<] Int 0) [then]
                (Var "array" >> Var "neigh") <- Var "new_dist";;
                h_insert <* Var "h" <* RecV [Var "neigh"; Var "new_dist"]
              [else] [if] (Var "new_dist" [<] Var "dist_neigh") [then]
                (Var "array" >> Var "neigh") <- Var "new_dist";;
                h_decrease_key <* Var "neigh" <* Var "new_dist"
              [else]
                U_val (* Nothing happens. *)
              [end]
            [end]
            [end]
            [end];;
            Var "neighs" <- l_tail <* Var "neighs"
          [end]
        [end]
        [end]
        [end]
        [end]
      [end]
    [end]
    [end]
    [end]
    [end]%string.
