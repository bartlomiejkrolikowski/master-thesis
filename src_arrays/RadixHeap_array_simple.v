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
Parameter s_add : Value string. (* add to a set *)
Parameter s_get : Value string. (* take any value from a set *)
Parameter s_extract_ref : Value string. (* take a given value from a set *)
Parameter s_get_min : Value string. (* take min from the set *)
Parameter s_decrease_ref : Value string. (* change a given value in the set *)
Parameter s_empty : Value string. (* a set is empty *)
Parameter s_free : Value string.

Definition mkheap : Value string :=
  [-\] "n", [-\] "C",
    [let "b_count"] (log <* Var "C") [+] Int 1 [in]
    [let "buckets"] NewArray (Var "b_count") [in]
    (* buckets with their ranges *)
    (Var "array" >> Int 0) <- RecE [
      mkset <* U_val;
      Ref (Int 0);
      Ref (Int 1)
    ];;
    [let "i"] Ref (Int 1) [in]
      [while] ! Var "i" [<] Var "b_count" [do]
        (Var "array" >> ! Var "i") <- RecE [
          mkset <* U_val;
          Ref (pow <* Int 2 <* Var "i" [-] Int 1);
          Ref (pow <* Int 2 <* (Var "i"))
        ];;
        Var "i" <- ! Var "i" [+] Int 1
      [end];;
      Free (Var "i")
    [end];;
    [let "key_positions"] NewArray (Var "n") [in]
    [let "key_refs"] NewArray (Var "n") [in]
    [let "size"] Ref (Int 0) [in]
      RecV [Var "buckets"; Var "b_count"; Var "key_positions"; Var "key_refs"; Var "size"; Var "n"]
    [end]
    [end]
    [end]
    [end]
    [end]%string.

Definition b_content : nat := 0.
Definition b_rng_lo : nat := 1.
Definition b_rng_hi : nat := 2.

Definition h_buckets : nat := 0.
Definition h_b_count : nat := 1.
Definition h_key_positions : nat := 2.
Definition h_key_refs : nat := 3.
Definition h_size : nat := 4.
Definition h_n : nat := 5.

Definition in_range : Value string :=
  ([-\] "x", [-\] "min", [-\] "max",
    (Var "min" [=] Var "x") [||]
    (Var "min" [<] Var "x") [||]
    (Var "x" [<] Var "max"))%string.

Definition h_insert : Value string :=
  ([-\] "h", [-\] "key", [-\] "value",
    Get h_size (Var "h") <- (! Get h_size (Var "h")) [+] Int 1;;
    [let "i"] Ref (Int 0) [in]
    [let "buckets"] Get h_buckets (Var "h") [in]
    [let "key_positions"] Get h_key_positions (Var "h") [in]
    [let "key_refs"] Get h_key_positions (Var "h") [in]
      [while] [~] (
        in_range <* Var "value"
          <* (! Get b_rng_lo (Var "buckets" >> Var "i"))
          <* ! Get b_rng_hi (Var "buckets" >> Var "i")
      ) [do]
        Var "i" <- (! Var "i") [+] Int 1
      [end];;
      (Var "key_positions" >> Var "key") <- ! Var "i";;
      [let "b"] Var "buckets" >> Var "i" [in]
        (Var "key_refs" >> Var "key") <-
          (s_add <* (Get b_content (Var "b")) <* RecV [Var "key"; Var "value"])
      [end]
    [end]
    [end]
    [end]
    [end])%string.

Definition h_empty : Value string :=
  ([-\] "h",
    ! Get h_size (Var "h") [=] Int 0)%string.
(*
Definition move_ranges_up : Value string :=
  [-\] "h",
*)
Definition h_extract_min : Value string :=
  ([-\] "h",
    Get h_size (Var "h") <- (! Get h_size (Var "h")) [-] Int 1;;
    [let "buckets"] Get h_buckets (Var "h") [in]
    [let "key_positions"] Get h_key_positions (Var "h") [in]
    [let "key_refs"] Get h_key_positions (Var "h") [in]
    [let "i"] Ref (Int 0) [in]
      (* find the first nonempty bucket *)
      [while] s_empty <* Get b_content (! (Var "buckets" >> ! Var "i")) [do]
        Var "i" <- ! Var "i" [+] Int 1
      [end];;
      [if] [~] (! Var "i" [=] Int 0) [then]
        (* bucket 0 is empty *)
        (* move the content of the bucket to the lower buckets *)
        [let "bucket"] ! (Var "buckets" >> ! Var "i") [in]
        [let "content"] Get b_content (Var "bucket") [in]
        [let "rec_min"] s_get_min <* (Var "content") [in]
        [let "min_key"] Get 0 (Var "min_key") [in]
        [let "min_val"] Get 1 (Var "min_val") [in]
        [let "rng_lo"] Var "min_val" [in]
        [let "rng_hi"] Get b_rng_hi (Var "bucket") [in]
          (* set new ranges *)
          Get b_rng_lo (! (Var "buckets" >> Int 0)) <- Var "rng_lo";;
          Get b_rng_hi (! (Var "buckets" >> Int 0)) <- Var "rng_lo" [+] Int 1;;
          [let "new_lo"] Ref (Var "rng_lo" [+] Int 1) [in]
          [let "new_width"] Ref (Int 1) [in]
          [let "new_hi"] Ref (! Var "new_lo" [+] ! Var "new_width") [in]
          [if] Var "rng_hi" [<] ! Var "new_hi" [then]
            Var "new_hi" <- Var "rng_hi"
          [else]
            U_val
          [end];;
          [let "j"] Ref (Int 1) [in]
            [while] Var "j" [<] Var "i" [do]
              (* set ranges *)
              Get b_rng_lo (! (Var "buckets" >> Var "j")) <- Var "new_lo";;
              Get b_rng_hi (! (Var "buckets" >> Var "j")) <- Var "new_hi";;
              (* compute next ranges *)
              Var "new_lo" <- ! Var "new_hi";;
              Var "new_width" <- Int 2 [*] ! Var "new_width";;
              Var "new_hi" <- ! Var "new_lo" [+] ! Var "new_width";;
              [if] Var "rng_hi" [<] ! Var "new_hi" [then]
                Var "new_hi" <- Var "rng_hi"
              [else]
                U_val
              [end];;
              Var "j" <- (! Var "j") [+] Int 1
            [end];;
            Free (Var "j")
          [end]
          [end]
          [end]
          [end];;
          Get b_rng_lo (! (Var "buckets" >> Var "i")) <- Var "rng_hi";;
          Get b_rng_hi (! (Var "buckets" >> Var "i")) <- Var "rng_hi";;
          (* move the content *)
          [while] [~] (s_empty <* Var "content") [do]
            (* move a single value to the proper bucket *)
            [let "rec_x"] s_get <* Var "content" [in]
            [let "x_key"] Get 0 (Var "rec_x") [in]
            [let "x_value"] Get 1 (Var "rec_x") [in]
            [let "j"] Ref (! Var "i" [-] Int 1) [in]
              [while] [~] (
                in_range <* Var "value"
                  <* (! Get b_rng_lo (Var "buckets" >> Var "j"))
                  <* ! Get b_rng_hi (Var "buckets" >> Var "j")
              ) [do]
                Var "j" <- (! Var "j") [-] Int 1
              [end];;
              [let "new_bucket"] ! (Var "buckets" >> ! Var "j") [in]
                (Var "key_positions" >> Var "x_key") <- Var "j";;
                (Var "key_refs" >> Var "x_key") <-
                  s_add <* Get b_content (Var "new_bucket") <* Var "rec_x"
              [end];;
              Free (Var "j")
            [end]
            [end]
            [end]
            [end]
          [end];;
          Free (Var "i");;
          Var "rec_min"
        [end]
        [end]
        [end]
        [end]
        [end]
        [end]
        [end]
      [else]
        (* bucket 0 is nonempty *)
        Free (Var "i");;
        s_get <* Get b_content (! (Var "buckets" >> Int 0))
      [end]
    [end]
    [end]
    [end]
    [end])%string.

Definition h_decrease_key : Value string :=
  [-\] "h", [-\] "key", [-\] "value",
    [let "buckets"] Get h_buckets (Var "h") [in]
    [let "key_positions"] Get h_key_positions (Var "h") [in]
    [let "key_refs"] Get h_key_positions (Var "h") [in]
    [let "key_i"] ! (Var "key_positions" >> Var "key") [in]
    [let "key_r"] ! (Var "key_refs" >> Var "key") [in]
    [let "bucket"] ! (Var "buckets" >> Var "key_i") [in]
    [let "content"] Get b_content (Var "bucket") [in]
    [let "rng_lo"] Get b_rng_lo (Var "bucket") [in]
    [let "rng_hi"] Get b_rng_hi (Var "bucket") [in]
      [if] in_range <* Var "value" <* Var "rng_lo" <* Var "rng_hi" [then]
        (Var "key_refs" >> Var "key_i") <-
          s_decrease_ref <* Var "content" <* Var "key_r" <* Var "value"
      [else]
        s_extract_ref <* Var "content" <* Var "key_r";;
        [let "j"] Ref (Var "key_i" [-] Int 1) [in]
          [while] [~] (
            in_range <* Var "value"
              <* (! Get b_rng_lo (Var "buckets" >> Var "j"))
              <* ! Get b_rng_hi (Var "buckets" >> Var "j")
          ) [do]
            Var "j" <- (! Var "j") [-] Int 1
          [end];;
          [let "new_bucket"] ! (Var "buckets" >> ! Var "j") [in]
            (Var "key_positions" >> Var "key") <- Var "j";;
            (Var "key_refs" >> Var "key") <-
              s_add <* Get b_content (Var "new_bucket") <* RecV [Var "key"; Var "value"]
          [end];;
          Free (Var "j")
        [end]
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

Definition h_free : Value string :=
  [-\] "h",
    [let "buckets"] Get h_buckets (Var "h") [in]
    [let "b_count"] Get h_b_count (Var "h") [in]
    [let "key_positions"] Get h_key_positions (Var "h") [in]
    [let "key_refs"] Get h_key_refs (Var "h") [in]
    [let "n"] Get h_n (Var "h") [in]
      [let "i"] Ref (Int 0) [in]
        [while] ! Var "i" [<] Var "b_count" [do]
          s_free <* (Get b_content (! (Var "buckets" >> ! Var "i")));;
          Var "i" <- (! Var "i") [+] Int 1
        [end];;
        Free (Var "i")
      [end];;
      free_array <* Var "buckets" <* Var "b_count";;
      free_array <* Var "key_positions" <* Var "n";;
      free_array <* Var "key_refs" <* Var "n"
    [end]
    [end]
    [end]
    [end]
    [end]%string.
