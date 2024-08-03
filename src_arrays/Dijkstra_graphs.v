From GraphTheory Require Import digraph.
Import fintype.Finite.

(* weighted graphs *)
Record wGraph := {
  Gr :> diGraph;
  W : sort (rel_car Gr) -> sort (rel_car Gr) -> nat
}.

(*Print path.path.*)
