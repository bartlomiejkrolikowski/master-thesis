Require Import ZArith.
Require Import Relation_Operators.

Inductive direction : Set := L | R.

Module ComputableTM.

Definition Step (State Symbol : Set) : Set :=
  direction * State * Symbol.

Record TMstate (State Symbol : Set) : Set := {
  tape  : Z -> option Symbol;
  state : State;
}.

(* a generic type of Turing machines,
 * acceptation when (step state tape = None) *)
Record TuringMachine (State Symbol : Set) : Set := {
  tm_state : TMstate State Symbol;
  step     : State -> option Symbol -> option (Step State Symbol);
}.

Arguments tape     {State Symbol}.
Arguments state    {State Symbol}.
Arguments tm_state {State Symbol}.
Arguments step     {State Symbol}.

Definition shift_tape {Symbol : Set}
  (tape : Z -> option Symbol) (d : direction) :
  Z -> option Symbol :=
  fun i : Z => tape (
    match d with
    | L => i-1
    | R => i+1
    end
  )%Z.

Definition update_tape {Symbol : Set}
  (tape : Z -> option Symbol) (s : Symbol) :
  Z -> option Symbol :=
  fun i : Z => if (0 =? i)%Z then Some s else tape i.

Definition state_make_step {State Symbol : Set}
  (tm : TuringMachine State Symbol) :
  option (TMstate State Symbol) :=
  let opt_symbol := tape (tm_state tm) 0 in
  let state  := state (tm_state tm) in
  option_map (fun '(d, state, symbol) =>
    {|
      tape :=
        let tape' := (update_tape (tape (tm_state tm)) symbol) in
        shift_tape tape' d;
      state := state;
    |}
  ) (step tm state opt_symbol).

Definition make_step {State Symbol : Set}
  (tm : TuringMachine State Symbol) :
  option (TuringMachine State Symbol) :=
  option_map (fun state =>
    {|
      tm_state := state;
      step     := step tm;
    |}
  ) (state_make_step tm).

(* a type of step counting Turing machines *)
Record CountingTM (State Symbol : Set) : Set := {
  tm      : TuringMachine State Symbol;
  counter : nat;
}.

Arguments tm      {State Symbol}.
Arguments counter {State Symbol}.

Definition cnt_make_step {State Symbol : Set}
  (ctm : CountingTM State Symbol) :
  option (CountingTM State Symbol) :=
  option_map (fun tm =>
    {|
      tm := tm;
      counter := S (counter ctm);
    |}
  ) (make_step (tm ctm)).

End ComputableTM.

Module NDTM.
(* ================================== *)
(* a non-deterministic Turing Machine *)

Record NDTuringMachine (State Symbol : Set) : Set := {
  state : State;
  index : Z;
  tape  : Z -> option Symbol;
}.

Arguments state {State Symbol}.
Arguments index {State Symbol}.
Arguments tape  {State Symbol}.

Definition read_tape {State Symbol : Set}
  (ntm : NDTuringMachine State Symbol) : option Symbol :=
  tape ntm (index ntm).

Inductive NTM_step {State Symbol : Set}
  (step_rel :
    (State * option Symbol) -> (direction * State * Symbol) -> Prop) :
  NDTuringMachine State Symbol -> NDTuringMachine State Symbol ->
  Prop :=
| step_left (ntm ntm' : NDTuringMachine State Symbol) a :
  tape ntm' = tape ntm ->
  index ntm' = (index ntm - 1)%Z ->
  Some a = read_tape ntm' ->
  step_rel (state ntm, read_tape ntm) (L, state ntm', a) ->
  NTM_step step_rel ntm ntm'

| step_right (ntm ntm' : NDTuringMachine State Symbol) a :
  tape ntm' = tape ntm ->
  index ntm' = (index ntm + 1)%Z ->
  Some a = read_tape ntm' ->
  step_rel (state ntm, read_tape ntm) (R, state ntm', a) ->
  NTM_step step_rel ntm ntm'
.

(** Reflexive and transitive closure of the step relation *)
Notation NTM_step_rtc r ntm ntm' :=
  (clos_refl_trans_1n _ (NTM_step r) ntm ntm').
End NDTM.


(* ================================== *)
(* a non-deterministic Turing Machine with a counter *)

Record CntNDTuringMachine (State Symbol : Set) : Set := {
  state      : State;
  tape_left  : list Symbol;
  current    : option Symbol;
  tape_right : list Symbol;
  counter    : nat;
}.

Arguments state      {State Symbol}.
Arguments tape_left  {State Symbol}.
Arguments current    {State Symbol}.
Arguments tape_right {State Symbol}.
Arguments counter    {State Symbol}.

Inductive CNTM_step {State Symbol : Set}
  (step_rel :
    (State * option Symbol) -> (direction * option State * Symbol) -> Prop) :
  CntNDTuringMachine State Symbol -> CntNDTuringMachine State Symbol ->
  Prop :=
| step_left s s' tl' a oa a' tr c :
  step_rel (s, oa) (L, Some s', a') ->
  CNTM_step step_rel
    {|
      state      := s;
      tape_left  := a :: tl';
      current    := oa;
      tape_right := tr;
      counter    := c;
    |}
    {|
      state      := s';
      tape_left  := tl';
      current    := Some a;
      tape_right := a' :: tr;
      counter    := S c;
    |}

| step_left_nil s s' oa a' tr c :
  step_rel (s, oa) (L, Some s', a') ->
  CNTM_step step_rel
    {|
      state      := s;
      tape_left  := nil;
      current    := oa;
      tape_right := tr;
      counter    := c;
    |}
    {|
      state      := s';
      tape_left  := nil;
      current    := None;
      tape_right := a' :: tr;
      counter    := S c;
    |}

| step_right s s' tl oa a a' tr' c :
  step_rel (s, oa) (L, Some s', a') ->
  CNTM_step step_rel
    {|
      state      := s;
      tape_left  := tl;
      current    := oa;
      tape_right := a :: tr';
      counter    := c;
    |}
    {|
      state      := s';
      tape_left  := a' :: tl;
      current    := Some a;
      tape_right := tr';
      counter    := S c;
    |}

| step_right_nil s s' tl oa a' c :
  step_rel (s, oa) (L, Some s', a') ->
  CNTM_step step_rel
    {|
      state      := s;
      tape_left  := tl;
      current    := oa;
      tape_right := nil;
      counter    := c;
    |}
    {|
      state      := s';
      tape_left  := a' :: tl;
      current    := None;
      tape_right := nil;
      counter    := S c;
    |}

.

(** Reflexive and transitive closure of the step relation *)
Notation CNTM_step_rtc r ntm ntm' :=
  (clos_refl_trans_1n _ (CNTM_step r) ntm ntm').

Inductive CNTM_accept {State Symbol : Set}
  (step_rel :
    (State * option Symbol) -> (direction * option State * Symbol) -> Prop) :
  CntNDTuringMachine State Symbol -> Prop :=
| step_none s tl oa a' tr c d :
  step_rel (s, oa) (d, None, a') ->
  CNTM_accept step_rel
    {|
      state      := s;
      tape_left  := tl;
      current    := oa;
      tape_right := tr;
      counter    := c;
    |}.

Definition Accepts {State Symbol : Set}
  (cntm : CntNDTuringMachine State Symbol)
  (step_rel :
    (State * option Symbol) -> (direction * option State * Symbol) -> Prop) :
  Prop :=
  exists cntm', CNTM_step_rtc step_rel cntm cntm' /\
    CNTM_accept step_rel cntm'.
