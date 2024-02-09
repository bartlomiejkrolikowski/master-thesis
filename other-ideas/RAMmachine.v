Require Import ZArith.
Require Import Relation_Operators.

Inductive InstructionF (Value Address IAddress : Set) : Set :=
(* sets the register to the given constant value *)
| setR     : Value -> InstructionF Value Address IAddress
(* adds a value from the given location to the register *)
| add      : Address -> InstructionF Value Address IAddress
(* negates the register *)
| neg      : InstructionF Value Address IAddress
(* multiplies a value from the given location by the register *)
| mul      : Address -> InstructionF Value Address IAddress
(* divides the register by a value from the given location *)
| div      : Address -> InstructionF Value Address IAddress
(* loads a value from the given location to the register *)
| load     : Address -> InstructionF Value Address IAddress
(* loads a value from the location
  stored at the given location
  to the register *)
| loadI    : Address -> InstructionF Value Address IAddress
(* stores the register at the given location *)
| store    : Address -> InstructionF Value Address IAddress
(* stores the register at the location
  stored at the given location *)
| storeI   : Address -> InstructionF Value Address IAddress
(* jumps to the given instruction *)
| jumpZero : IAddress -> InstructionF Value Address IAddress
(* jumps if register is positive *)
| jumpPos  : IAddress -> InstructionF Value Address IAddress
(* no operation *)
| nop      : InstructionF Value Address IAddress
| halt     : InstructionF Value Address IAddress
.

Arguments setR     {Value Address IAddress}.
Arguments add      {Value Address IAddress}.
Arguments neg      {Value Address IAddress}.
Arguments mul      {Value Address IAddress}.
Arguments div      {Value Address IAddress}.
Arguments load     {Value Address IAddress}.
Arguments loadI    {Value Address IAddress}.
Arguments store    {Value Address IAddress}.
Arguments storeI   {Value Address IAddress}.
Arguments jumpZero {Value Address IAddress}.
Arguments jumpPos  {Value Address IAddress}.
Arguments nop      {Value Address IAddress}.
Arguments halt     {Value Address IAddress}.

(* Z is the type of stored values,
  nat is the type of instruction indexes *)
Definition Instruction : Set := InstructionF Z Z nat.

Record RMstate : Set := {
  register     : Z;
  memory       : Z -> Z;
  (* instruction pointer *)
  i_pointer    : nat;
}.

Record RAMmachine : Set := {
  rm_state     : RMstate;
  instrucitons : nat -> Instruction;
}.

Definition next_instruction (s : RMstate) : RMstate :=
  {|
    register  := register s;
    memory    := memory s;
    i_pointer := S (i_pointer s);
  |}.

Definition set_register (s : RMstate) (x : Z) : RMstate :=
  {|
    register  := x;
    memory    := memory s;
    i_pointer := i_pointer s;
  |}.

Definition set_i_pointer (s : RMstate) (ip : nat) : RMstate :=
  {|
    register  := register s;
    memory    := memory s;
    i_pointer := ip;
  |}.

Definition step_set_register (s : RMstate) (x : Z) : RMstate :=
  next_instruction (set_register s x).

Definition set_memory_cell (mem : Z -> Z) (i : Z) (x : Z) : Z -> Z :=
  fun j : Z => if (i =? j)%Z then x else mem j.

Definition set_memory (s : RMstate) (i x : Z) : RMstate :=
  {|
    register  := register s;
    memory    := set_memory_cell (memory s) i x;
    i_pointer := i_pointer s;
  |}.

Definition step_set_memory (s : RMstate) (i x : Z) : RMstate :=
  next_instruction (set_memory s i x).

Definition step (s : RMstate) (i : Instruction) :
  option RMstate :=
  match i with
  | setR c     => Some (step_set_register s c)
  | add a      => Some (step_set_register s (register s + memory s a))
  | neg        => Some (step_set_register s (Z.opp (register s)))
  | mul a      => Some (step_set_register s (register s * memory s a))
  | div a      => Some (step_set_register s (register s / memory s a))
  | load a     => Some (step_set_register s (memory s a))
  | loadI a    => Some (step_set_register s (memory s (memory s a)))
  | store a    => Some (step_set_memory s a (register s))
  | storeI a   => Some (step_set_memory s (memory s a) (register s))
  | jumpZero i => if (0 =? register s)%Z
    then Some (set_i_pointer s i)
    else Some (next_instruction s)
  | jumpPos i  => if (0 <? register s)%Z
    then Some (set_i_pointer s i)
    else Some (next_instruction s)
  | nop        => Some (next_instruction s)
  | halt       => None
  end.

Definition state_make_step (s : RMstate) (is : nat -> Instruction) :
  option RMstate :=
  step s (is (i_pointer s)).

Definition make_step (rm : RAMmachine) : option RAMmachine :=
  option_map (fun s =>
    {|
      rm_state     := s;
      instrucitons := instrucitons rm;
    |}
  ) (state_make_step (rm_state rm) (instrucitons rm)).

Record CountingRM : Set := {
  rm      : RAMmachine;
  counter : nat;
}.

Definition cnt_make_step (crm : CountingRM) : option CountingRM :=
  option_map (fun rm =>
    {|
      rm      := rm;
      counter := S (counter crm);
    |}
  ) (make_step (rm crm)).

Definition CRM_step (crm crm' : CountingRM) : Prop :=
  Some crm' = cnt_make_step crm.

(** Reflexive and transitive closure of the step relation *)
Notation CRM_step_rtc crm crm' :=
  (clos_refl_trans_1n _ CRM_step crm crm').

Definition CRM_stop (crm : CountingRM) : Prop :=
  cnt_make_step crm = None.

Definition Result (crm crm' : CountingRM) : Prop :=
  CRM_step_rtc crm crm' /\ CRM_stop crm'.

Definition Stops (crm : CountingRM) : Prop :=
  exists crm', Result crm crm'.
