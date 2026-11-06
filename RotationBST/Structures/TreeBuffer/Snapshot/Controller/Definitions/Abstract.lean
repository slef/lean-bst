module

public import RotationBST.Structures.TreeBuffer.Snapshot.Definitions.Abstract

@[expose] public section
namespace RotationBST.TreeBuffer.Snapshot.Controller
open Multifinger

inductive Mode where
  | scan | promote | ascend
  deriving DecidableEq

/-- A cursor, one spine-depth counter, and a finite control mode. The tree in
the cursor is the machine's tree, not an additional saved copy. -/
structure State where
  cursor : Pointer.Config
  depth : Nat
  mode : Mode
  deriving DecidableEq

/-- Select the next action using only the current focus, mode, and depth counter.
`none` as the opcode is a control-only transition into the return phase. -/
def choose (s : State) : Option (Option Opcode × Mode × Nat) :=
  match s.mode, s.cursor.focus, s.depth with
  | .scan, .nil, d => some (none, .ascend, d)
  | .scan, .node .nil .nil, d => some (none, .ascend, d)
  | .scan, .node .nil (.node _ _), d => some (some .downRight, .scan, d + 1)
  | .scan, .node (.node _ _) _, d => some (some .downLeft, .promote, d)
  | .promote, _, d => some (some .rotateLeftChild, .scan, d)
  | .ascend, _, 0 => none
  | .ascend, _, d + 1 => some (some .upRight, .ascend, d)

/-- Execute the selected pointer instruction. A failed instruction is not
silently converted into a state change. -/
def tick (s : State) : Option (Option Opcode × State) :=
  (choose s).bind fun (op, mode, depth) =>
    match op with
    | none => some (none, ⟨s.cursor, depth, mode⟩)
    | some instruction => (perform instruction s.cursor).map fun cursor =>
        (some instruction, ⟨cursor, depth, mode⟩)

/-- Exact emitted log, including the control-only transition separately from
the physical instruction count. A run may end at an intermediate state. -/
inductive Run : State → List Opcode → State → Prop where
  | refl {s : State} : Run s [] s
  | silent {s t u : State} {ops : List Opcode} :
      tick s = some (none, t) → Run t ops u → Run s ops u
  | instruction {s t u : State} {op : Opcode} {ops : List Opcode} :
      tick s = some (some op, t) → Run t ops u → Run s (op :: ops) u

end RotationBST.TreeBuffer.Snapshot.Controller
