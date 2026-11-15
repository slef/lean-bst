module

import RotationBST.Audit.Check
public import RotationBST.Models.RealWorld.PointerMachine.AbstractBridge

@[expose] public section
namespace RotationBST.RealWorld.PointerMachine.Results

variable {w e : Nat}

/-- Completed request prefixes uniquely determine the actual machine state and time. -/
theorem causal {p : Protocol w e} {s t u : State w e}
    {xs : List (BitVec w)} {a b : Nat}
    (h : Execution p s xs t a) (k : Execution p s xs u b) : t = u ∧ a = b :=
  execution_unique h k

/-- A child-pointer load is one charged upstream instruction. -/
theorem navigation_time (s : State w e) (side : Fin 2) (pc : s.pc = 0) :
    Cslib.PointerMachine.Runs [down side, .halt] s (effects [down side] s) 1 :=
  down_runs s side pc

/-- Navigation reaches the represented left subtree without changing its storage. -/
theorem navigation {s : State w e} {l r : Tree w} {x : Nat × BitVec w}
    (h : Represents s.heap (.node l x r)) (cursor : s.ptr 0 = some x.1) :
    (effects [down 0] s).ptr 0 = root l ∧
      Represents (effects [down 0] s).heap l := down_left_refines h cursor

/-- A root right rotation takes five upstream instructions before halt. -/
theorem rotation_time (s : State w e) (pc : s.pc = 0) :
    Cslib.PointerMachine.Runs (rotateRight ++ [.halt]) s (effects rotateRight s) 5 :=
  rotateRight_runs s pc

/-- A root rotation preserves the ordered BST, its exact node storage, and validity. -/
theorem rotation {s : State w e} {a b c : Tree w} {x y : Nat × BitVec w}
    (h : Boundary s (.node (.node a x b) y c)) (pc : s.pc = 0) :
    Boundary (effects rotateRight s) (.node a x (.node b y c)) ∧
      (effects rotateRight s).heap.length = s.heap.length := rotateRight_boundary h pc

/-- The same change is down-left followed by the existing child rotation. -/
theorem rotation_bst (a b c : Tree w) (x y : Nat × BitVec w) :
    (LabelledCursor.perform .downLeft ⟨.node (.node a x b) y c, []⟩).bind
      (LabelledCursor.perform .rotateLeftChild) =
      some ⟨.node a x (.node b y c), []⟩ := rotateRight_cursor a b c x y

end RotationBST.RealWorld.PointerMachine.Results

/-- info: abstract audit passed for `RotationBST.RealWorld.PointerMachine.Results`: 6 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.RealWorld.PointerMachine.Results allowing [
  RotationBST.Models.RealWorld.PointerMachine.Definitions.Abstract,
  RotationBST.Models.Labelled.Cursor.Definitions.Abstract,
  RotationBST.Models.Multifinger.Program.Definitions.Abstract,
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Models.Labelled.Ordering.Definitions.Abstract,
  CslibFrontier.Computability.PointerMachine.Defs]
