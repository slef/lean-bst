module

import RotationBST.Audit.Check
public import RotationBST.Models.RealWorld.Linked.AbstractBridge

@[expose] public section
namespace RotationBST.RealWorld.Linked.Results

/-- Every legal abstract pointer operation has a bounded-time concrete
implementation preserving the entire tree, all node data, and exact storage. -/
theorem primitive {w e regs : Nat} {s : State w e regs} {c d : Cursor w e}
    {op : Multifinger.Opcode} (rep : Realizes s c)
    (legal : LabelledCursor.perform op c = some d) :
    ∃ t time, time ≤ 19 ∧ Cslib.PointerMachine.Executes (program op) (start s) t time ∧
      Realizes t d ∧ t.heap.length = s.heap.length := Linked.primitive rep legal

end RotationBST.RealWorld.Linked.Results

/-- info: abstract audit passed for `RotationBST.RealWorld.Linked.Results`: 1 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.RealWorld.Linked.Results allowing [
  RotationBST.Models.RealWorld.Linked.Definitions.Abstract,
  RotationBST.Models.RealWorld.PointerMachine.Definitions.Abstract,
  RotationBST.Models.Labelled.Cursor.Definitions.Abstract,
  RotationBST.Models.Multifinger.Program.Definitions.Abstract,
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Models.Labelled.Ordering.Definitions.Abstract,
  CslibFrontier.Computability.PointerMachine.Defs]
