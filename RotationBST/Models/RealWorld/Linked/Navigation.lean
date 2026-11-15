module

public import RotationBST.Models.RealWorld.Linked.Definitions.Abstract

@[expose] public section
namespace RotationBST.RealWorld.Linked
open Cslib.PointerMachine (Instr Runs Executes)
variable {w e regs : Nat}

/-- Named endpoint of a single pointer load. -/
def moved (s : State w e regs) (field : Fin 3) : State w e regs :=
  { (Instr.loadPtr 0 field 0).effect s with pc := 1 }

theorem move_executes (s : State w e regs) (field : Fin 3) :
    Executes (move field) (start s) (moved s field) 2 := by
  refine ⟨1, .single ?_, rfl, rfl⟩
  cases hd : s.deref 0 <;>
    simp only [Cslib.PointerMachine.State.deref] at hd <;>
    simp [Cslib.PointerMachine.step, move, start, moved, Instr.next, Instr.effect,
      Cslib.PointerMachine.State.deref, Cslib.PointerMachine.State.setPtr, hd]

theorem moved_eq {s : State w e regs} {x : Label w e} {l r p : Cslib.PointerMachine.Pointer}
    (cur : s.ptr 0 = some x.1) (hr : s.heap[x.1]? = some (node l r p x)) (f : Fin 3) :
    moved s f = { s.setPtr 0 ((node (regs := regs) l r p x).ptr f) with pc := 1 } := by
  simp [moved, Instr.effect, Cslib.PointerMachine.State.deref, cur, hr]

theorem downLeft {s : State w e regs} {a b r : Tree w e} {x y : Label w e}
    {cs : List (LabelledCursor.Frame (Label w e))}
    (h : Realizes s ⟨.node (.node a x b) y r, cs⟩) :
    Realizes (moved s 0) ⟨.node a x b, .left y r :: cs⟩ := by
  have hv := (move_executes s 0).valid h.valid
  have eq := moved_eq h.cursor h.focus.1 0
  rw [eq]
  refine ⟨?_, h.focus.2.1, ?_, h.distinct, h.covers, h.ordered, ?_, h.rootReg, by simp⟩
  · simpa [start, eq] using hv
  · exact ⟨h.focus.1, h.focus.2.2, h.context⟩
  · simp [Cslib.PointerMachine.State.setPtr, node, root]

theorem downRight {s : State w e regs} {l a b : Tree w e} {x y : Label w e}
    {cs : List (LabelledCursor.Frame (Label w e))}
    (h : Realizes s ⟨.node l x (.node a y b), cs⟩) :
    Realizes (moved s 1) ⟨.node a y b, .right l x :: cs⟩ := by
  have hv := (move_executes s 1).valid h.valid
  have eq := moved_eq h.cursor h.focus.1 1
  rw [eq]
  refine ⟨?_, h.focus.2.2, ?_, h.distinct, h.covers, h.ordered, ?_, h.rootReg, by simp⟩
  · simpa [start, eq] using hv
  · exact ⟨h.focus.1, h.focus.2.1, h.context⟩
  · simp [Cslib.PointerMachine.State.setPtr, node, root]

theorem upLeft {s : State w e regs} {a b r : Tree w e} {x y : Label w e}
    {cs : List (LabelledCursor.Frame (Label w e))}
    (h : Realizes s ⟨.node a x b, .left y r :: cs⟩) :
    Realizes (moved s 2) ⟨.node (.node a x b) y r, cs⟩ := by
  have hv := (move_executes s 2).valid h.valid
  have eq := moved_eq h.cursor h.focus.1 2
  rw [eq]
  refine ⟨?_, ?_, h.context.2.2, h.distinct, h.covers, h.ordered, ?_, h.rootReg, by simp⟩
  · simpa [start, eq] using hv
  · exact ⟨h.context.1, h.focus, h.context.2.1⟩
  · simp [Cslib.PointerMachine.State.setPtr, node, root, parent]

theorem upRight {s : State w e regs} {l a b : Tree w e} {x y : Label w e}
    {cs : List (LabelledCursor.Frame (Label w e))}
    (h : Realizes s ⟨.node a y b, .right l x :: cs⟩) :
    Realizes (moved s 2) ⟨.node l x (.node a y b), cs⟩ := by
  have hv := (move_executes s 2).valid h.valid
  have eq := moved_eq h.cursor h.focus.1 2
  rw [eq]
  refine ⟨?_, ?_, h.context.2.2, h.distinct, h.covers, h.ordered, ?_, h.rootReg, by simp⟩
  · simpa [start, eq] using hv
  · exact ⟨h.context.1, h.context.2.1, h.focus⟩
  · simp [Cslib.PointerMachine.State.setPtr, node, root, parent]

end RotationBST.RealWorld.Linked
