module

public import RotationBST.Models.RealWorld.Linked.Refinement

@[expose] public section
namespace RotationBST.RealWorld.Linked
variable {w e regs : Nat}

theorem same_storage {s t : State w e regs} {c d : Cursor w e}
    (hs : Realizes s c) (ht : Realizes t d) (same : c.tree.inorder = d.tree.inorder) :
    t.heap.length = s.heap.length := by
  have cov : ∀ a, a < s.heap.length ↔ a < t.heap.length := by
    intro a
    rw [hs.covers, ht.covers]
    simp only [addresses, same]
  have := cov s.heap.length
  have := cov t.heap.length
  omega

/-- Every legal primitive has a concrete upstream program. The bound includes
halt, and no records are allocated. Dispatch between primitive programs is
not represented by this theorem; compiling a controller is a separate step. -/
theorem primitive {s : State w e regs} {c d : Cursor w e} {op : Multifinger.Opcode}
    (h : Realizes s c) (legal : LabelledCursor.perform op c = some d) :
    ∃ t time, time ≤ 19 ∧ Cslib.PointerMachine.Executes (program op) (start s) t time ∧
      Realizes t d ∧ t.heap.length = s.heap.length := by
  have same := LabelledCursor.perform_inorder legal
  suffices result : ∃ t time, time ≤ 19 ∧
      Cslib.PointerMachine.Executes (program op) (start s) t time ∧ Realizes t d by
    obtain ⟨t, time, bound, exec, rep⟩ := result
    exact ⟨t, time, bound, exec, rep, same_storage h rep same⟩
  unfold LabelledCursor.perform at legal
  split at legal <;> simp_all only [Option.some.injEq, reduceCtorEq]
  all_goals subst d
  · exact ⟨moved s 0, 2, by decide, move_executes s 0, downLeft h⟩
  · exact ⟨moved s 1, 2, by decide, move_executes s 1, downRight h⟩
  · exact ⟨moved s 2, 2, by decide, move_executes s 2, upLeft h⟩
  · exact ⟨moved s 2, 2, by decide, move_executes s 2, upRight h⟩
  · obtain ⟨time, bound, exec⟩ := rotate_time s 0 1
    exact ⟨_, time, bound, exec, rotateLeftChild h⟩
  · obtain ⟨time, bound, exec⟩ := rotate_time s 1 0
    exact ⟨_, time, bound, exec, rotateRightChild h⟩

end RotationBST.RealWorld.Linked
