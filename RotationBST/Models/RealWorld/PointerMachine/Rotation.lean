module

public import RotationBST.Models.RealWorld.PointerMachine.Proofs

@[expose] public section
namespace RotationBST.RealWorld.PointerMachine
open Cslib.PointerMachine (Instr)
variable {w e : Nat}

/-- The two writes made by the right-rotation program. -/
def rewired (heap : List (Record w e)) (x y : Nat) (beta : Cslib.PointerMachine.Pointer) :=
  (heap.modify y (fun r => { r with ptr := Function.update r.ptr 0 beta })).modify x
    (fun r => { r with ptr := Function.update r.ptr 1 (some y) })

theorem rotation_effect (s : State w e) (x y : Nat) (rx ry : Record w e)
    (cur : s.ptr 0 = some y) (hy : s.heap[y]? = some ry)
    (hx : s.heap[x]? = some rx) (left : ry.ptr 0 = some x) :
    (effects rotateRight s).heap = rewired s.heap x y (rx.ptr 1) ∧
    (effects rotateRight s).ptr 0 = some x := by
  simp [effects, rotateRight, Instr.effect, Cslib.PointerMachine.State.deref,
    Cslib.PointerMachine.State.setPtr, Cslib.PointerMachine.State.modify,
    cur, hy, hx, left, rewired]

theorem rewired_other (heap : List (Record w e)) (x y z : Nat)
    (beta : Cslib.PointerMachine.Pointer) (hx : z ≠ x) (hy : z ≠ y) :
    (rewired heap x y beta)[z]? = heap[z]? := by
  simp [rewired, Ne.symm hx, Ne.symm hy]

/-- Rotation preserves arbitrary represented subtrees away from the two pivots. -/
theorem rewired_frame {heap : List (Record w e)} {t : Tree w} {x y : Nat}
    {beta : Cslib.PointerMachine.Pointer} (h : Represents heap t)
    (apart : ∀ z ∈ addresses t, z ≠ x ∧ z ≠ y) :
    Represents (rewired heap x y beta) t :=
  represents_frame h (fun z hz => rewired_other heap x y z beta (apart z hz).1 (apart z hz).2)

/-- Full recursive representation after a root rotation. Address separation is
explicit here; a valid tree with distinct addresses supplies it. -/
theorem rotateRight_represents {s : State w e} {a b c : Tree w} {x y : Nat × BitVec w}
    (rep : Represents s.heap (.node (.node a x b) y c))
    (cur : s.ptr 0 = some y.1) (different : x.1 ≠ y.1)
    (apart : ∀ z ∈ addresses a ++ addresses b ++ addresses c, z ≠ x.1 ∧ z ≠ y.1) :
    Represents (effects rotateRight s).heap (.node a x (.node b y c)) ∧
    (effects rotateRight s).ptr 0 = some x.1 := by
  obtain ⟨⟨ry, hy, ly, ryright, ky⟩, ⟨⟨rx, hx, lx, rxright, kx⟩, ra, rb⟩, rc⟩ := rep
  have eff := rotation_effect s x.1 y.1 rx ry cur hy hx ly
  rw [eff.1]
  refine ⟨⟨?_, ?_, ?_⟩, eff.2⟩
  · refine ⟨{ rx with ptr := Function.update rx.ptr 1 (some y.1) }, ?_, ?_, ?_, kx⟩
    · simp [rewired, Ne.symm different, hx]
    · simpa using lx
    · rfl
  · exact rewired_frame ra (fun z hz => apart z (by simp [hz]))
  · refine ⟨?_, ?_, ?_⟩
    · refine ⟨{ ry with ptr := Function.update ry.ptr 0 (rx.ptr 1) }, ?_, ?_, ryright, ky⟩
      · simp [rewired, different, hy]
      · simpa using rxright
    · exact rewired_frame rb (fun z hz => apart z (by simp [hz]))
    · exact rewired_frame rc (fun z hz => apart z (by simp [hz]))

/-- The represented change is precisely the existing down-left then rotation
operation. There is no new notion of tree rotation hidden in the machine layer. -/
theorem rotateRight_cursor (a b c : Tree w) (x y : Nat × BitVec w) :
    (LabelledCursor.perform .downLeft ⟨.node (.node a x b) y c, []⟩).bind
      (LabelledCursor.perform .rotateLeftChild) =
      some ⟨.node a x (.node b y c), []⟩ := rfl

/-- The entire BST boundary invariant survives the program, with no new records. -/
theorem rotateRight_boundary {s : State w e} {a b c : Tree w} {x y : Nat × BitVec w}
    (h : Boundary s (.node (.node a x b) y c)) (hpc : s.pc = 0) :
    Boundary (effects rotateRight s) (.node a x (.node b y c)) ∧
      (effects rotateRight s).heap.length = s.heap.length := by
  have nd := h.distinct
  simp only [addresses, LabelledTree.inorder, List.map_append, List.map_cons,
    List.append_assoc, List.nodup_append, List.nodup_cons,
    List.mem_append, List.mem_cons, List.mem_map] at nd
  have different : x.1 ≠ y.1 := by grind
  have apart : ∀ z ∈ addresses a ++ addresses b ++ addresses c, z ≠ x.1 ∧ z ≠ y.1 := by
    simp only [addresses, List.mem_append, List.mem_map]
    grind
  obtain ⟨rep, cur⟩ := rotateRight_represents h.represents h.cursor different apart
  obtain ⟨⟨ry, hy, ly, _, _⟩, ⟨⟨rx, hx, _, _, _⟩, _, _⟩, _⟩ := h.represents
  have length : (effects rotateRight s).heap.length = s.heap.length := by
    rw [(rotation_effect s x.1 y.1 rx ry h.cursor hy hx ly).1]
    simp [rewired]
  have addr : addresses (.node a x (.node b y c)) = addresses (.node (.node a x b) y c) := by
    simp [addresses, LabelledTree.inorder, List.append_assoc]
  refine ⟨⟨(rotateRight_runs s hpc).valid h.valid, rep, ?_, ?_, ?_, cur⟩, length⟩
  · rw [addr]; exact h.distinct
  · intro z; rw [length, addr]; exact h.covers z
  · rw [Representation.ordered_iff]
    simpa [keys, LabelledTree.inorder, List.append_assoc] using
      (Representation.ordered_iff _).mp h.ordered

end RotationBST.RealWorld.PointerMachine
