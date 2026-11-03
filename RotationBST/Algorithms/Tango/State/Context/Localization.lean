module

public import RotationBST.Algorithms.Tango.State.Context.Lifting

@[expose] public section
namespace RotationBST.Tango.Context
open MarkedTree

theorem plug_append (xs ys : List Frame) (s : MarkedTree) :
    plug (xs ++ ys) s = plug ys (plug xs s) := by
  induction xs generalizing s with
  | nil => rfl
  | cons f fs ih => exact ih _

private theorem boundary_append {xs : List Frame} (nonempty : xs ≠ []) (boundary : Boundary xs)
    (ys : List Frame) : Boundary (xs ++ ys) := by
  cases xs with
  | nil => contradiction
  | cons f fs => exact boundary

/-- Every nonempty marked fringe subtree has a genuine component-boundary
context. Empty fringe slots are excluded because they need not carry a mark. -/
theorem locate_fringe (s child : MarkedTree) (member : child ∈ s.fringe) (nonempty : child ≠ .nil) :
    ∃ fs : List Frame, fs ≠ [] ∧ Boundary fs ∧ plug fs child = s := by
  induction s with
  | nil =>
    have h : child = .nil := by simpa [fringe] using member
    exact False.elim (nonempty h)
  | node l r cl cr il ir =>
    change child ∈ (if cl then [l] else l.fringe) ++ (if cr then [r] else r.fringe) at member
    rcases List.mem_append.mp member with hm | hm
    · cases cl
      · obtain ⟨fs, hn, hb, hp⟩ := il hm
        refine ⟨fs ++ [.left r false cr], ?_, boundary_append hn hb _, ?_⟩
        · simp
        · rw [plug_append, hp]; rfl
      · have eq : child = l := List.mem_singleton.mp hm
        subst child
        exact ⟨[.left r true cr], by simp, rfl, rfl⟩
    · cases cr
      · obtain ⟨fs, hn, hb, hp⟩ := ir hm
        refine ⟨fs ++ [.right l false cl], ?_, boundary_append hn hb _, ?_⟩
        · simp
        · rw [plug_append, hp]; rfl
      · have eq : child = r := List.mem_singleton.mp hm
        subst child
        exact ⟨[.right l true cl], by simp, rfl, rfl⟩

/-- A local component update has exactly the same rotation count and amortized
potential change when performed in its containing marked BST. -/
theorem embed_update (whole child target : MarkedTree) (member : child ∈ whole.fringe)
    (nonempty : child ≠ .nil) {cost : Nat} (rotations : Rotations child.tree target.tree cost) :
    ∃ result : MarkedTree, Rotations whole.tree result.tree cost ∧
      result.potential - whole.potential = target.potential - child.potential := by
  obtain ⟨fs, _, boundary, source⟩ := locate_fringe whole child member nonempty
  refine ⟨plug fs target, ?_, ?_⟩
  · simpa only [source] using plug_rotations fs rotations
  · simpa only [source] using boundary_potential fs boundary child target

end RotationBST.Tango.Context
