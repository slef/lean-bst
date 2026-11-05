module

public import RotationBST.Structures.FingerHand.Packed.Neighbors.Root

@[expose] public section
namespace RotationBST.FingerHand.Hand

/-- Make the left child of the specified pseudofinger available. The child may
be the root of a knuckle, inside a tendon, or already a pseudofinger. -/
theorem expose_left (fs : List ContextFrame) (cs : List Pointer.Frame) (d : Tendon.State) (l r : Hand)
    (valid : (Context.plug fs (.node cs d l r)).Valid) (nonempty : l.reference ≠ .nil) :
    ∃ (after : Hand) (k : Nat), Exposure (Context.plug fs (.node cs d l r)) after
        (Pointer.offset (Context.referencePath fs) + Pointer.offset cs + rootRank l.reference) ∧
      Pointer.Trace ⟨(Context.plug fs (.node cs d l r)).tree, []⟩ ⟨after.tree, []⟩ k ∧
      k + after.potential ≤ 142 + 10 * fs.length + (Context.plug fs (.node cs d l r)).potential := by
  obtain ⟨after, k, ex, trace, cost⟩ := expose_region (.left cs d r :: fs) l valid nonempty
  refine ⟨after, k, ?_, trace, ?_⟩
  · simpa only [Context.referencePath, Context.plug, Pointer.offset_append, Pointer.offset,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ex
  · simp only [List.length_cons, Context.plug] at cost
    omega

/-- The right-child counterpart, retaining the full left-subtree rank offset. -/
theorem expose_right (fs : List ContextFrame) (cs : List Pointer.Frame) (d : Tendon.State) (l r : Hand)
    (valid : (Context.plug fs (.node cs d l r)).Valid) (nonempty : r.reference ≠ .nil) :
    ∃ (after : Hand) (k : Nat), Exposure (Context.plug fs (.node cs d l r)) after
        (Pointer.offset (Context.referencePath fs) + Pointer.offset cs + l.reference.size + 1 + rootRank r.reference) ∧
      Pointer.Trace ⟨(Context.plug fs (.node cs d l r)).tree, []⟩ ⟨after.tree, []⟩ k ∧
      k + after.potential ≤ 142 + 10 * fs.length + (Context.plug fs (.node cs d l r)).potential := by
  obtain ⟨after, k, ex, trace, cost⟩ := expose_region (.right cs d l :: fs) r valid nonempty
  refine ⟨after, k, ?_, trace, ?_⟩
  · simpa only [Context.referencePath, Context.plug, Pointer.offset_append, Pointer.offset,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ex
  · simp only [List.length_cons, Context.plug] at cost
    omega

end RotationBST.FingerHand.Hand
