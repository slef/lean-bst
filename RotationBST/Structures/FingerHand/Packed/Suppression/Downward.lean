module

public import RotationBST.Structures.FingerHand.Packed.Geometry.Children
public import RotationBST.Structures.FingerHand.Packed.Suppression.Normalize

@[expose] public section
namespace RotationBST.FingerHand.Hand

/-- Clean up an obsolete pseudofinger after moving to its retained actual
left child. The shape is inferred from canonicality, rather than assumed. -/
theorem suppress_down_left (fs : List ContextFrame) (cs : List Pointer.Frame) (d : Tendon.State)
    (l r : Hand) (marks : Finset Nat)
    (valid : (Context.plug fs (.node cs d l r)).Valid)
    (canonical : (Context.plug fs (.node cs d l r)).labels 0 =
      compress (insert (Pointer.offset (Context.referencePath fs) + Pointer.offset cs +
        l.reference.size) marks) (Context.plug fs (.node cs d l r)).reference 0)
    (absent : Pointer.offset (Context.referencePath fs) + Pointer.offset cs + l.reference.size ∉
      (compress marks (Context.plug fs (.node cs d l r)).reference 0).inorder)
    (nonempty : l.reference ≠ .nil)
    (child : Pointer.offset (Context.referencePath fs) + Pointer.offset cs + rootRank l.reference ∈
      ((Context.plug fs (.node cs d l r)).labels 0).inorder) :
    ∃ (after : Hand) (k : Nat), after.Valid ∧
      after.reference = (Context.plug fs (.node cs d l r)).reference ∧
      after.labels 0 = compress marks after.reference 0 ∧
      Suppress marks (Pointer.offset (Context.referencePath fs) + Pointer.offset cs + l.reference.size)
        ((Context.plug fs (.node cs d l r)).labels 0) (after.labels 0) ∧
      Pointer.Trace ⟨(Context.plug fs (.node cs d l r)).tree, []⟩ ⟨after.tree, []⟩ k ∧
      k + after.potential ≤ 134 + 10 * fs.length + (Context.plug fs (.node cs d l r)).potential := by
  have shape := obsolete_left_shape fs cs d l r marks 0 (by simpa only [Nat.zero_add] using canonical)
    (by simpa only [Nat.zero_add] using absent) nonempty (by simpa only [Nat.zero_add] using child)
  have unmarked := obsolete_unmarked _ marks 0 _
    (Context.node_member fs cs d l r 0) (by simpa only [Nat.zero_add] using absent)
  simp only [Nat.zero_add] at unmarked
  obtain ⟨e, a, b, g, rfl, rfl⟩ := shape
  obtain ⟨afterValid, reference, suppression, k, trace, cost⟩ :=
    suppress_bottom_empty fs cs d e (.left g) a b marks valid
  refine ⟨_, k, afterValid, reference, ?_, suppression, trace, cost⟩
  exact suppression_canonical marks 0 _ reference suppression unmarked canonical

theorem suppress_down_right (fs : List ContextFrame) (cs : List Pointer.Frame) (d : Tendon.State)
    (l r : Hand) (marks : Finset Nat)
    (valid : (Context.plug fs (.node cs d l r)).Valid)
    (canonical : (Context.plug fs (.node cs d l r)).labels 0 =
      compress (insert (Pointer.offset (Context.referencePath fs) + Pointer.offset cs +
        l.reference.size) marks) (Context.plug fs (.node cs d l r)).reference 0)
    (absent : Pointer.offset (Context.referencePath fs) + Pointer.offset cs + l.reference.size ∉
      (compress marks (Context.plug fs (.node cs d l r)).reference 0).inorder)
    (nonempty : r.reference ≠ .nil)
    (child : Pointer.offset (Context.referencePath fs) + Pointer.offset cs + l.reference.size + 1 +
      rootRank r.reference ∈ ((Context.plug fs (.node cs d l r)).labels 0).inorder) :
    ∃ (after : Hand) (k : Nat), after.Valid ∧
      after.reference = (Context.plug fs (.node cs d l r)).reference ∧
      after.labels 0 = compress marks after.reference 0 ∧
      Suppress marks (Pointer.offset (Context.referencePath fs) + Pointer.offset cs + l.reference.size)
        ((Context.plug fs (.node cs d l r)).labels 0) (after.labels 0) ∧
      Pointer.Trace ⟨(Context.plug fs (.node cs d l r)).tree, []⟩ ⟨after.tree, []⟩ k ∧
      k + after.potential ≤ 134 + 10 * fs.length + (Context.plug fs (.node cs d l r)).potential := by
  have shape := obsolete_right_shape fs cs d l r marks 0 (by simpa only [Nat.zero_add] using canonical)
    (by simpa only [Nat.zero_add] using absent) nonempty (by simpa only [Nat.zero_add] using child)
  have unmarked := obsolete_unmarked _ marks 0 _
    (Context.node_member fs cs d l r 0) (by simpa only [Nat.zero_add] using absent)
  simp only [Nat.zero_add] at unmarked
  obtain ⟨g, e, a, b, rfl, rfl⟩ := shape
  obtain ⟨afterValid, reference, suppression, k, trace, cost⟩ :=
    suppress_bottom_empty fs cs d e (.right g) a b marks valid
  refine ⟨_, k, afterValid, reference, ?_, suppression, trace, cost⟩
  exact suppression_canonical marks 0 _ reference suppression unmarked canonical

end RotationBST.FingerHand.Hand
