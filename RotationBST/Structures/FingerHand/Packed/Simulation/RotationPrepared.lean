module

public import RotationBST.Structures.FingerHand.Packed.Geometry.Rotation
public import RotationBST.Structures.FingerHand.Packed.Simulation.RotationLocal

@[expose] public section
namespace RotationBST.FingerHand.Hand

/-- A prepared right rotation is realized on the actual reference tree, with
canonical temporary marks and unchanged hand count and potential. -/
theorem rotate_right_prepared (h : Hand) (marks : Finset Nat) (a b c : Tree) (anc : List Pointer.Frame)
    (valid : h.Valid) (reference : h.reference = Pointer.plug anc (.node (.node a b) c))
    (canonical : h.labels 0 = compress marks h.reference 0)
    (child : Pointer.offset anc + a.size ∈ marks)
    (parent : Pointer.offset anc + (Tree.node a b).size ∈ marks) :
    ∃ (after : Hand) (k : Nat), after.Valid ∧
      after.reference = Pointer.plug anc (.node a (.node b c)) ∧
      after.labels 0 = compress marks after.reference 0 ∧
      after.count = h.count ∧ after.potential = h.potential ∧
      Pointer.Trace ⟨h.tree, []⟩ ⟨after.tree, []⟩ k ∧
      k + after.potential ≤ 10 + 10 * h.count + h.potential := by
  have childMember := canonical_cursor_member h marks canonical ⟨.node a b, .left c :: anc⟩ _ reference.symm rfl child
  have parentMember := canonical_cursor_member h marks canonical ⟨.node (.node a b) c, anc⟩ _ reference.symm rfl parent
  obtain ⟨fs, cs, d, e, l, r, sibling, rfl, rfl, rfl, rfl, rfl, depth⟩ :=
    rotation_right_shape h a b c anc reference childMember parentMember
  have lower : Pointer.offset (Context.referencePath fs) + Pointer.offset cs + l.reference.size ∈ marks := by
    simpa only [Pointer.offset_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using child
  have upper : Pointer.offset (Context.referencePath fs) + Pointer.offset cs + l.reference.size + 1 + r.reference.size ∈ marks := by
    simpa only [Pointer.offset_append, Tree.size, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using parent
  obtain ⟨afterValid, normal, count, phi, k, trace, cost⟩ :=
    rotate_right_empty fs cs d e l r sibling marks valid canonical lower upper
  refine ⟨_, k, afterValid, ?_, normal, count, phi, trace, by omega⟩
  simp only [Context.plug_reference, Hand.reference, fork, Pointer.plug, Pointer.plug_append]

theorem rotate_left_prepared (h : Hand) (marks : Finset Nat) (a b c : Tree) (anc : List Pointer.Frame)
    (valid : h.Valid) (reference : h.reference = Pointer.plug anc (.node a (.node b c)))
    (canonical : h.labels 0 = compress marks h.reference 0)
    (child : Pointer.offset anc + a.size + 1 + b.size ∈ marks)
    (parent : Pointer.offset anc + a.size ∈ marks) :
    ∃ (after : Hand) (k : Nat), after.Valid ∧
      after.reference = Pointer.plug anc (.node (.node a b) c) ∧
      after.labels 0 = compress marks after.reference 0 ∧
      after.count = h.count ∧ after.potential = h.potential ∧
      Pointer.Trace ⟨h.tree, []⟩ ⟨after.tree, []⟩ k ∧
      k + after.potential ≤ 10 + 10 * h.count + h.potential := by
  have childMember := canonical_cursor_member h marks canonical ⟨.node b c, .right a :: anc⟩ _ reference.symm rfl child
  have parentMember := canonical_cursor_member h marks canonical ⟨.node a (.node b c), anc⟩ _ reference.symm rfl parent
  obtain ⟨fs, cs, d, e, sibling, l, r, rfl, rfl, rfl, rfl, rfl, depth⟩ :=
    rotation_left_shape h a b c anc reference childMember parentMember
  have lower : Pointer.offset (Context.referencePath fs) + Pointer.offset cs + sibling.reference.size ∈ marks := by
    simpa only [Pointer.offset_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using parent
  have upper : Pointer.offset (Context.referencePath fs) + Pointer.offset cs + sibling.reference.size + 1 + l.reference.size ∈ marks := by
    simpa only [Pointer.offset_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using child
  obtain ⟨afterValid, normal, count, phi, k, trace, cost⟩ :=
    rotate_left_empty fs cs d e sibling l r marks valid canonical lower upper
  refine ⟨_, k, afterValid, ?_, normal, count, phi, trace, by omega⟩
  simp only [Context.plug_reference, Hand.reference, fork, Pointer.plug, Pointer.plug_append]

end RotationBST.FingerHand.Hand
