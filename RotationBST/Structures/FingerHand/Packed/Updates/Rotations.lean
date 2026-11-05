module

public import RotationBST.Structures.FingerHand.Packed.Updates.Shapes

@[expose] public section
namespace RotationBST.FingerHand.Hand

theorem LocalRotation.valid {a b : Hand} (rot : LocalRotation a b) (valid : a.Valid) : b.Valid := by
  cases rot with
  | right cs d a b c =>
    exact ⟨valid.1, valid.2.1.2.1, Tendon.State.ofPath_represents [], valid.2.1.2.2, valid.2.2⟩
  | left cs d a b c =>
    exact ⟨valid.1, ⟨Tendon.State.ofPath_represents [], valid.2.1, valid.2.2.2.1⟩, valid.2.2.2.2⟩

theorem LocalRotation.reference {a b : Hand} (rot : LocalRotation a b) :
    RotationBST.Rotate a.reference b.reference := by
  cases rot with
  | right cs d a b c => exact Pointer.Rotate.plug .right cs
  | left cs d a b c => exact Pointer.Rotate.plug .left cs

/-- The same ordinary rotation occurs on the rank-labelled pseudofinger
skeleton, so all existing pseudofingers retain their global key identities. -/
theorem LocalRotation.labels {a b : Hand} (rot : LocalRotation a b) (lo : Nat) :
    LabelledTree.Rotate (a.labels lo) (b.labels lo) := by
  cases rot <;>
    simp only [fork, Hand.labels, Hand.reference, Pointer.plug, Pointer.offset, Nat.add_zero,
      Tree.size, Nat.add_assoc]
  · exact .right
  · exact .left

theorem LocalRotation.potential {a b : Hand} (rot : LocalRotation a b) : a.potential = b.potential := by
  cases rot <;> simp only [Hand.potential, fork, empty_tendon_potential] <;> omega

theorem LocalRotation.count {a b : Hand} (rot : LocalRotation a b) : a.count = b.count := by
  cases rot <;> simp only [Hand.count, fork] <;> omega

/-- Two pointer instructions perform the exposed rotation. Reaching its bottom
through the incoming tendon and returning adds at most eight instructions. -/
theorem LocalRotation.trace {a b : Hand} (rot : LocalRotation a b) :
    ∃ k, k ≤ 10 ∧ Pointer.Trace ⟨a.tree, []⟩ ⟨b.tree, []⟩ k := by
  cases rot with
  | right cs d a b c =>
    have localTrace : Pointer.Trace ⟨.node (.node a.tree b.tree) c.tree, []⟩
        ⟨.node a.tree (.node b.tree c.tree), []⟩ 2 :=
      .step .downLeft (.step .rotateLeftChild .refl)
    have run := localTrace.inContext (by simp) (by simp) d.context
    refine ⟨d.context.length + 2 + d.context.length, ?_, ?_⟩
    · have := d.context_length; omega
    · simp only [tree, fork, empty_tendon_tree]
      exact run
  | left cs d a b c =>
    have localTrace : Pointer.Trace ⟨.node a.tree (.node b.tree c.tree), []⟩
        ⟨.node (.node a.tree b.tree) c.tree, []⟩ 2 :=
      .step .downRight (.step .rotateRightChild .refl)
    have run := localTrace.inContext (by simp) (by simp) d.context
    refine ⟨d.context.length + 2 + d.context.length, ?_, ?_⟩
    · have := d.context_length; omega
    · simp only [tree, fork, empty_tendon_tree]
      exact run

end RotationBST.FingerHand.Hand
