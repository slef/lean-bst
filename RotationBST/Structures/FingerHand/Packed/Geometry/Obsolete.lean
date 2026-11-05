module

public import RotationBST.Structures.FingerHand.Packed.Geometry.Reduced

@[expose] public section
namespace RotationBST.FingerHand.Hand

theorem obsolete_unmarked (h : Hand) (marks : Finset Nat) (lo x : Nat)
    (member : x ∈ (h.labels lo).inorder)
    (absent : x ∉ (compress marks h.reference lo).inorder) : x ∉ marks := by
  intro marked
  exact absent (marked_mem marks h.reference lo x ((labels_sublist h lo).subset member) marked)

/-- Removing a mark cannot discard a vertex with two retained descendants.
Consequently an obsolete pseudofinger has a knuckle on at least one side. -/
theorem obsolete_shape (fs : List ContextFrame) (cs : List Pointer.Frame) (d : Tendon.State)
    (l r : Hand) (marks : Finset Nat) (lo : Nat)
    (canonical : (Context.plug fs (.node cs d l r)).labels lo =
      compress (insert (lo + Pointer.offset (Context.referencePath fs) + Pointer.offset cs +
        l.reference.size) marks) (Context.plug fs (.node cs d l r)).reference lo)
    (absent : lo + Pointer.offset (Context.referencePath fs) + Pointer.offset cs +
      l.reference.size ∉
        (compress marks (Context.plug fs (.node cs d l r)).reference lo).inorder) :
    (∃ t, l = .knuckle t) ∨ (∃ t, r = .knuckle t) := by
  let x := lo + Pointer.offset (Context.referencePath fs) + Pointer.offset cs + l.reference.size
  have normal : Reduced (insert x marks) ((Context.plug fs (.node cs d l r)).labels lo) := by
    rw [canonical]
    exact compress_reduced _ _ _
  have inside := Context.reduced fs (.node cs d l r) (insert x marks) lo normal
  have distinct := node_distinct (labels_distinct (.node cs d l r)
    (lo + Pointer.offset (Context.referencePath fs)))
  have fixedLeft := (inside.1.without distinct.2.2.1).fixed
  have fixedRight := (inside.2.1.without distinct.2.2.2.1).fixed
  cases l with
  | knuckle t => exact Or.inl ⟨t, rfl⟩
  | node ls ld ll lr =>
    cases r with
    | knuckle t => exact Or.inr ⟨t, rfl⟩
    | node rs rd rl rr =>
      exfalso
      apply absent
      rw [← prune_compress (Finset.subset_insert x marks), ← canonical]
      apply Context.prune_member
      change x ∈ (join marks (prune marks _) x (prune marks _)).inorder
      rw [fixedLeft, fixedRight]
      by_cases marked : x ∈ marks <;>
        simp [join, marked, labels, LabelledTree.inorder]

end RotationBST.FingerHand.Hand
