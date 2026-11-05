module

public import RotationBST.Structures.FingerHand.Packed.Geometry.Root
public import RotationBST.Structures.FingerHand.Packed.Geometry.Obsolete

@[expose] public section
namespace RotationBST.FingerHand.Hand

/-- An obsolete parent of a retained actual left child has precisely the
shape required by bottom contraction: an exposed child and a knuckle sibling. -/
theorem obsolete_left_shape (fs : List ContextFrame) (cs : List Pointer.Frame) (d : Tendon.State)
    (l r : Hand) (marks : Finset Nat) (lo : Nat)
    (canonical : (Context.plug fs (.node cs d l r)).labels lo =
      compress (insert (lo + Pointer.offset (Context.referencePath fs) + Pointer.offset cs +
        l.reference.size) marks) (Context.plug fs (.node cs d l r)).reference lo)
    (absent : lo + Pointer.offset (Context.referencePath fs) + Pointer.offset cs + l.reference.size ∉
      (compress marks (Context.plug fs (.node cs d l r)).reference lo).inorder)
    (nonempty : l.reference ≠ .nil)
    (child : lo + Pointer.offset (Context.referencePath fs) + Pointer.offset cs + rootRank l.reference ∈
      ((Context.plug fs (.node cs d l r)).labels lo).inorder) :
    ∃ (e : Tendon.State) (a b : Hand) (g : Tree), l = .node [] e a b ∧ r = .knuckle g := by
  have retained : lo + Pointer.offset (Context.referencePath (.left cs d r :: fs)) + rootRank l.reference ∈
      ((Context.plug (.left cs d r :: fs) l).labels lo).inorder := by
    simpa only [Context.plug, Context.referencePath, Pointer.offset_append, Pointer.offset,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using child
  obtain ⟨e, a, b, eq⟩ := Context.root_shape (.left cs d r :: fs) l lo nonempty retained
  rcases obsolete_shape fs cs d l r marks lo canonical absent with ⟨g, knuckle⟩ | ⟨g, knuckle⟩
  · rw [eq] at knuckle
    cases knuckle
  · exact ⟨e, a, b, g, eq, knuckle⟩

theorem obsolete_right_shape (fs : List ContextFrame) (cs : List Pointer.Frame) (d : Tendon.State)
    (l r : Hand) (marks : Finset Nat) (lo : Nat)
    (canonical : (Context.plug fs (.node cs d l r)).labels lo =
      compress (insert (lo + Pointer.offset (Context.referencePath fs) + Pointer.offset cs +
        l.reference.size) marks) (Context.plug fs (.node cs d l r)).reference lo)
    (absent : lo + Pointer.offset (Context.referencePath fs) + Pointer.offset cs + l.reference.size ∉
      (compress marks (Context.plug fs (.node cs d l r)).reference lo).inorder)
    (nonempty : r.reference ≠ .nil)
    (child : lo + Pointer.offset (Context.referencePath fs) + Pointer.offset cs + l.reference.size + 1 +
      rootRank r.reference ∈ ((Context.plug fs (.node cs d l r)).labels lo).inorder) :
    ∃ (g : Tree) (e : Tendon.State) (a b : Hand), l = .knuckle g ∧ r = .node [] e a b := by
  have retained : lo + Pointer.offset (Context.referencePath (.right cs d l :: fs)) + rootRank r.reference ∈
      ((Context.plug (.right cs d l :: fs) r).labels lo).inorder := by
    simpa only [Context.plug, Context.referencePath, Pointer.offset_append, Pointer.offset,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using child
  obtain ⟨e, a, b, eq⟩ := Context.root_shape (.right cs d l :: fs) r lo nonempty retained
  rcases obsolete_shape fs cs d l r marks lo canonical absent with ⟨g, knuckle⟩ | ⟨g, knuckle⟩
  · exact ⟨g, e, a, b, knuckle, eq⟩
  · rw [eq] at knuckle
    cases knuckle

end RotationBST.FingerHand.Hand
