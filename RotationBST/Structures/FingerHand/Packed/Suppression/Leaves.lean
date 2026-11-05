module

public import RotationBST.Structures.FingerHand.Packed.Suppression.Canonical
public import RotationBST.Structures.FingerHand.Packed.Updates.Shapes

@[expose] public section
namespace RotationBST.FingerHand.Hand

/-- Demote a leaf pseudofinger below a marked parent. Its entire physical
subtree becomes a knuckle without changing any pointer or any potential. -/
theorem demote_left (fs : List ContextFrame) (cs : List Pointer.Frame) (d : Tendon.State)
    (l r : Tree) (sibling : Hand) (marks : Finset Nat)
    (valid : (Context.plug fs (.node cs d (fork (.knuckle l) (.knuckle r)) sibling)).Valid)
    (parent : Pointer.offset (Context.referencePath fs) + Pointer.offset cs + (Tree.node l r).size ∈ marks) :
    let before := Context.plug fs (.node cs d (fork (.knuckle l) (.knuckle r)) sibling)
    let after := Context.plug fs (.node cs d (.knuckle (.node l r)) sibling)
    let key := Pointer.offset (Context.referencePath fs) + Pointer.offset cs + l.size
    after.Valid ∧ after.reference = before.reference ∧
      Suppress marks key (before.labels 0) (after.labels 0) ∧
      Pointer.Trace ⟨before.tree, []⟩ ⟨after.tree, []⟩ 0 ∧ after.potential = before.potential := by
  dsimp only
  obtain ⟨inside, outside⟩ := (Context.plug_valid_iff fs _).mp valid
  have target : (Hand.node cs d (.knuckle (.node l r)) sibling).Valid := ⟨inside.1, trivial, inside.2.2⟩
  refine ⟨Context.plug_valid outside target, ?_, ?_, ?_, ?_⟩
  · simp only [Context.plug_reference, Hand.reference, fork, Pointer.plug]
  · apply Context.suppress fs (by simp only [Hand.reference, fork, Pointer.plug]) 0
    simp only [labels, fork, Hand.reference, Pointer.plug, Pointer.offset, Nat.add_zero, Nat.zero_add]
    exact .leafLeft parent
  · have same : (Context.plug fs (.node cs d (fork (.knuckle l) (.knuckle r)) sibling)).tree =
        (Context.plug fs (.node cs d (.knuckle (.node l r)) sibling)).tree := by
      simp only [Context.plug_tree, tree, fork, empty_tendon_tree]
    rw [same]
    exact .refl
  · simp only [Context.plug_potential, potential, fork, empty_tendon_potential]

theorem demote_right (fs : List ContextFrame) (cs : List Pointer.Frame) (d : Tendon.State)
    (sibling : Hand) (l r : Tree) (marks : Finset Nat)
    (valid : (Context.plug fs (.node cs d sibling (fork (.knuckle l) (.knuckle r)))).Valid)
    (parent : Pointer.offset (Context.referencePath fs) + Pointer.offset cs + sibling.reference.size ∈ marks) :
    let before := Context.plug fs (.node cs d sibling (fork (.knuckle l) (.knuckle r)))
    let after := Context.plug fs (.node cs d sibling (.knuckle (.node l r)))
    let key := Pointer.offset (Context.referencePath fs) + Pointer.offset cs + sibling.reference.size + 1 + l.size
    after.Valid ∧ after.reference = before.reference ∧
      Suppress marks key (before.labels 0) (after.labels 0) ∧
      Pointer.Trace ⟨before.tree, []⟩ ⟨after.tree, []⟩ 0 ∧ after.potential = before.potential := by
  dsimp only
  obtain ⟨inside, outside⟩ := (Context.plug_valid_iff fs _).mp valid
  have target : (Hand.node cs d sibling (.knuckle (.node l r))).Valid := ⟨inside.1, inside.2.1, trivial⟩
  refine ⟨Context.plug_valid outside target, ?_, ?_, ?_, ?_⟩
  · simp only [Context.plug_reference, Hand.reference, fork, Pointer.plug]
  · apply Context.suppress fs (by simp only [Hand.reference, fork, Pointer.plug]) 0
    simp only [labels, fork, Hand.reference, Pointer.offset, Nat.add_zero, Nat.zero_add]
    exact .leafRight parent
  · have same : (Context.plug fs (.node cs d sibling (fork (.knuckle l) (.knuckle r)))).tree =
        (Context.plug fs (.node cs d sibling (.knuckle (.node l r)))).tree := by
      simp only [Context.plug_tree, tree, fork, empty_tendon_tree]
    rw [same]
    exact .refl
  · simp only [Context.plug_potential, potential, fork, empty_tendon_potential]

end RotationBST.FingerHand.Hand
