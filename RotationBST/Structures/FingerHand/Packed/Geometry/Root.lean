module

public import RotationBST.Structures.FingerHand.Packed.Geometry.Intervals
public import RotationBST.Structures.FingerHand.Packed.Updates.Shapes

@[expose] public section
namespace RotationBST.FingerHand.Hand

/-- A retained reference root is an exposed pseudofinger with no incoming
reference path. A hidden tendon vertex cannot have the same retained key. -/
theorem root_shape (h : Hand) (lo : Nat)
    (member : lo + rootRank h.reference ∈ (h.labels lo).inorder) :
    ∃ (d : Tendon.State) (l r : Hand), h = .node [] d l r := by
  cases h with
  | knuckle t => simp [labels, LabelledTree.inorder] at member
  | node cs d l r =>
    cases cs using List.reverseRecOn with
    | nil => exact ⟨d, l, r, rfl⟩
    | append_singleton cs f =>
      have bounds := node_labels_bounds (cs ++ [f]) d l r lo _ member
      have size := Pointer.offset_add_size_le_plug cs (.node l.reference r.reference)
      cases f <;>
        simp only [Hand.reference, Pointer.plug_append, Pointer.plug, rootRank,
          Pointer.offset_append, Pointer.offset, Nat.add_zero] at bounds <;> omega

/-- Normalize the stored representation of an already retained root without
changing the physical tree, potential, reference tree, or any labelled key. -/
theorem normalize_root (h : Hand) (valid : h.Valid) (lo : Nat)
    (member : lo + rootRank h.reference ∈ (h.labels lo).inorder) :
    ∃ (l r : Hand), (fork l r).Valid ∧ (fork l r).reference = h.reference ∧
      (fork l r).tree = h.tree ∧ (fork l r).potential = h.potential ∧
      ∀ base, (fork l r).labels base = h.labels base := by
  obtain ⟨d, l, r, rfl⟩ := root_shape h lo member
  have empty := Tendon.State.represents_empty valid.1
  refine ⟨l, r, ⟨Tendon.State.ofPath_represents [], valid.2⟩, rfl, ?_, ?_, fun _ => rfl⟩
  · change (Tendon.State.ofPath []).tree _ = d.tree _
    rw [empty_tendon_tree]
    simp only [Tendon.State.tree, empty.1, Pointer.plug]
  · simp only [fork, potential, empty_tendon_potential, empty.2]

/-- Global retention of a nonempty region's reference root forces that region
to expose its root. This applies in particular to either actual child of a
located pseudofinger. -/
theorem Context.root_shape (fs : List ContextFrame) (h : Hand) (lo : Nat)
    (nonempty : h.reference ≠ .nil)
    (member : lo + Pointer.offset (Context.referencePath fs) + rootRank h.reference ∈
      ((Context.plug fs h).labels lo).inorder) :
    ∃ (d : Tendon.State) (l r : Hand), h = .node [] d l r := by
  apply Hand.root_shape h (lo + Pointer.offset (Context.referencePath fs))
  apply Context.local_member fs h lo _ member (by omega)
  have bound : rootRank h.reference < h.reference.size := by
    cases eq : h.reference with
    | nil => exact False.elim (nonempty eq)
    | node l r => simp only [rootRank, Tree.size]; omega
  omega

end RotationBST.FingerHand.Hand
