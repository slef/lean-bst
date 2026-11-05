module

public import RotationBST.Structures.FingerHand.Packed.Construction
public import RotationBST.Structures.FingerHand.Pruning.Contraction

@[expose] public section
namespace RotationBST.FingerHand

theorem Contracts.under_path (cs : List Pointer.Frame) (t : Tree) (lo : Nat) {u : LabelledTree Nat}
    (h : Contracts (t.labelFrom (lo + Pointer.offset cs)) u) :
    Contracts ((Pointer.plug cs t).labelFrom lo) u := by
  induction cs generalizing t lo with
  | nil => simpa only [Pointer.plug, Pointer.offset, Nat.add_zero] using h
  | cons f cs ih =>
    cases f with
    | left g =>
      apply ih
      apply Contracts.left
      simpa only [Pointer.offset] using h
    | right g =>
      apply ih
      apply Contracts.right
      simpa only [Pointer.offset, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

namespace Hand

/-- The labelled hand is a contraction of the actual reference tree, even
before specifying which fingers or marks it must retain. -/
theorem labels_contracts (h : Hand) (lo : Nat) : Contracts (h.reference.labelFrom lo) (h.labels lo) := by
  induction h generalizing lo with
  | knuckle t => exact .empty _
  | node cs d l r il ir =>
    apply Contracts.under_path
    exact .node _ (il _) (ir _)

theorem labels_sublist (h : Hand) (lo : Nat) :
    (h.labels lo).inorder.Sublist (h.reference.labelFrom lo).inorder := (labels_contracts h lo).sublist

theorem labels_distinct (h : Hand) (lo : Nat) : (h.labels lo).inorder.Nodup := by
  apply List.Nodup.sublist (labels_sublist h lo)
  rw [Representation.Bridge.inorder_label]
  exact List.nodup_range'

/-- Retaining every requested mark suffices to compute its exact compressed
skeleton from the hand alone. No canonical deque state is assumed. -/
theorem prune_labels (h : Hand) (marks : Finset Nat) (lo : Nat)
    (covers : ∀ x ∈ (h.reference.labelFrom lo).inorder, x ∈ marks → x ∈ (h.labels lo).inorder) :
    prune marks (h.labels lo) = compress marks h.reference lo := by
  rw [← prune_label]
  apply (labels_contracts h lo).project marks _ covers
  rw [Representation.Bridge.inorder_label]
  exact List.nodup_range'

/-- Marking an already retained pseudofinger does not change the canonical
skeleton, including when that vertex was retained only because it branches. -/
theorem mark_retained (h : Hand) (marks : Finset Nat) (lo x : Nat)
    (canonical : h.labels lo = compress marks h.reference lo)
    (member : x ∈ (h.labels lo).inorder) :
    h.labels lo = compress (insert x marks) h.reference lo := by
  have projected := h.prune_labels (insert x marks) lo (by
    intro y hy hm
    rcases Finset.mem_insert.mp hm with rfl | hm
    · exact member
    · rw [canonical]
      exact marked_mem marks h.reference lo y hy hm)
  have retained := compress_submarks (Finset.subset_insert x marks) h.reference lo
  rw [← canonical] at retained
  have lower := retained.length_le
  simp only [Representation.Bridge.inorder_length] at lower
  have contraction := prune_contracts (insert x marks) (h.labels lo)
  have upper := contraction.size_le
  rw [projected] at upper
  have size : (h.labels lo).erase.size = (prune (insert x marks) (h.labels lo)).erase.size := by
    rw [projected]
    omega
  exact (contraction.eq_of_size size).trans projected

end Hand
end RotationBST.FingerHand
