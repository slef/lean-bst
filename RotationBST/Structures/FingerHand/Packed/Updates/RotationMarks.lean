module

public import RotationBST.Structures.FingerHand.Packed.Updates.Rotations
public import RotationBST.Structures.FingerHand.Packed.Pruning
public import RotationBST.Structures.FingerHand.Pruning.Rotations

@[expose] public section
namespace RotationBST.FingerHand.Hand

/-- A local exposed rotation whose two participating reference keys are marked
preserves exact canonicality, not just the set of retained keys. -/
theorem rotation_canonical {a b : Hand} (marks : Finset Nat) (lo : Nat)
    (rot : LabelledTree.Rotate (a.labels lo) (b.labels lo))
    (marked : MarkedRotation marks (a.reference.labelFrom lo) (b.reference.labelFrom lo))
    (canonical : a.labels lo = compress marks a.reference lo) :
    b.labels lo = compress marks b.reference lo := by
  have referenceKeys := Representation.Bridge.inorder_rotate marked.rotate
  have skeletonKeys := Representation.Bridge.inorder_rotate rot
  have covers : ∀ x ∈ (b.reference.labelFrom lo).inorder, x ∈ marks → x ∈ (b.labels lo).inorder := by
    intro x hx hm
    rw [← referenceKeys] at hx
    have member := marked_mem marks a.reference lo x hx hm
    rw [← canonical, skeletonKeys] at member
    exact member
  have projected := b.prune_labels marks lo covers
  have rotation := marked.project
  rw [prune_label, prune_label] at rotation
  have size := (Representation.Bridge.erase_rotate rotation).size_eq
  rw [← canonical, labels_size] at size
  have count := (Representation.Bridge.erase_rotate rot).size_eq
  simp only [labels_size] at count
  have equal : (b.labels lo).erase.size = (prune marks (b.labels lo)).erase.size := by
    rw [projected, labels_size]
    omega
  exact ((prune_contracts marks (b.labels lo)).eq_of_size equal).trans projected

theorem LocalRotation.canonical {a b : Hand} (rot : LocalRotation a b) (marks : Finset Nat) (lo : Nat)
    (marked : MarkedRotation marks (a.reference.labelFrom lo) (b.reference.labelFrom lo))
    (canonical : a.labels lo = compress marks a.reference lo) :
    b.labels lo = compress marks b.reference lo :=
  rotation_canonical marks lo (rot.labels lo) marked canonical

theorem marked_reference_right (cs : List Pointer.Frame) (d : Tendon.State) (a b c : Hand)
    (marks : Finset Nat) (lo : Nat)
    (lower : lo + Pointer.offset cs + a.reference.size ∈ marks)
    (upper : lo + Pointer.offset cs + a.reference.size + 1 + b.reference.size ∈ marks) :
    MarkedRotation marks ((Hand.node cs d (fork a b) c).reference.labelFrom lo)
      ((Hand.node cs d a (fork b c)).reference.labelFrom lo) := by
  apply MarkedRotation.under_path
  simp only [reference, fork, Pointer.plug, Tree.labelFrom, Tree.size, Nat.add_assoc]
  exact .right (by simpa only [Nat.add_assoc] using lower) (by simpa only [Nat.add_assoc] using upper)

theorem canonical_right (cs : List Pointer.Frame) (d : Tendon.State) (a b c : Hand)
    (marks : Finset Nat) (lo : Nat)
    (canonical : (Hand.node cs d (fork a b) c).labels lo =
      compress marks (Hand.node cs d (fork a b) c).reference lo)
    (lower : lo + Pointer.offset cs + a.reference.size ∈ marks)
    (upper : lo + Pointer.offset cs + a.reference.size + 1 + b.reference.size ∈ marks) :
    (Hand.node cs d a (fork b c)).labels lo =
      compress marks (Hand.node cs d a (fork b c)).reference lo :=
  (LocalRotation.right cs d a b c).canonical marks lo
    (marked_reference_right cs d a b c marks lo lower upper) canonical

theorem canonical_left (cs : List Pointer.Frame) (d : Tendon.State) (a b c : Hand)
    (marks : Finset Nat) (lo : Nat)
    (canonical : (Hand.node cs d a (fork b c)).labels lo =
      compress marks (Hand.node cs d a (fork b c)).reference lo)
    (lower : lo + Pointer.offset cs + a.reference.size ∈ marks)
    (upper : lo + Pointer.offset cs + a.reference.size + 1 + b.reference.size ∈ marks) :
    (Hand.node cs d (fork a b) c).labels lo =
      compress marks (Hand.node cs d (fork a b) c).reference lo :=
  (LocalRotation.left cs d a b c).canonical marks lo
    (marked_reference_right cs d a b c marks lo lower upper).symm canonical

end RotationBST.FingerHand.Hand
