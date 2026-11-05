module

public import RotationBST.Structures.FingerHand.Packed.Suppression.Canonical
public import RotationBST.Structures.FingerHand.Packed.Updates.Endpoints

@[expose] public section
namespace RotationBST.FingerHand.Hand

/-- Suppressing an exposed top endpoint deletes its root label and retains its
nonempty child skeleton. The existing tendon representation is updated in place. -/
theorem suppress_top_labels (cs : List Pointer.Frame) (d : Tendon.State) (f : Pointer.Frame)
    (l r : Hand) (marks : Finset Nat) (lo : Nat) :
    Suppress marks (lo + rootRank (graft [] (Tendon.State.ofPath []) f (.node cs d l r)).reference)
      ((graft [] (Tendon.State.ofPath []) f (.node cs d l r)).labels lo)
      ((Hand.node (cs ++ [f]) (d.addTop f) l r).labels lo) := by
  cases f <;>
    simp only [graft, labels, Hand.reference, rootRank, Pointer.plug, Pointer.offset_append, Pointer.offset,
      Nat.add_zero, Nat.zero_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  · exact .unaryLeft (by simp)
  · exact .unaryRight (by simp)

/-- Absorbing an exposed bottom parent likewise removes precisely one unary
vertex, while retaining the immediate child as the new tendon endpoint. -/
theorem suppress_bottom_labels (cs : List Pointer.Frame) (d : Tendon.State) (f : Pointer.Frame)
    (l r : Hand) (marks : Finset Nat) (lo : Nat) :
    Suppress marks (lo + Pointer.offset cs + rootRank (Pointer.plug [f] (.node l.reference r.reference)))
      ((graft cs d f (fork l r)).labels lo)
      ((Hand.node (f :: cs) (d.addBottom f) l r).labels lo) := by
  cases f <;>
    simp only [graft, fork, labels, Hand.reference, rootRank, Pointer.plug, Pointer.offset,
      Nat.zero_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  · exact .unaryLeft (by simp)
  · exact .unaryRight (by simp)

end RotationBST.FingerHand.Hand
