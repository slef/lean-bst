module

public import RotationBST.Structures.FingerHand.Packed.Updates.Definitions.Abstract
public import RotationBST.Structures.FingerHand.Packed.Invariant

@[expose] public section
namespace RotationBST.FingerHand.Hand

theorem empty_tendon_tree (t : Tree) : (Tendon.State.ofPath []).tree t = t := rfl
theorem empty_tendon_potential : (Tendon.State.ofPath []).potential = 0 := rfl

theorem graft_reference (cs : List Pointer.Frame) (d : Tendon.State) (f : Pointer.Frame) (h : Hand) :
    (graft cs d f h).reference = Pointer.plug cs (Pointer.plug [f] h.reference) := by
  cases f <;> rfl

theorem graft_tree (cs : List Pointer.Frame) (d : Tendon.State) (f : Pointer.Frame) (h : Hand) :
    (graft cs d f h).tree = d.tree (Pointer.plug [f] h.tree) := by
  cases f <;> rfl

theorem graft_potential (cs : List Pointer.Frame) (d : Tendon.State) (f : Pointer.Frame) (h : Hand) :
    (graft cs d f h).potential = d.potential + h.potential := by
  cases f <;> simp [graft, potential]

theorem graft_count (cs : List Pointer.Frame) (d : Tendon.State) (f : Pointer.Frame) (h : Hand) :
    (graft cs d f h).count = h.count + 1 := by
  cases f <;> simp [graft, count, Nat.add_comm]

theorem graft_valid {cs : List Pointer.Frame} {d : Tendon.State} (f : Pointer.Frame) {h : Hand}
    (tendon : d.Represents cs) (valid : h.Valid) : (graft cs d f h).Valid := by
  cases f <;> simp only [graft, Valid]
  · exact ⟨tendon, valid, trivial⟩
  · exact ⟨tendon, trivial, valid⟩

theorem graft_valid_iff (cs : List Pointer.Frame) (d : Tendon.State) (f : Pointer.Frame) (h : Hand) :
    (graft cs d f h).Valid ↔ d.Represents cs ∧ h.Valid := by
  cases f <;> simp [graft, Valid]

theorem top_reference (cs : List Pointer.Frame) (d e : Tendon.State) (f : Pointer.Frame) (l r : Hand) :
    (graft [] (Tendon.State.ofPath []) f (.node cs e l r)).reference =
      (Hand.node (cs ++ [f]) d l r).reference := by
  simp only [graft_reference, reference, Pointer.plug_append, Pointer.plug]

theorem bottom_reference (cs : List Pointer.Frame) (d e : Tendon.State) (f : Pointer.Frame) (l r : Hand) :
    (graft cs e f (.node [] (Tendon.State.ofPath []) l r)).reference =
      (Hand.node (f :: cs) d l r).reference := by
  cases f <;> rfl

theorem top_keys (cs : List Pointer.Frame) (d e : Tendon.State) (f : Pointer.Frame) (l r : Hand)
    (lo : Nat) : ((Hand.node (cs ++ [f]) d l r).labels lo).inorder.Sublist
      ((graft [] (Tendon.State.ofPath []) f (.node cs e l r)).labels lo).inorder := by
  cases f with
  | left g =>
    simp only [graft, labels, LabelledTree.inorder, Pointer.offset_append, Pointer.offset,
      Nat.add_zero]
    exact List.sublist_append_left _ _
  | right g =>
    simp only [graft, labels, LabelledTree.inorder, Pointer.offset_append, Pointer.offset,
      Nat.add_zero, Nat.zero_add, List.nil_append]
    have eq : lo + (Pointer.offset cs + (g.size + 1)) = lo + g.size + 1 + Pointer.offset cs := by omega
    rw [eq]
    exact (List.Sublist.refl _).cons _

theorem bottom_keys (cs : List Pointer.Frame) (d e : Tendon.State) (f : Pointer.Frame) (l r : Hand)
    (lo : Nat) : ((Hand.node (f :: cs) d l r).labels lo).inorder.Sublist
      ((graft cs e f (.node [] (Tendon.State.ofPath []) l r)).labels lo).inorder := by
  cases f with
  | left g =>
    simp only [graft, labels, LabelledTree.inorder, Pointer.offset, Nat.add_zero]
    exact List.sublist_append_left _ _
  | right g =>
    simp only [graft, labels, LabelledTree.inorder, Pointer.offset, Nat.add_zero, reference,
      List.nil_append]
    have eq : lo + (Pointer.offset cs + g.size + 1) = lo + Pointer.offset cs + g.size + 1 := by omega
    rw [eq]
    exact (List.Sublist.refl _).cons _

end RotationBST.FingerHand.Hand
