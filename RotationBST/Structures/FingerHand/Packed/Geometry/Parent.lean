module

public import RotationBST.Structures.FingerHand.Packed.Geometry.Intervals

@[expose] public section
namespace RotationBST.FingerHand.Hand

/-- The immediate reference parent of an endpoint is absent from the retained
skeleton whenever it lies inside the endpoint's incoming tendon. -/
theorem tendon_parent_absent (fs : List ContextFrame) (cs : List Pointer.Frame)
    (f : Pointer.Frame) (d : Tendon.State) (l r : Hand) (lo : Nat) :
    lo + Pointer.offset (Context.referencePath fs) + Pointer.offset cs +
        rootRank (Pointer.plug [f] (.node l.reference r.reference)) ∉
      ((Context.plug fs (.node (f :: cs) d l r)).labels lo).inorder := by
  intro member
  have size := Pointer.offset_add_size_le_plug cs (Pointer.plug [f] (.node l.reference r.reference))
  have inside := Context.local_member fs (.node (f :: cs) d l r) lo _ member
    (by cases f <;> simp only [Pointer.plug, rootRank] <;> omega)
    (by cases f <;> simp only [reference, Pointer.plug, rootRank, Tree.size] at size ⊢ <;> omega)
  have bounds := node_labels_bounds (f :: cs) d l r _ _ inside
  cases f <;> simp only [Pointer.offset, Pointer.plug, rootRank, Tree.size] at bounds <;> omega

/-- If a located pseudofinger's actual parent is retained, the incoming
reference tendon is empty; its parent is an enclosing hand vertex. -/
theorem retained_parent_path (fs : List ContextFrame) (cs : List Pointer.Frame)
    (d : Tendon.State) (l r : Hand) (lo : Nat) (f : Pointer.Frame) (anc : List Pointer.Frame)
    (path : cs ++ Context.referencePath fs = f :: anc)
    (member : lo + Pointer.offset anc + rootRank (Pointer.plug [f] (.node l.reference r.reference)) ∈
      ((Context.plug fs (.node cs d l r)).labels lo).inorder) : cs = [] := by
  cases cs with
  | nil => rfl
  | cons g cs =>
    simp only [List.cons_append, List.cons.injEq] at path
    obtain ⟨rfl, rfl⟩ := path
    apply False.elim
    apply tendon_parent_absent fs cs g d l r lo
    simpa only [Pointer.offset_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using member

end RotationBST.FingerHand.Hand
